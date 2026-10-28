import Path
import Proofs.Rules

/-!
  The code against the stack of `Proofs/Rules.lean`. Go's loop reads
  the elements one by one, and after each its buffer holds the
  elements on the stack, with a slash between each two and one in
  front when the path is rooted. `dotdot` is the length of the `..`
  elements at the start of the buffer, or 1 for the root.
-/

namespace Spec.Proof

open Spec Path

/-- The buffer for the elements `es`, first first. -/
def buf (r : Bool) (es : List Element) : List Char :=
  if r then '/' :: List.intercalate ['/'] es else List.intercalate ['/'] es

/-- The state of Go's loop holds the stack `acc`. -/
def Rel (r : Bool) (acc : List Element) (out : List Char) (w dd : Nat) : Prop :=
  ∃ k names, acc.reverse = List.replicate k dotdot ++ names ∧ (r = true → k = 0) ∧
    (∀ e ∈ names, IsName e ∧ '/' ∉ e) ∧
    out.reverse = buf r (List.replicate k dotdot ++ names) ∧ w = out.length ∧
    dd = (buf r (List.replicate k dotdot)).length

theorem rel_init (r : Bool) :
    Rel r [] (if r then ['/'] else []) (if r then 1 else 0) (if r then 1 else 0) := by
  refine ⟨0, [], by simp, fun _ => rfl, by simp, ?_, ?_, ?_⟩ <;> cases r <;> simp [buf]

theorem intercalate_ne_nil (es : List Element) (h : es ≠ []) (hne : ∀ e ∈ es, e ≠ []) :
    List.intercalate ['/'] es ≠ [] := by
  cases es with
  | nil => exact absurd rfl h
  | cons e es =>
    have he := hne e (by simp)
    cases es with
    | nil => simpa using he
    | cons e' es => simp

theorem intercalate_snoc (es : List Element) (x : Element) (h : es ≠ []) :
    List.intercalate ['/'] (es ++ [x]) = List.intercalate ['/'] es ++ '/' :: x := by
  induction es with
  | nil => exact absurd rfl h
  | cons e es ih =>
    cases es with
    | nil => simp
    | cons e' es =>
      rw [List.cons_append, List.cons_append, List.intercalate_cons_cons,
        List.intercalate_cons_cons, ← List.cons_append, ih (by simp)]
      simp

theorem buf_snoc (r : Bool) (es : List Element) (x : Element) (h : es ≠ []) :
    buf r (es ++ [x]) = buf r es ++ '/' :: x := by
  cases r <;> simp [buf, intercalate_snoc es x h]

theorem buf_single (r : Bool) (x : Element) :
    buf r [x] = (if r then ['/'] else []) ++ x := by
  cases r <;> simp [buf]

theorem buf_nil (r : Bool) : buf r [] = if r then ['/'] else [] := by
  cases r <;> simp [buf]

theorem intercalate_append (es fs : List Element) (h1 : es ≠ []) (h2 : fs ≠ []) :
    List.intercalate ['/'] (es ++ fs) =
      List.intercalate ['/'] es ++ '/' :: List.intercalate ['/'] fs := by
  induction es with
  | nil => exact absurd rfl h1
  | cons e es ih =>
    cases es with
    | nil =>
      cases fs with
      | nil => exact absurd rfl h2
      | cons f fs => simp
    | cons e' es =>
      rw [List.cons_append, List.cons_append, List.intercalate_cons_cons,
        List.intercalate_cons_cons, ← List.cons_append, ih (by simp)]
      simp

theorem buf_prefix_length (r : Bool) (es fs : List Element) :
    (buf r es).length ≤ (buf r (es ++ fs)).length := by
  by_cases h1 : es = []
  · subst h1; cases r <;> simp [buf]
  by_cases h2 : fs = []
  · subst h2; simp
  cases r <;> simp [buf, intercalate_append es fs h1 h2]

/-! ### `backtrack` -/

theorem backtrack_sep (dd : Nat) (pre : List Char) (hpre : dd ≤ pre.length) :
    ∀ xr : List Char, (∀ c ∈ xr, c ≠ '/') →
      backtrack dd (xr ++ '/' :: pre) (pre.length + 1 + xr.length) = (pre, pre.length) := by
  intro xr hxr
  induction xr with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.add_zero]
    rw [backtrack.eq_1]
    simp
  | cons c xr ih =>
    rw [List.cons_append, List.length_cons, show pre.length + 1 + (xr.length + 1)
      = (pre.length + 1 + xr.length) + 1 by omega, backtrack.eq_1]
    rw [ite_eq_left ⟨by omega, hxr c (by simp)⟩]
    exact ih (fun c hc => hxr c (by simp [hc]))

theorem backtrack_first (pre : List Char) :
    ∀ xr : List Char, xr ≠ [] → (∀ c ∈ xr, c ≠ '/') →
      backtrack pre.length (xr ++ pre) (pre.length + xr.length) = (pre, pre.length) := by
  intro xr hne hxr
  induction xr with
  | nil => exact absurd rfl hne
  | cons c xr ih =>
    rw [List.cons_append, List.length_cons, ← Nat.add_assoc, backtrack.eq_1]
    cases xr with
    | nil => simp
    | cons c' xr =>
      rw [ite_eq_left ⟨by simp, hxr c (by simp)⟩]
      exact ih (by simp) (fun c hc => hxr c (by simp [hc]))

/-! ### One element -/

theorem names_snoc (k : Nat) (names : List Element) (acc : List Element) (x : Element)
    (hx : x ≠ dotdot) (h : (x :: acc).reverse = List.replicate k dotdot ++ names) :
    ∃ names', names = names' ++ [x] ∧ acc.reverse = List.replicate k dotdot ++ names' := by
  cases hn : names.reverse with
  | nil =>
    rw [List.reverse_eq_nil_iff] at hn
    subst hn
    rw [List.append_nil, List.reverse_cons] at h
    cases k with
    | zero => simp at h
    | succ k =>
      rw [List.replicate_succ'] at h
      exact absurd (List.append_inj_right' h rfl) (by simp [hx])
  | cons y rest =>
    have hnames : names = rest.reverse ++ [y] := by
      rw [← List.reverse_reverse names, hn]; simp
    subst hnames
    rw [List.reverse_cons, ← List.append_assoc] at h
    obtain ⟨h1, h2⟩ := List.append_inj' h rfl
    simp only [List.cons.injEq, and_true] at h2
    subst h2
    exact ⟨rest.reverse, rfl, h1⟩

theorem rel_parent_name (r : Bool) (acc : List Element) (x : Element) (out : List Char)
    (w dd : Nat) (hx : IsName x) (h : Rel r (x :: acc) out w dd) :
    ∃ out' w', parent r dd out w = (out', w', dd) ∧ Rel r acc out' w' dd := by
  obtain ⟨k, names, hacc, hk, hnames, hout, hw, hdd⟩ := h
  obtain ⟨names', rfl, hacc'⟩ := names_snoc k names acc x hx.2.2 hacc
  have hxs : '/' ∉ x := (hnames x (by simp)).2
  have hxr : ∀ c ∈ x.reverse, c ≠ '/' := fun c hc h => hxs (h ▸ List.mem_reverse.mp hc)
  have hxne : x.reverse ≠ [] := by simpa using hx.1
  have hnames' : ∀ e ∈ names', IsName e ∧ '/' ∉ e := fun e he => hnames e (by simp [he])
  refine ⟨(buf r (List.replicate k dotdot ++ names')).reverse,
    (buf r (List.replicate k dotdot ++ names')).length, ?_,
    ⟨k, names', hacc', hk, hnames', by simp, by simp, hdd⟩⟩
  rw [← List.append_assoc] at hout
  by_cases hL : List.replicate k dotdot ++ names' = []
  · -- `x` is the first element: the buffer is the root, or empty, and then `x`
    have hk0 : k = 0 := by simpa using (List.append_eq_nil_iff.mp hL).1
    subst hk0
    rw [hL, List.nil_append, buf_single] at hout
    rw [hL]
    have hout' : out = x.reverse ++ (buf r []).reverse := by
      rw [← List.reverse_reverse out, hout, buf_nil]; simp
    have hdd' : dd = (buf r []).reverse.length := by rw [hdd]; simp
    have hw' : w = (buf r []).reverse.length + x.reverse.length := by
      rw [hw, hout']; simp; omega
    unfold parent
    rw [ite_eq_left (by rw [hw', hdd']; simp; exact List.length_pos_iff.mpr hx.1), hout', hw', hdd',
      backtrack_first _ _ hxne hxr]
    simp
  · rw [buf_snoc r _ x hL] at hout
    have hout' : out = x.reverse ++ '/' :: (buf r (List.replicate k dotdot ++ names')).reverse := by
      rw [← List.reverse_reverse out, hout]; simp
    have hle : dd ≤ (buf r (List.replicate k dotdot ++ names')).reverse.length := by
      rw [hdd, List.length_reverse]; exact buf_prefix_length r _ _
    have hw' : w = (buf r (List.replicate k dotdot ++ names')).reverse.length + 1 + x.reverse.length := by
      rw [hw, hout']; simp; omega
    unfold parent
    rw [ite_eq_left (by omega), hout', hw', backtrack_sep dd _ hle _ hxr]
    simp

/-- A path that is not rooted, with only `..` on the stack, keeps one more. -/
theorem rel_parent_dotdots (k : Nat) (out : List Char) (w dd : Nat)
    (h : Rel false (List.replicate k dotdot) out w dd) :
    ∃ out' w', parent false dd out w = (out', w', w') ∧
      Rel false (dotdot :: List.replicate k dotdot) out' w' w' := by
  obtain ⟨k', names, hacc, -, hnames, hout, hw, hdd⟩ := h
  rw [List.reverse_replicate] at hacc
  have hnames0 : names = [] := by
    cases names with
    | nil => rfl
    | cons e names =>
      have hm : e ∈ List.replicate k dotdot := by rw [hacc]; simp
      exact absurd (List.mem_replicate.mp hm).2 (hnames e (by simp)).1.2.2
  subst hnames0
  rw [List.append_nil] at hacc
  have hk : k' = k := by simpa using (congrArg List.length hacc).symm
  subst hk
  rw [List.append_nil] at hout
  have hwdd : w = dd := by rw [hw, hdd, ← List.length_reverse, hout]
  have hpos : (w > 0) = (k' > 0) := by
    rw [hw, ← List.length_reverse, hout]
    cases k' with
    | zero => simp [buf]
    | succ k =>
      simp only [buf, Bool.false_eq_true, ite_false, gt_iff_lt, Nat.zero_lt_succ, iff_true,
        eq_iff_iff]
      exact List.length_pos_iff.mpr
        (intercalate_ne_nil _ (by simp) (fun e he => by
          rw [(List.mem_replicate.mp he).2]; exact dotdot_ne_nil))
  unfold parent
  rw [ite_eq_right (by omega)]
  simp only [Bool.not_false, ite_true]
  by_cases hk0 : k' = 0
  · subst hk0
    have hw0 : ¬ w > 0 := by simp [hpos]
    have hout0 : out = [] := by rw [← List.reverse_reverse out, hout]; simp [buf]
    subst hout0
    simp only [hw0, ite_false]
    refine ⟨_, _, rfl, 1, [], by simp, by simp, by simp, by simp [buf, dotdot], by simp [hw],
      by simp [buf, dotdot, hw]⟩
  · have hw0 : w > 0 := by rw [hpos]; omega
    simp only [hw0, ite_true]
    have hbuf : ('.' :: '.' :: '/' :: out).reverse = buf false (List.replicate (k' + 1) dotdot) := by
      rw [List.replicate_succ', buf_snoc false _ _ (by simpa using hk0)]
      simp [hout, dotdot]
    refine ⟨_, _, rfl, k' + 1, [], by simp [List.replicate_succ'], by simp, by simp,
      by simpa using hbuf, by simp [hw], ?_⟩
    rw [← hbuf]; simp [hw]

/-- The copy of a name, up to the next slash. -/
theorem copy_name (r : Bool) (dd : Nat) (cs : List Char) (hcs : '/' ∉ cs) :
    ∀ out w, copy r dd out w cs = (cs.reverse ++ out, w + cs.length) ∧
      ∀ rest, copy r dd out w (cs ++ '/' :: rest) =
        loop r dd (cs.reverse ++ out) (w + cs.length) rest := by
  induction cs with
  | nil =>
    intro out w
    refine ⟨by rw [copy.eq_1]; simp, fun rest => ?_⟩
    rw [List.nil_append, copy.eq_2]; simp
  | cons c cs ih =>
    intro out w
    have hc : c ≠ '/' := fun h => hcs (by simp [h])
    have hcs' : '/' ∉ cs := fun h => hcs (by simp [h])
    obtain ⟨ih1, ih2⟩ := ih hcs' (c :: out) (w + 1)
    refine ⟨?_, fun rest => ?_⟩
    · rw [copy.eq_3 _ _ _ _ _ _ hc, ih1]; simp; omega
    · rw [List.cons_append, copy.eq_3 _ _ _ _ _ _ hc, ih2 rest]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons]
      rw [show w + 1 + cs.length = w + (cs.length + 1) by omega]

/-- `loop` on a name starts its copy. -/
theorem loop_name (r : Bool) (dd : Nat) (out : List Char) (w : Nat) (c : Char) (cs t : List Char)
    (hn : IsName (c :: cs)) (hs : '/' ∉ c :: cs) (ht : t = [] ∨ ∃ rest, t = '/' :: rest) :
    loop r dd out w (c :: (cs ++ t)) =
      (let (out, w) :=
        if (r && w != 1 || !r && w != 0) = true then ('/' :: out, w + 1) else (out, w)
      copy r dd (c :: out) (w + 1) (cs ++ t)) := by
  obtain ⟨hn1, hn2, hn3⟩ := hn
  have hc : c ≠ '/' := fun h => hs (by simp [h])
  rw [loop.eq_7]
  · exact fun h => hc h
  · intro h1 h2
    subst h1
    rcases List.append_eq_nil_iff.mp h2 with ⟨rfl, -⟩
    exact hn2 rfl
  · intro tail h1 h2
    subst h1
    cases cs with
    | nil =>
      exact hn2 rfl
    | cons c2 cs =>
      simp only [List.cons_append, List.cons.injEq] at h2
      exact hs (by simp [h2.1])
  · intro h1 h2
    subst h1
    cases cs with
    | nil =>
      simp only [List.nil_append] at h2
      rcases ht with rfl | ⟨rest, rfl⟩ <;> simp at h2
    | cons c2 cs =>
      simp only [List.cons_append, List.cons.injEq, List.append_eq_nil_iff] at h2
      obtain ⟨rfl, rfl, -⟩ := h2
      exact hn3 rfl
  · intro tail h1 h2
    subst h1
    cases cs with
    | nil =>
      simp only [List.nil_append] at h2
      rcases ht with rfl | ⟨rest, rfl⟩ <;> simp at h2
    | cons c2 cs =>
      simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, h2⟩ := h2
      cases cs with
      | nil =>
        exact hn3 rfl
      | cons c3 cs =>
        simp only [List.cons_append, List.cons.injEq] at h2
        exact hs (by simp [h2.1])

theorem rel_name (r : Bool) (acc : List Element) (out : List Char) (w dd : Nat)
    (e : Element) (hn : IsName e) (hs : '/' ∉ e) (h : Rel r acc out w dd)
    (out1 : List Char) (w1 : Nat)
    (hc : (if (r && w != 1 || !r && w != 0) = true then ('/' :: out, w + 1) else (out, w))
      = (out1, w1)) :
    Rel r (e :: acc) (e.reverse ++ out1) (w1 + e.length) dd := by
  obtain ⟨k, names, hacc, hk, hnames, hout, hw, hdd⟩ := h
  have hw1 : w1 = out1.length := by
    split at hc <;> simp only [Prod.mk.injEq] at hc <;> obtain ⟨rfl, rfl⟩ := hc <;> simp [hw]
  refine ⟨k, names ++ [e], by simp [hacc], hk, ?_, ?_, by simp [hw1, Nat.add_comm], hdd⟩
  · intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hnames x hx
    · exact ⟨hn, hs⟩
  · rw [← List.append_assoc]
    by_cases hL : List.replicate k dotdot ++ names = []
    · rw [hL, List.nil_append, buf_single]
      rw [hL, buf_nil] at hout
      have hw' : w = if r then 1 else 0 := by
        rw [hw, ← List.length_reverse, hout]; cases r <;> simp
      have : out1 = out := by
        cases r <;> simp [hw'] at hc <;> exact hc.1.symm
      rw [this]; simp [hout]
    · rw [buf_snoc r _ e hL]
      have hne : ∀ x ∈ List.replicate k dotdot ++ names, x ≠ [] := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · rw [(List.mem_replicate.mp hx).2]; exact dotdot_ne_nil
        · exact (hnames x hx).1.1
      have hI := List.length_pos_iff.mpr (intercalate_ne_nil _ hL hne)
      have hw' : w = (buf r (List.replicate k dotdot ++ names)).length := by
        rw [hw, ← List.length_reverse, hout]
      have : out1 = '/' :: out := by
        have hcond : (r && w != 1 || !r && w != 0) = true := by
          cases r <;> simp [buf] at hw' ⊢ <;> omega
        rw [ite_eq_left hcond] at hc
        simp only [Prod.mk.injEq] at hc
        exact hc.1.symm
      rw [this]; simp [hout]

/-- The top of the stack is `..` only when the path is not rooted and
    the whole stack is `..`. -/
theorem rel_top_dotdot (r : Bool) (acc : List Element) (out : List Char) (w dd : Nat)
    (h : Rel r (dotdot :: acc) out w dd) :
    r = false ∧ ∃ k, dotdot :: acc = List.replicate k dotdot := by
  obtain ⟨k, names, hacc, hk, hnames, -⟩ := h
  have hn : names = [] := by
    cases hrev : names.reverse with
    | nil => simpa using hrev
    | cons y rest =>
      have hnames' : names = rest.reverse ++ [y] := by
        rw [← List.reverse_reverse names, hrev]; simp
      subst hnames'
      rw [List.reverse_cons, ← List.append_assoc] at hacc
      obtain ⟨-, h2⟩ := List.append_inj' hacc rfl
      simp only [List.cons.injEq, and_true] at h2
      subst h2
      exact absurd rfl (hnames dotdot (by simp)).1.2.2
  subst hn
  rw [List.append_nil] at hacc
  have hacc2 : dotdot :: acc = List.replicate k dotdot := by
    rw [← List.reverse_reverse (dotdot :: acc), hacc, List.reverse_replicate]
  refine ⟨?_, k, hacc2⟩
  cases r with
  | false => rfl
  | true =>
    have := hk rfl
    subst this
    simp at hacc2

/-- Go's loop on one element, at the end or followed by a slash. -/
theorem loop_elem (r : Bool) (acc : List Element) (out : List Char) (w dd : Nat)
    (e : Element) (hs : '/' ∉ e) (h : Rel r acc out w dd) (hacc : StackOk r acc) :
    ∃ out' w' dd', Rel r (push r acc e) out' w' dd' ∧
      loop r dd out w e = (out', w') ∧
      ∀ rest, loop r dd out w (e ++ '/' :: rest) = loop r dd' out' w' rest := by
  by_cases h1 : e = []
  · subst h1
    refine ⟨out, w, dd, by rw [push_nil]; exact h, by rw [loop.eq_1], fun rest => ?_⟩
    rw [List.nil_append, loop.eq_2]
  by_cases h2 : e = dot
  · subst h2
    refine ⟨out, w, dd, by rw [push_dot]; exact h, by simp [dot, loop.eq_3], fun rest => ?_⟩
    simp only [dot, List.cons_append, List.nil_append]
    rw [loop.eq_4, loop.eq_2]
  by_cases h3 : e = dotdot
  · subst h3
    -- what `parent` does, with the stack it leaves
    have hp : ∃ out' w' dd', parent r dd out w = (out', w', dd') ∧
        Rel r (push r acc dotdot) out' w' dd' := by
      cases acc with
      | nil =>
        rw [push_dotdot_nil]
        cases r with
        | false =>
          obtain ⟨out', w', hp, hrel⟩ := rel_parent_dotdots 0 out w dd (by simpa using h)
          exact ⟨out', w', w', hp, by simpa using hrel⟩
        | true =>
          obtain ⟨k, names, hacc', hk, -, hout, hw, hdd⟩ := h
          have hk0 := hk rfl
          subst hk0
          have hn0 : names = [] := by simpa using hacc'.symm
          subst hn0
          refine ⟨out, w, dd, ?_, ⟨0, [], by simp, fun _ => rfl, by simp, hout, hw, hdd⟩⟩
          have : w = dd := by rw [hw, hdd, ← List.length_reverse, hout]; simp
          unfold parent
          simp [this]
      | cons x acc =>
        rw [push_dotdot_cons]
        by_cases hx : x = dotdot
        · subst hx
          simp only [ite_true]
          -- the whole stack is `..`
          obtain ⟨hr, k, hk⟩ := rel_top_dotdot r acc out w dd h
          subst hr
          rw [hk] at h ⊢
          obtain ⟨out', w', hp, hrel⟩ := rel_parent_dotdots k out w dd h
          exact ⟨out', w', w', hp, hrel⟩
        · simp only [hx, ite_false]
          have hxn : IsName x := by
            obtain ⟨k, names, hacc', -, hnames, -⟩ := h
            have hm : x ∈ List.replicate k dotdot ++ names := by rw [← hacc']; simp
            rcases List.mem_append.mp hm with hm | hm
            · exact absurd (List.mem_replicate.mp hm).2 hx
            · exact (hnames x hm).1
          obtain ⟨out', w', hp, hrel⟩ := rel_parent_name r acc x out w dd hxn h
          exact ⟨out', w', dd, hp, hrel⟩
    obtain ⟨out', w', dd', hp, hrel⟩ := hp
    refine ⟨out', w', dd', hrel, ?_, fun rest => ?_⟩
    · simp only [dotdot]; rw [loop.eq_5, hp]
    · simp only [dotdot, List.cons_append, List.nil_append]
      rw [loop.eq_6, hp]
      simp only
      rw [loop.eq_2]
  · -- a name
    have hn : IsName e := ⟨h1, h2, h3⟩
    obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil h1
    have hcs : '/' ∉ cs := fun h => hs (by simp [h])
    obtain ⟨out1, w1, hc⟩ : ∃ out1 w1,
        (if (r && w != 1 || !r && w != 0) = true then ('/' :: out, w + 1) else (out, w))
          = (out1, w1) := ⟨_, _, rfl⟩
    have hrel := rel_name r acc out w dd (c :: cs) hn hs h out1 w1 hc
    refine ⟨(c :: cs).reverse ++ out1, w1 + (c :: cs).length, dd,
      by rw [push_name r acc _ hn]; exact hrel, ?_, fun rest => ?_⟩
    · have := loop_name r dd out w c cs [] hn hs (Or.inl rfl)
      rw [List.append_nil] at this
      rw [this, hc]
      dsimp only
      rw [(copy_name r dd cs hcs _ _).1]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons]
      rw [show w1 + 1 + cs.length = w1 + (cs.length + 1) by omega]
    · have := loop_name r dd out w c cs ('/' :: rest) hn hs (Or.inr ⟨rest, rfl⟩)
      rw [List.cons_append, this, hc]
      dsimp only
      rw [(copy_name r dd cs hcs _ _).2 rest]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons]
      rw [show w1 + 1 + cs.length = w1 + (cs.length + 1) by omega]

end Spec.Proof
