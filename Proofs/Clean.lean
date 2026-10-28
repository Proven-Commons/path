import Proofs.Loop

/-!
  `cleanChars` is the stack on the elements of its input, written out
  as `render` writes elements. The facts about elements the statements
  need: how to split a path, and what splitting paths joined by a slash
  or written by `render` gives.
-/

namespace Spec.Proof

open Spec Path

theorem loop_elems (r : Bool) (es : List Element) (hne : es ≠ []) (hs : ∀ e ∈ es, '/' ∉ e) :
    ∀ acc out w dd, Rel r acc out w dd → StackOk r acc →
      ∃ out' w' dd', Rel r (es.foldl (push r) acc) out' w' dd' ∧
        loop r dd out w (List.intercalate ['/'] es) = (out', w') := by
  induction es with
  | nil => exact absurd rfl hne
  | cons e es ih =>
    intro acc out w dd h hacc
    obtain ⟨out1, w1, dd1, hrel, h1, h2⟩ := loop_elem r acc out w dd e (hs e (by simp)) h hacc
    cases es with
    | nil => exact ⟨out1, w1, dd1, hrel, by simpa using h1⟩
    | cons e' es =>
      rw [List.intercalate_cons_cons, List.append_assoc, List.singleton_append, h2,
        List.foldl_cons]
      exact ih (by simp) (fun e he => hs e (by simp [he])) _ _ _ _ hrel
        (stackOk_push r acc e hacc)

theorem rel_out (r : Bool) (acc : List Element) (out : List Char) (w dd : Nat)
    (h : Rel r acc out w dd) : out.reverse = buf r acc.reverse ∧ w = out.length := by
  obtain ⟨k, names, hacc, -, -, hout, hw, -⟩ := h
  exact ⟨by rw [hacc, hout], hw⟩

theorem shape_ne_nil (r : Bool) (es : List Element) (h : Shape r es) : ∀ e ∈ es, e ≠ [] := by
  obtain ⟨k, names, rfl, -, hnames⟩ := h
  intro e he
  rcases List.mem_append.mp he with he | he
  · rw [(List.mem_replicate.mp he).2]; exact dotdot_ne_nil
  · exact (hnames e he).1

theorem cleanChars_eq (p : List Char) (es : List Element) (h : Splits p es) :
    cleanChars p = render (Rooted p) (nf (Rooted p) es) := by
  obtain ⟨hne, hp, hs⟩ := h
  have hnf := shape_ne_nil _ _ (nf_shape (Rooted p) es)
  cases p with
  | nil =>
    -- the one element is empty
    have hes : es = [[]] := by
      match es, hne, hp with
      | [e], _, hp => simp at hp; rw [hp]
      | e :: e' :: es, _, hp => simp at hp
    subst hes
    simp [cleanChars, Rooted, nf, push_nil, render, dot]
  | cons c rest =>
    by_cases hc : c = '/'
    · subst hc
      -- the first element is the empty one before the root's slash
      match es, hne, hp, hs with
      | [e], _, hp, hs =>
        simp at hp
        exact absurd (by rw [← hp]; simp) (hs e (by simp))
      | e :: e' :: es, _, hp, hs =>
        rw [List.intercalate_cons_cons, List.append_assoc, List.singleton_append] at hp
        have he : e = [] := by
          cases e with
          | nil => rfl
          | cons d e =>
            simp only [List.cons_append, List.cons.injEq] at hp
            exact absurd (by rw [← hp.1]; simp) (hs (d :: e) (by simp))
        subst he
        simp only [List.nil_append, List.cons.injEq, true_and] at hp
        subst hp
        obtain ⟨out', w', dd', hrel, hloop⟩ := loop_elems true (e' :: es) (by simp)
          (fun x hx => hs x (by simp [hx])) [] ['/'] 1 1 (by simpa using rel_init true)
          (stackOk_nil true)
        obtain ⟨hout, hw⟩ := rel_out _ _ _ _ _ hrel
        have hroot : Rooted ('/' :: List.intercalate ['/'] (e' :: es)) = true := by
          simp [Rooted]
        rw [hroot]
        have hnfeq : nf true ([] :: e' :: es) = ((e' :: es).foldl (push true) []).reverse := by
          simp [nf, push_nil]
        have hw0 : (w' == 0) = false := by
          have : out'.length > 0 := by
            rw [← List.length_reverse, hout]; simp [buf]
          simp; omega
        simp only [cleanChars, beq_self_eq_true, ite_true, hloop, hw0, Bool.false_eq_true,
          ite_false]
        rw [hout, hnfeq]
        simp [buf, render]
    · have hroot : Rooted (c :: rest) = false := by simp [Rooted, hc]
      rw [hroot] at hnf ⊢
      obtain ⟨out', w', dd', hrel, hloop⟩ := loop_elems false es hne hs [] [] 0 0
        (by simpa using rel_init false) (stackOk_nil false)
      obtain ⟨hout, hw⟩ := rel_out _ _ _ _ _ hrel
      have hc' : (c == '/') = false := by simp [hc]
      simp only [cleanChars, hc', Bool.false_eq_true, ite_false]
      rw [hp, hloop]
      dsimp only
      have hnfeq : nf false es = (es.foldl (push false) []).reverse := rfl
      rw [hnfeq] at hnf ⊢
      by_cases hw0 : w' = 0
      · -- nothing is left
        have hout0 : out' = [] := by
          rw [hw] at hw0; exact List.length_eq_zero_iff.mp hw0
        rw [hout0] at hout
        have hempty : (es.foldl (push false) []).reverse = [] := by
          by_cases h0 : (es.foldl (push false) []).reverse = []
          · exact h0
          · exact absurd (by simpa [buf] using hout.symm) (intercalate_ne_nil _ h0 hnf)
        simp [hw0, hempty, render, dot]
      · have hw0' : (w' == 0) = false := by simp [hw0]
        rw [hw0', ite_eq_right (by simp)]
        have hne' : (es.foldl (push false) []).reverse ≠ [] := by
          intro h0
          rw [h0] at hout
          simp [buf] at hout
          exact hw0 (by rw [hw, ← List.length_reverse, hout]; rfl)
        rw [hout]
        simp [buf, render, hne']

/-! ### Splitting -/

/-- The elements of a path. -/
def elems : List Char → List Element
  | [] => [[]]
  | c :: cs =>
    if c = '/' then [] :: elems cs
    else match elems cs with
      | e :: es => (c :: e) :: es
      | [] => [[c]]

theorem elems_splits (p : List Char) : Splits p (elems p) := by
  induction p with
  | nil => exact ⟨by simp [elems], by simp [elems], by simp [elems]⟩
  | cons c cs ih =>
    obtain ⟨hne, hp, hs⟩ := ih
    obtain ⟨e, es, hee⟩ := List.exists_cons_of_ne_nil hne
    by_cases hc : c = '/'
    · subst hc
      refine ⟨by simp [elems], ?_, ?_⟩
      · simp only [elems, ite_true, hee]
        rw [List.intercalate_cons_cons, ← hee, ← hp]; simp
      · simp only [elems, ite_true, List.mem_cons]
        rintro x (rfl | hx)
        · simp
        · exact hs x hx
    · simp only [elems, hc, ite_false, hee]
      refine ⟨by simp, ?_, ?_⟩
      · rw [List.intercalate_cons_cons_left, ← hee, ← hp]
      · simp only [List.mem_cons]
        rintro x (rfl | hx)
        · simp only [List.mem_cons, not_or]
          exact ⟨fun h => hc h.symm, hs e (by simp [hee])⟩
        · exact hs x (by simp [hee, hx])

theorem splits_append (x y : List Char) (E F : List Element) (hx : Splits x E) (hy : Splits y F) :
    Splits (x ++ '/' :: y) (E ++ F) := by
  obtain ⟨hE, rfl, hEs⟩ := hx
  obtain ⟨hF, rfl, hFs⟩ := hy
  refine ⟨by simp [hE], (intercalate_append E F hE hF).symm, ?_⟩
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hEs e he
  · exact hFs e he

theorem rooted_append (x y : List Char) (hx : x ≠ []) : Rooted (x ++ y) = Rooted x := by
  obtain ⟨c, x, rfl⟩ := List.exists_cons_of_ne_nil hx
  simp [Rooted]

/-! ### What `render` writes -/

theorem push_foldl_nil (r : Bool) (acc es : List Element) :
    (([] : Element) :: es).foldl (push r) acc = es.foldl (push r) acc := by
  simp [push_nil]

/-- `render` writes elements that split back into themselves, with an
    empty element for the root and a `.` for an empty path, which the
    stack drops. -/
theorem splits_render (r : Bool) (E : List Element) (hE : ∀ e ∈ E, e ≠ [] ∧ '/' ∉ e) :
    ∃ S, Splits (render r E) S ∧ ∀ r' acc, S.foldl (push r') acc = E.foldl (push r') acc := by
  have hEs : ∀ e ∈ E, '/' ∉ e := fun e he => (hE e he).2
  cases r with
  | true =>
    by_cases h0 : E = []
    · subst h0
      refine ⟨[[], []], ⟨by simp, by simp [render], by simp⟩, fun r' acc => by simp [push_nil]⟩
    · refine ⟨[] :: E, ⟨by simp, ?_, ?_⟩, fun r' acc => push_foldl_nil r' acc E⟩
      · obtain ⟨e, E', rfl⟩ := List.exists_cons_of_ne_nil h0
        simp [render]
      · simp only [List.mem_cons]
        rintro x (rfl | hx)
        · simp
        · exact hEs x hx
  | false =>
    by_cases h0 : E = []
    · subst h0
      refine ⟨[dot], ⟨by simp, by simp [render, dot], by simp [dot]⟩,
        fun r' acc => by simp [push_dot]⟩
    · refine ⟨E, ⟨h0, by simp [render, h0], hEs⟩, fun _ _ => rfl⟩

theorem rooted_render (r : Bool) (E : List Element) (hE : ∀ e ∈ E, e ≠ [] ∧ '/' ∉ e) :
    Rooted (render r E) = r := by
  cases r with
  | true => simp [render, Rooted]
  | false =>
    by_cases h0 : E = []
    · simp [render, h0, Rooted, dot]
    · obtain ⟨e, E', rfl⟩ := List.exists_cons_of_ne_nil h0
      obtain ⟨he1, he2⟩ := hE e (by simp)
      obtain ⟨c, e', rfl⟩ := List.exists_cons_of_ne_nil he1
      have hc : c ≠ '/' := fun h => he2 (by simp [h])
      cases E' with
      | nil => simp [render, Rooted, hc]
      | cons e2 E'' => simp [render, Rooted, hc]

theorem normal_elems (r : Bool) (E : List Element) (hn : Normal r E) (hs : ∀ e ∈ E, '/' ∉ e) :
    ∀ e ∈ E, e ≠ [] ∧ '/' ∉ e :=
  fun e he => ⟨shape_ne_nil r E (shape_of_normal r E hn) e he, hs e he⟩

/-- Cleaning what `render` writes gives it back. -/
theorem cleanChars_render (r : Bool) (E : List Element) (hn : Normal r E)
    (hs : ∀ e ∈ E, '/' ∉ e) : cleanChars (render r E) = render r E := by
  have hE := normal_elems r E hn hs
  obtain ⟨S, hS, hfold⟩ := splits_render r E hE
  rw [cleanChars_eq _ _ hS, rooted_render r E hE]
  unfold nf
  rw [hfold r]
  exact congrArg (render r) (nf_of_normal r E hn)

/-! ### The stack keeps slash-free elements slash-free -/

theorem push_slashfree (r : Bool) (acc : List Element) (e : Element)
    (hacc : ∀ x ∈ acc, '/' ∉ x) (he : '/' ∉ e) : ∀ x ∈ push r acc e, '/' ∉ x := by
  intro x hx
  unfold push at hx
  split at hx
  · exact hacc x hx
  split at hx
  · split at hx
    · split at hx
      · simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp [dotdot]
        · exact hacc x (List.mem_cons.mpr hx)
      · exact hacc x (by simp [hx])
    · split at hx
      · simp at hx
      · simp only [List.mem_singleton] at hx; subst hx; simp [dotdot]
  · simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact he
    · exact hacc x hx

theorem nf_slashfree (r : Bool) (es : List Element) (hs : ∀ e ∈ es, '/' ∉ e) :
    ∀ x ∈ nf r es, '/' ∉ x := by
  have : ∀ acc, (∀ x ∈ acc, '/' ∉ x) → ∀ x ∈ es.foldl (push r) acc, '/' ∉ x := by
    induction es with
    | nil => intro acc h; exact h
    | cons e es ih =>
      intro acc h
      exact ih (fun x hx => hs x (by simp [hx])) _
        (push_slashfree r acc e h (hs e (by simp)))
  intro x hx
  exact this [] (by simp) x (List.mem_reverse.mp hx)

/-- `clean p` and its elements. -/
theorem clean_names' (p : String) :
    Names (Path.clean p) (Rooted p.toList) (nf (Rooted p.toList) (elems p.toList)) := by
  refine ⟨?_, nf_normal _ _, nf_slashfree _ _ (elems_splits _).2.2⟩
  rw [Path.clean, String.toList_ofList, cleanChars_eq _ _ (elems_splits _)]

end Spec.Proof
