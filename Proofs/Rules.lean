import Spec.Defs

/-!
  The rules on elements. `nf` applies them with a stack, left to
  right; every rule leaves `nf` unchanged, the rules lead from any
  elements to `nf` of them, and `nf` of elements to which no rule
  applies is those elements. So the rules end in one place, whatever
  their order.
-/

namespace Spec.Proof

open Spec

/-- A name: an element that is not empty, `.` or `..`. -/
def IsName (e : Element) : Prop := e ≠ [] ∧ e ≠ dot ∧ e ≠ dotdot

/-- One element of the stack. `acc` is the elements kept, last first. -/
def push (rooted : Bool) (acc : List Element) (e : Element) : List Element :=
  if e = [] ∨ e = dot then acc
  else if e = dotdot then
    match acc with
    | x :: acc' => if x = dotdot then dotdot :: acc else acc'
    | [] => if rooted then [] else [dotdot]
  else e :: acc

/-- The elements left by the stack. -/
def nf (rooted : Bool) (es : List Element) : List Element :=
  (es.foldl (push rooted) []).reverse

theorem dot_ne_nil : dot ≠ [] := by simp [dot]
theorem dotdot_ne_nil : dotdot ≠ [] := by simp [dotdot]
theorem dotdot_ne_dot : dotdot ≠ dot := by simp [dot, dotdot]

theorem push_nil (r : Bool) (acc : List Element) : push r acc [] = acc := by
  simp [push]

theorem push_dot (r : Bool) (acc : List Element) : push r acc dot = acc := by
  simp [push]

theorem push_name (r : Bool) (acc : List Element) (e : Element) (h : IsName e) :
    push r acc e = e :: acc := by
  obtain ⟨h1, h2, h3⟩ := h
  simp [push, h1, h2, h3]

theorem push_dotdot_cons (r : Bool) (x : Element) (acc : List Element) :
    push r (x :: acc) dotdot = if x = dotdot then dotdot :: x :: acc else acc := by
  simp [push, dotdot_ne_nil, dotdot_ne_dot]

theorem push_dotdot_nil (r : Bool) :
    push r [] dotdot = if r then [] else [dotdot] := by
  simp [push, dotdot_ne_nil, dotdot_ne_dot]

theorem foldl_names (r : Bool) (acc names : List Element) (h : ∀ e ∈ names, IsName e) :
    names.foldl (push r) acc = names.reverse ++ acc := by
  induction names generalizing acc with
  | nil => rfl
  | cons e names ih =>
    rw [List.foldl_cons, push_name r acc e (h e (by simp)),
      ih _ (fun e he => h e (by simp [he]))]
    simp

theorem foldl_dotdots (acc : List Element) (k : Nat) (hacc : ∀ x ∈ acc, x = dotdot) :
    (List.replicate k dotdot).foldl (push false) acc = List.replicate k dotdot ++ acc := by
  induction k generalizing acc with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.foldl_cons]
    have : push false acc dotdot = dotdot :: acc := by
      cases acc with
      | nil => simp [push_dotdot_nil]
      | cons x acc => simp [push_dotdot_cons, hacc x (by simp)]
    rw [this, ih _ (by
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with hx | hx
      · exact hx
      · exact hacc x hx)]
    rw [show List.replicate k dotdot ++ dotdot :: acc
        = (List.replicate k dotdot ++ [dotdot]) ++ acc by simp,
      ← List.replicate_succ', List.replicate_succ, List.cons_append]

/-! ### Each rule leaves `nf` unchanged -/

theorem step_foldl (r : Bool) (es es' : List Element) (h : Step r es es') :
    es.foldl (push r) [] = es'.foldl (push r) [] := by
  cases h with
  | empty xs ys => simp [List.foldl_append, push_nil]
  | dot xs ys => simp [List.foldl_append, push_dot]
  | parent xs e ys h1 h2 h3 =>
    simp only [List.foldl_append, List.foldl_cons]
    rw [push_name r _ e ⟨h1, h2, h3⟩, push_dotdot_cons]
    simp [h3]
  | root ys hr =>
    simp [List.foldl_cons, push_dotdot_nil, hr]

theorem steps_nf (r : Bool) (es es' : List Element) (h : Steps r es es') :
    nf r es = nf r es' := by
  induction h with
  | refl => rfl
  | step h _ ih => rw [← ih]; unfold nf; rw [step_foldl r _ _ h]

/-! ### The shape of elements to which no rule applies -/

/-- Some `..`, none if rooted, then names. -/
def Shape (rooted : Bool) (es : List Element) : Prop :=
  ∃ k names, es = List.replicate k dotdot ++ names ∧ (rooted = true → k = 0) ∧
    ∀ e ∈ names, IsName e

theorem normal_tail (r : Bool) (e : Element) (es : List Element) (h : Normal r (e :: es)) :
    Normal false es := by
  intro es' hs
  cases hs with
  | empty xs ys => exact h _ (Step.empty (e :: xs) ys)
  | dot xs ys => exact h _ (Step.dot (e :: xs) ys)
  | parent xs x ys h1 h2 h3 => exact h _ (Step.parent (e :: xs) x ys h1 h2 h3)
  | root ys hr => cases hr

theorem shape_of_normal (r : Bool) (es : List Element) (h : Normal r es) : Shape r es := by
  induction es generalizing r with
  | nil => exact ⟨0, [], rfl, fun _ => rfl, by simp⟩
  | cons e es ih =>
    obtain ⟨k, names, hes, -, hnames⟩ := ih false (normal_tail r e es h)
    have he1 : e ≠ [] := by
      rintro rfl; exact h _ (Step.empty [] es)
    have he2 : e ≠ dot := by
      rintro rfl; exact h _ (Step.dot [] es)
    by_cases he3 : e = dotdot
    · subst he3
      cases r with
      | true => exact absurd (Step.root es rfl) (h _)
      | false =>
        exact ⟨k + 1, names, by simp [hes, List.replicate_succ], by simp, hnames⟩
    · refine ⟨0, e :: names, ?_, fun _ => rfl, ?_⟩
      · cases k with
        | zero => simpa using hes
        | succ k =>
          exfalso
          rw [List.replicate_succ, List.cons_append] at hes
          subst hes
          exact h _ (Step.parent [] e _ he1 he2 he3)
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨he1, he2, he3⟩
        · exact hnames x hx

theorem normal_of_shape (r : Bool) (es : List Element) (h : Shape r es) : Normal r es := by
  obtain ⟨k, names, hes, hk, hnames⟩ := h
  intro es' hs
  have hdd : dotdot ∉ names := fun hm => (hnames _ hm).2.2 rfl
  have hrep : ∀ x ∈ List.replicate k dotdot, x = dotdot := fun x hx =>
    (List.mem_replicate.mp hx).2
  cases hs with
  | empty xs ys =>
    have : ([] : Element) ∈ List.replicate k dotdot ++ names := by
      rw [← hes]; simp
    rcases List.mem_append.mp this with hm | hm
    · exact dotdot_ne_nil (hrep _ hm).symm
    · exact (hnames _ hm).1 rfl
  | dot xs ys =>
    have : dot ∈ List.replicate k dotdot ++ names := by
      rw [← hes]; simp
    rcases List.mem_append.mp this with hm | hm
    · exact dotdot_ne_dot (hrep _ hm).symm
    · exact (hnames _ hm).2.1 rfl
  | parent xs e ys h1 h2 h3 =>
    rcases List.append_eq_append_iff.mp hes with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩
    · cases c with
      | nil =>
        simp only [List.nil_append] at hc2
        exact hdd (by rw [← hc2]; simp)
      | cons x c =>
        simp only [List.cons_append, List.cons.injEq] at hc2
        obtain ⟨rfl, -⟩ := hc2
        exact h3 (hrep e (by rw [hc1]; simp))
    · exact hdd (by rw [hc2]; simp)
  | root ys hr =>
    have : dotdot ∈ List.replicate k dotdot ++ names := by rw [← hes]; simp
    rw [hk hr] at this
    exact hdd (by simpa using this)

theorem normal_iff_shape (r : Bool) (es : List Element) : Normal r es ↔ Shape r es :=
  ⟨shape_of_normal r es, normal_of_shape r es⟩

/-! ### The stack: what it holds, and the rules lead to it -/

theorem Steps.trans {r : Bool} {a b c : List Element} (h1 : Steps r a b) (h2 : Steps r b c) :
    Steps r a c := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact Steps.step h (ih h2)

theorem Steps.single {r : Bool} {a b : List Element} (h : Step r a b) : Steps r a b :=
  Steps.step h (Steps.refl _)

/-- The stack, first element last, is in shape. -/
def StackOk (r : Bool) (acc : List Element) : Prop := Shape r acc.reverse

theorem stackOk_nil (r : Bool) : StackOk r [] := ⟨0, [], rfl, fun _ => rfl, by simp⟩

theorem stackOk_push (r : Bool) (acc : List Element) (e : Element) (h : StackOk r acc) :
    StackOk r (push r acc e) := by
  obtain ⟨k, names, hacc, hk, hnames⟩ := h
  by_cases h1 : e = [] ∨ e = dot
  · rcases h1 with rfl | rfl
    · rw [push_nil]; exact ⟨k, names, hacc, hk, hnames⟩
    · rw [push_dot]; exact ⟨k, names, hacc, hk, hnames⟩
  have hne : e ≠ [] ∧ e ≠ dot := by
    constructor <;> intro h <;> exact h1 (by simp [h])
  by_cases h2 : e = dotdot
  · subst h2
    -- the stack, last element first, is the names reversed, then the `..`
    have hacc' : acc = names.reverse ++ List.replicate k dotdot := by
      rw [← List.reverse_reverse acc, hacc]; simp
    cases hrev : names.reverse with
    | nil =>
      rw [List.reverse_eq_nil_iff] at hrev
      subst hrev
      cases k with
      | zero =>
        simp at hacc'
        subst hacc'
        rw [push_dotdot_nil]
        cases r
        · exact ⟨1, [], by simp, by simp, by simp⟩
        · exact ⟨0, [], by simp, by simp, by simp⟩
      | succ k =>
        simp [List.replicate_succ] at hacc'
        subst hacc'
        rw [push_dotdot_cons]
        simp only [ite_true]
        refine ⟨k + 2, [], ?_, ?_, by simp⟩
        · rw [List.append_nil,
            show dotdot :: dotdot :: List.replicate k dotdot = List.replicate (k + 2) dotdot
              from rfl, List.reverse_replicate]
        · intro hr; exact absurd (hk hr) (by simp)
    | cons x rest =>
      have hnames' : names = rest.reverse ++ [x] := by
        rw [← List.reverse_reverse names, hrev]; simp
      rw [hrev] at hacc'
      subst hacc'
      have hx : IsName x := hnames x (by simp [hnames'])
      rw [List.cons_append, push_dotdot_cons]
      simp only [hx.2.2, ite_false]
      refine ⟨k, rest.reverse, by simp, hk, fun e he => hnames e (by simp [hnames', he])⟩
  · rw [push_name r acc e ⟨hne.1, hne.2, h2⟩]
    refine ⟨k, names ++ [e], by simp [hacc], hk, ?_⟩
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hnames x hx
    · exact ⟨hne.1, hne.2, h2⟩

theorem stackOk_foldl (r : Bool) (acc es : List Element) (h : StackOk r acc) :
    StackOk r (es.foldl (push r) acc) := by
  induction es generalizing acc with
  | nil => exact h
  | cons e es ih => exact ih _ (stackOk_push r acc e h)

theorem nf_shape (r : Bool) (es : List Element) : Shape r (nf r es) :=
  stackOk_foldl r [] es (stackOk_nil r)

theorem nf_normal (r : Bool) (es : List Element) : Normal r (nf r es) :=
  normal_of_shape r _ (nf_shape r es)

/-- One element pushed is reached by at most one rule. -/
theorem steps_push (r : Bool) (acc : List Element) (e : Element) (ys : List Element)
    (h : StackOk r acc) :
    Steps r (acc.reverse ++ e :: ys) ((push r acc e).reverse ++ ys) := by
  obtain ⟨k, names, hacc, hk, hnames⟩ := h
  by_cases h1 : e = []
  · subst h1; rw [push_nil]; exact Steps.single (Step.empty _ _)
  by_cases h2 : e = dot
  · subst h2; rw [push_dot]; exact Steps.single (Step.dot _ _)
  by_cases h3 : e = dotdot
  · subst h3
    cases acc with
    | nil =>
      rw [push_dotdot_nil]
      cases r
      · simpa using Steps.refl (rooted := false) (dotdot :: ys)
      · simpa using Steps.single (Step.root (rooted := true) ys rfl)
    | cons x acc =>
      rw [push_dotdot_cons]
      by_cases hx : x = dotdot
      · subst hx; simp only [ite_true]; simpa using Steps.refl _
      · simp only [hx, ite_false]
        have hxn : IsName x := by
          have hm : x ∈ List.replicate k dotdot ++ names := by rw [← hacc]; simp
          rcases List.mem_append.mp hm with hm | hm
          · exact absurd (List.mem_replicate.mp hm).2 hx
          · exact hnames x hm
        simpa using Steps.single (Step.parent acc.reverse x ys hxn.1 hxn.2.1 hxn.2.2)
  · rw [push_name r acc e ⟨h1, h2, h3⟩]
    simpa using Steps.refl _

theorem steps_foldl (r : Bool) (acc es ys : List Element) (h : StackOk r acc) :
    Steps r (acc.reverse ++ es ++ ys) ((es.foldl (push r) acc).reverse ++ ys) := by
  induction es generalizing acc with
  | nil => simpa using Steps.refl _
  | cons e es ih =>
    rw [List.foldl_cons]
    have h1 := steps_push r acc e (es ++ ys) h
    have h2 := ih (push r acc e) (stackOk_push r acc e h)
    simp only [List.append_assoc, List.cons_append] at h1 h2 ⊢
    exact Steps.trans h1 h2

theorem steps_nf_self (r : Bool) (es : List Element) : Steps r es (nf r es) := by
  simpa [nf] using steps_foldl r [] es [] (stackOk_nil r)

theorem nf_of_shape (r : Bool) (es : List Element) (h : Shape r es) : nf r es = es := by
  obtain ⟨k, names, rfl, hk, hnames⟩ := h
  unfold nf
  rw [List.foldl_append]
  cases r with
  | false =>
    rw [foldl_dotdots [] k (by simp), foldl_names _ _ _ hnames]
    simp
  | true =>
    rw [hk rfl]
    simp [foldl_names _ _ _ hnames]

theorem nf_of_normal (r : Bool) (es : List Element) (h : Normal r es) : nf r es = es :=
  nf_of_shape r es (shape_of_normal r es h)

/-- Whatever order the rules are applied in, they end at `nf`. -/
theorem steps_normal_eq (r : Bool) (es es' : List Element) (h : Steps r es es')
    (hn : Normal r es') : es' = nf r es := by
  rw [steps_nf r es es' h, nf_of_normal r es' hn]

end Spec.Proof
