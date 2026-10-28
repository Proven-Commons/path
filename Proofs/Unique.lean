import Proofs.Join

/-!
  A path splits into one list of elements, and a path names one list of
  elements; the rules only drop elements, so they keep them free of
  slashes.
-/

namespace Spec.Proof

open Spec Path

/-- Two slash-free elements, each followed by nothing or by a slash, are
    the same element when the whole strings are. -/
theorem slash_prefix (e f X Y : List Char) (he : '/' ∉ e) (hf : '/' ∉ f)
    (hX : X = [] ∨ X.head? = some '/') (hY : Y = [] ∨ Y.head? = some '/')
    (h : e ++ X = f ++ Y) : e = f ∧ X = Y := by
  induction e generalizing f with
  | nil =>
    cases f with
    | nil => simpa using h
    | cons c f =>
      exfalso
      simp only [List.nil_append, List.cons_append] at h
      subst h
      rcases hX with hX | hX
      · simp at hX
      · simp only [List.head?_cons, Option.some.injEq] at hX
        exact hf (by simp [hX])
  | cons c e ih =>
    cases f with
    | nil =>
      exfalso
      simp only [List.nil_append, List.cons_append] at h
      subst h
      rcases hY with hY | hY
      · simp at hY
      · simp only [List.head?_cons, Option.some.injEq] at hY
        exact he (by simp [hY])
    | cons c' f =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨h1, h2⟩ := ih f (fun h => he (by simp [h])) (fun h => hf (by simp [h])) h
      exact ⟨by rw [h1], h2⟩

/-- What follows the first element: nothing, or a slash and the rest. -/
def after (E : List Element) : List Char :=
  match E with
  | [] => []
  | _ :: _ => '/' :: List.intercalate ['/'] E

theorem intercalate_cons (e : Element) (E : List Element) :
    List.intercalate ['/'] (e :: E) = e ++ after E := by
  cases E with
  | nil => simp [after]
  | cons e' E => simp [after, List.intercalate_cons_cons]

theorem after_slash (E : List Element) : after E = [] ∨ (after E).head? = some '/' := by
  cases E <;> simp [after]

theorem splits_unique (p : List Char) (E F : List Element) (hE : Splits p E)
    (hF : Splits p F) : E = F := by
  induction E generalizing p F with
  | nil => exact absurd rfl hE.1
  | cons e E ih =>
    obtain ⟨-, hp, hs⟩ := hE
    obtain ⟨hF0, hq, ht⟩ := hF
    obtain ⟨f, F, rfl⟩ := List.exists_cons_of_ne_nil hF0
    rw [intercalate_cons] at hp hq
    obtain ⟨rfl, hrest⟩ := slash_prefix e f _ _ (hs e (by simp)) (ht f (by simp))
      (after_slash E) (after_slash F) (hp.symm.trans hq)
    cases E with
    | nil =>
      cases F with
      | nil => rfl
      | cons f' F => simp [after] at hrest
    | cons e' E =>
      cases F with
      | nil => simp [after] at hrest
      | cons f' F =>
        simp only [after, List.cons.injEq, true_and] at hrest
        rw [ih (List.intercalate ['/'] (e' :: E)) (f' :: F)
          ⟨by simp, rfl, fun x hx => hs x (by simp [hx])⟩
          ⟨by simp, hrest, fun x hx => ht x (by simp [hx])⟩]

/-- The elements `render` writes, split back: an empty element for the
    root, and `.` for nothing. -/
def rsplit (r : Bool) (E : List Element) : List Element :=
  if r then [] :: (if E = [] then [[]] else E) else if E = [] then [dot] else E

theorem splits_rsplit (r : Bool) (E : List Element) (hE : ∀ e ∈ E, e ≠ [] ∧ '/' ∉ e) :
    Splits (render r E) (rsplit r E) := by
  have hEs : ∀ e ∈ E, '/' ∉ e := fun e he => (hE e he).2
  cases r with
  | true =>
    by_cases h0 : E = []
    · subst h0; exact ⟨by simp [rsplit], by simp [render, rsplit], by simp [rsplit]⟩
    · refine ⟨by simp [rsplit], ?_, ?_⟩
      · obtain ⟨e, E', rfl⟩ := List.exists_cons_of_ne_nil h0
        simp [render, rsplit]
      · simp only [rsplit, ite_true, h0, ite_false, List.mem_cons]
        rintro x (rfl | hx)
        · simp
        · exact hEs x hx
  | false =>
    by_cases h0 : E = []
    · subst h0; exact ⟨by simp [rsplit], by simp [render, rsplit, dot], by simp [rsplit, dot]⟩
    · exact ⟨by simp [rsplit, h0], by simp [render, rsplit, h0], by simp [rsplit, h0]; exact hEs⟩

theorem dot_not_normal (r : Bool) (E : List Element) (hn : Normal r E) : dot ∉ E := by
  obtain ⟨k, names, rfl, -, hnames⟩ := shape_of_normal r E hn
  intro h
  rcases List.mem_append.mp h with h | h
  · exact dotdot_ne_dot (List.mem_replicate.mp h).2.symm
  · exact (hnames dot h).2.1 rfl

/-- A path names one list of elements. -/
theorem names_unique (s : String) (r : Bool) (e1 e2 : List Element) (h1 : Names s r e1)
    (h2 : Names s r e2) : e1 = e2 := by
  obtain ⟨h1s, h1n, h1f⟩ := h1
  obtain ⟨h2s, h2n, h2f⟩ := h2
  have hE1 := normal_elems r e1 h1n h1f
  have hE2 := normal_elems r e2 h2n h2f
  have hs := splits_rsplit r e1 hE1
  rw [← h1s, h2s] at hs
  have heq := splits_unique _ _ _ (splits_rsplit r e2 hE2) hs
  cases r with
  | true =>
    simp only [rsplit, ite_true, List.cons.injEq, true_and] at heq
    by_cases a : e1 = [] <;> by_cases b : e2 = [] <;> simp only [a, b, ite_true, ite_false] at heq
    · rw [a, b]
    · exact absurd (by rw [heq]; simp) (fun h => (hE2 [] h).1 rfl)
    · exact absurd (by rw [← heq]; simp) (fun h => (hE1 [] h).1 rfl)
    · exact heq.symm
  | false =>
    simp only [rsplit, Bool.false_eq_true, ite_false] at heq
    by_cases a : e1 = [] <;> by_cases b : e2 = [] <;> simp only [a, b, ite_true, ite_false] at heq
    · rw [a, b]
    · exact absurd (by rw [heq]; simp) (dot_not_normal false e2 h2n)
    · exact absurd (by rw [← heq]; simp) (dot_not_normal false e1 h1n)
    · exact heq.symm

/-! ### The rules only drop elements -/

theorem step_subset (r : Bool) (es es' : List Element) (h : Step r es es') :
    ∀ x ∈ es', x ∈ es := by
  intro x hx
  cases h with
  | empty xs ys =>
    simp only [List.mem_append, List.mem_cons] at hx ⊢
    rcases hx with hx | hx <;> simp [hx]
  | dot xs ys =>
    simp only [List.mem_append, List.mem_cons] at hx ⊢
    rcases hx with hx | hx <;> simp [hx]
  | parent xs e ys =>
    simp only [List.mem_append, List.mem_cons] at hx ⊢
    rcases hx with hx | hx <;> simp [hx]
  | root ys _ => exact List.mem_cons_of_mem _ hx

theorem steps_subset (r : Bool) (es es' : List Element) (h : Steps r es es') :
    ∀ x ∈ es', x ∈ es := by
  induction h with
  | refl => exact fun x hx => hx
  | step h _ ih => exact fun x hx => step_subset r _ _ h x (ih x hx)

end Spec.Proof
