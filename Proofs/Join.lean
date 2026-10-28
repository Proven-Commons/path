import Proofs.Clean

/-!
  `join`: the elements of joined strings, and what cleaning them gives.
-/

namespace Spec.Proof

open Spec Path

theorem splits_intercalate (L : List (List Char)) (hL : L ≠ []) :
    Splits (List.intercalate ['/'] L) (L.flatMap elems) := by
  induction L with
  | nil => exact absurd rfl hL
  | cons x L ih =>
    cases L with
    | nil => simpa using elems_splits x
    | cons y L =>
      rw [List.intercalate_cons_cons, List.append_assoc, List.singleton_append,
        List.flatMap_cons]
      exact splits_append _ _ _ _ (elems_splits x) (ih (by simp))

theorem foldl_filter (r : Bool) (ss : List String) :
    ∀ acc, ((ss.map String.toList).flatMap elems).foldl (push r) acc =
      (((ss.filter (· ≠ "")).map String.toList).flatMap elems).foldl (push r) acc := by
  induction ss with
  | nil => intro acc; rfl
  | cons s ss ih =>
    intro acc
    by_cases hs : s = ""
    · subst hs
      simp only [List.map_cons, List.flatMap_cons, List.foldl_append, ne_eq,
        not_true_eq_false, decide_false, Bool.false_eq_true, not_false_eq_true,
        List.filter_cons_of_neg]
      rw [show "".toList = [] by simp, show elems [] = [[]] from rfl]
      simp only [List.foldl_cons, List.foldl_nil, push_nil]
      exact ih acc
    · rw [List.filter_cons_of_pos (by simpa using hs)]
      simp only [List.map_cons, List.flatMap_cons, List.foldl_append]
      exact ih _

theorem toList_slash_intercalate (ss : List String) :
    ("/".intercalate ss).toList = List.intercalate ['/'] (ss.map String.toList) := by
  rw [String.toList_intercalate]; rfl

theorem rooted_intercalate (x : List Char) (L : List (List Char)) (hx : x ≠ []) :
    Rooted (List.intercalate ['/'] (x :: L)) = Rooted x := by
  cases L with
  | nil => simp
  | cons y L => rw [List.intercalate_cons_cons, List.append_assoc]; exact rooted_append _ _ hx

/-- Leaving out the empty strings changes nothing once cleaned. -/
theorem join_core (es : List String) (h : ∃ s ∈ es, s ≠ "") :
    Path.clean ("/".intercalate (es.dropWhile (·.isEmpty))) =
      Path.clean ("/".intercalate (es.filter (· ≠ ""))) := by
  induction es with
  | nil => obtain ⟨s, hs, -⟩ := h; simp at hs
  | cons s es ih =>
    by_cases hs : s = ""
    · subst hs
      have h' : ∃ s ∈ es, s ≠ "" := by
        obtain ⟨t, ht, htne⟩ := h
        simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact absurd rfl htne
        · exact ⟨t, ht, htne⟩
      simpa using ih h'
    · have hse : s.isEmpty = false := by simpa [String.isEmpty_iff] using hs
      rw [List.dropWhile_cons, hse, List.filter_cons_of_pos (by simpa using hs)]
      simp only [Bool.false_eq_true, ite_false]
      apply String.toList_inj.mp
      have hsl : s.toList ≠ [] := by simpa using hs
      simp only [Path.clean, String.toList_ofList, toList_slash_intercalate, List.map_cons]
      rw [cleanChars_eq _ _ (splits_intercalate _ (by simp)),
        cleanChars_eq _ _ (splits_intercalate _ (by simp)),
        rooted_intercalate _ _ hsl, rooted_intercalate _ _ hsl]
      unfold nf
      simp only [List.flatMap_cons, List.foldl_append]
      rw [foldl_filter]

theorem render_ne_nil (r : Bool) (E : List Element) (hE : ∀ e ∈ E, e ≠ [] ∧ '/' ∉ e) :
    render r E ≠ [] := by
  cases r with
  | true => simp [render]
  | false =>
    by_cases h0 : E = []
    · simp [render, h0, dot]
    · simp only [render, Bool.false_eq_true, ite_false, h0]
      exact intercalate_ne_nil E h0 (fun e he => (hE e he).1)

/-- Joining a path `b` and the path `q` that `render` writes for names. -/
theorem join_names (b q : String) (hb : b ≠ "") (r' : Bool) (eq : List Element)
    (hq : q.toList = render r' eq) (hnames : ∀ e ∈ eq, IsName e ∧ '/' ∉ e) :
    Names (Path.join [b, q]) (Rooted b.toList) (nf (Rooted b.toList) (elems b.toList) ++ eq) := by
  have hE : ∀ e ∈ eq, e ≠ [] ∧ '/' ∉ e := fun e he => ⟨(hnames e he).1.1, (hnames e he).2⟩
  have hqne : q ≠ "" := by
    intro h; subst h; exact render_ne_nil r' eq hE (by rw [← hq]; simp)
  have hbl : b.toList ≠ [] := by simpa using hb
  have hjoin : (Path.join [b, q]).toList = cleanChars (b.toList ++ '/' :: q.toList) := by
    have hbe : b.isEmpty = false := by simpa [String.isEmpty_iff] using hb
    have hqe : q.isEmpty = false := by simpa [String.isEmpty_iff] using hqne
    simp only [Path.join, List.all_cons, hbe, hqe, Bool.false_and, List.all_nil,
      Bool.false_eq_true, ite_false, List.dropWhile_cons]
    simp [Path.clean]
  obtain ⟨S, hS, hfold⟩ := splits_render r' eq hE
  rw [← hq] at hS
  have hsplit := splits_append _ _ _ _ (elems_splits b.toList) hS
  have hnf : nf (Rooted b.toList) (elems b.toList ++ S) =
      nf (Rooted b.toList) (elems b.toList) ++ eq := by
    unfold nf
    rw [List.foldl_append, hfold, foldl_names _ _ _ (fun e he => (hnames e he).1)]
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hjoin, cleanChars_eq _ _ hsplit, rooted_append _ _ hbl, hnf]
  · rw [← hnf]; exact nf_normal _ _
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact nf_slashfree _ _ (elems_splits _).2.2 e he
    · exact (hnames e he).2

theorem names_of_shape_no_dotdot (r : Bool) (E : List Element) (hn : Normal r E)
    (hd : dotdot ∉ E) : ∀ e ∈ E, IsName e := by
  obtain ⟨k, names, rfl, -, hnames⟩ := shape_of_normal r E hn
  cases k with
  | zero => simpa using hnames
  | succ k => exact absurd (by simp [List.replicate_succ]) hd

end Spec.Proof
