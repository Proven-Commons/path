/-
  The statements of `Spec.lean`, each proved from the lemmas in the
  other files of `Proofs/`. `lake comparator` checks that each theorem
  here is exactly the one in `Spec.lean`.
-/

import Proofs.Join

namespace Spec

open Spec.Proof

theorem clean_rules (p : String) (es es' : List Element)
    (hp : Splits p.toList es) (hs : Steps (Rooted p.toList) es es')
    (hn : Normal (Rooted p.toList) es') :
    (Path.clean p).toList = render (Rooted p.toList) es' := by
  rw [Path.clean, String.toList_ofList, cleanChars_eq _ _ hp, ← steps_normal_eq _ _ _ hs hn]

theorem rules_end (p : String) :
    ∃ es es', Splits p.toList es ∧ Steps (Rooted p.toList) es es' ∧
      Normal (Rooted p.toList) es' :=
  ⟨elems p.toList, nf _ (elems p.toList), elems_splits _, steps_nf_self _ _, nf_normal _ _⟩

theorem step_shortens (rooted : Bool) (es es' : List Element) (h : Step rooted es es') :
    es'.length < es.length := by
  cases h <;> simp <;> omega

theorem rules_unique (rooted : Bool) (es e1 e2 : List Element)
    (h1 : Steps rooted es e1) (n1 : Normal rooted e1)
    (h2 : Steps rooted es e2) (n2 : Normal rooted e2) : e1 = e2 := by
  rw [steps_normal_eq _ _ _ h1 n1, steps_normal_eq _ _ _ h2 n2]

theorem normal_iff (rooted : Bool) (es : List Element) :
    Normal rooted es ↔
      ∃ k names, es = List.replicate k dotdot ++ names ∧ (rooted = true → k = 0) ∧
        ∀ e ∈ names, e ≠ [] ∧ e ≠ dot ∧ e ≠ dotdot :=
  normal_iff_shape rooted es

theorem clean_names (p : String) : ∃ es, Names (Path.clean p) (Rooted p.toList) es :=
  ⟨_, clean_names' p⟩

theorem clean_idem (p : String) : Path.clean (Path.clean p) = Path.clean p := by
  obtain ⟨h1, h2, h3⟩ := clean_names' p
  apply String.toList_inj.mp
  show (String.ofList (Path.cleanChars (Path.clean p).toList)).toList = _
  rw [String.toList_ofList, h1, cleanChars_render _ _ h2 h3]

theorem join_eq (es : List String) :
    Path.join es =
      if es.all (· = "") then "" else Path.clean ("/".intercalate (es.filter (· ≠ ""))) := by
  have hall : es.all (·.isEmpty) = es.all (· = "") := by
    congr 1; funext s; by_cases h : s = "" <;> simp [h, String.isEmpty_iff]
  unfold Path.join
  rw [hall]
  split
  · rfl
  · rename_i h
    exact join_core es (by simpa using h)

theorem join_inside (b q : String) (eq : List Element) (hq : Names q false eq)
    (hd : dotdot ∉ eq) :
    ∃ eb, Names (Path.clean b) (Rooted b.toList) eb ∧
      Names (Path.join [b, q]) (Rooted b.toList) (eb ++ eq) := by
  obtain ⟨hq1, hq2, hq3⟩ := hq
  have hnames := names_of_shape_no_dotdot false eq hq2 hd
  refine ⟨_, clean_names' b, ?_⟩
  by_cases hb : b = ""
  · subst hb
    have hE : ∀ e ∈ eq, e ≠ [] ∧ '/' ∉ e := fun e he => ⟨(hnames e he).1, hq3 e he⟩
    have hqne : q ≠ "" := by
      intro h; subst h; exact render_ne_nil false eq hE (by rw [← hq1]; simp)
    have hqe : q.isEmpty = false := by simpa [String.isEmpty_iff] using hqne
    have hjoin : Path.join ["", q] = Path.clean q := by
      simp [Path.join, hqe]
    have hn0 : nf (Rooted "".toList) (elems "".toList) = [] := by
      simp [Rooted, elems, nf, push_nil]
    rw [hjoin, hn0, List.nil_append]
    simp only [show Rooted "".toList = false by simp [Rooted]]
    refine ⟨?_, hq2, hq3⟩
    rw [Path.clean, String.toList_ofList, hq1, cleanChars_render _ _ hq2 hq3]
  · exact join_names b q hb false eq hq1 (fun e he => ⟨hnames e he, hq3 e he⟩)

theorem join_root_inside (b u : String) (hb : b ≠ "") :
    ∃ eb ext, dotdot ∉ ext ∧ Names (Path.clean b) (Rooted b.toList) eb ∧
      Names (Path.join [b, Path.clean ("/" ++ u)]) (Rooted b.toList) (eb ++ ext) := by
  obtain ⟨h1, h2, h3⟩ := clean_names' ("/" ++ u)
  have hr : Rooted ("/" ++ u).toList = true := by simp [Rooted]
  rw [hr] at h1 h2 h3
  have hnames : ∀ e ∈ nf true (elems ("/" ++ u).toList), IsName e := by
    obtain ⟨k, names, hE, hk, hn⟩ := shape_of_normal _ _ h2
    rw [hE, hk rfl]; simpa using hn
  refine ⟨_, _, fun h => (hnames _ h).2.2 rfl, clean_names' b,
    join_names b _ hb true _ h1 (fun e he => ⟨hnames e he, h3 e he⟩)⟩

theorem go_clean_tests :
    ∀ t ∈ [
      -- Already clean
      ("", "."), ("abc", "abc"), ("abc/def", "abc/def"), ("a/b/c", "a/b/c"),
      (".", "."), ("..", ".."), ("../..", "../.."), ("../../abc", "../../abc"),
      ("/abc", "/abc"), ("/", "/"),
      -- Remove trailing slash
      ("abc/", "abc"), ("abc/def/", "abc/def"), ("a/b/c/", "a/b/c"), ("./", "."),
      ("../", ".."), ("../../", "../.."), ("/abc/", "/abc"),
      -- Remove doubled slash
      ("abc//def//ghi", "abc/def/ghi"), ("//abc", "/abc"), ("///abc", "/abc"),
      ("//abc//", "/abc"), ("abc//", "abc"),
      -- Remove . elements
      ("abc/./def", "abc/def"), ("/./abc/def", "/abc/def"), ("abc/.", "abc"),
      -- Remove .. elements
      ("abc/def/ghi/../jkl", "abc/def/jkl"), ("abc/def/../ghi/../jkl", "abc/jkl"),
      ("abc/def/..", "abc"), ("abc/def/../..", "."), ("/abc/def/../..", "/"),
      ("abc/def/../../..", ".."), ("/abc/def/../../..", "/"),
      ("abc/def/../../../ghi/jkl/../../../mno", "../../mno"),
      -- Combinations
      ("abc/./../def", "def"), ("abc//./../def", "def"),
      ("abc/../../././../def", "../../def")],
      Path.clean t.1 = t.2 ∧ Path.clean t.2 = t.2 := by
  decide +kernel

theorem go_join_tests :
    ∀ t ∈ [
      ([], ""), ([""], ""), (["a"], "a"),
      (["a", "b"], "a/b"), (["a", ""], "a"), (["", "b"], "b"), (["/", "a"], "/a"),
      (["/", ""], "/"), (["a/", "b"], "a/b"), (["a/", ""], "a"), (["", ""], ""),
      (["", "/etc"], "/etc")],
      Path.join t.1 = t.2 := by
  decide +kernel

end Spec
