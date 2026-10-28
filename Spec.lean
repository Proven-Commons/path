import Path
import Spec.Defs

/-!
  The statements a reviewer approves. Each `sorry` is proved under the
  same name in `Proofs/`, and `lake comparator` checks that each proof
  proves exactly the statement here.

  `Spec/Defs.lean` states Go's rules on the elements of a path.
  `Path.clean` and `Path.join` are the code, in `Path/Basic.lean`.
-/

namespace Spec

/-- Whatever order the rules are applied in, once none applies, the
    path with the elements left is `clean p`. -/
theorem clean_rules (p : String) (es es' : List Element)
    (hp : Splits p.toList es) (hs : Steps (Rooted p.toList) es es')
    (hn : Normal (Rooted p.toList) es') :
    (Path.clean p).toList = render (Rooted p.toList) es' := by
  sorry

/-- The rules can always be applied until none applies, so
    `clean_rules` says something about every path. -/
theorem rules_end (p : String) :
    ∃ es es', Splits p.toList es ∧ Steps (Rooted p.toList) es es' ∧
      Normal (Rooted p.toList) es' := by
  sorry

/-- Every rule drops at least one element, so the rules, applied in any
    order, always come to an end. -/
theorem step_shortens (rooted : Bool) (es es' : List Element) (h : Step rooted es es') :
    es'.length < es.length := by
  sorry

/-- Applied in any order, the rules end at the same elements: once none
    applies, what is left does not depend on the order. -/
theorem rules_unique (rooted : Bool) (es e1 e2 : List Element)
    (h1 : Steps rooted es e1) (n1 : Normal rooted e1)
    (h2 : Steps rooted es e2) (n2 : Normal rooted e2) : e1 = e2 := by
  sorry

/-- No rule applies exactly when the elements are some `..`, none if
    the path is rooted, then names: elements that are not empty, `.`
    or `..`. -/
theorem normal_iff (rooted : Bool) (es : List Element) :
    Normal rooted es ↔
      ∃ k names, es = List.replicate k dotdot ++ names ∧ (rooted = true → k = 0) ∧
        ∀ e ∈ names, e ≠ [] ∧ e ≠ dot ∧ e ≠ dotdot := by
  sorry

/-- So `clean p` has no empty element and no `.`, `..` only at the
    start and none if `p` is rooted, and it is rooted when `p` is. -/
theorem clean_names (p : String) : ∃ es, Names (Path.clean p) (Rooted p.toList) es := by
  sorry

/-- Cleaning a clean path changes nothing. -/
theorem clean_idem (p : String) : Path.clean (Path.clean p) = Path.clean p := by
  sorry

/-- `join`, as Go's documentation says: "Join joins any number of path
    elements into a single path, separating them with slashes. Empty
    elements are ignored. The result is Cleaned. However, if the
    argument list is empty or all its elements are empty, Join returns
    an empty string." -/
theorem join_eq (es : List String) :
    Path.join es =
      if es.all (· = "") then "" else Path.clean ("/".intercalate (es.filter (· ≠ ""))) := by
  sorry

/-- A clean relative path `q` with no `..`, joined to any path `b`,
    stays inside `b`: the elements of the result are those of
    `clean b`, then those of `q`. -/
theorem join_inside (b q : String) (eq : List Element) (hq : Names q false eq)
    (hd : dotdot ∉ eq) :
    ∃ eb, Names (Path.clean b) (Rooted b.toList) eb ∧
      Names (Path.join [b, q]) (Rooted b.toList) (eb ++ eq) := by
  sorry

/-- Any path `u`, cleaned as a rooted path and joined to a path `b`
    that is not empty, stays inside `b`. If `b` is empty, `join` leaves
    it out, and the result is rooted (see `go_join_tests`). -/
theorem join_root_inside (b u : String) (hb : b ≠ "") :
    ∃ eb ext, dotdot ∉ ext ∧ Names (Path.clean b) (Rooted b.toList) eb ∧
      Names (Path.join [b, Path.clean ("/" ++ u)]) (Rooted b.toList) (eb ++ ext) := by
  sorry

/-- Go's tests of `Clean`, `cleantests` in src/path/path_test.go
    (go1.24.7): each path cleans to its result, and the result cleans
    to itself. Among them, `//abc` cleans to `/abc`: two slashes at the
    start are one slash, though POSIX lets a system give them a meaning
    of their own. -/
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
  sorry

/-- Go's tests of `Join`, `jointests` in src/path/path_test.go
    (go1.24.7), and one more: an empty first element is left out, so
    joining it to a rooted path gives a rooted path. -/
theorem go_join_tests :
    ∀ t ∈ [
      ([], ""), ([""], ""), (["a"], "a"),
      (["a", "b"], "a/b"), (["a", ""], "a"), (["", "b"], "b"), (["/", "a"], "/a"),
      (["/", ""], "/"), (["a/", "b"], "a/b"), (["a/", ""], "a"), (["", ""], ""),
      (["", "/etc"], "/etc")],
      Path.join t.1 = t.2 := by
  sorry

end Spec
