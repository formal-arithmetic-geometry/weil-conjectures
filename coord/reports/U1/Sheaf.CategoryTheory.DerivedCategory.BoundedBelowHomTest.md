## What changed

Proved `DerivedCategory.isIso_of_boundedBelow_hom_bijective` in
`Sheaf.CategoryTheory.DerivedCategory.BoundedBelowHomTest`, with its existing
signature, universes, visibility, and public imports unchanged. Added one fully
proved private helper, `DerivedCategory.isZero_of_boundedBelow_hom_zero`.

The shorter proof completes the morphism to a distinguished triangle. Injectivity
at shift -1, transported through the shift adjunction, and surjectivity at shift 0
show that every map from a bounded-below object to the cone is zero. To detect its
cohomology in degree q, represent it by a complex K and use the actual inclusion
of the brutal truncation starting at q-1. This inclusion is an isomorphism on all
three terms defining degree-q cohomology. Its localized map is zero but induces
an isomorphism in that degree, so that cohomology object vanishes. The cohomology
criterion and the zero-cone criterion finish the proof.

The helper works for any abelian category with the specified derived category;
no Grothendieck or countable-colimit hypothesis is used. Its representative
`Q.objPreimage` comes from the existing essentially-surjective localization API,
not from a newly postulated existence theorem. The truncation and inclusion are
actual existing constructions.

Replaced the private proof imports by
`WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc` and
`Mathlib.Algebra.Homology.DerivedCategory.TStructure`. Updated the theorem's proof
in words and the existing node's `proof`, `proof_deps`, and `proof_origin` to
match. Removed its obsolete telescope `tool_uses` entry. The unit statement and
its route are unchanged: this module still supplies the bounded-below Hom test
at step 4 of `sk-prop-sf-rf-shriek-preservation`.

Validation: the full final module compiled through the prescribed `lcompile.py`
with exit 0, no warnings, in 41.7 seconds after the final qualification-only repair. Checked the unchanged theorem signature
against the original; all Lean lines have at most 100 characters. Restored the original file-level open
command after preflight classified its extension as an interface change; the
proof now qualifies its triangle lemmas explicitly. A direct read-only check of
`leanindex.interface_changes` returns the empty list after that repair. The empty site,
zero ring, zero objects, negative q, and unbounded endpoints require no extra
hypothesis. The private helper handles arbitrary cohomologically bounded-below
test objects; the proof itself tests actual strictly bounded-below truncations.

Searches actually run: leanfinder on bounded-below Hom detection (eight hits on
localization and individual truncations, no matching theorem); loogle on
`"DerivedCategory", "IsIso"` (five cohomology/localization criteria); msearch grep
on `quasiIsoAt_of_isIso|ιStupidTrunc|isZero.*homology` (25 homology-related hits).
Direct rg searches of both library roots located the actual brutal-truncation
inclusion and its component isomorphism theorem in the adopted source library.
Read their proofs, Mathlib's short-complex isomorphism API, derived cohomology
criterion, shift adjunction, and triangle exactness/zero-cone lemmas. Sources read:
Stacks `homology.tex`, section-truncations (Tag 0118), and `derived.tex`,
lemma-composition-zero and lemma-representable-homological (Tags 0146 and 0149).

## Proved and sorry left

Closed 1 of 1 original holes:
`DerivedCategory.isIso_of_boundedBelow_hom_bijective`
(node `lem-sf-bounded-below-hom-test`).

Added 0 holes; split off 0 statements. The private helper
`DerivedCategory.isZero_of_boundedBelow_hom_zero` is fully proved.
No sorry remains anywhere in the delivered Lean module.

## No longer needed

Removed private imports:

- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`: its composite wrapper
  and homotopy-colimit predicate are unnecessary. The brutal-truncation portion
  of `def-kun-truncations` remains mathematically used, through the actual
  Mathlib construction and adopted inclusion API.
- `Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit`: the telescope comparison
  `lem-kun-complex-colimit-hocolim` is unnecessary for this proof. Removed that
  node from proof dependencies and its obsolete top-level tool-use approval.
- `Mathlib.CategoryTheory.Limits.HasLimits`: neither colimits nor coproducts are
  used; `def-weil-pbc-category-colimit` leaves this node's proof dependencies.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`: no separate direct
  import is necessary, since the retained public derived-category import exposes
  the triangle API used by the proof. The triangulated-category dependency stays.

`lem-weil-pbc-hom-out-of-triangle-exact` is no longer needed: the cone argument
uses the existing Mathlib leaf `lem-weil-pbc-hom-into-triangle-exact`, rotated to
factor maps into the cone. No source-library declaration or module is removed.
No claim is made that these modules cease to be needed by other consumers.

## Where the brief, the DAG or earlier work was wrong

The seven-step telescope plan is valid but stronger than needed. A cone argument
reduces detection to a single brutal truncation in each cohomological degree,
so no degreewise colimit, derived coproduct, or telescope comparison is needed.
This is a shorter proof below the unit level, with the exact original statement.
There is no statement or definition repair, no forced consumer adaptation, and
no new node.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
