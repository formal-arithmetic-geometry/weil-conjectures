## Worker report

The module defines `AlgebraicGeometry.IsUniversalFirstOrderThickening` and states
`AlgebraicGeometry.IsUniversalFirstOrderThickening.unique` with a sorry proof.
Source: Stacks Project, More on Morphisms, Section 37.7 (Tag 04F2), opening
paragraph; Definition 37.7.2 (Tag 04F4), item 1. The local literature checkout
does not contain `more-morphisms.tex`; I read the cited Stacks pages online.

Statement mapping:

- The schemes `Z`, `Z'`, and `X` and the map `h : Z ⟶ X` are the definition's
  binders. `i : Z ⟶ Z'` and `h' : Z' ⟶ X` are the proposed thickening and its
  structure morphism.
- `IsFirstOrderThickening i` is the closed immersion with square-zero kernel
  ideal sheaf. Its recorded definition is `IsClosedImmersion i ∧ i.ker ^ 2 = ⊥`.
- `i ≫ h' = h` says the thickening is over `X` with the given structure on `Z`.
- `∀ {T T' : Scheme.{u}} ...` ranges over arbitrary schemes, including
  non-affine schemes. `IsFirstOrderThickening j` is the test thickening;
  `b : T' ⟶ X` supplies its structure morphism.
- `j ≫ b = a ≫ h` says `a : T ⟶ Z` is over `X`.
- `∃! a' : T' ⟶ Z', a' ≫ h' = b ∧ j ≫ a' = a ≫ i` gives exactly one extension
  over `X` making the square commute.
- The theorem binds two such universal triples. Its first conjunct
  `∃! φ : Z₁ ⟶ Z₂, φ ≫ h₂ = h₁ ∧ i₁ ≫ φ = i₂` gives precisely one map
  over `X` restricting to the identity on `Z`; its second conjunct makes
  every map satisfying those equations an isomorphism. No existence of a
  universal thickening is asserted by the definition.

Dependencies read and used: `AlgebraicGeometry.IsFirstOrderThickening` from
`Sheaf.AlgebraicGeometry.Thickening`; `AlgebraicGeometry.Scheme` and scheme
morphisms from `Mathlib.AlgebraicGeometry.Scheme`; `Scheme.Over` and `Hom.IsOver`
from `Mathlib.AlgebraicGeometry.Over` (rendered explicitly by commuting
equations); `AlgebraicGeometry.IsClosedImmersion` from
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` and `Scheme.Hom.ker`
from `Mathlib.AlgebraicGeometry.IdealSheaf.Basic` (both through the recorded
first-order thickening definition).

Edge cases: the definition makes no affine, nonempty, reduced, separated,
Noetherian, or characteristic assumption. Empty schemes and zero ideals are
included. There is no indexing set or integer parameter. The same arbitrary
universe `u` is used for every scheme, as in the dependency declaration.

Searches for an existing notion:

- `msearch.py leanfinder "universal first order thickening of a scheme over
  another scheme"`: eight hits concerning schemes over a base and related
  constructions, none defining the universal thickening.
- `msearch.py loogle "AlgebraicGeometry.UniversalFirstOrderThickening,
  AlgebraicGeometry.IsUniversalFirstOrderThickening"`: zero hits.
- `msearch.py grep "UniversalFirstOrderThickening|universal.*first.order.*thickening"
  AlgebraicGeometry`: zero hits.
- `rg -n "UniversalFirstOrderThickening|universal.*first.order.*thickening|
  IsFirstOrderThickening"` in `WeilConjectures` and the project `lean/Sheaf`:
  only the existing non-universal `IsFirstOrderThickening` dependency.
- `grep -rn "def-weil-pbc-universal-first-order-thickening"` in
  `WeilConjectures`: no hits.

The server compiler reported no errors or warnings.

## Second reading by C1

I read the node statement and `UniversalFirstOrderThickening.lean` independently.
The objects and clauses match as follows.

- The node's morphism `h : Z \to X` is the Lean binder
  `{Z Z' X : Scheme.{u}} (h : Z ⟶ X)`; `i : Z \to Z'` and
  `h' : Z' \to X` are the remaining explicit binders.
- The node's first-order thickening condition on `i` is exactly
  `IsFirstOrderThickening i`, whose recorded dependency is the closed immersion
  with square-zero kernel ideal sheaf. The compatibility `h' \circ i = h` is
  `i ≫ h' = h`.
- The universal quantifiers over arbitrary schemes `T,T'`, a thickening
  `j : T ⟶ T'`, structure map `b : T' ⟶ X`, and map `a : T ⟶ Z` are rendered
  by the implicit scheme binders and explicit binders on lines 39--40. The
  hypotheses `IsFirstOrderThickening j` and `j ≫ b = a ≫ h` match the node's
  thickening and over-`X` conditions.
- The extension clause is exactly
  `∃! a' : T' ⟶ Z', a' ≫ h' = b ∧ j ≫ a' = a ≫ i`, preserving both
  required equations and their quantifier order.
- The node's uniqueness-up-to-unique-isomorphism clause is rendered by
  `IsUniversalFirstOrderThickening.unique`: its first conjunct is the unique
  `φ : Z₁ ⟶ Z₂` satisfying `φ ≫ h₂ = h₁` and `i₁ ≫ φ = i₂`, and its second
  conjunct states `IsIso φ` for every morphism satisfying those equations.
  This is equivalent to the node's assertion that the unique map is an
  isomorphism over `X`; no existence of a universal thickening is added.

Edge cases were checked: the binders allow empty schemes, zero ideal sheaves,
identity thickenings, arbitrary (including non-affine) test schemes, and all
universe values represented by the common universe `u`. There is no index,
integer, characteristic, Noetherian, separated, reduced, affine, or nonempty
hypothesis to exclude an edge case.

I searched Mathlib and the slopmaster2/source checkout with LeanSearch,
LeanFinder/Loogle, and `rg`/`grep` for universal first-order thickening,
square-zero scheme thickenings, and `IsUniversalFirstOrderThickening`.
The searches found only the existing non-universal `IsFirstOrderThickening`
dependency and formally-unramified lifting lemmas; no exact declaration exists.

No mismatch was found and no code or node statement was changed. The module
compiled cleanly with `scompile.py`, and `deliver2.py --no-push` passed.
