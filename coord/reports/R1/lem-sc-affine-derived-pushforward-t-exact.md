## Worker report

The module states that for an affine morphism `f : X ⟶ Y`, derived direct image
preserves quasi-coherent cohomology, preserves and reflects both standard derived
`t`-structure bounds at every integer, and reflects isomorphisms between objects
with quasi-coherent cohomology. The exact Lean statement is the theorem
`AlgebraicGeometry.schemeDerivedDirectImage_tExact_and_conservative_of_affine` in
`lean/Sheaf/AlgebraicGeometry/AffineDerivedPushforwardTExact.lean`; its proof is
`sorry` as required for stage 2.

The binders `{X Y : Scheme.{u}}` render the schemes and `(f : X ⟶ Y)` renders the
morphism. The two `HasDerivedCategory` instances provide the derived categories of
sheaves of modules on `X` and `Y`, and `[IsAffineHom f]` renders the affine
hypothesis. For every `E` and its quasi-coherent-cohomology hypothesis, the first
conclusion gives quasi-coherent cohomology after pushforward and, for every
`n : ℤ`, the two equivalences `DerivedCategory.IsLE E n ↔ IsLE (Rf_* E) n`
and `DerivedCategory.IsGE E n ↔ IsGE (Rf_* E) n`. The second conclusion quantifies
`E F`, their quasi-coherent-cohomology hypotheses, and every morphism `a : E ⟶ F`,
then states that `IsIso ((Rf_*).map a)` implies `IsIso a`.

The dependency declarations used are:

- `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom` from Mathlib's
  `Mathlib/AlgebraicGeometry/Scheme.lean` (node `def-pc-scheme`).
- `AlgebraicGeometry.schemeDerivedCategory` and
  `AlgebraicGeometry.schemeDerivedQCohProperty` from
  `Sheaf.AlgebraicGeometry.DerivedCategory` (node `def-pc-derived-category`).
- `AlgebraicGeometry.schemeDerivedDirectImage` from
  `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage` (node
  `def-pc-derived-direct-image`).
- `DerivedCategory.TStructure.t`, `DerivedCategory.IsLE`, and
  `DerivedCategory.IsGE` from Mathlib
  `Mathlib/Algebra/Homology/DerivedCategory/TStructure.lean` (node
  `def-sbc-standard-tstructure-derived-category`).
- `AlgebraicGeometry.IsAffineHom` from Mathlib's
  `Mathlib/AlgebraicGeometry/Morphisms/Affine.lean`.

Edge cases checked: `n` ranges over all integers, including `n = 0`; no nonempty or
boundedness assumption is imposed on the derived objects; the affine identity map
is covered by Mathlib's affine instance; and zero objects and zero morphisms are
included by the universal quantifiers.

Searches for an existing declaration: LeanFinder query “affine morphism derived
direct image preserves and reflects cohomological bounds and isomorphisms” returned
only generic Mathlib `DerivedCategory` t-structure declarations, with no usable
theorem. Loogle query “DerivedCategory.IsLE, DerivedCategory.IsGE” returned the
standard t-structure declarations only. `msearch.py ... grep` for
`affine.*[tT].*[eE]xact|derived.*[cC]onservative` found no matching theorem in
Mathlib. `rg` found no declaration in `WeilConjectures`; the only related project
modules are the already-recorded affine concentration and conservative statements.
LeanSearch was attempted with the affine derived pushforward query but was
unavailable (internal server error). The Stacks source was checked at Tags 0AVW
(Lemma 36.5.4: affine pushforward gives the cohomology comparison and the
quasi-coherent derived equivalence) and 08I8 (Lemma 36.5.2: `Rf_*` reflects
isomorphisms).

## Second reading by R1

I reread the node statement and the module signature item by item.

- Objects: the node introduces schemes `X,Y` and an affine morphism `f : X ⟶ Y`.
  The Lean binders `{X Y : Scheme.{u}}`, `(f : X ⟶ Y) [IsAffineHom f]` render exactly
  these objects and the affine hypothesis; no separated, Noetherian, finiteness, or field
  hypotheses are added.
- Ambient categories: the node's `D_QCoh(X)` and `D_QCoh(Y)` are rendered by
  `schemeDerivedCategory X/Y` together with the explicit predicates
  `schemeDerivedQCohProperty X/Y`.  The two `HasDerivedCategory` binders are the
  instances required by the recorded `def-pc-derived-category` declaration and do not
  restrict the schemes or objects.
- Derived direct image: `schemeDerivedDirectImage f` is the recorded
  `def-pc-derived-direct-image` functor.  Its object and map are used throughout, with
  no private or alternate pushforward definition.
- T-exactness clauses: for every `E : schemeDerivedCategory X` satisfying the source
  quasi-coherent-cohomology predicate, the first conjunct states preservation of that
  predicate on `Rf_* E`.  For every `n : ℤ` (including zero and negative integers), it
  states both exact equivalences
  `DerivedCategory.IsLE E n ↔ DerivedCategory.IsLE (Rf_* E) n` and
  `DerivedCategory.IsGE E n ↔ DerivedCategory.IsGE (Rf_* E) n`.  Thus both directions
  and both standard bounds in the node are present, with the same quantifier order.
- Conservativity: the second conjunct quantifies `E,F` and their two QCoh predicates,
  then every `a : E ⟶ F`; the implication
  `IsIso ((schemeDerivedDirectImage f).map a) → IsIso a` is exactly reflection of
  isomorphisms on `D_QCoh`, with no extra conclusion or omitted hypothesis.

Edge cases checked: the integer quantifier includes `n = 0`; all objects including zero
objects and all morphisms including zero morphisms are covered; the identity affine map
is covered by `[IsAffineHom f]`; no index-set, nonemptiness, characteristic, or
Noetherian assumption is present, and the universe parameter is shared by both schemes
and their module-sheaf categories as required by the dependency declarations.

I searched the project and slopmaster2 source with `rg`, and used the recorded
LeanFinder/Loogle/msearch searches (LeanSearch was unavailable).  No declaration states
this affine derived t-exactness/conservativity theorem; only the generic t-structure,
derived-category, direct-image, affine-morphism, concentration, and conservative
components were found.  I also checked the recorded dependency signatures and their
modules; each is the notion named by the node.  No mismatch was found, so no Lean or
node statement change was necessary.
