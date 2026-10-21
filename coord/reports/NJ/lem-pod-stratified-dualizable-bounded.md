## Worker report

The module `Sheaf.Paper.StratifiedDualizableBounded` states
`AlgebraicGeometry.ProEtale.stratified_dualizable_bounded`, with its proof `sorry`.
It adds no definitions. The node is unchanged except for its `lean` record.

Source read: Hemo--Richarz--Scholbach, Constructible sheaves on schemes,
Definition 3.3, Lemma 4.1(2), Lemma 4.10 and Corollary 4.11, in the local PDF.
Definition 3.3 identifies constructibility on a qcqs scheme with a finite
constructible locally closed partition whose restrictions are dualizable.
Lemma 4.10 bounds the lisse case; Corollary 4.11 gives the finite-stratum case.
The seven-step proof in the node is reproduced in the theorem docstring,
including the finite open/closed refinement, singleton w-contractible cover,
finite-projective retracts, brutal-tail induction, exact/conservative restriction,
finite-tree induction and good lower truncation. The statement uses the ordinary
unbounded derived category, not a completed or bounded derived category.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| A scheme Y | `(Y : Scheme.{u})` |
| Quasi-compact | `[CompactSpace Y]` |
| Quasi-separated | `[QuasiSeparatedSpace Y]`, the underlying-space characterization of quasi-separatedness of the structure morphism |
| Arbitrary commutative condensed ring Λ | `(Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]` |
| B = p_Y^* Λ on the small pro-etale site | `condensedRingObj Λ.X Y`, with ambient sheaves `Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}` |
| K in the ordinary unbounded derived category D(B) of module sheaves | `K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ.X Y))` |
| Ordinary relative derived tensor | The existing `Mod.derivedMonoidalCategory` instance exported by the recorded tensor/Hom module; it derives relative module tensor by K-flat resolutions |
| A finite locally closed scheme stratification | `S : Scheme.FiniteLocallyClosedStratification Y`; it stores `n`, a partition indexed by `Fin S.n`, locally closed subsets, actual scheme domains, immersion maps and their prescribed images |
| Constructible strata | `hconstructible : ∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)` |
| Derived restriction of K to each stratum | `(CondensedRing.upperStar Λ.X (S.immersion i)).mapDerivedCategory.obj K`; the canonical coefficient map is an isomorphism and this exact inverse image is the published derived restriction |
| A dual object D on each stratum | `hdual` quantifies `∃ D : DerivedCategory (Mod ... (condensedRingObj Λ.X (S.domain i)))` |
| Evaluation D tensor K to B, coevaluation B to K tensor D | `Nonempty (ExactPairing restrictedK D)`; its fields are `evaluation' : D ⊗ restrictedK ⟶ 𝟙_ _` and `coevaluation' : 𝟙_ _ ⟶ restrictedK ⊗ D` |
| Both duality contractions are identities with the usual associators and unitors | The two triangle equations of Mathlib `ExactPairing`, `coevaluation_evaluation'` and `evaluation_coevaluation'` |
| Integers a <= b | `∃ a b : ℤ, a ≤ b ∧ ...` |
| H^j(K) = 0 for j < a and j > b | `∀ j : ℤ, j < a ∨ b < j → IsZero ((DerivedCategory.homologyFunctor _ j).obj K)` |
| A cochain representative C of K | `∃ C : CochainComplex ... ℤ, Nonempty (DerivedCategory.Q.obj C ≅ K) ∧ ...` |
| C^j = 0 below the same a | `∀ j : ℤ, j < a → IsZero (C.X j)` |
| No Noetherian, dimension or regularity condition | No such binder or typeclass appears |

The monoidal unit here is the coefficient ring as a module, placed in degree zero.
`ExactPairing restrictedK D` has exactly the orientation in the node, also the
orientation of `HasRightDual restrictedK`. It is the existing duality structure,
not a new predicate. `IsZero` expresses categorical vanishing, so it does not
mistake a chosen zero object for the only object isomorphic to zero.

Dependency declarations read and reused:

- `def-weil-pbc-quasi-compact-scheme`: `CompactSpace` in
  `Mathlib.Topology.Defs.Filter` (no separation axiom).
- `def-weil-quasi-separated-morphism`: `AlgebraicGeometry.QuasiSeparated` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`, together with its
  underlying-space characterization `QuasiSeparatedSpace`.
- `sk-def-sfb-condensed-ring`: `Profinite.CondensedRing` in
  `Sheaf.Topology.ProfiniteCondensedRing` (bundled ring objects on the coherent profinite site).
- `def-weil-pbc-proetale-site`: `AlgebraicGeometry.Scheme.ProEt` and `ProEt.topology`
  in `Mathlib.AlgebraicGeometry.Sites.Proetale`.
- `sk-def-sfb-pulled-back-coefficients`: `AlgebraicGeometry.ProEtale.coefficientRing`,
  `coefficientRing_X`, `condensedRingObj` and `isCommMonObj_condensedRingObj` in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
- `def-weil-sheaf-of-modules-category`: `CategoryTheory.ringedSiteModules` in
  `Sheaf.CategoryTheory.RingedSiteModules` transparently gives Mathlib's general
  sectionwise module sheaves. The tensor dependency specifies its internal module-object
  encoding `Mod (Sheaf ...) B`, which carries exactly a sheaf of abelian groups with
  a B-action. We use that published encoding throughout, with no duplicate category.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory` and
  `DerivedCategory.Q` in `Mathlib.Algebra.Homology.DerivedCategory.Basic`;
  `DerivedCategory.homologyFunctor` in its `HomologySequence` module.
- `sk-def-sfb-derived-tensor-hom`: the recorded
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`, exporting
  `CondensedRing.derivedTensor`, `CondensedRing.derivedHom` and
  `CategoryTheory.Mod.derivedMonoidalCategory`. No extra choice of monoidal structure.
- `def-constructible-stratification`: `Topology.FiniteLocallyClosedStratification` and
  `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification` in
  `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`.
- `def-weil-constructible-subset`: Mathlib match `Topology.IsConstructible`, defined
  by the Boolean algebra generated by open retrocompact subsets, in
  `Mathlib.Topology.Constructible`.
- `def-sfb-monoidal-category`: Mathlib match `CategoryTheory.MonoidalCategory` in
  `Mathlib.CategoryTheory.Monoidal.Category`; the usual duality structure is
  `CategoryTheory.ExactPairing` in `Mathlib.CategoryTheory.Monoidal.Rigid.Basic`.

Derived restriction is the existing exact module inverse image, whose full signature
and comparison with left derivation were read in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`;
`CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory` identifies the two forms.
All recorded proof-dependency modules are imported without `public` unless already
part of a public statement-dependency import closure. In particular, coefficient
morphisms come from the public `Basic` closure. The imports retain the node's proof
plan even though this stage leaves the theorem unproved.

Edge cases checked before writing:

- Empty Y and the empty partition (`S.n = 0`) are allowed; the covering axiom then
  forces Y empty. The conclusion allows a = b = 0 and the zero representative.
- Empty strata and a zero coefficient ring are allowed. There is no nonempty-stratum,
  nonzero-ring or positive-rank hypothesis.
- K = 0, a one-stratum partition, and a one-term finite-projective local model are
  included. Bounds a = b are allowed.
- Neither lower nor upper degree is constrained to be nonnegative. All degrees and
  bounds are integers, as required for cochain complexes.
- The same a is used in the cohomological bound and the termwise-vanishing conclusion.
- The coefficient and scheme universe is u, the pro-etale site has its published
  object/morphism universes, and module sheaves take values in Ab.{u + 1}. No equality
  of the site's distinct universes or extra smallness condition is imposed.
- No additional qcqs hypothesis is imposed on the original stratum domains.

Searches made using the prescribed wrapper (recorded by it in searches.jsonl):

- LeanFinder: “A complex of condensed sheaves dualizable on a finite constructible
  stratification of a qcqs scheme has bounded cohomology”. Eight hits concern
  condensed module constructors or general derived cohomological bounds, none this theorem.
- Loogle: `DerivedCategory.IsGE, DerivedCategory.IsLE`. Two hits give bounded or
  single-term representatives after bounds are assumed; neither proves geometric boundedness.
- Mathlib grep: `dualiz.*[Bb]ounded|[Bb]ounded.*dualiz|stratif.*dualiz`. No hits.
- LeanSearch: “Constructible complexes with condensed coefficients are cohomologically
  bounded on a quasi compact scheme”. Eight hits, including
  `DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE`; this assumes bounds and only
  gives the final representative consequence. No exact match.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for stratified dualizability and
  dualizable/bounded combinations. The finite-coefficient Perfect module gives
  `bounded_and_homology_of_isDualizable`, with discrete coefficients and a globally
  dualizable object, so it does not state this arbitrary-condensed stratified result.
  Other hits prove bounded complexes dualizable or give unrelated duality results.
- Identifier grep for `lem-pod-stratified-dualizable-bounded` in upstream and project
  source: no existing declaration. Full proposed declaration name also absent from
  Mathlib, upstream and project sources.

No statement correction, missing notion, dependency repair or disputed statement.
The only postponed proof is the named theorem matching this item.

Validation: prescribed scompile.py compiled both sandbox and library names cleanly
(3.1 seconds and 3.2 seconds), with no errors or warnings.

## Second reading by NJ

I reopened the node and the completed module for a separate clause-by-clause reading.
The qcqs binders match the first sentence, and Λ is genuinely arbitrary condensed,
with commutativity on its ring object. The coefficient is the canonical point
pullback and the derived category uses the recorded relative tensor framework.
The finite locally closed stratification structure itself supplies immersion,
cover and disjointness data; constructibility is an additional explicit hypothesis,
not silently built into the wrong general stratification interface. The existential
D and ExactPairing have precisely the required evaluation and coevaluation
orientations and both triangle equations. The bound assertion includes both tails,
a <= b, and a representative with termwise zeros below the same a. It contains no
assumption on Noetherianity, dimension, regularity, nonemptiness or nonzero coefficients.
No mismatch was found and no statement was changed. This is the worker's second
reading; independent maintainer review follows delivery, as specified by the brief.
