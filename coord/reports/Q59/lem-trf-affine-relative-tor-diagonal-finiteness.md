## Worker report

Item: `lem-trf-affine-relative-tor-diagonal-finiteness`.
Module: `Sheaf.AlgebraicGeometry.AffineRelativeTorDiagonalFiniteness`.
Main declaration: `AlgebraicGeometry.affine_relative_tor_diagonal_finiteness`.
Stage 2 only: its sole postponed theorem has proof `by sorry`; both auxiliary
arrows have real constructions. No statement correction, new node, dependency
repair, or mathematical dispute is needed.

The theorem states the full affine finiteness package. A cochain witness `C`
presents the existential derived object `M = DerivedCategory.Q.obj C`. This makes
the termwise tilde and restriction of scalars explicit without choosing an
arbitrary affine equivalence or an arbitrary tensor comparison as a hypothesis.
The helper `affineTorScalarRestriction` is an abbreviation for the existing
`SheafOfModules.restrictScalars` along the canonical inverse-image structure map.
The helper `affineDiagonalPullback` is the exact scalar-extension functor along
`p₁`, localized by Mathlib's `Functor.mapDerivedCategory`. Its additivity and
exactness are supplied by existing named theorems, not postponed proofs.

Hypotheses, matched with the node:

| Node hypothesis/object | Lean rendering |
| --- | --- |
| Commutative rings and a ring map R to A | `{R A : Type u} [CommRing R] [CommRing A] [Algebra R A]`, map `algebraMap R A`. An algebra structure is the data of the specified map; it imposes no injectivity assumption. |
| R Noetherian | `[IsNoetherianRing R]`. |
| Map flat | `[Module.Flat R A]`, equivalent to `(algebraMap R A).Flat` by `RingHom.flat_algebraMap_iff`. |
| Map finitely presented | `[Algebra.FinitePresentation R A]`. |
| U, V and g | `Spec (.of A)`, `Spec (.of R)`, `Spec.map (CommRingCat.ofHom (algebraMap R A))`. |
| B is the tensor square | `A ⊗[R] A`, with its standard first-factor A-algebra structure. |
| E in D(O_U) | `E : schemeDerivedCategory (Spec (.of A))`. |
| E pseudo-coherent | `hE : Scheme.IsPseudoCoherent (Spec (.of A)) E`. |
| Every point has an open neighbourhood | In `hlocal`, `∀ x, ∃ T, x ∈ T ∧ ...`. |
| Local integers a_T ≤ b_T | `∃ a b : ℤ, a ≤ b ∧ ...` inside the neighbourhood quantifiers. |
| Every O_V-module sheaf, not merely quasi-coherent sheaves | `∀ G : SheafOfModules.{u} (moduleRings (Spec (.of R)).toRingedSpace)`. |
| Inverse image of each test sheaf | `TopCat.Sheaf.inverseImageModule g.base V.sheaf G`, then `.over T`. |
| E restricted to the inverse-image coefficient ring and to T | `affineTorScalarRestriction` mapped termwise to a complex `K` with `Nonempty (Q.obj K ≅ E)`, followed by `(SheafOfModules.overFunctor _ T).mapHomologicalComplex (.up ℤ)`. |
| Tensor vanishing outside the local interval | `i < a ∨ b < i → CochainComplex.sheafDerivedTensorVanishes ((inverseImageRing ...).over T) ... ... i`. |
| Derived tensor computed by K-flat resolutions | The cited existing `sheafDerivedTensorVanishes` requires an actual K-flat complex P, a quasi-isomorphism P to the scalar-restricted/open-restricted representative, and vanishing of the signed total tensor with the degree-zero test module. |

The initial existential representative in `hlocal` only spells out the derived
object E; it adds no boundedness or termwise-flatness condition. Every E has such
a representative, and the K-flat tensor test is invariant under its replacement.
Restriction is to the localized open site, the same convention as the recorded
scheme pseudo-coherence definition. The ring is exactly `(g⁻¹O_V)|_T`, not O_T.

Conclusion clauses, in the order in the file:

| Node conclusion | Lean rendering |
| --- | --- |
| E has quasi-coherent cohomology | `schemeDerivedQCohProperty (Spec (.of A)) E`. |
| There exist M and a tilde isomorphism | `∃ C : CochainComplex (ModuleCat.{u} A) ℤ`, with `Nonempty (Q.obj (termwiseTilde.obj C) ≅ E)`. Set M = Q(C); the termwise tilde signature uses precisely the zero-map proof from `exists_affineQCohDerivedEquivalence`. |
| There exist integers a ≤ b | `∃ a b : ℤ, a ≤ b ∧ ...`. |
| M pseudo-coherent over A | `DerivedCategory.IsPseudoCoherent (Q.obj C)`. |
| M tensor-derived over R with every R-module vanishes outside [a,b] | `DerivedCategory.torAmplitudeIn (ModuleCat.{u} R) a b (Q.obj (restrictScalarsComplex.obj C))`. This is the existing K-flat derived tensor condition quantified over all degree-zero R-modules. It is relative amplitude over R, not absolute amplitude over A. |
| In particular H^i(M) = 0 outside [a,b] | `∀ i, i < a ∨ b < i → IsZero (C.homology i)`. Canonical `homologyFunctorFactors` identifies this homology with H^i(Q(C)). |
| B Noetherian | `IsNoetherianRing (A ⊗[R] A)`. |
| A as the B-module through multiplication μ | `(ModuleCat.restrictScalars (Algebra.TensorProduct.lmul' R).toRingHom).obj (ModuleCat.of A A)`. `lmul'_apply_tmul` sends x tensor y to xy. |
| Bounded-above finite-free resolution of that module | Existential ranks `n : ℕ → ℕ`, augmentation `ε`, and differentials `d`; `Function.Surjective ε`, `ker ε = range (d 0)`, and `∀ j, ker (d j) = range (d (j+1))`. The finite function modules represent B^{n_j}; put them in degrees -j and zero in positive degrees. No finite-length assertion is made. |
| A[0] pseudo-coherent in D(B) | `DerivedCategory.IsPseudoCoherent ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj diagonalModule)`. |
| B flat over A through p₁(a) = a tensor 1 | `∃ hflat : (algebraMap A (A ⊗[R] A)).Flat`. The tensor square's `leftAlgebra` uses `Algebra.TensorProduct.includeLeftRingHom`. |
| B[0] is the flat representative computing the tensor | The degree-zero single of the scalar-restricted regular B-module is `.kFlat`; `Q ⋙ affineDiagonalPullback hflat ≅ extendScalars.mapHomologicalComplex (.up ℤ) ⋙ Q` expresses exact termwise computation. |
| M₁ is M tensor-derived over A,p₁ with B | `affineDiagonalPullback hflat` is the exact localization of p₁-extension. The following natural isomorphism identifies its scalar restriction with `tensorRight (singleFunctor A 0 Bmodule)` in D(A), so this is the derived tensor, with its B-action retained by the target D(B). |
| Natural H^i(M₁) ≅ H^i(M) tensor over A,p₁ with B, for every i | `∀ i, Nonempty (affineDiagonalPullback hflat ⋙ homologyFunctor B i ≅ homologyFunctor A i ⋙ ModuleCat.extendScalars p₁)`. These are natural isomorphisms of functors D(A) to ModuleCat B, hence B-linear and natural in M, not a disconnected family of abstract isomorphic types. |
| H^i(M₁) = 0 for i < a | Last clause: `∀ i, i < a → IsZero ((homologyFunctor B i).obj ((affineDiagonalPullback hflat).obj (Q.obj C)))`. |

The `HasDerivedCategory` binders only choose localizations. Their universes wA,
wR, wB and wU remain independent. The open localizations for pseudo-coherence use
the same wU as their existing definition. Ring universes can be jointly enlarged
to u; no nonempty spectrum, nonzero ring, regularity, or finite global dimension
is assumed. `HasMonoidalDerivedCategory` supplies the canonical K-flat derived
monoidal structure without equating localization and coefficient universes.

Dependency declarations read and used:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, `RingHom.flat_algebraMap_iff`, `Module.Flat` (defined in `Mathlib.RingTheory.Flat.Basic`).
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `CategoryTheory.Limits.pullback` and its projections. This recorded dependency is retained; the statement uses its specified affine coordinate ring B rather than adding a second fibre-product construction.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`, `schemeDerivedQCohProperty`.
- `WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex`: `Scheme.IsPseudoCoherent`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`: the recorded K-flat interface and its public `CategoryTheory.MorphismProperty.kFlat`, specialized to module-complex quasi-isomorphisms for B[0].
- `WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence`: `exists_affineQCohDerivedEquivalence`; the signature's termwise tilde construction is reused explicitly.
- `WeilConjectures.RingTheory.RingPseudoCoherent`: `DerivedCategory.IsPseudoCoherent`.
- `Sheaf.Algebra.Homology.SheafComplexDerivedTensorVanishes`: `CochainComplex.sheafDerivedTensorVanishes` (landed node `def-trf-ringed-complex-derived-tensor-vanishing`, added to stmt_deps).
- `WeilConjectures.Topology.InverseImageModule`: `TopCat.Sheaf.inverseImageRing` and `inverseImageModule` (landed node `def-pc-topological-inverse-image-module`, added to stmt_deps).
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`: `SheafOfModules.localizedSystemRestrictionAdditive`, the existing instance for actual open restriction (landed node `lem-pur-site-restriction-module-adjunction-exact`, added to stmt_deps).
- `WeilConjectures.AlgebraicGeometry.TensorPullback`: `Scheme.Modules.tensorPullbackRingMap`.
- `Mathlib.Algebra.Category.ModuleCat.Descent`: `ModuleCat.preservesFiniteLimits_extendScalars_of_flat`; Mathlib's `extendRestrictScalarsAdj` supplies additivity.
- `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`: `DerivedCategory.torAmplitudeIn`.

All recorded proof-dependency modules are imported, including the Mathlib leaves:
`PseudoCoherentQCoh`, `AffinePseudoCoherentCriterion`, `AffineQCohDerivedEquivalence`,
`RingPseudoCoherent`, `KFlatResolutionIndependentCoefficients`,
`RingedSiteRestrictionKFlat`, `LocalizedSiteTensorRestriction`,
`AffineRelativeTorAmplitudeCriterion`, `RingedFlatSingleTensorCohomology`,
`Mathlib.RingTheory.FiniteType`, `WeilConjectures.RingTheory.FiniteFreeResolution`,
`Mathlib.RingTheory.Flat.Stability`, `Mathlib.AlgebraicGeometry.AffineScheme`, and
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`. In particular the five proof
steps in the docstring follow the node's recorded dependencies, including its
empty-cover case and the B-linearity argument by multiplication endomorphisms.

Sources checked: local `duality.tex`, lemma-relative-dualizing-complex-algebra,
lines 7054 onwards (0E2U); `perfect.tex`, lemma-tor-dimension-rel-affine (0DHY);
`more-algebra.tex`, lemma-Noetherian-pseudo-coherent; and the full signatures and
docstrings of the recorded affine equivalence, pseudo-coherence and K-flat APIs.
The current example `Sheaf/CategoryTheory/CompactObject.lean` is withdrawn; its
node now records `WeilConjectures.CategoryTheory.CompactObject`, which was read
for the current public module conventions.

Edge cases checked mathematically before and after writing:

- A = 0: Spec A is empty, the local hypothesis is vacuous, and every A- or B-module is zero. Choose interval [0,0] and ranks all zero. No nonempty finite cover is required.
- E = 0: the zero model satisfies every interval, and all vanishing conclusions hold.
- R = A with the identity map: B identifies with A and first-projection scalar extension is the identity. No unwanted faithful-flat or nonzero hypothesis appears.
- A nonregular finitely presented algebra over a field, e.g. k[x,y]/(xy): the diagonal may have an infinite resolution; the delivered ranks/differentials permit it. No perfectness of the diagonal is asserted.
- Negative cohomological degrees and a = b: all indices are integers, and the outside condition is the strict disjunction `i < a ∨ b < i`.
- Unbounded input complexes are allowed. Only the resulting model's cohomology is bounded by [a,b]; neither a bounded representative nor absolute A-Tor amplitude is assumed.

Searches performed with the prescribed `msearch.py Q59 <item>` wrapper:

- LeanFinder: `A pseudo coherent affine complex with locally finite relative Tor dimension has bounded relative Tor amplitude and a pseudo coherent diagonal module`. Eight hits were derived t-structure bounds and single-complex morphism lemmas; no exact package.
- Loogle: `Module.Flat, IsNoetherianRing`. Three hits were completion-flatness and smooth/formally-smooth flatness; no exact statement.
- Mathlib grep: `relative.*[Tt]or|diagonal.*[Pp]seudo`. Twenty-two lexical hits in unrelated colimit, topology and algebra files; no exact statement.
- LeanSearch: `A pseudo coherent complex on Spec A with locally finite relative Tor dimension over a Noetherian ring has a uniform relative Tor bound and pseudo coherent tensor square diagonal`. Eight hits included `diagonal_SpecMap`, finite-presentation/quasi-coherence and completion facts; none states the package.
- Local `rg` over both `lean/WeilConjectures` and `lean/Sheaf`: item id, `flatBaseChange|flat_baseChange|flat_base_change|diagonal.*[Pp]seudo`, scalar-extension/derived-tensor names, and all three proposed declaration names. No exact declaration or name collision. Existing flat scalar extension at a successor coefficient universe was inspected; the specialization here uses the existing general `mapDerivedCategory` to retain arbitrary u and independent localization universes.
- `dag/lean_names_upstream.json` was searched for all three new declaration names: no collision.

Validation: prescribed `scompile.py` compiled both the sandbox module and its
library-path module cleanly. Initial elaboration diagnostics were repaired by
opening the existing tensor-product notation, exposing the existing additive
restriction instance, and importing the general derived-monoidal instance. No
extra mathematical hypothesis was introduced for any diagnostic.

## Second reading by Q59

I reopened the node and reread the completed signature clause by clause. This is
a separate pass by the same worker; the dispatcher explicitly forbids starting
other agents, and the maintainer supplies the independent review.

The reading checked the important distinctions explicitly: the local tests range
over all O_V-module sheaves and tensor over the inverse-image ring restricted to
T; the global interval is relative over R; the diagonal action is multiplication
and the first projection is a tensor 1; the diagonal resolution is bounded above
with possibly infinitely many terms; and the cohomology comparisons are natural
B-linear isomorphisms. The cochain witness is a presentation of the existential
M, not an added boundedness condition. The final vanishing uses the same lower
bound a as the relative interval. All hypotheses and conclusions in the tables
above were matched against the node. No mathematical mismatch or statement
change was found. The auxiliary arrows are actual existing restriction and
localization constructions, with no arbitrary map or nonunique existence choice.
