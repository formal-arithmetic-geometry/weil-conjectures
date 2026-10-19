## Worker report

The module `Sheaf.Algebra.Homology.PseudoCoherentRHomFlatBaseChange` states
`CategoryTheory.pseudoCoherentRHom_flat_base_change`, with its only theorem proof
`sorry`. It defines the actual canonical component
`pseudoCoherentRHomScalarMap`, derived punctual evaluation, and the standard
localization instances. All definition data are explicit constructions from the
recorded interfaces. No theorem is proved in this delivery.

The node's statement is unchanged. Two already landed nodes are added to
`stmt_deps`: `lem-sfb-dc-hom-scalar-adjunction` supplies the canonical representing
Hom bijections and normalized presentations, and
`lem-weil-pbc-singleton-site-module-comparison` supplies the precise equivalence
between the node's ordinary-module and one-object-site descriptions. No new
notion or dependency repair is needed.

### Hypotheses and conclusions, clause by clause

| Node clause | Lean rendering |
| --- | --- |
| Commutative rings R,S and a homomorphism | `{R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)` |
| Flat homomorphism | `hφ : RingHom.Flat φ`, the recorded Mathlib predicate |
| Ordinary module derived categories regarded on the trivial one-object site | `DerivedCategory (singletonModuleCategory R)` and the analogous S category. `singletonSite = Discrete PUnit`, `singletonTopology = ⊥`, and `singletonRingSheaf R` are the existing punctual-site constructions. |
| The identification with ordinary modules | `e : singletonModuleCategory R ≌ ModuleCat R`, `he : e.functor = singletonEvaluation R`; `pseudoCoherentRHomEvaluation e he` is its actual exact induced derived functor. The additive instance is transported from the existing evaluation instance using he. |
| No additional existence assumption on this equivalence | `singleton_site_module_comparison R` supplies exactly such e and he, together with compatibility of localization, tensor, K-flatness and the scalar unit. Both e and the bound are presentations, not restrictions on R. |
| RHom is the existing K-injective construction | Each occurrence is `derivedInternalHomOfUniverses.{0, 0, u, u+1} singletonTopology (singletonRingSheaf R)` or its S version. No private RHom is defined. |
| Derived scalar extension | `(M.scalar (singletonRingMap φ)).derived`. `ScalarDerivedPair` fixes ordinary sheafified scalar tensor on objects and maps, the universal left-derived pair and K-flat comparisons, as well as the ordinary and derived adjunction normalizations. |
| Availability of the presentations M, μ | `scalarInternalHomAdjunction_exists` specializes to this punctual site and supplies M and a normalized `ScalarHomTensorComparison M (singletonRingMap φ)` for every map. The quantification is over these canonical presentations, all determined by their universal properties and representative normalizations. It is not an assumption of an arbitrary functor, isomorphism or arrow. |
| E is pseudo-coherent | `DerivedCategory.IsPseudoCoherent ((pseudoCoherentRHomEvaluation e he).obj E)`. This is exactly the recorded definition: an isomorphic bounded-above finite-free complex in D(R), with no lower bound and no perfectness requirement. |
| L is in D+ | `∃ a : ℤ, L.IsGE a`. `DerivedCategory.isGE_iff` identifies this with vanishing of every cohomology object in degrees below a. Exact punctual evaluation identifies this with the same condition on ordinary modules. No termwise bound on a prescribed representative is imposed. |
| Source of the displayed map | The source bifunctor is `derivedInternalHomOfUniverses ... R ⋙ (M.scalar ...).derived`, hence scalar extension of RHom_R(E,L). |
| Target of the displayed map | The target bifunctor is `((M.scalar ...).derived.op.prod (M.scalar ...).derived) ⋙ derivedInternalHomOfUniverses ... S`, hence RHom_S(F E,F L). |
| Canonical map, not an unspecified isomorphism | `pseudoCoherentRHomScalarMap`: first apply RHom_R(E,-) to `(M.scalar ...).adjunction.unit.app L`; apply `(scalarHomBijection ...).symm` to obtain the map into restricted RHom_S(F E,F L); finally apply scalar-adjunction `homEquiv.symm`. These are literally the operations defining Equation 0E1X via Tag 0E1W. |
| Naturality in both variables | `∃ β : sourceBifunctor ⟶ targetBifunctor` with `∀ E L, β.app (op E,L) = pseudoCoherentRHomScalarMap M φ μ E L`. A natural transformation on the opposite/product domain expresses contravariance in E and covariance in L, including arbitrary derived morphisms. Its components are fixed on all pairs, not just qualifying pairs. |
| Isomorphism in D(S) | For every E,L, the pseudo-coherence and D+ conditions imply `IsIso (β.app (op E,L))`. The components are the specified canonical map by the preceding equality. |
| No Noetherian hypothesis and no perfectness of E | Neither occurs in the signature. |
| Chosen morphism sizes | `pseudoCoherentRHomModuleDerived` and `pseudoCoherentRHomSingletonDerived` use `HasDerivedCategory.standard` at u+1. These are constructions; no small-localization assumption is added. The site has object/morphism universes 0, coefficients and modules u, and localization u+1. u is arbitrary. |

The proof docstring follows all seven steps of the DAG proof: bounded-above
finite-free and bounded-below models, exact flat tensor on cycles and boundaries,
K-flat comparison with ordinary scalar extension, the bounded-above projective
Hom model, the normalized pure-tensor chain map, degree-dependent bounded stupid
cutoffs, and identification with the unit/adjunction construction plus naturality.

### Dependency declarations read and used

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat` (its definition is
  `Module.Flat R S` for φ.toAlgebra); `Mathlib.RingTheory.Flat.Basic`:
  `Module.Flat.lTensor_exact`, `Module.Flat.rTensor_exact` for the proof plan.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory.Q`; the localization is at
  cochain quasi-isomorphisms. `Mathlib.Algebra.Homology.DerivedCategory.TStructure`:
  `IsGE`, `isGE_iff` and the standard t-structure, publicly available through
  the pseudo-coherence module.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`; read the K-injective
  localization definition and its replacement/representative comparisons.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `nonempty_derivedChangeOfRingsCochainModel`; read the ordinary object/map
  equations, universal counit, triangulatedness and K-flat computation fields.
  The imported normalized scalar-pair interface presents this same universal
  construction with its adjunction, rather than selecting a second operation.
- `Sheaf.RingTheory.RingPseudoCoherent`:
  `DerivedCategory.IsPseudoCoherent`; its full body is the bounded-above
  finite-free representative condition used here verbatim.
- `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction`:
  `ScalarHomModels`, `ScalarHomTensorComparison`, `scalarHomBijection`,
  `scalarInternalHomAdjunction_exists`, and `SheafOfModules.ScalarDerivedPair`.
  Read the full presentation and normalization fields and the five composed
  representing equivalences. Their inverse direction is crucial in our map.
- `Sheaf.ProperBaseChange.SingletonSiteModuleComparison`:
  `singletonSite`, `singletonTopology`, `singletonRingSheaf`,
  `singletonRingMap`, `singletonModuleCategory`, `singletonEvaluation`,
  `singletonEvaluationAdditive`, `singleton_site_module_comparison`.
  Read its actual functors, tensor comparison, scalar unit normalization and
  derived comparison rather than identifying coefficient categories by name.

Proof-only imports follow all recorded proof dependencies with Lean records:
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.AlgebraicGeometry.MixedGlobalExtension`,
`Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel`,
`Sheaf.Algebra.Homology.NormalizedRingHomExtension`,
`Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap`,
`Sheaf.Algebra.Homology.PerfectRingHomScalarExtension`, and
`Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`. The Hom-complex
module is imported transitively by the recorded perfect-map module; the
standard t-structure and flat exactness Mathlib modules are also present.
There is no import cycle with the two consumers of this item.

### Source and edge cases

Read `more-algebra.tex`, lemma-base-change-RHom clause (3) (Tag 0A6A),
Equation equation-base-change-RHom (0E1X), lemma-upgrade-adjoint-tensor-RHom
(0E1W), and the finite-support proof of
lemma-internal-hom-evaluate-tensor-isomorphism (0ATK(3)). They impose precisely
flatness, pseudo-coherence and bounded-below target, with no ring finiteness.

Checked zero E and zero L; zero source and/or target rings whenever a unital
map exists; the identity ring map; shifted finite-free objects; a source
unbounded to the left; arbitrary integer lower bounds for L; and genuinely
non-Noetherian rings. None is excluded. A nonperfect E is allowed; the degreewise
bounded cutoff is only a proof tool and is never imposed on E. An unbounded-below
L does not receive the isomorphism assertion, although its canonical component
and naturality are still specified. The punctual topology imposes no geometric
condition. There is no false or disputed statement and no correction.

### Searches for an existing statement

All required searches were made through the prescribed wrapper and direct
read-only source searches:

- LeanFinder: “Derived Hom from a pseudo coherent complex to a bounded below
  complex commutes with flat scalar extension”: eight hits on Ext, exact-functor
  Ext maps, projective resolutions and derived-category fractions; no match.
- Loogle: `MonoidalClosed, Functor.closedComparison`: no hits (unknown
  identifier MonoidalClosed in the search index). Inspected the actual
  Mathlib/WeilConjectures internal-Hom comparison sources separately.
- Mathlib grep through msearch: `PseudoCoherent|RHom|closedComparison` in
  `Algebra/Homology`: 25 hits on complex bifunctors, monoidal complexes and
  linear Hom; none is this pseudo-coherent base-change assertion.
- LeanSearch: “derived Hom pseudo coherent flat ring homomorphism bounded
  below base change isomorphism”: eight ordinary flatness, base-change and
  differentials hits; no derived-Hom match.
- Direct rg in WeilConjectures and lean/Sheaf for pseudo-coherence, RHom,
  scalar extension, flat base change, singleton comparison and normalized Hom
  extension found the existing interfaces used above, perfect-source base
  change and quasi-coherent RHom statements, not the present theorem.
- Direct rg for the exact node id in WeilConjectures returned no hit. The
  side-library occurrence in `AlgebraicShriekCalculus` is a proof-docstring
  citation of this node, not a declaration of it.
- Direct rg for all five proposed full declaration names in Mathlib,
  WeilConjectures, the side library and dag/lean_names_upstream.json returned
  no collision.

### Validation

The delivered module compiles without errors or warnings through `scompile.py`.
The initial diagnostics were an incorrectly guessed proof-import module and
universe inference in the comparison application; the former now imports the
actual Mathlib flat-exactness module, and all scalar comparison universes are
explicit. A helper transports evaluation additivity along he, so no new
additivity or exactness hypothesis is assumed. Only the theorem ends in sorry.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
