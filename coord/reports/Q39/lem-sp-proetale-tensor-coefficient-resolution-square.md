## Worker report

The module `Sheaf.Paper.ProEtaleTensorCoefficientResolutionSquare` states the entire
coefficient-resolution square as
`AlgebraicGeometry.Scheme.proEtale_tensor_coefficient_resolution_square`.
This theorem has the sole `sorry` in the file. Seven helpers only expand existing
constructions or the resolution-independence clause; their data contain no `sorry`.
No dependency module, new DAG node or statement correction is needed.

Source read: `literature/stacks-project/sites-cohomology.tex`,
`lemma-pullback-tensor-product` (Tag 07A4), including its representative proof and
its use of flat-term K-flat tensor representatives; the construction preceding
`definition-derived-tor` (Tag 06YU) supplies the one-sided normalization. The node's
seven proof steps are included in the theorem docstring.

The hypothesis and clause correspondence is as follows.

| Node text | Lean rendering |
| --- | --- |
| A scheme morphism f:X→Y with its small pro-etale sites | `{X Y : Scheme.{u}}`, `f : X ⟶ Y`; all ring sheaves use `ProEt.topology`. The original site object universe is u+1 and its Hom universe is u. |
| R_Y a commutative ring sheaf, identified inverse-image coefficients c | `R : Sheaf (ProEt.topology Y) CommRingCat.{u+1}`, analogous `S` on X, and `c : (proEtaleSheafInverseImage f CommRingCat.{u+1}).obj R ≅ S`. No constant-ring, finiteness or torsion assumption. |
| F exact identified-coefficient inverse image | The published `proEtaleRingModulePullback f R S c`; its termwise functor is abbreviated `proEtaleResolutionPullback`. Exactness is supplied by its published instances. |
| Ordinary uncompleted unbounded L and its epsilon | The existing `proEtaleRingDerivedPullback` and `proEtaleRingDerivedPullbackFactors`. The latter is the exact `mapDerivedCategoryFactors`, on all complexes, with direction LQ→QF. |
| Localization Q at quasi-isomorphisms | `DerivedCategory.Q`, with `QuasiIso` from Mathlib. |
| Sheafified tensor, signed direct-sum total tensor | `proEtaleOrdinaryTensor` is the existing localization tensor on module sheaves. `proEtaleResolutionTotal` is just `Functor.uncurry.obj` of its `map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ)`. It gives `CochainComplex.mapBifunctor`, with direct sums and the sign (-1)^p. |
| The specified two-representative tensor isomorphisms | Parameters `a : ProEtaleTensorModel Y R`, `b : ProEtaleTensorModel X S`; their `representative` fields are natural isomorphisms on the full flat-term K-flat representative subcategories. These are exactly the published tensor-presentation data, not arbitrary objectwise isomorphisms. |
| Canonical derived tensor pullback tau | `proEtaleCanonicalTensorComparison f R S c a b`, selected by the published unique representative-square characterization. No freely chosen comparison map is a hypothesis. |
| P is flat-term K-flat | `hP : proEtaleFlatRepresentatives Y R P`, defined upstream as `P.IsAcyclicTensorKFlat ∧ ∀ n, IsFlatOnSite (P.X n)`. At these site/coefficient universes the K-flat predicate agrees definitionally with the recorded independent-coefficient predicate. |
| N any module sheaf | `N : proEtaleRingModules Y R`. There are no other assumptions on N. |
| H flat-term K-flat, q:H→N[0] any quasi-isomorphism | `hH : proEtaleFlatRepresentatives Y R H`, `q : H ⟶ proEtaleResolutionSingle Y R N`, `[QuasiIso q]`. `proEtaleResolutionSingle` is Mathlib's single-complex functor at zero. |
| Sigma induced by inverse-image sheaf tensor with unit normalization | `proEtaleResolutionSigma` is the inverse of the published `proEtaleTensorPullbackTotalIso`. That total map is built from `proEtaleOrdinaryTensorPullback`, uniquely normalized by the module adjunction unit on pure tensors; its naturality is retained. Thus no choice of sigma is added. |
| Commuting square of complexes | The first conjunct is `sigma(P,H).hom ≫ (1 tensor Fq) = F(1 tensor q) ≫ sigma(P,N[0]).hom`. `proEtaleResolutionTensorMap` is exactly the total bifunctor's map at `(𝟙 P,q)`. Lean composition reads left to right. |
| Both vertical arrows quasi-isomorphisms | The next two `QuasiIso` conjuncts, with exactly `F(1 tensor q)` and `1 tensor Fq`. |
| Top source total and its inverse image flat-term K-flat | The next two `proEtaleFlatRepresentatives` conjuncts at Tot(P,H) and F Tot(P,H). |
| Top target total flat-term K-flat | The existential `hFP,hFH` give the pullback representatives; the following conjunct gives the property for Tot(FP,FH). |
| Localized top arrow is exactly tau under r and epsilon | The next equality is `L(rY) ≫ tau ≫ tensor(epsilonP,epsilonH) = epsilonTot ≫ Q(sigma) ≫ rX`, with the precise published representative maps. |
| AlphaY and alphaX are the stated composites | `proEtaleCoefficientResolutionAlpha` is the actual composite `e.inv ≫ representative.hom ≫ tensor.map (𝟙,Qq)`. The witnesses `eY,eX` have their forward maps explicitly equated to Q(1 tensor q) and Q(1 tensor Fq), respectively, so their inverse is forced. This encodes the specified canonical inverse without assuming a vertical quasi-isomorphism. |
| Both alpha maps are isomorphisms | Two explicit `IsIso` conjuncts for these composites. |
| Both maps independent of q | Two `ProEtaleCoefficientResolutionIndependent` conjuncts, one over Y at N[0], one over X at F(N[0]). This transparent predicate expands to equality of the formula for every pair of flat-term K-flat quasi-isomorphisms resolving the fixed second argument and every pair of inverse witnesses with the prescribed forward maps. It is part of the main theorem's conclusion, not a new hypothesis. |
| F(N[0]) identified with (FN)[0] | The target uses F(N[0]) literally. The existing `(proEtaleRingModulePullback f R S c).mapCochainComplexSingleFunctor 0` is the canonical identification with (FN)[0]; it is constructed by `HomologicalComplex.singleMapHomologicalComplex`. Expressing the square before this canonical identification keeps all arrows composable without inserting unrelated choices or weakening it. |
| Final derived identity | The last equality is exactly `epsilonU ≫ Q(sigma(P,N[0])) ≫ alphaX = L(alphaY) ≫ tau(QP,QN[0]) ≫ tensor(epsilonP,epsilonN[0])`, the node's right-to-left formula written in Lean's order. |
| No boundedness of P,H, no flatness or boundedness restriction on N; bottom need not be K-flat | P and H are unrestricted integer-indexed complexes and N is unrestricted. Flatness/K-flatness is asserted only for the listed top complexes and representatives. |

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` publicly imports
  `ProEtaleOperationsCanonicalAdjunction` and `ProEtaleOperations`, retaining the
  full arbitrary-ring-sheaf `proEtaleRingModules`, `proEtaleRingModulePullback`,
  `proEtaleRingDerivedPullback`, and `proEtaleRingDerivedPullbackFactors` interfaces.
  The primary constant-ring abbreviation is not used to specialize this theorem.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, its preadditive structure and total-tensor
  colimit instances; `Mathlib.Algebra.Homology.BifunctorShift`:
  `CochainComplex.mapBifunctor`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses` publicly retains
  `ProEtaleCanonicalTensorPullback`: `proEtaleOrdinaryTensor`,
  `proEtaleFlatRepresentatives`, `ProEtaleTensorModel`,
  `proEtaleOrdinaryTensorPullback`, `proEtaleTensorPullbackTotalIso`,
  `proEtaleCanonicalTensorComparison`. The primary general ringed-topos theorem's
  representative equation was also read, including its comparison orientation.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` and its definitional specialization;
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`; `Mathlib.Algebra.Homology.QuasiIso`: `QuasiIso`.

All nine recorded proof-dependency modules are imported without `public` unless
already a statement dependency. They are CochainPullbackTensorCoherence,
ProEtaleInverseImageTensorComparison, KFlatRingedToposPullback,
KFlatTotalTensorModel, SiteOneSidedTensorNormalization,
Mathlib's DerivedCategory.ExactFunctor, SiteDerivedTensorDescentIndependentCoefficients,
TensorPullbackRepresentativeDescent, and RingedTopoiCanonicalTensorPullbackOfUniverses.
Their relevant signatures and docstrings were read; the proof follows their canonical
comparisons rather than introducing a new tensor or normalization.

Edge cases checked before and after writing: identity f; P=0; H=0 when permitted by q;
N=0; the empty scheme; zero coefficient ring; complexes unbounded in both directions;
nonflat N (e.g. a torsion quotient over the constant integer ring); and arbitrary
(nonidentity) coefficient identification c. None is excluded by the binders. The
bottom total is never assumed K-flat. Inverting localized vertical maps is encoded
by prescribed-forward-arrow isomorphisms, whose existence is a conclusion. Resolution
independence quantifies over all eligible resolutions, including the identity resolution
when N[0] itself is flat-term K-flat. Universes do not identify the site's Hom universe
with its object universe.

Searches performed with the prescribed `msearch.py` wrapper:

- LeanFinder: `Exact inverse image tensor comparison coefficient resolution square with K flat complexes and arbitrary module sheaves`. Eight hits, all ordinary `Module.Flat` tensor-exactness lemmas; no match.
- Loogle: `"QuasiIso", "tensor"`. Zero hits.
- Mathlib grep: `KFlat|tensorPullback`, subdirectory `Algebra/Homology`. Zero hits.
- LeanSearch: `A coefficient resolution of an arbitrary sheaf gives a commuting tensor pullback square and a resolution independent derived tensor comparison`. Eight hits about ordinary sheaf pullback/free modules, pullback adjunctions and Mayer-Vietoris; no match.
- `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for
  `coefficientResolution|resolutionSquare|tensorCoefficient`: unrelated coefficient,
  cone, and scalar-change declarations, no theorem with these clauses.
- `rg` for the item id in `lean/WeilConjectures`: no hits.
- Exact-name `rg` in both source trees and `dag/lean_names_upstream.json` for the new
  helper and theorem names: no collisions. The canonical constructions that do exist
  are reused by abbreviation or explicit composition.

No statement dispute or node fault found. The retired example CompactObject module
was read: it now contains only a withdrawal notice, so the current required module-mode
header and public-section convention are followed instead.

Validation: the prescribed `scompile.py` compiled the full statement in sandbox and
library module contexts with no errors or warnings. The only postponed proof is the
main theorem. Final dry-run and delivery results follow below.

## Second reading by Q39

This is a self-check, not an independent agent review: the dispatcher explicitly
forbids starting another agent, and the maintainer provides the independent reading.
I reopened the node and the written signature and checked the correspondence above.
The initial draft put general-complex independence in a separate theorem; the final
version instead unfolds independence as a real predicate and asserts it for exactly
the source and pulled-back coefficient complexes in the main theorem, leaving only
one postponed theorem matching this DAG node. The two specified inverse witnesses
are concluded and constrained by forward-map equalities; neither becomes a hypothesis.
The top representative equality and bottom final equality both use the canonical
published tau, and the direction of sigma is the inverse of the published total map.
All of the node's hypotheses and clauses are present, with no flatness restriction
on N or K-flatness claim for P tensor N. No dependency record is changed.
