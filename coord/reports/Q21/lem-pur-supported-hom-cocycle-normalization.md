## Worker report

The module `Sheaf.Paper.SupportedHomCocycleNormalization` states
`AlgebraicGeometry.supportedHom_cocycle_normalization`, with its sole theorem proof
`sorry`. Its helpers give real definitions of the exact evaluation and cocycle
properties being asserted. No object, functor, or map is chosen from an existence
statement. The node copy changes only `lean`; there are no new nodes, dependency
repairs, statement corrections, or statement disputes.

The source was read: Milne, LEC, Section 9, Example 9.5 and the proof of Theorem 9.4,
pp. 66--67 (evaluation at 1, the open adjunction, and the open-closed Hom kernel).
I also read the current main-20261015 blueprint proof of lem-amb-closed-support-hom
(the exact constant sequence followed by its Hom triangle), the recorded roof
comparison, and the published closed-support cone construction and projections.

### Hypotheses and clauses

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| The finite coefficient datum A=A_(E,n) | `P : WeilConjectures.PurityFiniteSetting.{u}`; `P.Ring` is the actual quotient and `P.Coefficient` its standard `ULift` into the module universe. |
| Schemes and a closed immersion | `{Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]`. |
| Complementary open immersion | `i.openComplement.ι` and the existing `Etale.supportRestrictionArrow i` / `ProEtale.supportRestrictionArrow i`. Using the canonical complement names the same open subobject; arbitrary complementary immersions identify with it by their open-immersion isomorphism. |
| Either small site, ordinary module sheaves, and size convention | The two `supportedHomNormalization` specializations use `X.smallEtaleTopology` and `Scheme.ProEt.topology X` on their actual object types `Type (u+1)` with morphisms in `Type u`, and `ModuleCat.{u+1} P.Coefficient`. No equality of these two site universes is imposed. |
| Ordinary A_X-module sheaves | Fixed-scalar module-valued sheaves are the published ordinary constant-ring module presentation. On the pro-etale site `Scheme.sfIntrinsicModuleEquivalence` realizes them as `ringedSiteModules` over `proEtaleConstantRing`; it is the same ordinary module category, without any completed coefficients. |
| P=i_*A_Z with underived image | `Etale.lowerStar` and `ProEtale.lowerStar` applied to the rank-one constant module in the respective `supportedHomNormalization`. |
| Actual constant restriction rho | Etale: `supportedHomConstantRestriction`, the adjoint of `Scheme.upperStarConstantSheafIso.hom`. Pro-etale: the existing `Scheme.proEtaleConstantDirectImageMap`, defined by sheafifying the constant-presheaf unit. Both preserve the scalar itself. |
| The pro-etale constant coefficient object | `Scheme.proEtaleFixedConstantModule Z P.Ring` is literally `constantSheaf` on that site. It is canonically the same constant as `P.constant Z` via the published comparison constant-sheaf isomorphism; this presentation avoids introducing a second coefficient unit. |
| Actual support kernel S(M) | The existing `Sheaf.supportedSectionsFunctor`, whose object is `kernel (M.obj.map j.op)`. Its specialization agrees with the module-valued support functor in `SupportCohomology`. |
| Values and Hom are abelian groups | `SupportedHomEvaluationIso` has codomain the support functor followed by `forget₂ ... AddCommGrpCat`, and domain `preadditiveCoyoneda.obj (op B)`. All `chi` components are `≃+`. |
| Enough injectives | The specializations synthesize the existing enough-injectives instances for these small-site Grothendieck module-sheaf categories. The generic interface exposes this instance as a parameter, without adding a hypothesis to the theorem. No assertion that scalar forgetting preserves injectives is made. |
| Additive natural isomorphism theta | `SupportedHomCocycleNormalization.theta` is a natural isomorphism between those abelian-group-valued functors. |
| theta(f)=(f rho)(1) | Its `evaluation` field asserts `kernel.ι (...) (theta.hom.app M f) = ((constantSheafAdj ...).homEquiv ... (rho ≫ f)) 1`. The constant adjunction is exactly evaluation on the sheafification image of the scalar 1. |
| Open counit precomposition is actual restriction | `Etale.SupportedHomOpenEvaluation` and `ProEtale.SupportedHomOpenEvaluation` compare evaluation of the actual open adjunct of `supportedHomOpenCounit ≫ g` with `M.obj.map` of the site arrow whose underlying scheme map is `j`, applied to `g(1)`. The open constant maps are the sheafified scalar-preserving maps; the counits are their actual adjoints. Both are asserted in the main theorem. |
| No automorphism of S hidden in theta | `evaluation` is equality after the monic kernel inclusion, so it determines theta pointwise. |
| Cochain complexes, D+, integer shifts, and P in degree zero | `CochainComplex.Plus`, `DerivedCategory.Plus`, `(a : ℤ)`, `⟦a⟧`, and `(DerivedCategory.singleFunctor ... 0).obj B`. |
| All bounded-below F, naturally | `SupportedHomChi` quantifies over every `F : DerivedCategory.Plus ...`; `SupportedHomChiNatural` is the equation for every derived morphism `v : F ⟶ G`. |
| Every bounded-below degreewise injective resolution | `SupportedHomChiCocycle` quantifies over every `K I : CochainComplex.Plus ...`, `[∀ r, Injective (I.obj.X r)]`, `(e : K ⟶ I)` and `[QuasiIso e.hom]`. K-injectivity follows for such I and is not an extra assumption. |
| Supported cocycle s | `x : (S(I)).cycles a`; its underlying section is `(S(I)).iCycles a x`. Mathlib's cycles object is the actual kernel of the differential. |
| Unique f_s with the required evaluation | `∃! f : B ⟶ I.obj.X a` with `theta.hom.app ... f = iCycles ... x`; the evaluation field identifies this equality with the node's formula `(f rho)(1)=s`. |
| f_s is a cocycle | The same property includes `∃ hf : f ≫ I.obj.d a (a+1) = 0`. |
| Transport [s] to supported hypercohomology | `Sheaf.supportSequenceModelIso ... I (Plus.Q.obj K) (supportedHomResolutionIso ... e).symm a`, applied to `homologyπ a x`. This is the published canonical homology-to-Q comparison, followed by the actual derived unit on I and inverse derived resolution map. |
| Roof formula | The right side is `ShiftedHom.map (Cocycle.equivHomShift.symm (Cocycle.fromSingleMk f ... hf)) DerivedCategory.Q`, followed by the quotient-to-derived identification into `Plus.Q(I)` and the shifted inverse of `supportedHomResolutionIso`. Thus it is exactly Q(f_s) followed by inverse shifted Q(e). |
| Quotient comparisons | `supportedHomResolutionIso` uses `quotientCompQhIso.hom` at K, `asIso (Q.map e.hom)`, and `quotientCompQhIso.inv` at I. The cocycle arrow uses the same inverse at I. These directions are checked against the current API. |
| Resolution and cocycle independence | The same `chi F a` is used for all e and x and is defined on the homology object, not on cocycle representatives. A boundary has the same `homologyπ` image, and the canonical comparison transports any resolution to that same source object. Naturality is an additional explicit field. |
| Equivalent derivation of theta inverse and roof comparison | The uniquely evaluation-normalized theta, canonical derived-unit class, and roof equation specify this composite on every injective representative. Such classes exhaust cohomology, so this is precisely the comparison obtained by deriving theta inverse and composing with the roof-normalized RHom comparison. An unrelated comparison cannot meet the displayed formula. |
| Etale restriction-cone identification | `e.ConeAgreement` uses the actual restriction and kernel inclusion (`supportedHomAbelianRestriction` and `supportedHomAbelianInclusion`), mapped termwise, and the published `CochainComplex.closedConeLift`. It asserts that kernel-to-cone inclusion and the Hom-to-cone map obtained by composing termwise theta with that inclusion are quasi-isomorphisms. These fixed maps specify the cone realization, sending s to (0,s); their source-summand sign is the published one. Combined with `e.cocycle`, the inverse cone comparison sends (0,s) to exactly the same roof. |
| No geometric or coefficient finiteness conditions beyond the node | The main theorem has no quasi-compactness, constructibility, finite-Tor, purity, bounded-above, or restriction on a. |

### Dependencies and reuse

* `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, `.Ring`,
  `.Coefficient`, `.constantEtale`; the coefficient ring is not redefined.
* `Mathlib.AlgebraicGeometry.Scheme`, `...Morphisms.ClosedImmersion`, `...OpenImmersion`,
  `...Sites.Etale`, `...Sites.Proetale`: `Scheme`, `Scheme.Hom`, `IsClosedImmersion`,
  `IsOpenImmersion`, `Scheme.smallEtaleTopology`, `Scheme.ProEt` and its topology.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules` is
  Mathlib's `SheafOfModules`; the fixed-scalar realization is already published in
  `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero` as
  `Scheme.sfIntrinsicModuleEquivalence`, with extension `sfIntrinsicExtensionByZero`.
* `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`, `constantSheafAdj`.
* `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` and the pro-etale
  `...FiniteCoefficient.UpperLowerStar.Defs`: their `lowerStar`; the etale adjunction
  and `Scheme.upperStarConstantSheafIso` fix the closed constant map.
* `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `Scheme.proEtaleConstantDirectImageMap`, the fixed-scalar presentation of the recorded
  ordinary intrinsic module direct image `Scheme.proEtaleConstantModuleDirectImage`.
* The respective etale and pro-etale open `LowerShriek...Defs`:
  `openImmersionLowerShriekAdjunction`, `openImmersionRestriction`. The pro-etale
  constant open map is the existing `Scheme.proEtaleFixedOpenConstantMap` in
  `Sheaf.AlgebraicGeometry.ProEtaleSupportedConstantPresentation`.
* `Sheaf.AlgebraicGeometry.SupportCohomology`:
  `Sheaf.supportedSectionsFunctor`, `Etale.supportRestrictionArrow`, and its pro-etale
  counterpart. Its abelian etale `supportSections` is not silently used for module
  sheaves: the same general kernel functor is applied to ModuleCat, as the item asks.
* `Sheaf.AlgebraicGeometry.SupportLongExact`:
  `Sheaf.supportHypercohomologyFunctor`, `Sheaf.supportedSectionsInclusion`, and
  `Sheaf.supportSequenceModelIso`, whose definition includes the actual derived unit.
* Mathlib: `EnoughInjectives`, `DerivedCategory`, `DerivedCategory.Plus`,
  `Functor.rightDerivedFunctorPlus`, `CochainComplex.HomComplex.Cocycle.fromSingleMk`,
  `Cocycle.equivHomShift`, `ShiftedHom.map`, and `DerivedCategory.quotientCompQhIso`.
* `Sheaf.AlgebraicGeometry.ClosedSupportHom`: `Etale.closedSupportHom` is the recorded
  cone theorem; `CochainComplex.closedConeLift` and its projections are reused to
  specify its normalization. The cone map is not replaced by an arbitrary isomorphism.
* `Sheaf.Paper.SupportedCohomologyHom`: `ProEtale.supported_cohomology_hom` is the
  recorded existence statement, imported as the comparison this item normalizes.
* `Sheaf.CategoryTheory.Abelian.RHomDerivedRoof`:
  `CategoryTheory.Functor.exists_rhom_hom_derived_roof`, the recorded roof comparison.
  Its source and full signature were read; the current quotient isomorphism directions
  are spelled out in this delivery and were verified by compilation.
* The published proof dependencies are imported, including ringed-site Grothendieck
  abelianness, open-closed exactness, etale inverse-image exactness and the degreewise
  epi kernel-to-cone theorem. Mathlib-leaf dependencies are used from their recorded
  matches, not restated.

The additional definitions are interfaces and canonical maps belonging to this one
normalization, listed in `lean.declarations`. They introduce no separate mathematical
notion requiring a new node. In particular the generic interface asserts no theorem
for arbitrary site data: the sole theorem specializes it to the two actual closed pairs.
The public open-map helpers expose the canonical adjuncts needed to state the clause;
the similarly spelled helpers in `SupportedSectionsHom` are private, not a usable API.

### Edge cases checked before and during writing

* Empty support: B is zero, the restriction kernel is zero and the cone comparison
  is the zero-to-acyclic comparison; the formulas give the unique zero morphism.
* Full support: the complement is empty, S is global sections and theta is ordinary
  evaluation at 1. No nonempty-open assumption is present.
* Empty X: both cases above apply and all groups and maps are zero.
* Negative a and arbitrary lower bounds: indices are integers throughout, not natural
  numbers; no assumption `0 ≤ a` appears.
* Zero complex and zero cocycle: both sides of the roof are zero; no chosen nonzero
  representative is used. The generic helpers also allow the zero coefficient ring.
* A boundary change of a cycle has the same `homologyπ` image. The asserted formula
  therefore uses the same chi value, giving representative independence.
* Identity resolution: `supportedHomResolutionIso` is the identity after the canonical
  quotient identifications cancel, and the formula reduces to the localized cocycle.
* A non-quasi-compact open complement is admitted: only its open immersion and the
  existing kernel/cokernel presentations are used.
* Site object and morphism universes remain u+1 and u; modules live in u+1.

### Searches

All searches used the prescribed `msearch.py Q21
lem-pur-supported-hom-cocycle-normalization` wrapper, and the named read-only sources.

* LeanFinder query: `Evaluation at one identifies Hom from a closed supported constant
  sheaf with supported sections and the derived isomorphism sends an injective cocycle
  to its localized complex map`. Eight hits, including `Sheaf.ΓHomEquiv`,
  `SheafOfModules.unitHomEquiv`, `Sheaf.H`, and sheafification Hom equivalences.
  These give general ingredients, not the complete supported normalization.
* Loogle query: `CategoryTheory.InjectiveResolution.extEquivCohomologyClass`.
  Twelve hits in the Ext API. I read its declaration and
  `extEquivCohomologyClass_symm_mk_hom`; they concern ordinary Ext resolutions and do
  not state supported evaluation with the open counit or the etale cone sign.
* Wrapper grep query: `supportedHom|ΓHomEquiv|extEquivCohomologyClass_symm_mk_hom`.
  Thirteen hits in Mathlib global sections and projective/injective Ext modules;
  none states this item.
* LeanSearch query: `Evaluation at one identifies maps from the closed supported
  constant sheaf with the kernel of restriction, naturally, and gives the injective
  cocycle roof formula for cohomology with support`. Eight hits: smooth-sheaf
  evaluation maps, the condensed locally-constant counit, `Sheaf.ΓRes`,
  `sheafSectionsNatIsoEvaluation`, and a smooth-stalk nonunits lemma. No match.
* `rg` on WeilConjectures and Sheaf for `supportedHom`, `supported_cohomology`,
  `supportSections`, `SupportSections`, `cocycleNormalization`, `ΓHomEquiv`, and the
  exact new names found the existing support constructions and comparison ingredients.
  `grep -rn` of the exact item id in WeilConjectures found no declaration.
* The source `SupportedSectionsHom.supported_sections_hom` only states `Nonempty` of
  an underived natural isomorphism. `SupportedCohomologyHom.supported_cohomology_hom`
  only states `Nonempty` of the derived comparison. Neither states the complete
  evaluation/open-counit/roof/cone normalization.
* `SupportedHomPullback` has its own normalization interface, but the corresponding
  DAG theorem now lists this item as a proof dependency. I read that full interface
  and the server source. Importing it here would create a logical dependency cycle;
  this delivery instead uses the recorded prerequisites of this node and the existing
  kernel/unit/cocycle primitives. No downstream result is assumed.

### Validation

The complete module compiled cleanly with `scompile.py` in both its sandbox identity
and its final library identity: no errors, no warnings, each below 60 seconds.
The earlier elaboration cost of a single large structure was repaired by separating
its property definitions; no time limit was raised. There is exactly one postponed
named theorem, matching this node, with all ten proof steps and sources in its docstring.

## Second reading by Q21

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
