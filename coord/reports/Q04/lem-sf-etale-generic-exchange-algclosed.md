## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed` states the two
ordinary-etale geometric-generic isomorphism assertions and all five specified
normalizations/compatibilities. Its namespace is `AlgebraicGeometry.Etale`. Every theorem
has only `sorry` as proof. The geometric point, comparison maps, exceptional tensor
comparison, pasted comparisons, and adjoint shift structure have real data, supplied by
Spec, the existing derived operations, and adjunction transposition. No independent
notion or dependency module is added, and no node statement is corrected.

The two main declarations are `isIso_closedSupportExchange_geometricGeneric` and
`isIso_inverseImageHomExchange_geometricGeneric`. Their common binders render every
hypothesis as follows:

| Node hypothesis/object | Lean rendering |
| --- | --- |
| Arbitrary algebraically closed field F | `(F : Type u) [Field F] [IsAlgClosed F]` |
| Positive N, invertible in F | `(N : ℕ) (_hN : 1 ≤ N) (_hNF : IsUnit (N : F))` |
| Finite commutative A with NA=0 | `(A : Type (u + 1)) [CommRing A] [Finite A] (_hNA : (N : A) = 0)`; in a unital ring annihilation of A is equivalent to annihilation of 1 |
| B an F-scheme | `(B : Scheme.{u}) (b : B ⟶ Spec (.of F))` |
| B smooth, integral, finite type, dimension one | `[Smooth b] [IsIntegral B] [LocallyOfFiniteType b] [QuasiCompact b]` and `_hdim : topologicalKrullDim B = 1`; no separatedness of B is imposed |
| Any nonempty affine open of B | `(U : B.Opens) (hU : IsAffineOpen U) (_hUnonempty : Nonempty U)` |
| F(B), the fraction field of its coordinate ring | `(Q : Type u) [Field Q] [Algebra (B.presheaf.obj (op U)) Q] [IsFractionRing (B.presheaf.obj (op U)) Q]` |
| Algebraically closed algebraic extension L/Q | `(L : Type u) [Field L] [Algebra Q L] [Algebra.IsAlgebraic Q L] [IsAlgClosed L]`; no separability assumption |
| Geometric generic point and its map to B | `Spec (.of L)` and `geometricGenericMap U hU Q L`, constructed from the composite coordinate-ring map to L and `hU.fromSpec` |
| Separated finite-type B-scheme X | `(X : Scheme.{u}) (f : X ⟶ B) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]` |
| Generic inverse image g_X | Pullback along `pullback.fst f (geometricGenericMap U hU Q L)` |
| Ordinary small-etale constant-A module derived categories | `DerivedCategoryModule A X`, the recorded `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} A))` encoding |
| Exact inverse image | `(upperStar (ModuleCat.{u+1} A) g).leftDerivedFunctor`; the existing `leftDerivedUpperStarIsoMapDerivedCategory` identifies this canonically with termwise exact inverse image |

Every conclusion and its remaining inputs are rendered as follows:

| Node clause | Lean rendering |
| --- | --- |
| Closed immersion i:Z→X | `(Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]` in the first main theorem |
| Bounded constructible M | `DerivedCategory.isBoundedConstructible A X M`, using the recorded finite-stratification sheaf predicate and bounded cohomology |
| Ri! the ordinary closed direct-image right adjoint | `((lowerStar (ModuleCat.{u+1} A) i).rightDerivedFunctor).rightAdjoint`, using the instance of `lem-exc-closed-ambient` |
| Geometric base change of the closed immersion | `IsPullback.of_hasPullback i g_X`; its domain is `Z ×_X (X ×_B Spec L)`, canonically `Z ×_B Spec L` by pullback pasting; its two projections give g_Z and i_generic |
| Canonical closed-support isomorphism | `IsIso ((closedSupportExchange A (IsPullback.of_hasPullback i g_X)).app M)` |
| This is the canonical map, with its counit | `closedSupportExchange` is the mate of the inverse of the existing `derivedBaseChangeMap` under the two closed adjunctions; `closedSupportExchange_counit` asserts `Ex_i(Ri!M) ≫ Ri_generic,*.map(alpha_M) ≫ epsilon_generic = g_X*.map(epsilon_i)` |
| Bounded constructible K of finite Tor amplitude, and bounded constructible M | The second theorem has `_hK`, `_hM` using the recorded bounded constructibility, and `_hTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A X a b K`; this tests every sheaf in degree zero and all degrees outside that interval |
| Canonical internal-Hom comparison is an isomorphism | `IsIso (inverseImageHomExchange A g_X K M)` |
| Tensor-adjoint definition of beta | `inverseImageHomExchange` applies the existing `derivedTensorHomAdjunction` hom equivalence to inverse `leftDerivedUpperStarTensorIso` followed by inverse image of its counit/evaluation |
| Evaluation equation | `inverseImageHomExchange_evaluation` asserts `(1 ⊗ beta) ≫ ev = tensorIso.inv ≫ g*.map(ev)`; the existing adjunction writes K first, and the symmetric braiding changes this exactly to the node's Hom tensor K order |
| Closed-support comparison respects shifts | `closedSupportExchange_commShift` is the componentwise shift compatibility equation for every object M and integer n; `closedSupportShiftIso` is the canonical shift isomorphism transported across the closed adjunction |
| Closed-support comparison respects open restriction | `closedSupportExchange_openRestriction` equates the two pasted comparison paths around a commutative cartesian cube, with open `pX` and `qX`; `pastedClosedSupportExchange` explicitly inserts the canonical inverse-image composition isomorphisms and fixes common composite endpoints |
| Closed-support comparison respects invertible locally constant rank-one twists | `closedSupportExchange_tensor` uses a sheaf Q with an actual `Scheme.LocallyConstantDatum` cover and constant value `ModuleCat.of A A` on every member, and an explicit two-sided sheaf tensor inverse for the existing `GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall` structure (the canonical sheafified tensor); it asserts the commutative tensor square `ClosedSupportExchangeTensorCompatible` and invertibility of the two adjunction tensor comparisons |
| Canonical tensor identity for Ri! | `closedSupportTensorComparison` transposes inverse `rightDerivedLowerStarProjectionMap` followed by `epsilon_i ⊗ 1`; the tensor compatibility square explicitly includes both inverse-image tensor isomorphisms and `derivedSquareUpperStarIso` |
| No finite-field base | No finite-field datum, characteristic p, Padic coefficient construction, pro-etale site, or finite-field extension occurs in either main signature |

The formal compatibility declarations are stated for arbitrary closed cartesian squares:
the normalization equations themselves require no geometric-generic or constructibility
hypothesis. The two isomorphism assertions have exactly the node's geometric-generic
hypotheses. All helpers belong to the comparison constructions of this node and are listed
in `lean.declarations`; there is no new independent mathematical definition.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.BaseChangeConventions`: `Limits.pullback`, its projections,
  `baseChange_iterated`, and `baseChange_morphism_projections` are the recorded scheme
  base-change conventions. The structure-sheaf-module-only `moduleBaseChange` is not used
  in place of constant-coefficient etale inverse image.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, together with
  `QuasiCompact`; `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsSeparated` and
  `IsProper`; `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Sheaf.AlgebraicGeometry.DerivedCategories`, through upstream
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`: `DerivedCategoryModule`,
  `DerivedCategory.homologyFunctor`, and `DerivedCategory.singleFunctor`.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`: the recorded inverse-image
  exactness/constant-coefficient identification; the fixed-coefficient six-functor encoding
  uses `upperStar` from `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` and its
  canonical exact-derived identification from `...Derived.UpperLowerStar`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `DerivedCategory.isBoundedConstructible`; this is the recorded finite constant-value
  stratification predicate, rather than upstream's distinct constructibility predicate.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `derivedTensor` and its existing
  monoidal structure. `Sheaf.AlgebraicGeometry.EtaleTorAmplitude` records the bounded
  interval predicate `DerivedCategory.hasTorAmplitudeIn` in upstream `...Coefficients`.
- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`:
  `isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion`; its ordinary right adjoint is
  chosen by `Functor.rightAdjoint` and normalized by `Adjunction.ofIsLeftAdjoint`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `derivedInternalHomOfUniverses` is the recorded general ringed-site Hom-complex
  localization. The existing constant-coefficient `ModuleCat` encoding uses upstream
  `WeilConjectures.SixFunctors.Etale.Derived.Hom`, `derivedHom` and
  `derivedTensorHomAdjunction`, i.e. this same derived internal Hom specified as the
  tensor right adjoint. No second Hom construction is introduced.

Additional existing constructions used for real comparison data are
`derivedBaseChangeMap`, its proper-base-change isomorphism theorem,
`leftDerivedUpperStarTensorIso`, `derivedSquareUpperStarIso`,
`rightDerivedLowerStarProjectionMap`, its finite-coefficient proper projection formula
(with `closedSupportProjectionIso` recording this actual isomorphism),
`mateEquiv`, and `Adjunction.RightAdjointCommShift.iso`. The canonical shift instance
for derived inverse image is `commShiftLeftDerivedUpperStar` from upstream
`WeilConjectures.SixFunctors.Etale.Derived.Shift`. The recorded proof-dependency modules
with Lean records are imported without `public` unless already a statement import.
Unstated proof prerequisites are described in the theorem proof docstrings; they supply
no missing object required to type these statements.

Edge cases checked before writing:

- N=1 forces A to be the zero ring; no `Nontrivial A` hypothesis is added. The zero ring,
  zero sheaves, and zero complexes remain allowed, including the tensor inverse clauses.
- Empty X and Z, empty geometric fibres, the identity closed immersion, and the empty
  closed immersion are allowed. No point of X or Z is selected.
- B itself cannot be empty because it is integral; the affine chart is explicitly nonempty.
  Any such chart and any fraction field model are allowed.
- B need not be separated over F. Only the stated morphism X→B is separated.
- L/Q may be inseparable; no separable-closure or characteristic-zero restriction occurs.
- The finite Tor interval is existential and may occur in arbitrary integer degrees.
  If an empty interval witnesses it, the zero complex is included. M has no finite Tor
  hypothesis.
- Open restriction includes the empty open and identity restriction. Twists have a genuine
  tensor inverse and trivializations with value A, and every integer shift is covered.
- The site's object and morphism universes retain the project's ordinary-etale convention;
  coefficients are in u+1, and the geometric fields/schemes are in u.

Searches for existing statements/constructions:

- `msearch.py ... leanfinder`, query “Geometric generic inverse image commutes with closed
  exceptional inverse image and derived internal Hom of constructible finite Tor complexes”:
  8 hits (light condensed internal Hom, ordinary scheme-module pullback composition and
  exponentiable-morphism adjunction identities), no match.
- `msearch.py ... loogle`, query `AlgebraicGeometry.Etale.derivedHom,
  CategoryTheory.Functor.rightAdjoint`: 0 hits, the Mathlib index does not know the upstream
  `Etale.derivedHom` name. The source declaration was opened and reused directly.
- `msearch.py ... grep`, query `generic.*exchange|closedSupport|homComparison`: 2 hits,
  both `Topology/LocallyFinsupp` closed support; no etale generic exchange.
- `msearch.py ... leansearch`, query “Geometric generic etale inverse image preserves
  exceptional closed support and derived internal Hom of constructible finite Tor complexes”:
  8 hits (complex support transport, ideal-sheaf support, and etale ring base change), no match.
- `rg` of upstream `WeilConjectures/SixFunctors/Etale/Derived` for
  `generic.*(exchange|Exchange)|geometricGeneric|[Hh]om[Cc]omparison`: only comments/imports
  about pro-etale Hom comparison; no matching statement. The required `grep -rn` of the
  item id in upstream `WeilConjectures` returned no occurrence.
- `rg` of `lean/Sheaf` for generic exchange, closed-support and internal-Hom comparisons:
  existing finite-free comparison, ringed-site localization calculus, and mixed global-Hom
  adjunction modules have different sites or conclusions; none states this item.
- Direct source searches found and reused `Etale.derivedHom`,
  `derivedTensorHomAdjunction`, `leftDerivedUpperStarTensorIso`, `derivedBaseChangeMap`,
  `rightDerivedLowerStarProjectionMap`, and the canonical adjunction mate/shift APIs.

The cited local Stacks TeX checkout is absent on this machine. The actual cited sources
were read at [0F09](https://stacks.math.columbia.edu/tag/0F09),
[0GIT](https://stacks.math.columbia.edu/tag/0GIT),
[0A45](https://stacks.math.columbia.edu/tag/0A45), and
[09BI](https://stacks.math.columbia.edu/tag/09BI),
[0F1C](https://stacks.math.columbia.edu/tag/0F1C), and
[04DZ](https://stacks.math.columbia.edu/tag/04DZ).
No `STATEMENT-DISPUTED` issue was found.

Validation: all compilation is through the authorized `scompile.py` wrapper; no direct
live compilation, global build, source modification, or git command was run by the worker.
The final `scompile.py` invocation completed with exit 0 and no warnings in both the
sandbox-name and library-name checks. Delivery validation uses `deliver2.py --no-push`;
the independent second reader remains responsible for the second-reading section and push.

## Second reading by Q04

Independent reading of the node, the entire 453-line module, the dependency node
statements and their recorded source declarations. Verdict: the Lean states the node's
claims, with the specified canonical arrows. No mathematical mismatch was found. I kept
the Lean and node record unchanged and appended this reading and fresh validation.
There are no new definition nodes, dependency modules, or statement corrections in this
delivery, so H12/H13 and the correction-citer audit do not arise.

I obtained and read the actual
[Stacks etale-cohomology.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/etale-cohomology.tex)
and tag index in the sandbox scratchpad because the repository has no Stacks TeX checkout.
I read each cited label together with its enclosing section. In particular,
[0F09](https://stacks.math.columbia.edu/tag/0F09) requires a qcqs direct-image morphism,
bounded-below input and invertible torsion orders; it imposes no finite-field base.
[0F1C](https://stacks.math.columbia.edu/tag/0F1C) treats arbitrary field extensions, using
purely inseparable invariance, so an algebraic closure is not a separable-closure input.
The support section surrounding
[0A45](https://stacks.math.columbia.edu/tag/0A45) introduces no Noetherian or separatedness
assumption. The section containing
[09BI](https://stacks.math.columbia.edu/tag/09BI) assumes Noetherian coefficients; finite
A supplies this, and connectedness is used on connected strata for its common local model,
not as an extra global hypothesis. The additional limit and invariance references
[0GIT](https://stacks.math.columbia.edu/tag/0GIT) and
[04DZ](https://stacks.math.columbia.edu/tag/04DZ) agree with the proof's bounded-below limit
and universal-homeomorphism steps. These sources supply ingredients; the node explicitly
identifies the generic closed-support/Hom statement as their extension by its nine-step
argument, rather than claiming that a single tag states the entire result.

My object/hypothesis/conclusion checklist, made from the node before comparing signatures:

| Node item | Lean rendering inspected | Verdict |
| --- | --- | --- |
| Any algebraically closed F | `F : Type u`, `Field F`, `IsAlgClosed F` in both main theorems | Exact; arbitrary characteristic, no finite-field instance |
| N positive and invertible in F | `_hN : 1 ≤ N`, `_hNF : IsUnit (N : F)` | Exact; N=0 excluded by the node |
| Finite commutative coefficient ring annihilated by N | `A : Type (u + 1)`, `CommRing A`, `Finite A`, `_hNA : (N : A) = 0` | Exact: vanishing of N times 1 is equivalent to annihilating every element |
| F-scheme B | `B : Scheme.{u}`, `b : B ⟶ Spec (.of F)` | Exact structure morphism |
| Smooth integral finite-type B of dimension one | `Smooth b`, `IsIntegral B`, `LocallyOfFiniteType b`, `QuasiCompact b`, `_hdim : topologicalKrullDim B = 1` | Exact: finite type is local finite type plus quasi-compactness; no separatedness of b |
| Any nonempty affine chart | `U : B.Opens`, `hU : IsAffineOpen U`, `_hUnonempty : Nonempty U` | Exact universal chart choice, not a chosen special affine B |
| Fraction field F(B) of that chart | `Q : Type u`, `Field Q`, `Algebra (B.presheaf.obj (op U)) Q`, `IsFractionRing ... Q` | Exact; integrality and nonemptiness give the domain |
| Algebraically closed algebraic extension L/Q | `L : Type u`, `Field L`, `Algebra Q L`, `Algebra.IsAlgebraic Q L`, `IsAlgClosed L` | Exact; includes inseparability |
| Geometric generic point and its map | `Spec (.of L)`, `geometricGenericMap U hU Q L` | Exact: Spec of coordinate-ring-to-Q-to-L composite, followed by `hU.fromSpec` |
| Finite-type separated X over B | `X`, `f : X ⟶ B`, `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f` | Exact; does not assume X separated over F |
| g_X and generic fibre | `pullback.fst f (geometricGenericMap U hU Q L)` | Exact ordinary fibre-product projection |
| Small-etale constant-A ordinary derived categories | `DerivedCategoryModule A X` and corresponding generic-fibre categories | Exact recorded `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} A))` |
| Exact inverse image | `(upperStar (ModuleCat.{u+1} A) g).leftDerivedFunctor` | Exact via existing `leftDerivedUpperStarIsoMapDerivedCategory`; no extraordinary/pro-etale functor substituted |
| Closed immersion i | `Z`, `i : Z ⟶ X`, `IsClosedImmersion i` | Exact; no extra assumption on Z |
| Bounded constructible M | `_hM : DerivedCategory.isBoundedConstructible A X M` | Exact recorded bounded interval and finite-stratification sheaf predicate |
| Ordinary Ri! | `((lowerStar ... i).rightDerivedFunctor).rightAdjoint` | Exact closed-direct-image adjoint from `lem-exc-closed-ambient`, not compactification-dependent data |
| g_Z and generic i | `IsPullback.of_hasPullback i g_X` | Exact iterated pullback, canonically the B-base change by pullback pasting |
| Closed-support comparison is an isomorphism | `isIso_closedSupportExchange_geometricGeneric`, `IsIso ((closedSupportExchange A ...).app M)` | Exact direction and object order |
| Canonical closed-support arrow | `closedSupportExchange` uses `mateEquiv` on inverse `derivedBaseChangeMap` | Exact transpose of inverse direct-image exchange followed by pulled-back exceptional counit |
| K bounded constructible of finite Tor amplitude, M bounded constructible | `_hK`, `_hM`, `_hTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A X a b K` | Exact; no Tor hypothesis on M |
| Canonical internal-Hom comparison is an isomorphism | `isIso_inverseImageHomExchange_geometricGeneric`, `IsIso (inverseImageHomExchange A g_X K M)` | Exact; all shared geometric hypotheses repeated |
| Actual tensor-adjoint Hom arrow | `inverseImageHomExchange` applies `derivedTensorHomAdjunction ... .homEquiv` to inverse tensor pullback followed by pulled-back evaluation | Exact data; no arbitrary map or chosen isomorphism |
| Evaluation normalization | `inverseImageHomExchange_evaluation` | Exact equality of arrows; K-first evaluation is the symmetric monoidal rendering of the node's Hom-first evaluation |
| Exceptional counit normalization | `closedSupportExchange_counit` | Exact: direct-image exchange, pushed-forward comparison and new counit equal pullback of old counit |
| Open restriction | `closedSupportExchange_openRestriction` and `pastedClosedSupportExchange` | Exact cartesian-cube path equality, with explicit inverse-image composition isomorphisms and common endpoints |
| Invertible locally constant rank-one sheaf twist | `_hQ` in `closedSupportExchange_tensor` supplies an etale cover and constant value `ModuleCat.of A A`; `_hInv` supplies a sheaf tensor inverse | Exact sheaf notion, not an arbitrary derived invertible object |
| Tensor compatibility itself | `ClosedSupportExchangeTensorCompatible`, `closedSupportTensorComparison`, and the two `IsIso` clauses in `closedSupportExchange_tensor` | Exact commutative tensor square, including canonical tensor/composition identifications; exceptional tensor map is the adjoint of inverse projection formula and counit tensor identity |
| Shifts | `closedSupportExchange_commShift`, every `M` and `n : ℤ`, using `closedSupportShiftIso` | Exact canonical adjoint shift structures |

I opened the recorded dependency modules, not just their names. In
`BoundedConstructibleComplexes` and `IsConstructibleEtaleModuleSheaf`, the actual predicate
uses finite locally closed constructible strata, etale local finite constant module values,
and bounded cohomology. The similarly named upstream `boundedConstructible` is not used.
In upstream `Derived.Coefficients`, `hasTorAmplitudeIn` quantifies over *every* sheaf in
degree zero and every out-of-interval cohomology degree. `EtaleTorAmplitude` reuses this
bounded predicate. The `BaseChangeConventions` record includes the fibre-product and
iterated-base-change clauses used here; its primary `moduleBaseChange` is for structure
sheaf modules and is correctly not substituted for constant-A inverse image.

I also read the signatures of Mathlib's `Smooth`, `LocallyOfFiniteType`,
`IsClosedImmersion`, `IsProper`, `IsIntegral`, and `topologicalKrullDim`, and the closed
adjoint existence theorem. The Hom dependency `derivedInternalHomOfUniverses` is a
K-injective Hom-complex localization on `SheafOfModules`; upstream `Etale.derivedHom`
is its same ordinary internal Hom in the fixed-coefficient `ModuleCat` encoding, as the
right adjoint of the recorded derived tensor. Reusing that existing right adjoint and its
evaluation introduces no second Hom definition. Upstream `derivedTensor` is the K-flat
monoidal tensor, and `leftDerivedUpperStarIsoMapDerivedCategory` identifies the chosen
left-derived upper star with exact termwise inverse image. The proper-base-change and
finite-coefficient projection-formula theorems used to invert maps require no extra
hypotheses here: closed immersions are proper, and finite A is additive torsion.

Edge cases: N=1 and the zero coefficient ring remain allowed; no `Nontrivial A` appears.
Zero K or M, empty X or Z, empty generic fibre, identity and empty closed immersions are
included. An empty B is excluded by the node's integrality, while the nonempty chart
condition is explicit. Empty and identity open restrictions are included, and the shift
parameter ranges over all integers, including zero and negative integers. The Tor
interval is existential with arbitrary endpoints; an empty interval can witness the zero
object. M need not be Tor finite. No separability or characteristic-zero condition is
present. A nonseparated smooth B is covered. Schemes and fields use arbitrary `u`, with
coefficient/module size `u+1` as in the recorded small-etale convention; there is no new
equality of site object/morphism universes or smaller-universe test quantifier.

Independent searches, using wording different from the first worker:

- `msearch.py ... leanfinder`: “Restriction to the geometric generic fibre commutes with
  extraordinary pullback of a closed embedding and the derived sheaf Hom of constructible
  torsion modules”; eight hits, all structure-sheaf pullback/restriction or section maps;
  none states either comparison here.
- `msearch.py ... loogle`: `"Sheaf", "Hom", "pullback"`; twelve hits about underived
  `SheafOfModules` pullback or topological-presheaf pullback, none about the derived etale
  generic fibre statement.
- `msearch.py ... grep`: `([Gg]eneric.*(RHom|[Ee]xceptional|[Ss]upport)|([Ss]upport|RHom).*[Gg]eneric)`;
  three unrelated generic polynomial/tactic hits.
- Direct `rg` of Mathlib, upstream `WeilConjectures`, repository `lean/Sheaf`, and the upstream
  name index for generic/exceptional/RHom/support/exchange combinations found no existing
  statement or duplicate new comparison name. I inspected the closest candidates:
  Mathlib `CategoryTheory.expComparison` assumes *cartesian* monoidal categories and is
  inapplicable to derived tensor; upstream `derivedHomRightDerivedLowerShriekIso` is an
  ambient stratum-Hom/direct-image isomorphism, not inverse-image Hom comparison;
  `supportedLocalizationBoundary_baseChange` concerns the boundary between already
  pushed-forward support terms, not this ordinary closed-adjoint exchange. Their signatures
  are different. Existing tensor, Hom, projection and base-change constructions are reused.

H5/H6/H8/H9: each helper definition has actual Spec, functor, adjunction-mate or composition
data. The right adjoint is determined by its adjunction, not selected from an uncharacterized
existence assertion. All seven theorem bodies remain exactly `by sorry`. The first main
proof docstring follows node steps 1–4, the second follows 5–8, and the compatibility
proof docstrings spell out step 9, including normalization of arrows. Every declaration
has its source and blueprint marker. All universes and variables are explicitly bound,
no file-local notation/instance or private copy is introduced, and every Lean line is at
most 100 characters. The primary `lean.statement` was compared directly with the text
from `theorem` to `:= by` and matches verbatim; all 15 declarations are recorded.

Mismatches/changes: none in the mathematical statement or Lean module. Added only this
independent reading. Validation results follow below.

Additional independent `msearch.py ... leansearch` query: “For constructible torsion
etale complexes, pullback to a geometric generic fibre commutes with exceptional inverse
image and derived internal Hom”; eight results about underived module pullback composition,
free modules, or etale stability, with no matching declaration.

Fresh second-reader `scompile.py Q04 lem-sf-etale-generic-exchange-algclosed` on the delivered
module completed with exit 0: both sandbox-name and library-name compilations passed,
with no errors or warnings. No Lean or node correction was needed.

The second-reader `deliver2.py Q04 lem-sf-etale-generic-exchange-algclosed --no-push`
printed `OK (dry run)` after a clean compile and server preflight. The delivery contains
exactly the item's module, its node Lean record, and this report.
