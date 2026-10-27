## Worker report

Module: `Sheaf.Paper.DiagramOpenClopenShiftModels`.
Main declaration:
`AlgebraicGeometry.ProEtale.SemilinearProperOpen.DiagramShift.diagramOpenClopenShiftModels`.
This states existence of the simultaneous ordinary/complex models and derived
shift identities. The only postponed proof is this named theorem; its docstring
contains all eight proof steps and their dependency names. Definitions and
instances contain actual data. `TermwiseModel`, `OpenModels`, `ClopenModels` and
`Models` are assertion records belonging to this theorem, not alternative
constructions of any of the system categories or geometric operations.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Arbitrary inverse sequence of commutative rings | `C : ℕ → CommRingCat.{u + 1}`, `τ : ∀ n, C (n + 1) ⟶ C n`; starting at zero just relabels the sequence |
| Fixed small pro-etale sites and constant coefficient sheaves | The dependency's `coefficients`, `transition`, `ringSystem`, `Modules`, `Derived`; these use the small-site size convention and the actual ringed sequence site |
| Strict semilinear systems and their ordinary unbounded derived category | Exactly `SemilinearProperOpen.Modules C τ X` and `Derived C τ X`, not a tower of derived categories |
| Exact termwise inverse image for every scheme map | The dependency's `pull` and `P`; `pullShift` is the standard exact-functor `CommShift` instance |
| Complexes M[r]^p = M^(p+r) with signed differential | Mathlib `CochainComplex … ℤ` and its integer shift, with `TermwiseModel.degree`, `shiftedDegree`, `complexShift`; HEq only identifies the indices r+p and p+r |
| Exact open extension and normalized open units | Existing `extension`, `J`, `ordinaryOpenAdj`, `jAdj`; `extensionShift` is the existing termwise shift |
| Total right-derived direct image, with K-injective shift, equivalently its mate | Existing `push`, `R`, `adj`; `directShift` uses `(push C τ v).rightDerivedFunctor.CommShift ℤ` directly; `Models.direct_adjunction_shift` asserts compatibility with this fixed shift |
| Composable open immersions s,b and k=b∘s | `Models.opens`, with `s : U ⟶ V'`, `b : V' ⟶ V`, both `IsOpenImmersion`; k is literally `s ≫ b` |
| Canonical extension compositor c | Existing `jComp C τ s b`; `OpenModels.compositor` represents it, including the standard derived composition factorization |
| Transitivity and identity restriction to U | `compositor_normalization` fixes the ordinary map to `Adjunction.leftAdjointCompIso` of the existing ordinary adjunctions; `ordinary_compositor_identity` and `compositor_identity` give the explicit open-unit equations |
| Zero on a complementary/disjoint open | `OpenModels.compositor_zero`, for every open t with image disjoint from k(U) |
| Open-unit-normalized beta | `restrictionIso` is the canonical compositor followed by inverse open unit of b; `OpenModels.restriction`, `ordinaryRestriction`, `restriction_ordinary` identify its ordinary representative |
| Inverse beta is the specified open-adjunction adjunct for g=b,j=k,j'=s,g_U=id | `ordinary_adjunct` and `derived_adjunct`: transpose is exactly the k-unit followed by `pullComp` / `pComp`; the identity-map pullback has been removed using its canonical identity comparison |
| Restriction of beta to U is identity | `restriction_identity`, written under the same normalized open units and pullback compositor |
| Simultaneous complex representatives, compatible with every coefficient transition | `TermwiseModel.ordinary` is a natural transformation on the category of whole systems; `localizes` is an equation for the actual whole-system derived map, while `degree` and `complexShift` describe its termwise complex representative |
| Degree p at shifted input is degree p+r at original input | `TermwiseModel.shiftedDegree`, for arbitrary integer r,p and arbitrary unbounded complex |
| Clopen s and complementary open Z | `Models.clopens` additionally binds `IsClosedImmersion s` and an open z with `Set.range z = (Set.range s)ᶜ`; this includes the canonical complementary open subscheme and any isomorphic presentation of it |
| Ordinary restriction gives the product decomposition | `ClopenModels.ordinary` and `ordinaryRestriction`, the latter identifying its functor with `(pull s).prod' (pull z)` |
| Extension is (N,0), ordinary direct image is the same exact functor | `ordinaryInsertion`, `direct`; `Models.clopens` produces finite-colimit preservation of `push`, with finite-limit preservation inherited from its existing right adjunction; no exactness hypothesis is imposed on inputs |
| Delta is the localized comparison with the total derived direct image | `comparison.localizes`, `comparison_ordinary`, using exactly `openToS` followed by the existing `rightDerivedFunctorIsoMapDerivedCategory`; `direct_adjunct` pins its ordinary transpose to the inverse open unit |
| Ordinary component projection is (x,y)→(x,0) | `projection_unit` and `ordinary_projection`, using `Prod.mkHom (𝟙 _) 0` after the specified product identifications |
| Product decomposition extends to ordinary unbounded complexes | `complexes`, `complexRestriction`, with the two actual termwise restriction functors |
| Product decomposition extends to ordinary unbounded derived categories | `derived`, `derivedRestriction`, `derivedInsertion`, `derived_projection`; the derived restriction functors are exactly P_s,P_z |
| Precisely the clopen comparison/projector in proper/open mate pasting | All occurrences are literally the dependency's `openToS C τ s` and `pi C τ s`, the maps its `lambda` and `alpha` use, rather than new maps compared only after evaluation |
| Chi_G tau_(M[r]) = tau_M[r] chi_F, for c,beta,delta,pi | `compositor_shift`, `restriction_shift`, `comparison_shift`, `projection_shift` are `NatTrans.CommShift` on those exact derived transformations with the composite functor shift instances |
| Natural identities before evaluation/scalar restriction | Every derived field is a natural-transformation property in `Derived C τ X`; no joint faithfulness or evaluated equality is assumed |
| Coherence for adding shifts | The fixed `Functor.CommShift ℤ` structures include zero/addition coherence; the four `NatTrans.CommShift` properties use those structures |
| Coherence for iterating open composition | `Models.composition_assoc`, with the existing `jCongr` transport; `composition_left_unit`, `composition_right_unit` give the identity-immersion cases |
| Empty open, identity immersions, no extra assumptions | All schemes/opens are unrestricted, with no nonempty, boundedness, coefficient-flatness, cartesian/normalized-system, finite-coefficient or constructibility binders |

The ordinary adjunction units are read under their existing canonical localized
section identifications; the equality with the canonical left-adjoint compositor
and the explicit unit equations retain the node's identity normalization. The
clopen product projection is stated both before and after deriving. It is not
replaced by an arbitrary splitting or a chosen unrelated shift on R.

Recorded statement dependencies used:

- `Sheaf.Paper.SemilinearDerivedSections`:
  `WeilConjectures.SemilinearSections.semilinearDerivedSections` and its actual
  `Systems`/`DS` ringed sequence-site categories. The specialized `Modules` and
  `Derived` in the proper/open dependency are abbreviations of these categories.
- `Sheaf.SixFunctors.OpenTensorNormalization`:
  `SheafOfModules.openTensorNormalization`, including its arbitrary-system diagram
  case and normalized open adjunction/base-change words. The specialization uses
  the existing `ordinaryOpenAdj`, `jAdj`, `pullComp` and `pComp` interfaces.
- `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`:
  `AlgebraicGeometry.ProEtale.SemilinearProperOpen.semilinearProperOpenMatePasting`,
  and the existing `Modules`, `Derived`, `pull`, `push`, `extension`, `P`, `R`, `J`,
  `ordinaryAdj`, `ordinaryOpenAdj`, `adj`, `jAdj`, `pullComp`, `pComp`, `jComp`,
  `jId`, `jCongr`, `jAdj_unit_isIso`, `openToS`, `pi` declarations.

All recorded proof-dependency modules are imported. Mathlib leaves are used through
`Functor.mapDerivedCategoryFactors`, `Localization.liftNatIso` /
`Localization.natTrans_ext`, and the K-injective shift instance; their modules
are imported explicitly. `canonicalRightDerivedAdjunctionShift` is an additional
already available generic tool for the fixed right-derived adjunction shift.
No dependency node needs an interface repair, and no new independent notion is
missing. Only the item's `lean` field is changed.

Source read: the current `literature/blueprint/latest/blueprint/sec-six-functors/
sk-thm-sf-compatibility/fix-prop-coherence.proof.md`, in particular its maps-used
sentence; the node's agent-written section-model refinement and all eight proof
steps; the three dependency statements and their recorded Lean signatures and
docstrings. The refinement is not attributed to a theorem quoted verbatim by the
blueprint. Its ordinary construction is the stated open transitivity, normalized
adjunction and clopen gluing argument.

Edge cases checked before and after writing:

- U empty: its system category is zero; zero insertion, the disjoint-open maps and
  both projection formulas give the unique maps. No `Nonempty` hypothesis excludes it.
- Complement empty and identity open: ordinary and derived product decompositions
  have a zero second factor; the projector is identity after the open-unit comparison.
- r=0, r=-1, and r+t: the existing shifts use the correct signed differential;
  degree reindexing uses p+r and functor CommShift provides addition coherence.
- Nonflat transitions, for example Z/4→Z/2: all coefficient maps remain arbitrary;
  no tensoring with a coefficient transition is assumed exact.
- Arbitrary unbounded input and noncartesian system: all model and shift fields
  quantify over the whole ordinary complex/derived categories.

Searches (2026-10-24; prescribed msearch.py wrapper):

- `leanfinder`: "Termwise extension by zero on semilinear systems clopen projection
  natural transformations commute with derived integer shifts". Eight hits, notably
  `Functor.mapHomologicalComplex_commShiftIso_hom_app_f`, `...commShiftIso_eq`,
  `CochainComplex.shiftEval`, and standard exact-derived shift instances. These
  supply generic termwise shifts, not this normalized geometric assertion.
- `loogle`: `CategoryTheory.NatTrans.CommShift`. Twelve hits, including the class,
  its inverse/composition/whiskering helpers, and `shift_app_comm`. Used the existing
  class rather than restating a private notion of shift compatibility.
- `leansearch`: "Semilinear ring system open extension clopen product projection
  integer derived shift compatibility". Eight unrelated semilinear-map and
  Presburger hits; no match.
- `grep` through msearch: `CommShift|clopen|extensionByZero` in
  `Mathlib/CategoryTheory/Sites`: no hits.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `OpenClopenShift`, `openClopenShift`, `open.*clopen.*shift`, `clopen.*shift`,
  `jComp.*CommShift`, `restrictionIso.*CommShift`, and all proposed names:
  no exact declaration. Found only integral clopen restriction shifts and unrelated
  etale local shift loci. A broader search located the existing proper/open and
  varying-ring canonical maps, which this module reuses.
- `grep -rn` for the item id in `lean/WeilConjectures`: no hits.
- Read Mathlib exact-functor and cochain-shift declarations and the upstream
  right-derived `Defs` and K-injective comparison signatures. Their generic
  interfaces do not already state the node's complete assertion.

No statement correction and no STATEMENT-DISPUTED flag.

## Second reading by Q123

A separate second pass by the sole dispatched worker reread the node and the
module. No second agent was started, as the dispatcher explicitly prohibits it;
the maintainer supplies the independent delivery review.

The pass checked each row of the correspondence table against the record fields.
It found that the first draft pinned c to the canonical compositor but did not
write its identity restriction explicitly. Added `ordinary_compositor_identity`
and `compositor_identity`. It also checked the direction of the clopen adjunct:
`direct.hom` is transposed using `(ordinaryAdj.homEquiv _ _).symm`, not the
forward Hom equivalence. The zero object is Mathlib's scoped `ZeroObject`, and
the zero-insertion functor is its actual constant functor, not a placeholder.
The final read checked that the localization equation for delta uses the canonical
exact/right-derived comparison in its correct direction, that the pi model uses
both standard identity and composition factorization isomorphisms, and that all
four derived shift fields refer to the exact existing transformations. R's shift
is the library K-injective shift and is checked against the actual adjunction,
not defined by transport along delta. All variables/universes are explicit;
there is no local notation, private declaration, or definition with sorry data.

Validation: every compile was through scompile.py. The final compile and delivery
preflight results are recorded below after running the prescribed dry run.

Final validation: `deliver2.py Q123 lem-pur-diagram-open-clopen-shift-models
--no-push` printed `OK (dry run)` at commit `8c2d9d63ec2`: the delivery passed
maintainer preflight and both per-file sandbox/library compiles, with no errors
or unexpected warnings. No live library source was edited and no global build
or direct Git command was run by the worker.
