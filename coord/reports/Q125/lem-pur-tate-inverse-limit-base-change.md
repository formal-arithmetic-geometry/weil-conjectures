## Worker report

The delivery states `lem-pur-tate-inverse-limit-base-change` in
`Sheaf.Paper.TateInverseLimitBaseChange`. The node is unchanged except for its Lean record.
Its assertions are distributed over the recorded declarations, all in the namespace
`AlgebraicGeometry.Scheme`; every theorem has the whole proof `by sorry`.

The primary theorem is `tateInverseLimitBaseChange`. The second part, with only the
original coefficient and tower data, is
`tateInverseLimitCanonicalFiniteTensorBaseChange`. The other principal assertions are
`tateLimitMap_id`, `tateLimitMap_comp`, `tateTensorMap_id`, and `tateTensorMap_comp`.

Hypothesis and clause correspondence:

| Node data or assertion | Lean rendering |
| --- | --- |
| Prime ell | `(l : ℕ) [Fact l.Prime]` |
| Arbitrary scheme morphism h:T'→T | `{T T' : Scheme.{u}} (h : T' ⟶ T)` |
| Original small pro-etale sites | `ProEt.topology T`, with objects in u+1 and morphisms in u |
| R_S = constant Z_l | `proEtaleConstantRing S (ULift.{u} (PadicInt l))` |
| Sheaves of R_S-modules and linear morphisms | `tateModules S R`, transparently `proEtaleRingModules S (proEtaleConstantRing S R)` |
| Towers indexed by r≥1 and their transitions | `F : ℕᵒᵖ ⥤ tateModules T ...` and `F'`; `op r` denotes positive level r+1, with transitions supplied by the functors |
| l^r F_r = 0 on both sites | `hF : TateTowerKilled l F`, `hF' : TateTowerKilled l F'`; this is `(l ^ (r+1)) • x = 0` for every local section, using additive natural-number multiplication |
| L_S and coordinate projections | `limit F` and `limit.π F (op r)` |
| The canonical inverse-image ring maps are isomorphisms | `IsIso (proEtaleCoefficientInverseImageMap h R)`; the finite theorem has these instances for lifted Z_l, lifted Z/l^(n+1), and A |
| Modules transported along precisely these coefficient maps | `tatePullback h R` is `proEtaleRingModulePullback` with `asIso` of that map |
| Linear level isomorphisms commuting with all transitions | `β : F ⋙ tatePullback h R ≅ F'`; its naturality is exactly the transition compatibility |
| Canonical map c_h | `tateLimitMap h R F F' β`, constructed as `limit.post ... ≫ limMap β.hom` |
| Projection equations and uniqueness | The two conjuncts of `tateInverseLimitBaseChange`; uniqueness is equality to the constructed map for every map with those projection equations |
| Identity law, assuming the level identity law | `tateLimitMap_id`, with `hβ` equating each component to the canonical identity comparison |
| Composition law, assuming the level composition law | `tateLimitMap_comp`, with `hβ` giving precisely the compositor followed by the two level maps |
| Canonical inverse-image identity and composition identifications | `tatePullbackId`, selected from its unique unit specification `IsTatePullbackId` (fibre-product identity arrow); `tatePullbackComp`, the existing `exchangeModuleComposition` (conjugate = fibre-product pasting) transported along `proEtaleConstantRingCompositeCoefficients_eq` (maintainer review fix) |
| N≥1 | `N = n+1`, with arbitrary `n : ℕ` |
| Commutative Z_l-algebra A, killed by l^N | `(A : Type u) [CommRing A] [Algebra (PadicInt l) A]` and `hA : (l ^ (n+1) : A) = 0` |
| Q_S = constant Z/l^N | `proEtaleConstantRing S (ULift.{u} (ZMod (l ^ (n+1))))` |
| Canonical quotient map Z_l→Z/l^N | `tatePadicReduction l n`, the lifted `PadicInt.toZModPow (n+1)` |
| Q acts on A through its existing Z_l-algebra structure | `tateFiniteAlgebraMap l n A hA`, from the unique factorization with composite equal to `algebraMap` |
| F_N regarded as a Q-module | `tateFiniteModule l n F hF` and `tateFiniteModuleIso`; this quotient-action presentation exists for every killed level and is unique up to the unique isomorphism preserving its restriction identification |
| B_S = L_S ⊗_(R_S) A_S | `tateTensor S (a.comp q) (limit F)`; `tateTensor` is the recorded sheaf scalar-extension tensor, with its natural A_S-module structure |
| D_S = F_N,S ⊗_(Q_S) A_S | `tateTensor S a (tateFiniteModule l n F hF)` |
| α_S(x⊗a) = p_N,S(x)⊗a | `tateTowerReduction`; `IsTateReduction` gives its formula on every local pure tensor, transported through `tateFiniteModuleIso` |
| b_h = c_h⊗1 under the canonical tensor identification | `tateTensorMap h (a.comp q) (limit F) (limit F') (tateLimitMap ...)`, uniquely specified by `IsTateTensorMap` on inverse-image-unit pure tensors |
| d_h = β_N,h⊗1 under the canonical tensor identification | The existential `d` satisfies `IsTateFiniteTensorMap`, whose local formula uses exactly β at `op n` and the canonical quotient-action identifications |
| α_T' b_h = d_h h^-1(α_T) | The equality conjunct of `tateInverseLimitCanonicalFiniteTensorBaseChange`, written in Lean's left-to-right composition order as `b ≫ α' = pullback.map α ≫ d` |
| b identity and composition | `tateTensorMap_id` and `tateTensorMap_comp`, combined with the two limit-map laws; they use the same uniquely unit-normalized coefficient identifications |
| Isomorphism conclusion when both α maps are isomorphisms | Final implication of `tateInverseLimitCanonicalFiniteTensorBaseChange`; `d` is also explicitly an isomorphism |

The scalar-extension construction orders pure tensors as `a ⊗ x`; its canonical
symmetry is the node's `x ⊗ a`. This is the existing implementation of the node's
change-of-rings tensor, not a new tensor product. Its A-module structure retains the
underlying R-linear morphism required by the node. The equality specifying
`tateFiniteAlgebraMap` makes `a.comp q` exactly the original Z_l-algebra action on A.

The canonical finite theorem assumes no quotient module or finite scalar map as extra
data. The intermediate theorem `tateInverseLimitFiniteTensorBaseChange` allows any
presentation of those same quotient actions; the canonical theorem specializes it to
the uniquely determined presentations. In `tateFinitePresentation_exists`, the pair
(G,i) has the full universal property: every other pair has exactly one compatible
isomorphism from it. Thus its selection is a universal-property selection, and the
restriction identification is carried through every formula. Every other selected map
or natural isomorphism is fixed by an `∃!` normalization. No data definition contains
`sorry`; every supporting theorem belongs to the canonical constructions or laws
specified by this node and carries its blueprint/source and natural-language proof.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`; its actual intrinsic module
  category gives the unchanged original small-site and constant-ring presentation.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport` is the recorded inverse-image
  module and publicly reexports `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
  Its finite-only `sfIntrinsicConstantModuleAdjunction` is not specialized to Z_l.
  The arbitrary-coefficient declarations used are the reexported
  `proEtaleBaseChange`, `proEtaleSheafInverseImage`, `proEtaleModuleInverseImage`,
  `proEtaleConstantRing`, and `proEtaleCoefficientInverseImageMap`.
- `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction`:
  `proEtaleRingModulePullback`, `proEtaleRingModuleAdjunction`; the adjunction has its
  actual tensor-unit normalization, which is essential to the local section formulas.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Mathlib.NumberTheory.Padics.PadicIntegers`: `PadicInt`; and
  `Mathlib.NumberTheory.Padics.RingHoms`: `PadicInt.toZModPow`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  used through `proEtaleRingModules`; the category is Mathlib's `SheafOfModules`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `limit`, `limit.π`, `limit.post`, `limMap`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`: the recorded tensor
  interface, reexporting `changeOfRingsOfUniverses` from `TensorProductOfUniverses`.
  Scalar restriction is Mathlib's `SheafOfModules.restrictScalars`.
- `Sheaf.Paper.PurInverseImageTensorHom`: `purScalarSection`, the actual sheafification
  unit on sectionwise scalar-extension pure tensors, reused without copying it.
- `Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage`:
  `AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage`, a proof dependency,
  imported non-publicly. The other proof dependency,
  `lem-pur-proetale-inverse-image-tensor-comparison`, has no recorded Lean module in
  the inspected DAG, so there is no module of it to import. The item's required tensor
  maps are explicitly supplied here with their pure-tensor and coherence specifications.

Edge cases checked: n=0 gives exactly N=1; every tower level remains positive. Zero
towers, the zero coefficient ring/algebra, and empty source or target schemes are
included. No nonempty-scheme, characteristic, smoothness, flatness, surjectivity of
transitions, local freeness, finite generation, or preservation of infinite limits is
assumed. Identity and arbitrary composable scheme morphisms are included. The module
universe is u+1 while the site morphism universe remains u; no equality of these
universes was imposed. All variables and universes are explicitly bound and
`autoImplicit` is false.

Source inspection: the blueprint's finite Kummer-level proof, final sentence;
`literature/stacks-project/sites-modules.tex`, `lemma-limits-colimits` (03DB),
`lemma-limits-colimits-abelian-sheaves` (03CO), and `lemma-tensor-product-pullback`
(03EL), including their proofs. No source-based statement correction is needed.

Searches made with the prescribed tooling:

- LeanFinder: "inverse limit of sheaves of modules compatible base change tower maps
  tensor finite reduction". Eight hits; `SheafOfModules.createsLimit`/`hasLimit`
  concern limits themselves; other hits concern condensed modules and do not state
  this comparison and finite tensor square.
- Loogle: `CategoryTheory.Limits.limit.post`. Eleven hits, including `limit.post`,
  `limit.post_π`, `limit.post_post`; they supply the generic comparison construction
  reused in `tateLimitMap`, but not the full item.
- Mathlib grep via msearch: `limit.post|limit.lift|limit.hom_ext` in
  `CategoryTheory/Limits`. Generic limit and cone APIs, not the full statement.
- LeanSearch: "inverse limit comparison sheaf module tensor base change compatible
  towers". Eight hits on tensor direct limits and tensor base change of individual
  modules; none is the sheaf inverse-limit statement here.
- Direct rg over Mathlib, the upstream WeilConjectures source and `lean/Sheaf` for
  every introduced declaration name found no collisions. An earlier conceptual
  `Tate|tateInverse` search found group/field Tate modules and specialized finite
  twist constructions, which do not state the arbitrary module-sheaf tower theorem.
- The required upstream grep for the exact node ID found no declaration.

Validation: the complete module, including the canonical finite theorem and all
coherence declarations, passed scompile.py's sandbox and library-name checks with no
warnings or errors. The report and record are then checked by the prescribed delivery
dry run. All proofs remain postponed as required for stage 2.

## Second reading by Q125

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer review fix

Independent maintainer review (2026-10-17). The delivered module defined its own module-level
inverse-image compositor (`IsTatePullbackComp`, `tatePullbackComp_existsUnique`,
`tatePullbackComp`), although the library already has the canonical ordinary composition
comparison `AlgebraicGeometry.Scheme.exchangeModuleComposition`
(`Sheaf.Paper.StrictTowerOperations`, recorded under def-weil-pbc-strict-tower-operations),
characterized by its right-adjoint conjugate being the sectionwise fibre-product pasting for
the normalized module adjunctions (delivery-errors H4). The fix removes `IsTatePullbackComp`
and `tatePullbackComp_existsUnique` and defines `tatePullbackComp` as `exchangeModuleComposition`
transported by `eqToIso` along the existing equality
`proEtaleConstantRingCompositeCoefficients_eq` (composite constant-coefficient comparison
equals the comparison of the composite). The statements of `tateLimitMap_comp` and
`tateTensorMap_comp` are unchanged in text and now refer to the existing compositor. No
other declaration changed; the primary statement is unchanged. The fixed file compiles
cleanly with the server per-file compiler.
