## Worker report

Repair of the returned stage-2 packet at immutable head `0c4ba238c411`.
The module is `Sheaf.CategoryTheory.CechLocalizationUnitTotalization`; the theorem is
`CategoryTheory.CechLocalizationUnit.cech_localization_unit_totalization`.
It has exactly one postponed theorem, whose whole proof is `sorry`. All definitions
have actual data. The informal statement is unchanged; only `lean` and `stmt_deps`
differ from the current shared node.

The H4/H3 return is repaired by importing the already recorded
`Sheaf.CategoryTheory.CoherentCechImageModel` and adding its owning node
`def-sfb-coherent-cech-image-model`, together with
`def-sfb-element-site-localization`, to statement dependencies. The theorem takes
`D : CoherentCechImageModel` of the actual underlying ring sheaf. The private
`nerve`, `freeSheaf`, `sliceSections`, `generator`, `sliceSections_additive`,
`RestrictionAugmentation` and `derivedRestriction` are removed. It no longer
introduces a second notion of slice direct image or restriction augmentation.
The old additional dependencies on internal Hom and binary descent models are
unneeded and removed from this saved packet.

`power V p n` is exactly `(sheafCoverNerve (V.obj (op p))).obj (op n)`.
`slice RX D V p n` is only a transparent abbreviation for `D.image.obj` at that
power. By `D.imageIso`, it is the composite of the recorded
`elementModulePullback` with `D.push`; `D.adj` is its actual localization
adjunction. Thus `baseColumn` is `Rf_* R(j_n* j_n^*) (N[0])` for the existing
coherent model. Exactness and injective preservation of localization, followed
by the recorded normalized derived-composition comparison, identify it with
`R(f v_n)_*(v_n^*N[0])`. There is no internal-Hom bridge to supply.

`columnAugmentation` applies `Rf_*` to the right derivation of
`D.augmentation`, with the canonical identity-functor normalizations. The
existing `D.unit` equation transposes this ordinary augmentation to the identity,
fixing precisely the localization unit and its restriction-of-sections rule.
`D.augmentation_naturality` fixes its compatibility with every restriction.
`columnOperator` uses `D.image.map` of each actual nerve operator;
`columnChange` uses `D.image.map` of `Arrow.mapCechNerve` for the actual cover
refinement, followed by the coefficient map. In particular all degeneracies,
cofaces and noninvertible refinements have their prescribed maps.

Hypothesis and clause check against the node:

| Informal statement | Lean rendering |
| --- | --- |
| Five sheaf topoi on small sites | `CX CV CY CZ CB`, `SmallCategory` instances, and `JX JV JY JZ JB` |
| Commutative coefficient rings and their module categories | `RX RV RY RZ RB : Sheaf _ CommRingCat.{u}` and `Modules`, the recorded `ringedSiteModules` after forgetting commutativity |
| Ringed-topos morphisms f, g, t | The existing `RingedToposMorphism` values; direct images are their induced `.modules` fields |
| Exact module inverse images | `fInverse`, `gInverse`, `tInverse`, their additive and finite-limit/finite-colimit instances, with `fAdj`, `gAdj`, `tAdj` to those prescribed direct images |
| Specified additive exact h adjunction | `hInverse`, `hDirect`, their additive/exact instances, `hAdj`; H is literally `hInverse ⋙ hDirect` and eta is literally `hAdj.unit` |
| Grothendieck abelian categories; ordinary unbounded derived categories | Five `IsGrothendieckAbelian.{u}` and `HasDerivedCategory.{u+1}` instances; existing K-injective `rightDerivedFunctor`; no new injective-preservation hypothesis |
| Cover and arbitrary module | `V : Pᵒᵖ ⥤ Sheaf JX (Type u)`, `N : P ⥤ Modules RX`, `cover : ∀ p, Epi (terminal.from (V.obj (op p)))` |
| Cech slices and C_n | Existing `sheafCoverNerve`, `D.image`, `D.imageIso`, `D.adj`, and `baseColumn` as described above |
| Two displayed derived isomorphisms | `Comparison.sourceComparison` and `.targetComparison`; `sourceColumns` and `targetColumns` identify their columns with the prescribed `t* Rg* C_n` and `t* Rg* H(C_n)` |
| Compatible nonnegative resolutions and finite diagonals | `AugmentedModel` uses `CochainComplex _ ℕ`; `total` uses alternating cofaces, the existing nonnegative signed total and extension by zero; degree r has only n+q=r |
| Exact descent of H | Existing `mapDerivedCategory`; `derivedNatTrans` localizes the termwise transformation; `exactUnit` includes the identity normalization |
| Actual map is the total of the column units | `unitColumns`, `unit_columns` and `unit_total` refer to the specified `hAdj.unit`; no invertibility is imposed on that unit |
| Preserve augmentation and restriction of sections | `columnAugmentation` derives `D.augmentation`, fixed by `D.unit` and `D.augmentation_naturality`; `source_augmentation`, `target_augmentation`, `AugmentedModel.total_formula`, `source_normalization`, `target_normalization` fix both comparison maps |
| Natural in modules and cover refinements | Natural `sourcePoint`, `targetPoint`, `sourceComparison`, `targetComparison`, `unitColumns`; `source_natural`/`target_natural` and `source_operator`/`target_operator` fix all maps to the prescribed columns |
| Restriction of the entire square to B/U and its ring | `restrictDerived RB U` descends the recorded exact `localizedSystemRestriction.{u,u,u}` (= `overFunctor` with ring `RB.over U`); `Comparison.Restricts` applies it to the two paths of `unit_total` |
| Original restricted unit, no sliced h adjunction or unbounded product | The argument inside `S.map` is literally the original `t* Rg* eta_RfN`; there are no h functors on slices, no product totals and no hypothesis that hInverse preserves injectives |

The parameter category encodes simultaneous coefficient maps and covering
refinements: an arrow p→q accompanies V_q→V_p and N_p→N_q. For a single cover
and module take the one-object category. The coherent model is a presentation
of the canonical localization adjunctions, as explicitly requested by the
return; it does not assume the comparison conclusion. Its existence is already
stated in the proof's step-1 module.

Recorded dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings` (site convention).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`:
  `CategoryTheory.IsGrothendieckAbelian`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`; on these
  Grothendieck categories the published K-injective `rightDerivedFunctor` has
  the same normalized universal pair.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `Sheaf.over`, and `GrothendieckTopology.over`.
- `WeilConjectures.CategoryTheory.DoubleComplexTotal` and Mathlib's total-complex
  API: `HomologicalComplex₂.total`, `ιTotal`, `totalFunctor`; the finite diagonal
  at `ComplexShape.up ℕ` has the sign `d_Cech + (-1)^n d_internal`.
- `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`:
  `SheafOfModules.localizedSystemRestriction`, `localizedSystemExact` and its
  exactness instances, required by `mapDerivedCategory`.
- `Sheaf.CategoryTheory.CoherentCechImageModel`: `CategoryTheory.sheafCoverNerve`,
  `CategoryTheory.CoherentCechImageModel` and its `image`, `imageIso`, `adj`,
  `augmentation`, `unit`, `augmentation_naturality` fields.
- `Sheaf.CategoryTheory.RingedSheafSliceConstruction`:
  `CategoryTheory.elementModulePullback`, `elementRing`, `elementMap` and
  `elementModulePullbackOver`, exactly the element-site interfaces inside D.
- Size convention `def-weil-size-convention` is rendered by explicit universes;
  it has no separate declaration. The module uses `set_option autoImplicit false`.

The image-additivity instance transports additivity along `D.imageIso` from
restriction followed by `D.push`. Restriction is additive because `D.adj` makes
it a left adjoint between abelian categories; this uses existing Mathlib
additive-functor lemmas, not an additional postponed theorem.
Proof imports retain derived Cech descent, nonnegative derived totalization,
derived-composition normalization and topos-slice presentation. The proof
outline follows all six DAG steps: initial normalized Cech resolution; derived
f composition; termwise exact unit on finite sums; derived g and exact t;
coefficient/refinement naturality; exact restriction on B.

Edge cases rechecked after repair: identity cover, arbitrary nonrepresentable
covering sheaf, noninvertible cover refinement, zero module and zero ring,
identity h adjunction, noninvertible h unit, empty or non-subcanonical site,
Cech degree zero, negative total degree (extension by zero), and arbitrary
U in B's site. None requires a global section of V, representability, a finite
cover, or a uniform cohomological bound. D.unit fixes local restriction through
adjunction, rather than merely testing global sections.

Searches retained from the saved packet:

- `msearch.py ... leanfinder "Functorial bounded below Cech descent identifies an exact adjunction unit after derived direct images with first quadrant totalization"`: eight generic derived-adjunction-unit hits; no theorem matching this item.
- `msearch.py ... loogle '"mapDerivedCategory", "total"'`: no match.
- `msearch.py ... grep '(Cech|cech|Čech).*(derived|total)|(derived|total).*(Cech|cech|Čech)'`: no matching Mathlib theorem.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf`, and item-id search in the upstream tree: no existing theorem of this item.

Repair searches/readings: `msearch.py ... grep 'CoherentCechImageModel|sheafCoverNerve'`
returned no Mathlib hits. The project search finds the existing recorded model
and its consumer `DerivedCechImageTotalization.lean`; both full model signature
and docstrings were read. The element restriction bodies were read in
`RingedSheafSliceConstruction.lean`. Mathlib searches found
`Functor.additive_of_iso`, `additive_of_preservesBinaryBiproducts` and
`Adjunction.isLeftAdjoint`, so no new mathematical helper is needed.
The informal node, proof and source were reread, including blueprint
main-20261015 direct-images.proof.md (3), Stacks `sites-cohomology.tex` at
`lemma-injective-module-trivial-cech` (03FC), and `derived.tex` at
`lemma-two-ss-complex-functor` (015J) and `lemma-right-derived-exact-functor` (015F).

## Repair self-check by N6

Compared the saved packet with the return and current shared node. The only
changed node fields are `lean` and `stmt_deps`; the TeX and six proof steps
are unchanged. Every removed private declaration is absent from the repaired
file and its declaration list. `D.image` provides exactly the slice model used
by the proof's step-1 theorem. Its units and refinements replace every old
augmentation use. The signature is copied verbatim from `theorem` to `:=`.
The restricted-square clause follows from `unit_total`, as the return noted,
and retains precisely the stage-1 slice assertion. No new nodes or dependency
modules are delivered. All compilation uses scompile.py; all writes are inside
this sandbox, with delivery bookkeeping performed only by deliver2.py.

Final standalone verification: `scompile.py N6
lem-sfb-cech-localization-unit-totalization
lean/Sheaf/CategoryTheory/CechLocalizationUnitTotalization.lean` compiled both
the sandbox and actual library module cleanly (21.9 s and 19.3 s), without errors
or warnings. A local text check confirmed the verbatim signature, declaration
list, one `sorry`, no Lean line over 100 characters, and removal of all private
slice-model declarations. The explicit arrow type on the existing refinement
map avoids the initial elaboration-heartbeat timeout; no limit was increased.

## Second reading by N6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
