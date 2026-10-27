## Worker report

Delivery: `Sheaf.SixFunctors.FlatRingedExchangeResolutionUnit`, with the theorem
`CategoryTheory.RingedDerivedComparisons.flat_ringed_exchange_resolution_unit` and its
explicit ordinary-map helper `CategoryTheory.RingedDerivedComparisons.ordinaryBaseChangeMap`.
The helper constructs data from `mateEquiv`; the theorem has precisely `by sorry`.
No definition has postponed data. No statement correction, new node, or dependency repair
is needed. The item's node changes only in `lean`.

Source checked: `literature/stacks-project/sites-cohomology.tex`,
`lemma-base-change-map-flat-case` (Tag 0736, lines 2427–2485) and
`remark-base-change` (Tag 07A7, lines 4033–4072). The first constructs exchange using
bounded below injective resolutions and horizontal adjunctions; the second identifies
the derived counit mate for arbitrary ringed squares. The resolution-unit equation is
the normalization of that construction. Also read the current latest blueprint's
`sk-thm-sf-ctf-stability-direct-images.proof.md`, clause (3), the inherited proof ancestor;
this helper is not the statement of the blueprint unit itself.

Hypotheses and objects, clause by clause:

- Four small ringed sites: `{E E' F F' : Site.{u, w}}`. The existing `Site` has a
  `C : Type u` with `SmallCategory C`, topology `J`, and commutative ring sheaf
  `A : Sheaf J CommRingCat.{u}`. `Site.modules` is the recorded `ringedSiteModules`
  (Mathlib `SheafOfModules`), and `Site.D` is the ordinary unbounded derived category.
  The normalized comparison interface also carries its existing tensor presentations;
  the theorem uses the same interface as its recorded derived-map dependency, without
  constructing another module category or tensor structure. Universes `u` and `w` are
  explicitly declared and independent; `w` is the chosen derived Hom universe.
- Specified commutative square with structural ring maps:
  `S : DerivedBaseChangeSquare E E' F F'`. Its `f`, `f'`, `g`, `g'` are precisely the
  four edges in the node. `pInverse`, `qInverse`, `squareInverse`, `pRing`, `qRing`, and
  `squareRing` retain the given geometric square and ring compatibility. The six lifts,
  two path comparisons and geometric two-isomorphism comparison are the existing
  canonically normalized data, not arbitrary functors or transformations.
- Exact horizontal tensor pullbacks: `_hg : exactFunctor F.modules F'.modules
  S.lg.edge.pullback` and `_hg' : exactFunctor E.modules E'.modules
  S.lg'.edge.pullback`. Mathlib `exactFunctor` is the conjunction of preservation of
  finite limits and finite colimits. No exactness is required of `f*` or `f'*`.
- Module adjunctions: the lifts' `edge.moduleAdjunction` are the normalized
  scalar-extension/direct-image adjunctions. They are tied to the original ringed
  morphisms by `ordinary_adjunction`, `pushforward_eq` and the structural-map equation.
- Canonical total right derived pairs: `S.lf.edge.right`, `S.lf.eta`,
  `S.lf'.edge.right`, `S.lf'.eta`. `Lift.isRightDerived` supplies the universal property,
  and `eta_injective` its K-injective normalization. The dependency
  `def-sfb-right-derived-functor` describes this universal pair up to the unique
  unit-compatible isomorphism; the square's already supplied normalized pair is used
  directly, not replaced by a separately chosen right derived functor.
- Ordinary exchange `e`: `ordinaryBaseChangeMap S` is `mateEquiv` for the two vertical
  ordinary adjunctions, applied to
  `firstComposition.ordinary.symm ≪≫ squareComparison.ordinary ≪≫
  secondComposition.ordinary`. The geometric path and two-isomorphism comparisons are
  exactly those already specified in `S`. `NatTrans.mapHomologicalComplex ... (.up ℤ)`
  is its termwise extension to complexes, with no arbitrary chain map parameter.
- Canonical derived exchange beta: `derivedBaseChangeMap S (DerivedCategory.Q.obj P)`
  is the recorded dependency's actual definition, the vertical mate of the same
  three comparisons at the derived level.
- Every bounded below complex: `P : CochainComplex E.modules ℤ`, `n : ℤ`, and
  `_hP : P.IsStrictlyGE n`. Quantifying over every integer bound covers every strictly
  bounded below representative. There is no termwise injectivity, K-injectivity,
  acyclicity, flatness, or cohomological vanishing assumption on `P`.

Conclusion and the exact identifications:

Write `R_c` for `S.lf.edge.pushforward.mapHomologicalComplex (.up ℤ)` and `B_c` for
`S.lg'.edge.pullback.mapHomologicalComplex (.up ℤ)`, for this explanation only.
The displayed Lean equation is

```
Lg*(eta_f(P)) ≫ beta(QP) ≫ Rf'_*(alpha_g'(P))
  = alpha_g(R_c P) ≫ Q(e_P) ≫ eta_f'(B_c P).
```

Both sides start at `Lg*(Q(R_c P))` and end at `Rf'_*(Q(B_c P))` in `F'.D`.
`Lift.alpha` is the existing `derivedPullbackComplexComparison`, oriented
`Lg*(QP) → Q(g*P)`, defined using the left-derived counit and canonical quotient
comparisons. Under horizontal exactness it is the exact termwise identification.
The node suppresses these two identifications; Lean keeps them explicit.
Postcomposing the node's equality by `Rf'_*(alpha_g'(P))` and using its source
identification is exactly the displayed equation. Conversely those canonical
identifications are isomorphisms under the hypotheses, so this equation recovers the
node's equality. No additional conjunct or isomorphism assertion is made. In particular,
`eta_f(P)`, `eta_f'(B_c P)` and beta remain arbitrary maps in the conclusion.

Dependency declarations used/read:

- `def-weil-size-convention`: metatheoretic convention; explicit `u w`, the chosen
  `Site.derived`, and Mathlib `HasDerivedCategory` implement it. No module to import.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`;
  used via `Site.modules` and publicly available from the derived square's imports.
- `Sheaf.CategoryTheory.RingedToposMorphism`, `CategoryTheory.RingedToposMorphism`;
  used via `Morphism` and the square's actual four edges.
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`,
  `SheafOfModules.module_pullback_pushforward_adjunction`; its full signature and
  normalization docstring were read. The square's `Lift` stores precisely the
  normalized module adjunction, so no second choice is made. Public import retained.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; used through `Site.D` and explicitly.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`,
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`, its unit and
  universal/unique theorems; read all definitions and signatures and retained the
  public import. The supplied lifts implement this universal-pair notion directly.
- `Sheaf.CategoryTheory.DerivedBaseChangeMap`,
  `CategoryTheory.RingedDerivedComparisons.DerivedBaseChangeSquare` and
  `derivedBaseChangeMap`; both used directly. Its public comparison-data import supplies
  `Site`, `Lift.alpha`, `Composition.ordinary`, `TwoIso.ordinary`, the derived
  comparisons, and their normalization fields.

Every stated proof-dependency module is imported, without `public` when needed only
for the proof: `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
(`Functor.exactFunctor_derivedFunctor`),
`Sheaf.SixFunctors.RingedDerivedAdjointLift` (`adjointLift_exists`),
`Sheaf.SixFunctors.ResolvingDerivedAdjunction` (`derivedAdjunctionOfResolvingClass`),
`Sheaf.SixFunctors.RingedDerivedCompositionComparison` (`compositionCore_exists`),
`Sheaf.SixFunctors.RingedDerivedTwoIsoComparison` (`twoIsoComparison_exists`),
`Mathlib.CategoryTheory.Adjunction.Mates` (`mateEquiv_vcomp`, `mateEquiv_hcomp`,
`mateEquiv_conjugateEquiv_vcomp`, `conjugateEquiv_mateEquiv_vcomp`,
`conjugateEquiv_id`), `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
(`SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`),
and `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
(`CochainComplex.exists_isKFlatResolutionIndependentCoefficients`).
The derived-map proof dependency is already public as a statement dependency.
The theorem's docstring follows all five proof steps, including the comparison of
horizontal adjunctions via the K-flat/K-injective Hom formulas.

Edge cases checked mathematically before writing:

- Identity horizontal maps give the usual naturality/identity normalization of the
  resolution transformation; no nonidentity assumption is present.
- Identity vertical maps and an arbitrary compatible square isomorphism retain that
  very isomorphism in both mates; it was not silently replaced by an identity.
- Zero complex: both routes are the unique zero-object map; no nonzero hypothesis.
- A complex concentrated in degree zero with a non-acyclic direct image is admitted:
  no resolution unit is inverted or assumed invertible.
- Every integer lower bound, including negative bounds, is admitted. No upper bound
  is imposed. `g'*P` and `f*P` are formed termwise without resolution hypotheses.
- Empty site, zero coefficient ring, and arbitrary characteristic are not excluded
  by the statement. Its universe binders are exactly those of the recorded square.
- The theorem is an equality of maps, with no Cartesian, proper, base-change
  invertibility, or exactness-of-vertical-pullback hypothesis or conclusion.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leansearch "Derived base change mate compatibility with right
  derived resolution unit"`: 8 hits, including `Adjunction.derived_unit`,
  `Adjunction.derivedε`, `Functor.totalRightDerivedUnit`, `unit_mateEquiv`, and
  ordinary `Functor.rightDerived_map_eq`. These normalize individual adjunctions
  or ordinary higher-derived morphisms, not this normalized ringed-square equality.
- `msearch.py ... leanfinder "For flat horizontal pullbacks in a square of ringed
  topoi derived exchange commutes with right derived resolution units"`: 8 hits,
  including `SheafOfModules.pullbackComp`, `PresheafOfModules.pullbackComp`,
  `Adjunction.derived'_unit`, `Adjunction.derived_unit`, and
  `Adjunction.derivedε_fac_app`. None gives this square equality.
- `msearch.py ... loogle "CategoryTheory.mateEquiv,
  CategoryTheory.Adjunction.derivedη_fac_app"`: 0 hits.
- `msearch.py ... grep "derivedη_fac_app|derivedε_fac_app|
  rightDerivedFunctorComparison_fac" CategoryTheory`: 6 hits in the derived
  adjunction and pointwise-right-derived comparison modules. Read the actual
  Mathlib derived-adjunction signatures and mate-pasting signatures: they provide
  tools for the proof, not an existing statement of the item.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the node id and flat/exchange
  and resolution/unit combinations found no statement of this item. Also searched
  both trees, Mathlib, and `dag/lean_names_upstream.json` for the proposed full-name
  suffixes `ordinaryBaseChangeMap|flat_ringed_exchange_resolution_unit`: no collisions.
  Read `Sheaf.CategoryTheory.BoundedBelowDerivedMateModel`: it assumes both vertical
  left adjoints exact and therefore does not give this ringed statement, where only
  the two horizontal pullbacks are exact. Its mate construction cannot be reused
  by imposing extra vertical hypotheses.

Validation: the prescribed `scompile.py` compiled the final module both as its sandbox
probe and as its library module, cleanly, with no non-sorry warnings (20.0 s and 7.4 s).
An initial incorrect import of nonexistent `Mathlib.Algebra.Homology.Truncation` was
removed; the existing dependency imports already expose `IsStrictlyGE`.
No `#check` lines, local notation, local instances, hidden helpers or auto-bound
implicit parameters occur in the delivered module.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
