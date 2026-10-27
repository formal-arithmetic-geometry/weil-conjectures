## Worker report

The module `Sheaf.AlgebraicGeometry.UnpointedLevelNormalizationProjectivity` states
`AlgebraicGeometry.unpointedLevelNormalizationProjectivity`, with one `sorry` and no new
definitions. The natural-language statement, accepted split, and dependencies are unchanged.
The previous worker ending concerned a stage-1 unchanged-item rejection. The current live
node has no Lean attachment, and `coord/queue.tsv` assigns it to stage 2. The stage-handoff
rule in `coord/brief-stage2.md` therefore applies; no released repair note exists for this item.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`; genus is `(g : ℕ) (hg : 2 ≤ g)`. The prime,
  lower bound three and prime-to-characteristic condition are the recorded
  `ℓ : AbelianLevelPrime (Spec (.of k))`: its stalk-unit condition over a field is exactly
  invertibility of the prime. No perfectness, algebraic closure or roots of unity are assumed.
- `L`, `eL`, `hL` specify the smooth full abelian-level representative from rigidification,
  using `abelianLevelBased`. They do not replace the frame groupoid by its coarse points.
- `Q`, `π`, `hQ`, `hQft`, `hQqc`, `hQproj` specify the coarse scheme and the finite-type and
  H-projectivity properties supplied by the coarse-projectivity node. Finite type is the
  conjunction of `LocallyOfFiniteType` and `QuasiCompact`.
- `Z`, `a`, `c`, `hc`, `hcoarse`, `i`, `e`, `hnorm`, `hsmooth` are exactly the data and
  properties of `exists_stable_abelian_level_normalization`. `hnorm` uses the recorded
  integral-closure condition on charts, so Z is the full normalization, not an arbitrary
  finite cover. `hsmooth` retains the 2-cartesian comparison with the original L. No
  connected or generic component is selected. These binders unpack “write ... for” in
  the node: they are supplied representatives and their specified properties, not added
  mathematical assumptions.
- `LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ IsHProjective Z.hom` is precisely the
  first conclusion. The existing H-projectivity definition is the finite-coordinate
  closed-embedding convention. Nonempty finite coordinates can be reindexed by Fin (N+1);
  empty coordinates imply empty source, which embeds in P^0. Thus this is the stated
  existence of N ≥ 0 and a closed immersion into P^N over k.
- The actual universal family is `a.obj (CostructuredArrow.mk (𝟙 (yoneda.obj Z)))`.
  Its base is Z by `BasedFunctor.w_obj`; its curve and projection are concrete fields
  of `StablePointedModuli`. The stable-family field `stable` includes
  `IsProjectiveBundle projection` by the recorded `IsStablePointedCurve` definition.
  This data is already present in a; no existence choice or extra axiom constructs it.
  The existential natural transformation `η` with the indicated `IsHomLift` component
  equations identifies `a(z)` with the universal family's pullback along z. Since every
  arrow of the recorded family category is cartesian, these are actual family
  isomorphisms to the scheme fibre products, compatible with every further base change.
- `(F : Type u) [Field F] [Algebra k F]` quantifies all field extensions in the scheme
  universe. `C : StablePointedModuli.Smooth ... g 0` is the recorded smooth projective
  geometrically connected genus-g family; its `base = Over.mk (Spec.map ...algebraMap...)`
  specializes it to C/F. Its zero markings, nodal geometric-fibre predicate and smooth
  projection give precisely the unpointed connected smooth curves in the statement.
- `T : Over (Spec k)` together with `b : T ⟶ C.obj.base` runs over ALL F-schemes,
  including nonreduced and disconnected tests, using the usual equivalence of iterated
  over categories. The frame `α` is an actual module-sheaf isomorphism from
  `abelianLevelConstant` to `abelianLevelCohomology` of the specified pullback C_T.
- `P`, `r`, `IsFinite r.left ∧ Etale r.left ∧ Surjective r.left` supply the finite etale
  surjective F-scheme. `frameP` and the unique d for each frame α express its universal
  frame property. The arrow q is the cartesian comparison of the specified pullbacks:
  its base and first-projection equations determine its underlying curve map uniquely.
  `AbelianLevelModuli.HomCondition` is the canonical inverse-image/degree-one base-change
  frame equation, so the bijection is compatible with restriction. This is
  representability of the precise frame functor, not an unrelated set bijection.
- `t` and `ηC` specify the classifying map of C using cartesian family arrows, as in the
  recorded rigidification interface. `eP` is an equivalence from h_P to the 2-fibre of
  a over this map, with `ModuliTwoIso` identifying its projection with r. Thus the SAME
  h_P represents both the frame functor and the 2-fibre. Composing these natural
  identifications gives the natural isomorphism asserted in the item. In the recorded
  comma convention the comparison runs C_T → a(z); its inverse is exactly the pair's
  beta from the universal family to C_T. Scheme factors have discrete fibres, so this
  2-fibre has precisely the pairs (z,beta), without quotienting by curve automorphisms.
  The formula retains the actual isomorphism and every test scheme, not just field points.
- No F-rational frame or point of P is assumed. Surjectivity gives geometric nonemptiness
  and includes the torsor cases where P(F) is empty.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `StablePointedModuli`, its
  `Hom`, `forget`, `Smooth`, and `pullback`; `AbelianLevelPrime`,
  `abelianLevelConstant`, `abelianLevelCohomology`, `AbelianLevelModuli.HomCondition`;
  `CategoryTheory.discreteModuli`, `discreteModuliMap`, `moduliTwoFiberProduct`,
  `moduliTwoFiberFst`, `ModuliTwoIso`, `IsCoarseModuliScheme`.
- `Sheaf.AlgebraicGeometry.StableAbelianLevelNormalization`:
  `exists_stable_abelian_level_normalization` and the recorded `stableModuliBased`,
  `smoothModuliBased`, `smoothModuliInclusion`, `abelianLevelBased`,
  `abelianLevelToSmooth`, `abelianLevelSchemeMap`. The chart predicate and comparison
  `moduliTwoFiberLift` come transitively from `ModuliChartNormalization`.
- `Sheaf.AlgebraicGeometry.SmoothCurveAbelianLevelRigidification`:
  `smoothCurveAbelianLevelRigidification`, `smoothCurveModuliPullback`,
  `smoothCurveModuliBase`. Its frame universal property is reused verbatim.
- `Sheaf.AlgebraicGeometry.UnpointedStableCoarseProjective`:
  `unpointed_stable_coarse_projective`, whose coarse-scheme properties are unpacked.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective` and
  `IsProjective`; `Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism`: `IsProjectiveBundle`.
- Mathlib: `Field` (`Algebra.Field.Defs`), `Algebra` (`Algebra.Algebra.Defs`), `Scheme`
  and `Scheme.Hom` (`AlgebraicGeometry.Scheme`), `LocallyOfFiniteType`, `QuasiCompact`,
  `IsFinite`, `Smooth`, `Etale` (their recorded `AlgebraicGeometry.Morphisms` modules),
  and `CategoryTheory.Limits.pullback`, `.fst`, `.snd` (the recorded `HasPullback` module).
- Proof-only import `Sheaf.AlgebraicGeometry.FiniteOverProjective` supplies the
  recorded `finite_over_projective_affineLocally`. The other stated proof dependencies
  are already imports or public transitive dependencies. No import cycle is introduced.

Edge cases checked: g=2, prime 3 in characteristic different from 3, arbitrary imperfect
fields and extensions, empty test schemes, nonreduced tests, disconnected full level
covers, and finite etale frame torsors with no rational point. The empty base is allowed
in the frame universal property. IsHomLift is necessary because a based functor commutes
with its projection propositionally; it does not silently identify bases definitionally.
The field and scheme use the same universe, as in every recorded moduli dependency;
tests cover all schemes in that convention without an independent smaller test universe.

Searches before writing:

- `msearch.py ... leanfinder`: “The full abelian level normalization of the stable genus g
  curve moduli stack is projective and its smooth family isomorphism functor is the finite
  etale frame scheme”. Eight hits, concerning Weierstrass projective curves and smooth or
  etale morphisms, not this assertion.
- `msearch.py ... loogle`: `AlgebraicGeometry.IsHProjective, CategoryTheory.BasedFunctor`.
  Zero hits; unknown identifier AlgebraicGeometry.IsHProjective in the service index.
- `msearch.py ... grep`: `level.*normaliz|normaliz.*level|frame.*functor`, restricted to
  Mathlib/AlgebraicGeometry. Zero hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the node id and
  `unpointed.level.normalization|unpointedLevelNormalization|UnpointedLevelNormalization`:
  no existing declaration. Direct reading of the dependency modules found their
  normalization, coarse projectivity and frame interfaces, but no theorem combining
  these conclusions for the specified normalization.

No new nodes or dependency repairs were needed. No statement correction or disputed
statement is proposed. The module docstring includes all four accepted proof steps;
the last frame-comparison step is expanded into its inversion and naturality operations.

Validation: single-file server compilation with the prescribed `scompile.py`; dry-run
preflight and final delivery with `deliver2.py`. Their final results are recorded by the
launcher tools. Every variable and universe is explicit (`autoImplicit false`).

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
