## Worker report

The module `Sheaf.AlgebraicGeometry.ChartedLogMapLocalRightInverse` states
`AlgebraicGeometry.EtaleLogStructure.exists_local_rightInverse_of_chart` with
`sorry`. Two real helper definitions form the canonical map on the recorded monoid
stalk colimits (`EtalePrelogStructure.mapStalk`) and restrict a global chart using
the original sheaf restriction (`EtaleLogStructure.restrictGlobalChart`). They
belong to this statement's canonical maps and carry its blueprint/source tag.
No log structure, stalk, chart predicate or unit pushout is redefined. The node's
natural-language statement, dependencies and proof are unchanged.

Hypotheses and objects, clause by clause:

- `X : Scheme.{max u v}` and `[IsLocallyNoetherian X]` render the locally
  Noetherian scheme. The independent original site and chart universes are `u`
  and `v`; using their maximum and a canonical ULift for the chart predicate
  avoids imposing an equality of them.
- `Ω`, `[Field Ω]`, `[IsAlgClosed Ω]`, and `t : Spec (.of Ω) ⟶ X` render the
  geometric point in the universe required by the recorded geometric-stalk API.
- `N M : EtaleLogStructure X` are precisely the two log structures from
  `def-trf-fs-log-blowup`. These are not required to be fine or saturated.
- `f : N.monoidSheaf ⟶ M.monoidSheaf` is the monoid-sheaf homomorphism;
  `hf : f.hom ≫ M.alpha = N.alpha` says `alpha_M f = alpha_N`.
  Fixing units follows from the log unit condition and is not an extra assumption.
- `Q : Type v`, `[CommMonoid Q]`, and `hQ : Monoid.FG Q` render the arbitrary
  finitely generated commutative monoid. `q` maps to sections at
  `Scheme.Etale.mk (𝟙 X)`, and `hq` is the recorded `M.IsChart` of the same map,
  precomposed with the canonical `MulEquiv.ulift` down isomorphism.
- The `IsIso` assumption on `mapStalk ... f t` is invertibility of the induced
  geometric stalk homomorphism, formed by `colimMap` on the original diagrams.
  In particular an arbitrary stalk isomorphism is not substituted for this map.

Conclusions, clause by clause:

- `V : X.Etale`, `w : (Scheme.pointSmallEtale t).fiber.obj V`, and
  `IsAffine V.left` give the affine pointed etale neighbourhood. The fibre is
  exactly the lift of `t` to `V.left` together with its triangle equation.
- `k : Q →* N.monoidSheaf.obj.obj (op V)` is the required monoid homomorphism.
- The first equation of monoid homomorphisms is `alpha_N k = alpha_M(q|V)`.
- The second equation is `(f|V) k = q|V`.
- The third equation says `germ_N k = inv(f_stalk) (germ_M(q|V))`.
  `restrictGlobalChart` is the actual restriction of `q`; its germ is therefore
  `q` at the original geometric point, under the stipulated canonical identification.
- `g` is a natural transformation between the two presheaves restricted to
  `(Over V).op`. A test object is an etale `W → X` with a map `a : W ⟶ V`.
  This is the small etale site of `V.left`: maps between etale `X`-schemes are
  etale, and composing an etale `V.left`-scheme with `V.hom` is etale over `X`.
  The induced slice topology is the etale topology. Thus these presheaves are the
  actual restricted sheaves; no arbitrary replacement sheaves are introduced.
- `g ≫ Functor.whiskerLeft ... N.alpha = Functor.whiskerLeft ... M.alpha`
  makes `g` a log homomorphism over the identity of `V.left`.
- Evaluation at the terminal slice object `Over.mk (𝟙 V)` says `g(q|V) = k`.
- The quantified `g'` clause says precisely uniqueness among log homomorphisms
  with that chart value. The candidate `g'` is only required to respect structure
  maps and the chart, not to satisfy the later right-inverse/germ conclusions.
- `g ≫ Functor.whiskerLeft ... f.hom = 𝟙 _` says `(f|V) g = id`.
- Finally, for every `W`, `a : W ⟶ V`, pointed lift `z` mapping to `w`, and
  section `s`, `germ_N(g(s)) = inv(f_stalk)(germ_M(s))`. Every germ of the
  restricted sheaf has such a pointed representative. Thus this is exactly
  `g_stalk = f_stalk⁻¹` under canonical pointed restriction identifications.
  It specifies that map on all representatives, not only on the chart generators.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, used
  through the existing `Scheme.Etale` small-site object type.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`;
  `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.SpecToEquivOfField` read to
  verify the recorded inline geometric-point encoding.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`: `pointedEtaleStalkDiagram`,
  `pointedEtaleStalk`, `pointedEtaleGerm`, and the particular monoid-colimit instance.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: `EtalePrelogStructure`,
  `EtalePrelogStructure.stalk`, `EtalePrelogStructure.germ`, `EtaleLogStructure`,
  and `EtaleLogStructure.IsChart`.
- `Sheaf.AlgebraicGeometry.AssociatedLogUniversalStalks` is a plain proof import:
  its `associatedLog_universal_stalks` includes the chart universal property used
  in proof steps 3--4. Its `HomOverIdentity` was read: the restricted analogue is
  expressed directly by natural transformations and the same structural equation.
- The other proof dependency, `lem-trf-finite-monoid-stalk-data-spreading`, has
  no recorded Lean module in the read repository, so there is no proof import to
  add for it. The present statement needs none of its conclusion to typecheck.

Sources checked: ILO PDF pages 75 and 81 (printed 69 and 75), Expose VI 1.1
and 3.7(a), including the last chart-extension sentence; the current blueprint
`main-20261015`, `sk-i-curve-zero/lem-trf-local-term-locality.proof.md`; and the
item's accepted finite-monoid/associated-log proof extraction. The theorem
proof docstring records all four steps with the two original proof dependencies.

Edge cases checked before writing: the trivial monoid (empty generating tuple),
a finitely generated group chart, a nonintegral monoid with an idempotent, and
`f = id`. No `Nonempty` generating set, cancellativity, torsion-free condition,
saturation, fineness of `N`, or finite generation of its units is used. An empty
scheme has no geometric point, so the pointed assertion has no instance there.
The uniqueness quantifier covers every compatible extension, and the final
stalk equation covers all section representatives. No statement fault found.

Searches for existing declarations:

- `msearch.py ... leanfinder`: “A morphism of log structures invertible at a
  geometric stalk has a local right inverse on a pointed affine etale neighborhood
  when the target has a finitely generated monoid chart”. Eight results, including
  `AlgebraicGeometry.exists_lift_of_germInjective`, ordinary etale ring maps, and
  `StandardEtalePair.homEquiv_symm_apply`; none treats log-sheaf chart inverses.
- `msearch.py ... loogle 'LogStructure'`: zero results, unknown identifier.
- `msearch.py ... grep 'LogStructure|PrelogStructure|log_structure|charted.*right.*inverse'`:
  two results in manifold ChartedSpace, unrelated to logarithmic structures.
- `rg` of `lean/WeilConjectures` for `LogStructure`, `PrelogStructure`,
  `log_structure`, and this node id: no matching declaration.
- `rg` of `lean/Sheaf/AlgebraicGeometry/*Log*.lean` for `HomOverIdentity`,
  chart predicates, log restriction, and stalk maps found the recorded log and
  associated-log interfaces and the stronger fine-log chart-spreading theorem.
  The latter requires a fine source structure and integral source chart and
  concludes a chart, so it does not state this right-inverse lemma.
- `rg` of project Lean, upstream Lean and Mathlib algebraic geometry for
  `mapStalk`, `restrictGlobalChart`, and `exists_local_rightInverse_of_chart`:
  no name collision. The actual helper construction uses Mathlib `colimMap`
  and `Functor.whiskerLeft`; their signatures/docstrings were inspected.

All writes were confined to the assigned sandbox; all Lean checks use scompile.py.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
