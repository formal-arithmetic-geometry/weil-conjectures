## Worker report

Module: `Sheaf.Paper.TraceGraphCorrespondence`. Primary declaration:
`WeilConjectures.TraceFormulaCoefficientConventions.graphCorrespondence`.
The main entry is a partial application of the fully typed general constructor: its
remaining explicit arguments are K, h and v, with exactly the types recorded below.
This avoids re-elaborating the derived pullback after substituting the large coefficient
convention record. The item node changes only in `lean`. No statement correction, new node, or dependency
record repair is needed. Every theorem body is `sorry`; every definition has actual data.
The four postponed statements are the origin/adjunction typing obligations, identity
comparison invertibility, and fixed-scheme clause of this definition, all recorded in
`lean.declarations` with source and proof docstrings.

Hypothesis and clause matching:

- Global finite-field datum, prime l distinct from p, chosen finite extension inside the
  fixed algebraic closure, uniformizer quotient and positive level: the argument
  `T : TraceFormulaCoefficientConventions` stores exactly these data. The construction
  uses `T.datum`, `T.coefficients.l`, `T.coefficients.different`, `T.coefficientField`.
  Positive stage `T.level` is represented by index `T.level - 1`, since
  `T.level_pos` implies `T.level - 1 + 1 = T.level`. No zero coefficient level is added.
- The separated finite-type geometric fibre X from those conventions is exactly
  `T.geometricBaseChange`, bundled over s as `Over.mk T.structureMap`. Its separated,
  locally finite-type and quasi-compact instances are the recorded geometric instances.
  Finite type means locally finite type plus quasi-compactness.
- A k-endomorphism h is `h : Over.mk T.structureMap ⟶ Over.mk T.structureMap`.
  Its equation over Spec k is `h.w`. Separation and finite type follow from those of X
  by `IsSeparated.of_comp`, `locallyOfFiniteType_of_comp`, and `QuasiCompact.of_comp`,
  as in `trfCorrespondenceCompactifiable`; there is no additional property assumption.
- K in D^b_ctf is the full subcategory of `trfFiniteTorFixed` on this very scheme,
  at this coefficient field and positive level. This is the canonical fixed-scalar
  realization of `finiteTorConstructible`, not a replacement constructibility predicate.
- The arbitrary morphism v is an ambient derived morphism from the value of
  `(ProEtale.upperStar (ModuleCat (ULift A)) h.left).leftDerivedFunctor` at `K.obj`
  to `K.obj`, exactly the ordinary derived pullback in the fixed-scalar coordinates
  used by the recorded correspondence dependency.
- `trfGraphCorrespondence` constructs the dependency's actual
  `TrfCohomologicalCorrespondence`, with `C := X`, `c₁ := 𝟙 X`, `c₂ := h`.
  The map c is consequently its recorded `toProduct`, the fibre-product lift with
  these ordered projections. There is no arbitrary geometric map.
- The coefficient is `v ≫ (trfGraphIdentityIso ...).hom`, i.e. iota composed with v.
  Its codomain is literally `trfCorrespondenceExceptional ... (𝟙 X)`, hence the
  recorded `trfExceptional` / `sfFiniteExceptionalAt`, rather than an ambient
  pro-etale right adjoint or a freely supplied exceptional functor.
- `trfGraphIdentityMap` transposes the canonical `originCompactSupportId` component
  under `ProEtale.rightDerivedUpperShriekHomEquiv`. This is the specified
  constructible adjunction built from the etale exceptional adjunction and the
  site comparison. Transposing alpha is eta followed by G(alpha), exactly the node's
  transported unit. `originCompactSupportId` transports the ordinary etale identity
  comparison, obtained from the trivial compactification and canonical independence.
  The map is constructed first; `isIso_trfGraphIdentityMap` postpones only its
  invertibility. `trfGraphIdentityIso` uses `asIso`, whose inverse is determined by
  the already constructed map. No Nonempty choice of maps or adjunction is used.
- `trfGraphOrigin` states the existing origin property of bounded constructible K.
  `trfGraphIdentityBoundedBelow` supplies only the identity etale bounded-below
  adjoint typing obligation, since the published Hom equivalence requires it.
  They are named proof obligations, not added hypotheses or unspecified data.
- `trfGraphCorrespondence_fixedScheme` states equality with the exact dependency
  `trfEndomorphismFixedScheme X h`. The equalizer universal property and the two
  pullback projections are already provided by `TraceFixedScheme`; its
  `trfEndomorphismFixedScheme_equalizer` applies to all test schemes. This uses
  the whole scheme, including nilpotents, and is independent of v.

Dependencies read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum` and `CoefficientDatum`.
- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `TraceFormulaCoefficientConventions`, `coefficientField`, `geometricBaseChange`,
  `structureMap`, `geometricFiniteType`, `geometricQuasiCompact`, `geometricSeparated`.
- Scheme-property convention node defines no declaration: use Mathlib
  `AlgebraicGeometry.IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` and `Over`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback` is the intrinsic
  transport of the same fixed-scalar derived upper star. The recorded correspondence
  interface already uses the latter, which this delivery reuses without a private copy.
- `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`: `ProEtale.sfFiniteExceptionalAt`.
- `Sheaf.Paper.TraceExceptionalAdmissibility`: `trfFiniteTorFixed`, `trfExceptional`,
  `TrfExceptionalStage` and its specified constructible adjunction interface.
- `Sheaf.Paper.TraceCohomologicalCorrespondence`:
  `TrfCohomologicalCorrespondence`, `toProduct`, `trfCorrespondenceExceptional`,
  `trfCorrespondenceCompactifiable`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.lift`; Scheme pullbacks exist.
- `Sheaf.Paper.TraceFixedScheme`: `fixedScheme`, `trfEndomorphismFixedScheme`,
  `trfFixedGraphMap`, `trfEndomorphismFixedScheme_equalizer`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`: `sfIntrinsicCompactSupport`
  is the recorded intrinsic compactification formula; its fixed-scalar etale-origin
  identity comparison is `ProEtale.originCompactSupportId` from
  `Sheaf.Paper.CanonicalOriginCompactSupportComposition`.
- Published `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek`:
  `rightDerivedUpperShriekHomEquiv` (read using `scompile.py --source`), whose
  adjunction is constructed from the actual etale adjoint and comparison maps.
  `Etale.HasBoundedBelowUpperShriek` was read in the shared current upstream source;
  its identity case, unlike the obsolete unconditional upstream instance, is supplied
  explicitly as a named theorem. The exported graphBaseSeparated, graphBaseFiniteType and graphBaseQuasiCompact instances
  expose the same geometric proofs in the bundled over-scheme presentation; they add no
  hypothesis and prove no new theorem. All these dependencies are available transitively
  through the single public import `Sheaf.Paper.TraceFixedScheme`.

Edge cases checked before writing: h=id has both legs identity and retains the entire
fixed scheme, including nilpotents. An endomorphism without fixed points gives the empty
pullback. Empty X, K=0, and v=0 are allowed by the data, with no nonemptiness, nonzero,
invertibility, properness or Frobenius requirement. The graph is over the common base
by h.w, not by pointwise equality. The equalizer tests arbitrary schemes, so nilpotent
fixed structure is preserved. Level 1 uses n=0 in the n+1 API. Scheme and coefficient
universes match the published ModuleCat.{u+1}/ULift convention. No local notation,
private definition, file-local instance or auto-implicit variable is used.

Searches (2026-10-18):

- `msearch.py ... leanfinder "Graph correspondence of an endomorphism with coefficient
  morphism derived pullback exceptional identity inverse image"`: eight hits, on
  SimpleGraph maps and the RelCat graph functor; no cohomological correspondence match.
- `msearch.py ... leansearch "Graph endomorphism cohomological correspondence exceptional
  inverse image"`: eight unrelated End, module-endomorphism and graph hits; no match.
- `msearch.py ... loogle '"lowerShriek"'`: zero Mathlib hits.
- `msearch.py ... grep 'GraphCorrespondence|ofGraph|upperShriekIdIso' AlgebraicGeometry`:
  zero Mathlib hits.
- `rg` of the item label and `ofGraph|GraphCorrespondence` in the upstream source and
  `lean/Sheaf`, plus `dag/lean_names_upstream.json`: upstream
  `AlgebraicGeometry.ProEtale.Correspondence.ofGraph` is related but takes
  `GeometricOperations` and its `upperShriekIdIso`. Its exceptional functor is the
  GeometricOperations functor, not the dependency's specified constructible functor,
  and that full operations package is an extra assumption. Its signature and docstring
  were read; it cannot serve as an exact existing binding of this node. Side-project
  `trfFixedGraphMap` is only the geometric map, and is reused through its fixed scheme.
- `rg` for `TrfExceptionalStage`, `IsExceptionallyAdmissibleAt`, identity comparisons,
  and bounded-below upper shriek exposed the canonical origin identity and Hom
  equivalence used above. There is no existing canonical graph on this recorded
  correspondence structure.

Source checked: main-20261015 graph definition, order 2432, and the expanded DAG
statement including iota and the fibre product. No disputed statement was found.

## Second reading by NI

I reread the node and final module clause by clause in this worker session; no separate
agent was started, as the dispatcher brief forbids that. Maintainer independent review
remains separate. The main correction during this reading was to expose the exact
`TraceFormulaCoefficientConventions.graphCorrespondence` entry point: a bare arbitrary
separated finite-type k-scheme does not by itself record the node's chosen geometric
fibre and coefficient-field conventions. The main entry now takes T, h on its actual
geometric fibre, and K and v in the recorded fixed-scalar model at its positive level.
The more general implementation helper adds no assumption to this entry point.

I checked the unit normalization independently of the constructor syntax: the transpose
of alpha under the canonical Hom equivalence is G(alpha) after the unit, so the code
has the correct direction and composes v before iota. An arbitrary adjunction datum
would not fix that map; the code instead uses the published normalized Hom equivalence.
The origin and identity bounded-below obligations are theorems with sorry and complete
proof descriptions; no data is hidden in sorry. The resulting map is fixed before its
inverse is introduced. The support and both ordered legs agree with the node; fixed
schemes use the same diagonal pullback as the dependency and its all-test-schemes
equalizer statement. The empty, identity, zero and nilpotent cases remain present.
All theorem bodies remain sorry. No node fields other than lean changed.
