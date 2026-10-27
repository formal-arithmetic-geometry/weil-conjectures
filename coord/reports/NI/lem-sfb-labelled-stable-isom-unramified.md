## Worker report

The module `Sheaf.AlgebraicGeometry.LabelledStableIsomUnramified` states
`AlgebraicGeometry.exists_labelled_stable_isom_unramified`. Its sole theorem has
proof `sorry`; there are no new definitions or auxiliary postponed results.
The node statement and all dependencies are unchanged; only `lean` is recorded.

Hypothesis and clause correspondence:

- A locally Noetherian base is `{S : Scheme.{u}} [IsLocallyNoetherian S]`.
- The two schemes and structure maps are `W`, `W'`, `f : W ⟶ S`, and
  `f' : W' ⟶ S`.
- The integer `n : ℕ` allows zero; labels are `Fin n`. The sections are `s`, `s'`,
  with their section equations `hs`, `hs'`. These equations introduce the data
  required by the recorded stable-pointed predicate and are not additional
  geometric assumptions.
- Stability of both pointed curves is precisely `hstable : IsStablePointedCurve f s hs`
  and `hstable' : IsStablePointedCurve f' s' hs'`, using the recorded definition.
- The fixed permutation is `σ : Equiv.Perm (Fin n)`.
- An arbitrary test scheme over S is `T : Over S`. The base-changed schemes are
  the objects of `(Over.pullback T.hom)` applied to `Over.mk f` and `Over.mk f'`:
  their underlying schemes are exactly `pullback f T.hom` and `pullback f' T.hom`.
- A T-isomorphism is an isomorphism in `Over T.left`, so preservation of the
  structure morphism is part of the type rather than omitted.
- The labelled equation is the subtype predicate
  `∀ i : Fin n, f.baseChangeSection (s i) (hs i) T.hom ≫ a.hom.left =
  f'.baseChangeSection (s' (σ i)) (hs' (σ i)) T.hom`.
  This is equality of scheme morphisms, not merely equality of underlying points.
- The representing S-scheme is `J : Over S`. Its three required properties are
  `IsSeparated J.hom`, `LocallyOfFiniteType J.hom ∧ QuasiCompact J.hom`
  (the recorded finite-type convention), and `IsUnramified J.hom`.
- The representing bijections are the family of equivalences `e`, from `T ⟶ J`
  onto the exact labelled-isomorphism subtype for every T.
- Pullback compatibility along every `h : T' ⟶ T` is the final displayed equality
  using the canonical `baseChangeMap f h` and `baseChangeMap f' h`.
  Both sides are actual morphisms from W_T' to W'_T. Since the maps are over
  T and T', the equality characterizes base change by the pullback universal
  property; it includes the inverse maps because the elements are isomorphisms.
- The universal labelled isomorphism is explicitly available as `e J (𝟙 J)`.
  The final naturality clause specialized to `T = J`, `h = a`, and `a = 𝟙 J`
  says that the isomorphism corresponding to any test-point is its pullback.
  Thus no extra assumption supplying a universal isomorphism is introduced.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.StablePointedCurve`:
  `AlgebraicGeometry.IsStablePointedCurve`, including its full predicate, its
  normalized-component maps and genera, and its use of base-changed sections.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, and its
  universal property, supplied through the scheme and pullback imports.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`:
  `AlgebraicGeometry.IsSeparated` (the separated clause of the proper-morphism
  dependency); properness of J itself is not asserted.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`:
  `AlgebraicGeometry.IsUnramified`, the recorded finite-type/open-diagonal predicate.
- Existing canonical constructions: `CategoryTheory.Over.pullback` in
  `Mathlib.CategoryTheory.Comma.Over.Pullback`;
  `AlgebraicGeometry.Scheme.Hom.baseChangeSection` in
  `WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeSection` (publicly
  available from the stable-curve module); `AlgebraicGeometry.baseChangeMap` in
  `WeilConjectures.AlgebraicGeometry.PicardFunctor`.

The modules of recorded proof dependencies are imported privately, including
`ProjectiveCurveIsomGraphs`, `MarkedNodalInfinitesimalFields`, and
`GeometricTangentUnramified`, and the matched Mathlib modules. The three proof
nodes `lem-trf-projective-bundle-affine-presentations`,
`lem-sfb-isom-graph-representatives-zariski-gluing`, and
`lem-sfb-nodal-completed-normalization-model` have no recorded Lean module to
import at present; they occur only in the proof plan, not in the statement.
The full six-step natural-language proof is in the theorem docstring.

Edge cases checked before writing: `n = 0` has empty `Fin 0` and its unique
permutation, making the marking predicate vacuous and recovering the unpointed
Isom functor. Empty parameter fibres are allowed. Empty bases and test schemes
are allowed. Neither the bijections nor naturality imposes connectedness,
reducedness, finite type or Noetherian conditions on T or T'. All schemes and
morphisms range over the same arbitrary scheme universe u; there is no
independent smaller test universe or extra universe equality. No restriction
on characteristic or genus beyond the stable-pointed predicate is added.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leansearch "The isomorphism functor of stable pointed curves is
  represented by a separated finite type unramified scheme"`: 8 hits, including
  general local-representability/gluing and formal-unramifiedness permanence;
  none states the labelled stable Isom result.
- `msearch.py ... leanfinder "The relative functor of isomorphisms between stable
  pointed curves preserving the labels up to a fixed permutation is represented
  by a separated finite type unramified scheme"`: 8 generic hits about separated
  morphisms, etale schemes and formal unramifiedness; no labelled stable Isom theorem.
- `msearch.py ... loogle "AlgebraicGeometry.IsStablePointedCurve,
  CategoryTheory.Over.pullback, CategoryTheory.Functor.IsRepresentable"`:
  0 hits, unknown identifier `AlgebraicGeometry.IsStablePointedCurve` in the
  Mathlib search service. The project predicate was instead read directly.
- `msearch.py ... grep "StablePointed|labelled.*[Ii]som|[Ii]som.*[Ss]table"
  AlgebraicGeometry`: 0 Mathlib hits.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for labelled Isom,
  stable-pointed isomorphism and representability found the stable-pointed
  definition, the general projective-curve Isom theorem and the arithmetic
  unpointed finite Isom theorem. None is the fixed-permutation pointed theorem.
  `grep -rn "lem-sfb-labelled-stable-isom-unramified" lean/WeilConjectures`
  found no existing implementation.
- The full signatures and docstrings of the six statement-dependency records
  were read. The general projective-curve Isom statement was read in full;
  it supplies neither the marking equalizers nor unramifiedness.

Validation: prescribed `scompile.py NI lem-sfb-labelled-stable-isom-unramified`
compiled both its sandbox check and its library-name check successfully, with
no diagnostics. Every source line is at most 100 characters; all universes
and variables are explicitly bound and both auto-implicit options are disabled.
There are no statement faults, statement corrections, new nodes, or dependency repairs.

## Second reading by NI

Independent clause-by-clause reading (written by the maintainer's reviewer in
place of the dispatcher self-check note; the Lean and the records are unchanged).

Node objects, hypotheses, conclusion and their Lean:

- Locally Noetherian S (pqf-def-locnoeth): `{S : Scheme.{u}} [IsLocallyNoetherian S]`,
  Mathlib class. Exact.
- Stable pointed curves (W, s_i), (W', s'_i) over S, n ≥ 0 (def-sfb-stable-pointed-curve):
  `f`, `f'`, `n : ℕ`, `s s' : Fin n → (S ⟶ W/W')` with section equations `hs`, `hs'`
  that the recorded `IsStablePointedCurve f s hs` takes as arguments; the predicate is
  the landed one. No extra hypothesis. Exact.
- Permutation σ: `σ : Equiv.Perm (Fin n)`. For n = 0 there is one (`Fin 0`). Exact.
- W_T, W'_T (def-pc-fibre-product): `(Over.pullback T.hom).obj (Over.mk f)` has left
  `pullback f T.hom` and structure map `pullback.snd`; a T-isomorphism is an `Iso`
  in `Over T.left`. Exact.
- Pulled-back sections s_{i,T}: `f.baseChangeSection (s i) (hs i) T.hom =
  pullback.lift (T.hom ≫ s i) (𝟙 _)` (upstream DeformationSpace.BaseChangeSection),
  the canonical section of `pullback f T.hom`. Exact.
- Condition u ∘ s_{i,T} = s'_{σ(i),T}: `baseChangeSection … ≫ a.hom.left =
  f'.baseChangeSection (s' (σ i)) …`. Direction of σ matches the node. Exact.
- Representability by an S-scheme J_σ: `∃ J : Over S` with equivalences
  `e T : (T ⟶ J) ≃ {labelled isos}` for every `T : Over S` in the same universe, no
  connectedness, reducedness, finiteness or Noetherian condition on T. Exact.
- Separated, finite type, unramified: `IsSeparated J.hom` (from the
  def-weil-proper-morphism record), `LocallyOfFiniteType J.hom ∧ QuasiCompact J.hom`
  (the def-weil-finite-type-morphism record's convention), `IsUnramified J.hom` (the
  landed def-weil-unramified-morphism declaration). Exact.
- Compatibility with pullback along every S-morphism h : T' → T:
  `baseChangeMap f h ≫ (e T a).val.hom.left = (e T' (h ≫ a)).val.hom.left ≫
  baseChangeMap f' h`, with the upstream `baseChangeMap` (PicardFunctor, the canonical
  `pullback.map`). Because `W_{T'} = W_T ×_T T'` and both isos are over their bases,
  this equation determines e T' (h ≫ a) as the base change of e T a. Exact.
- Universal labelled isomorphism: `e J (𝟙 J)`; the naturality clause with
  T = J, h = a gives every `e T a` as its pullback. The node's clause is therefore
  contained in the statement, not assumed.

Edge cases: n = 0 (vacuous marking predicate, unique permutation, unpointed Isom);
empty S, empty T and empty fibres of J allowed; nonreduced and disconnected test
schemes allowed; a single universe u for S, W, W', J and T, as in the node.

Records and conventions: `lean.statement` equals the file's signature verbatim; the
only declaration is a theorem with proof `sorry`; no definitions (no hollow data);
module and theorem docstrings carry the source place, `(blueprint: …)` and the six
proof steps; stmt_deps unchanged from base and all six are used. The statement-level
constructions `Over.pullback`, `baseChangeSection`, `baseChangeMap` are Mathlib/upstream
definitions, not declarations owned by DAG theorem nodes.

Searches (H4): live `lean/Sheaf` and `lean/WeilConjectures` users of
`IsStablePointedCurve` (StablePointedModuliGroupoids, KnudsenPointedForgetfulUniversalCurve,
ProjectiveStablePointedLevelParameter, StablePointedGenericExtension, …) and the Isom
modules (ProjectiveCurveIsomGraphs, ArithmeticStableIsomFinite, DMIsomSpaceUnramified):
none states the fixed-permutation labelled Isom representability with unramifiedness.
No duplicate.

Mismatches found: none. The only change is this section.
