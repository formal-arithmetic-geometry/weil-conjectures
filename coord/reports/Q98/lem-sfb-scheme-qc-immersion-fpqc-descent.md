## Worker report

Item: lem-sfb-scheme-qc-immersion-fpqc-descent. The new module
`Sheaf.AlgebraicGeometry.QuasiCompactImmersionAffineDescent` states
`AlgebraicGeometry.quasiCompactImmersion_of_flat_surjective_affine_baseChange`.
Its entire proof is `sorry`; no definition, helper theorem, or new node is added.
The node changes only in `lean`. No statement correction or disputed statement.

The previous ending described an unchanged-node rejection after the stage-1
split landed. I checked the current node: it has `reviewed`, no `lean`, and the
current queue lists stage 2. The retained sandbox had only dispatcher markers,
no Lean module, report, node copy or interrupted delivery result. The stage
handoff in coord/brief-stage2.md §0 explicitly says to continue stage 2 here.

Source read: literature/stacks-project/descent.tex,
lemma-descending-property-quasi-compact-immersion (Stacks Tag 02L8), including
its proof. The node is its descent implication for one flat surjective map
between affine schemes. Such a map is automatically quasi-compact. The
module docstring reproduces all five accepted DAG proof steps, including the
dense-case scheme-image argument of Tag 081I, rather than silently substituting
the general scheme-image theorem for the split's chosen argument.

Hypotheses and clauses, individually:

- A scheme S: `{S : Scheme.{u}}`.
- Affine S-schemes U and V: `{U V : Scheme.{u}}`, `[IsAffine U]`,
  `[IsAffine V]`, `(sU : U ⟶ S)` and `(sV : V ⟶ S)`. Here affine means
  the schemes themselves are affine, exactly as the node's proof requires;
  no affineness of S or of the structure maps is assumed.
- A morphism of S-schemes p: `(p : V ⟶ U)` and `(_hp : p ≫ sU = sV)`.
  Composition is in Mathlib's diagrammatic order. This compatibility records
  the given S-linearity; it is not an extra geometrical assumption.
- Flat p: `[Flat p]`, equivalent to the stalkwise condition in its definition node.
- Surjective p: `[Surjective p]`, surjectivity on underlying points.
- A scheme X and an arbitrary scheme morphism f: `{X : Scheme.{u}}`
  and `(f : X ⟶ U)`. No extra structure map on X or constraint on f is added.
- The base change X ×_U V and its morphism to V: `pullback f p` and
  `pullback.snd f p`, using the chosen categorical fibre product.
- Quasi-compactness after base change: `[QuasiCompact (pullback.snd f p)]`.
- Immersion after base change: `[IsImmersion (pullback.snd f p)]`.
- The two conclusions: `QuasiCompact f ∧ IsImmersion f`.
- Immersion's closed-then-open definition: the existing
  `AlgebraicGeometry.IsImmersion.isImmersion_iff_exists` identifies the native
  class with precisely this factorization; no replacement predicate is defined.
- Quasi-compactness's affine-open definition: the existing
  `AlgebraicGeometry.quasiCompact_iff_forall_isAffineOpen` identifies the native
  class with quasi-compact preimages of affine opens. `CompactSpace` has no
  Hausdorff assumption; the assertion is about quasi-compactness of the morphism,
  not compactness of X alone.
- No Noetherian or finite-presentation assumption: neither is a binder; the
  universe u is explicit and arbitrary. `autoImplicit` is explicitly disabled.

Statement dependency interfaces read and used:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- def-weil-flat-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat` and its `iff_flat_stalkMap` characterization.
- def-weil-surjective-morphism:
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`,
  `AlgebraicGeometry.Surjective` (available publicly through the imports).
- def-weil-affine-spectrum: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`; affineness is the
  existing `AlgebraicGeometry.IsAffine` of `Mathlib.AlgebraicGeometry.AffineScheme`,
  with canonical `Scheme.isoSpec`. This retains all affine schemes without
  requiring a chosen presentation as Spec of a ring.
- def-pc-fibre-product:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback` and `pullback.snd`; existence for schemes
  is supplied by `Mathlib.AlgebraicGeometry.Pullbacks`.
- def-weil-closed-immersion:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`, and the immersion characterization in
  `Mathlib.AlgebraicGeometry.Morphisms.Immersion` just cited.
- def-weil-open-immersion: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`, used through that characterization.
- def-weil-pbc-quasi-compact-scheme: `Mathlib.Topology.Defs.Filter`,
  `CompactSpace`; the morphism property already exists as
  `AlgebraicGeometry.QuasiCompact` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` and has exactly the
  affine-open characterization read above. No dependency interface needs repair.

Proof imports include the recorded modules
`WeilConjectures.AlgebraicGeometry.FpqcDescendQuasiCompact`
(`AlgebraicGeometry.quasiCompact_of_fpqc_baseChange`),
`WeilConjectures.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange`
(`AlgebraicGeometry.isSeparated_of_flat_surjective_baseChange`), and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`
(`AlgebraicGeometry.Scheme.Hom.ker_pullback_snd`). Mathlib's image and image-factor
interfaces are in `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`, already
publicly imported through Immersion. FlatDescent supplies
`AlgebraicGeometry.descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'`.
QuasiSeparated and Separated provide the recorded permanence and cancellation
interfaces. The relevant clause (e) of lem-weil-pbc-proper-fp-permanence uses
Immersion's composition instance, already a statement import; unrelated properness
and finite-presentation clauses are not used by this proof and need no import.

Edge cases checked mathematically before writing:

- Empty U forces X and V empty because their morphisms to U exist; the conclusion
  is the empty immersion, without a nonemptiness hypothesis.
- Empty V and surjective p force empty U; thus descent has no vacuous bad case.
- Empty X is admitted over every U; the empty immersion is quasi-compact.
- Identity p is admitted for every affine U; the conclusion is exactly the
  supplied properties transported across its canonical pullback isomorphism.
- Open immersions with nonclosed image are covered; the conclusion does not
  erroneously ask for a closed immersion.
- Nonreduced schemes and arbitrary non-Noetherian rings are included. No
  reducedness, separatedness of X, finite type or finite presentation is assumed.
- S need not be affine and may be empty when structure maps exist. No
  independent test-object universe makes the hypotheses vacuous.

Searches actually run in this attempt:

- msearch.py leanfinder: "A quasi compact immersion of schemes descends along
  a faithfully flat morphism between affine schemes". Eight hits: open-immersion,
  surjectivity, isomorphism, universal-injectivity, universal-openness and
  universal-closedness descent, quasi-compact base-change stability, and the
  immersion factorization theorem. No exact statement.
- msearch.py loogle: `"IsImmersion", "Flat"`. Zero hits.
- msearch.py grep: `IsImmersion.*[Dd]escen|[Dd]escen.*IsImmersion|quasi.compact immersion`.
  One hit, Immersion.lean:243, a pullback description of a quasi-compact immersion,
  not its descent theorem.
- rg over both lean/WeilConjectures and lean/Sheaf with that same pattern and
  the item ID: unrelated uses of quasi-compact immersions; no exact statement.
- rg over Mathlib/AlgebraicGeometry, lean/WeilConjectures and lean/Sheaf for
  `qcImmersion_of|quasiCompact.*[Ii]mmersion.*[Dd]esc|[Ii]mmersion.*[Ff]lat.*[Ss]urjective|quasiCompactImmersion_of`:
  no hits before writing the new declaration.

Validation: scompile.py passed both checks for this exact module: sandbox
Sheaf.Stage2.Sandbox0 (12.1 s) and library
Sheaf.AlgebraicGeometry.QuasiCompactImmersionAffineDescent (11.3 s), with no
errors or unexpected warnings. The prescribed deliver2.py dry run performs the
final server preflight and per-file compile.

## Second reading by Q98

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
