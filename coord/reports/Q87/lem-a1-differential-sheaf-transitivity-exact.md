## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeDifferentialsTransitivityExact` states
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials_transitivity_exact` with one
whole-proof `sorry`. It introduces no definitions or auxiliary theorems, and changes
only the item's `lean` record. No statement correction or disputed statement.

The sources read were Stacks `morphisms.tex`, `lemma-triangle-differentials` (01UX),
`lemma-functoriality-differentials` (01UV), and the restriction and affine descriptions
01US/01UT, alongside the latest blueprint's `lem-a1-finite-map-curve.proof.md`, third
paragraph. The existing differential sheaf and first-arrow interfaces are usable.

Hypothesis and clause correspondence, in signature order:

- Arbitrary schemes and composable morphisms: `{X Y S : Scheme.{u}}`, `(h : X ⟶ Y)`
  and `(g : Y ⟶ S)`. There are no smoothness, flatness, finite-presentation,
  separatedness or nonemptiness binders.
- Relative sheaves and tensor pullback: `g.relativeDifferentials`,
  `(h ≫ g).relativeDifferentials`, `h.relativeDifferentials` and
  `(Modules.tensorPullback h).obj g.relativeDifferentials` are the recorded objects.
- Canonical first arrow and its local characterization: the theorem uses exactly
  `g.relativeDifferentialsPullbackMap h`, whose defining unique-existence theorem
  fixes its value on `relativeDifferentialsPullbackGenerator g h V b` to
  `d(h.app V b)`. The generator is the actual sheafified tensor `1 ⊗ db`.
- Canonical second arrow: existential `q`, with `∀ O a, q.app O (d a) = d a`.
  This determines q because differentials generate locally; no arbitrary map is
  assumed. Existence is part of the statement.
- Right exactness of the displayed sheaf sequence: an existential zero-composite
  witness `z`, `(ShortComplex.mk ... q z).Exact`, and `Epi q`.
- Exactness on every stalk and the terminal zero: `∀ x : X, Function.Exact`
  of the two maps under `RingedSpace.moduleStalkFunctor X.toRingedSpace x`,
  together with `Function.Surjective` of the second stalk map.
- Every affine triple: `U : X.affineOpens`, `V : Y.affineOpens`,
  `W : S.affineOpens`, `hUV : U.1 ≤ h ⁻¹ᵁ V.1` and
  `hVW : V.1 ≤ g ⁻¹ᵁ W.1`. The section rings are A = Γ(X,U), B = Γ(Y,V),
  R = Γ(S,W); the ring maps are the corresponding `appLE` maps.
- Affine identification of the first term: the existential sheaf isomorphism θ
  has target `tilde ((ModuleCat.extendScalars (h.appLE ...).hom).obj
  (CommRingCat.KaehlerDifferential (g.appLE ...)))`, namely
  the sheaf of A ⊗_B Ω(B/R).
- Normalization `db ↦ 1 ⊗ db`: the first θ condition pulls back the actual
  `relativeDifferentialsPullbackGenerator`, restricts it to U, transports it to
  the Spec chart by `sectionsRestrictFromSpecLinearEquiv.symm`, and equates its
  θ-image to `tilde.toOpen` of the scalar-extension unit applied to db.
  Mathlib's `extendRestrictScalarsAdj_unit_app_apply` identifies that unit with
  `1 ⊗ db`.
- Middle and last affine comparisons are precisely
  `(h ≫ g).relativeDifferentialsRestrictFromSpecIso W.2 U.2 ...` and
  `h.relativeDifferentialsRestrictFromSpecIso V.2 U.2 hUV`.
- The algebraic sequence is given by existential A-module maps uA and vA.
  Their required formulas are `uA (a • (1 ⊗ db)) = a • d(h.appLE ... b)`
  and `vA (da) = da`; there is also `Function.Exact uA vA` and
  `Function.Surjective vA`. The `@id` in the first formula merely views the
  scalar-extension unit element in its extended A-module before scalar action.
  These generators determine both linear maps uniquely.
- The two following sheaf morphism equalities are the commutative affine
  comparison squares, identifying the restricted first and second arrows with
  `(tilde.functor A).map uA` and `(tilde.functor A).map vA`.
- Agreement under principal localization is encoded by these being isomorphisms
  and equalities of sheaf morphisms, rather than isolated global-section
  bijections. In particular they commute with restriction to every principal
  open and every inclusion between such opens. `tilde.toOpen_res` and its
  `IsLocalizedModule.Away` instance identify these restrictions with the
  canonical module localizations; the existing relative-differential affine
  comparisons use the canonical derivations. The normalization fixes θ on
  generators, hence fixes all its localized maps as well.
- Every source open: `∀ O : X.Opens` gives an isomorphism e from the restricted
  first term to the actual tensor pullback along `O.ι ≫ h`, normalized on all
  pulled-back local differential sections, and a map qO. The first diagram
  identifies the restricted first arrow with the canonical first arrow on O;
  `relativeDifferentialsCongr` only adjusts associativity of composition.
  The second diagram identifies the restricted q with qO. Its local formula
  `qO (da) = da`, zero composite, `ShortComplex.Exact`, and `Epi qO` state the
  same canonical right exact sequence on O, without additional hypotheses.
  Since every open is included, the clause includes all principal refinements
  of the affine comparisons and identity/empty source opens.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`, `relativeDifferentialsDerivation`,
  `relativeDifferentialsRestrictFromSpecIso`, `relativeDifferentialsRestrictIso`
  and `relativeDifferentialsCongr`. Their full definitions/docstrings were read.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullbackSection` and the normalized adjunction;
  its public import retains upstream `Scheme.Modules.tensorPullback`.
- `Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap`:
  `Scheme.Hom.relativeDifferentialsPullbackGenerator`,
  `existsUnique_relativeDifferentialsPullbackMap`, `relativeDifferentialsPullbackMap`.
- `WeilConjectures.AlgebraicGeometry.ModulePullbackAffineChartUnit`:
  `Scheme.Modules.affineChart_pullback_unit`, and the imported
  `sectionsRestrictFromSpecLinearEquiv` used in the affine normalization.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackTilde`:
  `Scheme.Modules.exists_tensorPullback_tilde_iso` (proof import).
- `WeilConjectures.Algebra.Homology.ModuleStalkExact`:
  `RingedSpace.module_stalk_exact` and the public `moduleStalkFunctor`.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, its universal
  derivation, `exact_mapBaseChange_map`, `map_surjective`, and `mapBaseChange_tmul`.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `tilde`, `tilde.toOpen`,
  `tilde.toOpen_res`, and `tilde.toStalk` with its localization instance.
- `Mathlib.RingTheory.Etale.Kaehler`: `KaehlerDifferential.isLocalizedModule_map`
  (proof import). Mathlib-match dependencies have no new node records.

Searches (2026-10-24):

- msearch LeanFinder: “For scheme morphisms X to Y to S the canonical sequence
  of relative Kahler differential sheaves is right exact and compatible with
  affine charts and open restriction”. Eight hits; `exact_mapBaseChange_map`
  is the algebraic theorem, and the other hits are cotangent or presheaf maps.
  None states the full sheaf comparison and restriction result.
- msearch Loogle: `KaehlerDifferential.map, Function.Exact`. One hit,
  `KaehlerDifferential.exact_mapBaseChange_map`, algebraic exactness only.
- msearch grep: `relativeDifferentials.*exact|exact.*relativeDifferentials|exact_mapBaseChange_map`.
  Four hits, all algebraic or references to the algebraic theorem.
- msearch LeanSearch: “Right exact sequence of relative Kahler differential
  sheaves on schemes compatible with affine opens and restriction”. Eight hits,
  including the presheaf construction, algebraic exactness and localization;
  no full scheme theorem. The wrapper's verbatim search records are in
  sandbox `searches.jsonl`.
- rg in both `lean/WeilConjectures` and `lean/Sheaf`:
  `relativeDifferentials.*[Ee]xact|[Ee]xact.*relativeDifferentials|lem-a1-differential-sheaf-transitivity-exact`.
  Only proof-body lines and unrelated degree/invertibility statements; no
  transitivity sequence theorem. Explicit item-id and proposed full-name
  searches also found no existing declaration. Existing notions are reused.

Edge cases read against the source and signature:

- Empty X and empty affine/source opens are allowed. All stalk assertions are
  universal, and no inhabitedness or nonzero-ring assumptions are introduced.
- h = identity: the final differential sheaf vanishes; the sequence has the
  expected quotient to zero. g = identity: its first term vanishes and q is
  the canonical identification of the remaining differential sheaves.
- Closed immersions and positive-characteristic Frobenius show why no injectivity
  of the first arrow is claimed. The exactness and surjectivity clauses retain
  these cases; there are no smoothness or flatness assumptions.
- O = top and O = bottom are retained in the open-restriction clause, including
  its actual pullback-generator formula and composition associativity transport.
- Affine triples need no affine intersection assumption; all comparisons are
  sheaf morphisms and hence permit principal refinements.

Validation: scompile.py checked the sandbox module and the intended library
module independently, with the 60-second per-file limit. Both succeeded with no
errors or unexpected warnings. The first compile diagnosed an A-scalar action
on the B-restricted scalar-extension unit; the explicit `@id` target fixed that
without changing any mathematical objects or hypotheses.

## Second reading by Q87

Performed as a separate rereading pass by this worker; the dispatcher explicitly
forbids starting other agents, so this is not represented as an independent
worker review. The maintainer's independent review remains the next review.

Reopened the unchanged node and final Lean signature. The two scheme maps and
all three differential sheaves match. The first arrow is the recorded canonical
one; the existential second arrow is fixed by its formula on every local da.
Sheaf exactness, Epi q, and the stalk exactness/surjectivity render the terminal
zero without accidentally claiming a monomorphism on the left. The affine θ
condition retains the actual tensor generator, its chart transport, and its
unit normalization. The uA and vA formulas and two commuting diagrams give the
associated algebraic sequence, with no arbitrary identification of arrows.
Because these are sheaf diagrams, restrictions to principal opens commute and
are the localization maps of the recorded tilde/differential constructions.
The universal source-open clause retains both arrow diagrams, normalization of
e on generators, the formula for qO, and its right exactness. No clause, edge
case, or extra finiteness hypothesis was found missing. No statement edits
were made in this rereading. No new or dependency modules are needed.
