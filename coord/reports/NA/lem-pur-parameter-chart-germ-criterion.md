## Worker report

The module `Sheaf.AlgebraicGeometry.ParameterChartGermCriterion` states
`AlgebraicGeometry.flat_quasiFinite_parameterChart_iff`, with `sorry` and no new
construction or proof. The original node is unchanged except for its `lean` record.
No new nodes, dependency modules, statement corrections, or disputed statements.
There is no maintenance repair note for this item in `coord/repair-notes/`.

Source checked: the local PDF `literature/sga/SGA4-expose-18_reedition.pdf`, XVIII
Lemma 2.6, printed p. 552, first proof paragraph. It identifies flat quasi-finite
map germs sending x to zero with systems of parameters and treats other values by
coordinate translations. The theorem retains the prescribed representatives.
Its docstring gives all nine steps of the node's proof, including the affine
localization, evaluation fibre, radical criterion, both implications, flat-locus
shrinking, and final affine neighbourhood.

Hypothesis and clause correspondence:

- Algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- Finite-type k-scheme X: `(X : Scheme.{u})`,
  `[X.Over (Spec (CommRingCat.of k))]`, and the two instances
  `[LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]` and
  `[QuasiCompact (X ↘ Spec (CommRingCat.of k))]`. There is no separatedness,
  smoothness, reducedness, pure-dimension, or global Cohen--Macaulay assumption.
- Closed point: `(x : X) (hx : x ∈ closedPoints X)`.
- Local ring R: Mathlib's `X.presheaf.stalk x`, the actual structure-sheaf stalk.
  No replacement ring is introduced. Its maximal ideal is
  `IsLocalRing.maximalIdeal (X.presheaf.stalk x)`.
- Noetherian local ring: `[IsNoetherianRing (X.presheaf.stalk x)]` explicitly
  records the node's assertion. The local-ring structure is Mathlib's scheme
  stalk instance.
- Cohen--Macaulay condition: `hCM` is the equality of the recorded
  `IsLocalRing.depth` (cast into `WithBot ℕ∞`) and `ringKrullDim`. It is at x
  only; no additional dimension value is assumed.
- Identification of κ(x) with k via the structure map: `e : X.residueField x ≃+* k`
  with `he`. The equation in `he` says that evaluation at x of the global
  constant c, pulled back along the structure morphism and through
  `Scheme.ΓSpecIso`, is sent to c. Thus e is the inverse of the structural
  embedding, rather than an arbitrary field automorphism. This is the explicit
  identification the node instructs us to make, not a new restriction on X.
  At a closed point of a finite-type scheme over an algebraically closed field,
  that structural embedding is an isomorphism. The equation determines e on
  all residue-field elements.
- Nonnegative number of coordinates: `(d : ℕ)`. Coordinates are indexed by
  `ULift.{u} (Fin d)`, as in the recorded affine-space match; this keeps the
  coordinate type in the scheme universe and includes d = 0.
- Prescribed open neighbourhood and representatives:
  `(V : X.Opens) (hxV : x ∈ V)` and `s : ULift.{u} (Fin d) → Γ(X, V)`.
- Coordinate map f: the binder `f` is fixed by `hf` to exactly
  `AffineSpace.homOfVector (V.ι ≫ X ↘ Spec (CommRingCat.of k))
  (fun i ↦ V.topIso.inv (s i))`. The canonical `V.topIso` converts the given
  sections to global sections of the open subscheme. This is a defining
  equation for the prescribed map, not an arbitrary replacement chart.
- Coordinate values a_i: `a` with `ha : ∀ i, a i = e (X.evaluation V x hxV (s i))`.
- Centered germs t_i: `t` with `ht` equal to the germ of s_i minus the germ of
  the global structural constant a_i. Thus constants are lifted through the
  structure map; there is no arbitrary residue-field section. The first
  conclusion asserts `∀ i, t i ∈ IsLocalRing.maximalIdeal ...`, matching the
  node's explicit membership assertion.
- Generated ideal: `I` with `hI : I = Ideal.span (Set.range t)`. Together with
  `hf`, `ha`, and `ht`, these equation binders merely name the objects that
  the node defines; they neither alter nor add mathematical conditions.
- Clause (i): an existential `(U : X.Opens) (_hxU : x ∈ U) (hUV : U ≤ V)`
  with `(X.homOfLE hUV ≫ f).IsQuasiFinite ∧ Flat (X.homOfLE hUV ≫ f)`.
  `X.homOfLE hUV` is the canonical open-subscheme inclusion, so this is
  restriction of the original f, with no change of germs or values.
- Clause (ii): `ringKrullDim (X.presheaf.stalk x) = (d : WithBot ℕ∞) ∧
  I.radical = IsLocalRing.maximalIdeal (X.presheaf.stalk x)`.
  The second conclusion is exactly the equivalence (i) iff (ii).
- Affine-neighbourhood clause: the third conclusion repeats this equivalence
  with `IsAffineOpen U` inside the neighbourhood existential. It neither
  assumes that V is affine nor replaces the originally prescribed sections.
- Quotient reformulation: the final equivalence retains `dim R = d` on both
  sides and replaces the radical condition with
  `Nontrivial (R ⧸ I) ∧ ringKrullDim (R ⧸ I) = 0`. Thus both the nonzero
  requirement and the dimension of the ambient local ring are retained.
- The phrase “system of parameters” is rendered by the node's explicit
  dimension/radical formula, using `Ideal.span`, rather than introducing a
  second abstract parameter predicate.

The theorem uses equation binders instead of statement-local `let`s, in accordance
with the stage-2 convention. Each defining equation has a canonical solution;
in particular, `hf` rules out replacing the map by an arbitrary flat chart.

Dependency declarations inspected and used:

- `def-weil-algebraic-closure`: `IsAlgClosed` in
  `Mathlib.FieldTheory.IsAlgClosed.Basic` (the matching record explicitly names
  this algebraically-closed-field notion in addition to `AlgebraicClosure`).
- `def-pc-scheme`: `Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType` and `QuasiCompact`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`.
- `def-weil-closed-points`: `closedPoints`, `Mathlib.Topology.JacobsonSpace`.
- `def-weil-pbc-module-stalk`: imported
  `Sheaf.Topology.PresheafModuleStalkFunctor`; the statement needs the ring
  stalk and germs, which that node records as Mathlib's `TopCat.Presheaf.stalk`
  and germ maps, rather than a module-valued stalk functor. The full source of
  the recorded `PresheafOfModules.moduleStalkFunctor` was read; it does not
  define a second ring stalk, and none is introduced here.
- `def-weil-residue-field`: `Scheme.residueField` and `Scheme.evaluation`,
  `Mathlib.AlgebraicGeometry.ResidueField`. Its source explicitly defines
  evaluation as germ followed by residue.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`.
- `def-weil-pbc-depth`: `IsLocalRing.depth` and `Ideal.depth`,
  `Sheaf.RingTheory.Depth`.
- `def-weil-pbc-krull-dimension-ring`: `ringKrullDim`,
  `Mathlib.RingTheory.KrullDimension.Basic`.
- `def-sbc-affine-space`: `AffineSpace` with `ULift (Fin d)`, and its canonical
  `AffineSpace.homOfVector`, `Mathlib.AlgebraicGeometry.AffineSpace`.
- `pqf-def-quasifinite`: `Scheme.Hom.IsQuasiFinite`,
  `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`, including finite type and
  isolated fibre points, not Mathlib's weaker local quasi-finiteness predicate.
- `def-weil-flat-morphism`: `Flat`, `Mathlib.AlgebraicGeometry.Morphisms.Flat`.

Recorded proof-dependency modules that have statements are imported without
`public`, including polynomial maximal-localization dimension, the ring
quasi-finite/fibre-dimension criterion, closed-point dimension, isolation and
its converse for affine pairs, miracle flatness, the published Noetherian
flat-locus theorem, and openness of the quasi-finite locus. Relevant existing
Mathlib algebra tools are also imported. No downstream consumer is imported.

Edge cases checked before writing:

- d = 0: the index type is empty, the span is zero, affine zero-space is the
  base, and the criterion says exactly dim R = 0. No positivity hypothesis.
- A nonreduced Artinian local example, such as k[ε]/(ε²), satisfies the
  zero-dimensional criterion: no reducedness or regular-local-ring hypothesis
  has been substituted for Cohen--Macaulayness.
- Constant coordinates on a positive-dimensional local scheme generate zero
  after centering, so the radical condition fails as required.
- On the affine line, the coordinate T² at zero remains a parameter although
  it need not generate the maximal ideal. The conclusion uses radical I = m,
  not I = m or a regular system of parameters.
- In positive characteristic, T ↦ T^p is finite flat and fits the criterion;
  no separability or étaleness condition has been added.
- The empty scheme supplies no x; every neighbourhood existential explicitly
  contains x. The local quotient is required to be nonzero.
- V need not be affine or the whole scheme, and only the local ring at x
  is assumed Cohen--Macaulay. All shrinkings remain inside the given V.

Searches for an existing statement (2026-10-16):

- `msearch.py leansearch`, query “flat quasi finite chart iff parameters Cohen
  Macaulay local ring”: 8 hits, including `Algebra.QuasiFinite.mk`,
  `RingHom.QuasiFinite`, `Algebra.QuasiFiniteAt`, and `Flat.mk`; none states
  the prescribed-coordinate criterion.
- `msearch.py leanfinder`, query “A prescribed tuple of functions at a closed
  point of a Cohen Macaulay finite type scheme is a system of parameters if
  and only if its affine space morphism is flat quasi finite on a neighbourhood”:
  8 hits on smoothness, standard smoothness, and étale loci; no exact match.
- `msearch.py loogle`, query `AffineSpace.homOfVector, ringKrullDim, Flat`:
  no hits, with unknown identifier `AffineSpace.homOfVector` in that search
  index. The declaration itself was located and read in the Mathlib source.
- `msearch.py grep`, query
  `parameter.*chart|systemOfParameters|SystemOfParameters|germ.*criterion`:
  zero Mathlib hits.
- Direct `rg` with that pattern and the item id in the upstream
  `WeilConjectures/`, `dag/lean_names_upstream.json`, and project `lean/Sheaf/`:
  no exact theorem. Existing `IsLocalRing.IsRegularSystemOfParameters` belongs
  to regular systems, a different condition. `FlatCoordinateChain` is a
  downstream theorem using this germ criterion, not a duplicate statement.
- Read the full `AffineSpace.homOfVector` signature/docstring and `Opens.topIso`
  to use the canonical chart, and `Scheme.evaluation` to render its values.

Validation: the initial module passed `scompile.py` locally in both sandbox and
library contexts (2.2 s and 2.4 s), without errors or warnings. The final version
is recompiled by the required `deliver2.py --no-push` dry run; the dry-run result
is recorded below when complete. No global build, direct repository write, or
Git command was run by this worker.

Final validation: `deliver2.py NA lem-pur-parameter-chart-germ-criterion --no-push`
printed `OK (dry run)` for commit `4657692a44`: the final module compiles and
passes preflight except for the independent second reading, which the tool
explicitly reserves for the second reader. Nothing was pushed. A local structural
check also confirmed that only `lean` changed in the node copy, no Lean line
exceeds 100 characters, and the sole postponed theorem is the item's theorem.

## Second reading by NA

I independently read the repository node, the complete sandbox module, and the
source passage in SGA 4 XVIII 2.6 (printed p. 552; PDF page 53). The paragraph
identifies germs sending x to zero with parameter systems and then translates
coordinates for arbitrary values. I also read Stacks algebra.tex
`lemma-CM-over-regular-flat` (00R4), `theorem-openness-flatness` (00RC), and
morphisms.tex `lemma-quasi-finite-at-point-characterize` (01TH) and
`lemma-quasi-finite-points-open` (01TI), including their hypotheses. The local
Cohen--Macaulay assumption in this node suffices for the displayed local-ring
argument; no global Cohen--Macaulay, separatedness, smoothness, reducedness,
perfectness, or characteristic assumption is needed or added. No repair note
exists for this item.

My object/hypothesis/conclusion checklist and its Lean correspondence:

1. Algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
   Checked the dependency's algebraically closed notion (not its algebraic
   closure construction) against `IsAlgClosed` in Mathlib. Exact.
2. Finite-type k-scheme X: `X : Scheme.{u}`, `X.Over (Spec (.of k))`,
   `LocallyOfFiniteType` and `QuasiCompact` of its structure map. I read the
   two recorded Mathlib class signatures: this is precisely finite type,
   without an extra separatedness assumption. Exact.
3. Closed point x: `(x : X) (hx : x ∈ closedPoints X)`. Mathlib defines this
   as `IsClosed {x}`. Exact.
4. Local ring R, maximal ideal m, and Noetherianity: every occurrence of R is
   `X.presheaf.stalk x`; m is `IsLocalRing.maximalIdeal` of that same stalk.
   `[IsNoetherianRing ...]` records the node's Noetherian ring, which follows
   from finite type over k; it excludes no case here. The local ring instance
   is the scheme stalk instance. I read the module-stalk dependency's full
   source: it bundles Mathlib stalks and does not introduce a competing ring
   stalk. Exact.
5. Structural identification of the residue field with k: `e` is a ring
   equivalence and `he` makes it inverse to the structural constants map.
   `Scheme.residueField` is literally the quotient of this stalk by m;
   `evaluation` is germ followed by residue, and `Γevaluation` is its global
   specialization. The pulled-back constants in `he` are from `ΓSpecIso`.
   Consequently `e` is the prescribed identification, not an arbitrary
   automorphism of k. Such an identification exists for a closed point of a
   finite-type scheme over an algebraically closed field. Exact.
6. Cohen--Macaulay at x: `hCM` equates the recorded `IsLocalRing.depth R`
   with `ringKrullDim R`, using the inclusion from ℕ∞ to `WithBot ℕ∞`.
   I read `Ideal.depth` and `IsLocalRing.depth` in their dependency module;
   their data are actual regular-sequence suprema. Exact, with no extra
   finiteness or regularity condition.
7. Number d of coordinates: `(d : ℕ)` and `ULift.{u} (Fin d)`. This is the
   recorded affine-space coordinate convention, and includes zero. Exact.
8. Prescribed open V and sections: `V : X.Opens`, `hxV : x ∈ V`, and
   `s : ULift (Fin d) → Γ(X,V)`. No affineness of V is assumed. Exact.
9. Coordinate morphism: `f` and `hf` specify the actual
   `AffineSpace.homOfVector` of these sections. I read its full signature
   and definition, and `V.topIso : Γ(V.toScheme,⊤) ≅ Γ(X,V)`; its inverse
   has precisely the direction used here. Exact.
10. Values a and centered germs t: `ha` uses `e (X.evaluation ... (s i))`;
    `ht` subtracts the germ of the structural constant `a i` from the germ
    of `s i`. These equations uniquely name the objects the node defines;
    they do not ask for arbitrary lifts or alter any representative. Exact.
11. Generated ideal: `hI : I = Ideal.span (Set.range t)`. Exact.
12. The assertion that the centered germs lie in m is the first conjunct
    `∀ i, t i ∈ IsLocalRing.maximalIdeal ...`. It is concluded, not assumed.
    Exact.
13. Clause (i): `∃ U, ∃ _hxU : x ∈ U, ∃ hUV : U ≤ V, ...`, with
    `(X.homOfLE hUV ≫ f).IsQuasiFinite ∧ Flat (...)`. I read `homOfLE`:
    it is the canonical open inclusion. I read the dependency predicate
    `Scheme.Hom.IsQuasiFinite`: it is finite type plus isolation in the
    scheme-theoretic fibres. The `Flat.iff_flat_stalkMap` signature gives
    the node's stalkwise flatness. Exact, including the order of quantifiers.
14. Clause (ii): `ringKrullDim R = (d : WithBot ℕ∞) ∧ I.radical = m`.
    The second conjunct of the theorem is precisely (i) iff (ii). Exact.
15. Affine choice: the third conjunct gives the same equivalence with
    `IsAffineOpen U` added inside the existential. This expresses that the
    neighbourhood can be chosen affine, without assuming V affine. Exact.
16. Quotient version: the last conjunct replaces the radical condition by
    `Nontrivial (R ⧸ I) ∧ ringKrullDim (R ⧸ I) = 0`, retaining `dim R = d`
    on both sides. Exact: it does not confuse an arbitrary parameter ideal
    with generators of m or a regular system of parameters.
17. Prescribed germs and values: every neighbourhood uses the restriction
    of the one f fixed by `hf`; no alternative chart is existentially chosen.
    Exact.

Edge cases: d = 0 makes the index type empty and I = 0; the criterion still
says dim R = 0. Empty X has no x and hence no missing point case. The local
ring at an actual point is nonzero; the quotient's nonzero clause also rules
out an accidental zero-ring dimension convention. Nonreduced Artinian rings
are included, e.g. dual numbers for d = 0. On the affine line, T² at zero is
a parameter even though it need not generate m; in characteristic p the
coordinate T^p remains permitted (finite flat, possibly inseparable).
Constant coordinates in positive local dimension fail the radical test.
There is no characteristic restriction. All objects use an explicitly bound
arbitrary universe u, with the finite index lifted into it; there is no
independently quantified test universe or unbound variable.

Independent H4 searches, using queries different from the first reader's:

- `msearch.py ... leansearch`: “At a closed point a tuple of local functions
  defines a finite flat map to affine space exactly when the centered
  functions generate a primary parameter ideal”. Eight hits: flat-stalk,
  finite-morphism, flat-localization and affine-space finite-presentation
  declarations; no parameter-chart criterion.
- `msearch.py ... leanfinder`: “flat quasi finite parameter chart germs
  systems parameters”. Eight hits, including `Algebra.Smooth.flat`, smooth
  local presentations and germ spreading; none states the equivalence.
- `msearch.py ... grep`: `parameter.*chart|systemOfParameters|germ.*criterion`.
  Zero Mathlib hits.
- Direct `rg` in Mathlib, upstream `WeilConjectures/`, and project
  `lean/Sheaf/` for system/parameter, centered/germ and parameter/quasi-finite
  combinations, and for the proposed declaration in the upstream name map.
  No duplicate criterion exists. The project's `IsRegularSystemOfParameters`
  is a distinct, stronger notion and cannot replace the radical condition.

There are no new nodes, dependency modules, or statement corrections in this
delivery, so H12/H13 and citer-correction audits are not applicable. I checked
the existing dependency modules and signatures rather than accepting names
alone. The sole mismatch found was the module docstring opener `/-!+#`;
I repaired it to `/-! #`. The theorem, its nine-step proof docstring and the
node's mathematical statement required no change. There is one named theorem
with proof `sorry`, no definitions or additional proofs, no private notation,
and no hollow construction. All Lean lines are at most 100 characters.
The node changes only in `lean`; `lean.statement` is verbatim the source
signature, checked independently after the repair.

Validation: required `scompile.py NA lem-pur-parameter-chart-germ-criterion
lean/Sheaf/AlgebraicGeometry/ParameterChartGermCriterion.lean` passed both
sandbox and library contexts (2.1 s and 2.3 s), with no warnings or errors.

Second-reader dry run: `deliver2.py NA
lem-pur-parameter-chart-germ-criterion --no-push` printed `OK (dry run)` at
`bae1698ca1`; preflight and compilation both passed. Delivery follows using
the prescribed wrapper.
