## Worker report

Stage 2: states Stacks Project, Varieties, Tag 0AB6,
`lemma-quasi-finite-in-codim-1`, condition (1), with one named theorem and a
`sorry` proof. No definitions, new nodes, dependency repairs, or statement
corrections are needed. The docstring carries the ten proof steps, with their
DAG dependencies. All stated proof-dependency modules are imported privately.

The previous blocker concerned a stale stage-1 assignment. Q06's reviewed split
is present on the base. This delivery does not split the item again: it supplies
its missing stage-2 Lean statement.

Hypothesis and conclusion correspondence:

- Schemes and their morphism: `{Z S : Scheme.{u}} (g : Z ⟶ S)`.
  The arbitrary explicitly bound `u` follows Mathlib's scheme category convention.
- Locally of finite type: `[LocallyOfFiniteType g]`. There is no quasi-compactness,
  properness, normality, dominance, separatedness, or global Noetherian assumption.
- Target point: `(s : S)`.
- Noetherian local ring at that point:
  `[IsNoetherianRing (S.presheaf.stalk s)]`. The stalk is the actual local ring;
  its local-ring structure is already provided by the scheme.
- Local Krull dimension at most one:
  `hdim : ringKrullDim (S.presheaf.stalk s) ≤ 1`. The dimension is Mathlib's
  `WithBot ℕ∞` supremum of prime-chain lengths, including dimension zero.
- Every irreducible component: `∀ (T : Set Z), T ∈ irreducibleComponents Z →`.
- Every generic point of that component:
  `∀ (η : Z), IsGenericPoint η T →`. This means `closure {η} = T`, without
  choosing a point or assuming the whole source is irreducible or integral.
- Algebraicity of the induced extension:
  `@Algebra.IsAlgebraic (S.residueField (g η)) (Z.residueField η) _ _
  (g.residueFieldMap η).hom.toAlgebra`. This fixes the algebra structure to the
  canonical map induced by the local stalk map. `Algebra.IsAlgebraic` says that
  every element satisfies a nonzero polynomial, exactly as expanded in the node.
  No arbitrary algebra structure, finite-degree strengthening, or hidden let is used.
- Every point over `s`: `∀ z : Z, g z = s →`.
- Quasi-finite at that point: `Scheme.Hom.IsQuasiFiniteAtPoint g z`, the recorded
  finite-type-inclusive Stacks predicate of `pqf-def-quasifinite`. This is not
  a claim of global quasi-finiteness or of finiteness of the entire fibre.

Statement-dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`; `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`; `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`; `isNoetherianRing_iff`.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`; `ringKrullDim`.
- `def-sc-generic-point`: `Mathlib.Topology.Sober`; `IsGenericPoint`, `genericPoint`, `genericPoint_spec`.
- `def-weil-irreducible-components`: `Mathlib/Topology/Irreducible.lean`; `irreducibleComponents`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`; `AlgebraicGeometry.Scheme.residueField`, `AlgebraicGeometry.Scheme.Hom.residueFieldMap`.
- `pqf-def-quasifinite`: `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`; `AlgebraicGeometry.Scheme.Hom.IsQuasiFiniteAtPoint`, `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite`, `AlgebraicGeometry.Scheme.Hom.IsQuasiFinite`, `AlgebraicGeometry.Scheme.Hom.HasFiniteFibres`.

For algebraicity, `Mathlib.RingTheory.Algebraic.Defs` supplies
`Algebra.IsAlgebraic` and `IsAlgebraic`; the latter is explicitly a nonzero
annihilating polynomial. This is the inline notion already spelled out by the
item, not a new definition. The actual declaration signatures and docstrings
were opened in the pinned Mathlib and project sources.

Edge cases checked before writing:

- Empty source: the generic hypothesis and pointwise conclusion are vacuous.
  An empty target supplies no `s`, as the natural-language statement requires.
- Dimension zero: allowed by `≤ 1`; the closed-fibre argument uses the vertical
  component case. In particular a locally finite type scheme over a field with
  all component generic fields algebraic has isolated fibre points.
- Dimension one/DVR: both horizontal and vertical components occur. The hypothesis
  quantifies all components and imposes no dominance or flatness assumption.
- Infinitely many disjoint copies of the base: the morphism is locally of finite
  type and satisfies the generic condition but need not have a finite whole
  fibre. The delivered conclusion is only quasi-finiteness at each point.
- Nonreduced schemes and reducible bases are allowed; no reducedness, integrality,
  normality, or global Noetherian condition was introduced.
- `A¹_k → Spec k` does not satisfy generic algebraicity, so the generic hypothesis
  is substantive. A blowup of a smooth surface illustrates why the local
  dimension bound cannot be omitted.

Searches actually run:

- `msearch.py ... leanfinder`, query: "A locally finite type scheme morphism with
  algebraic residue field extensions at generic points is quasi finite over a
  point with Noetherian local ring of dimension at most one". Eight hits: basic
  `LocallyQuasiFinite`, `Algebra.QuasiFiniteAt`, `Algebra.quasiFinite_iff`,
  `LocallyOfFiniteType`, and its stalk-map lemma; no exact theorem.
- `msearch.py ... loogle`, query: `"LocallyQuasiFinite", "ringKrullDim"`.
  Zero hits.
- `msearch.py ... leansearch`, query: "A locally finite type morphism of schemes
  with algebraic generic residue extensions is quasi finite over a target point
  with Noetherian local ring of dimension at most one". Eight hits: constructors,
  recursors, finite morphisms, and proper-implies-locally-finite-type; no exact theorem.
- `msearch.py ... grep`, query:
  `quasiFiniteAtPoint_of_generic_algebraic|quasi.finite.in.codim|generic.*algebraic`
  in `AlgebraicGeometry`. Zero hits.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and the upstream name index for
  `generically.finite|quasifinite.over.dimension|quasiFinite.*[Dd]imension|algebraic.*generic|generic.*algebraic`
  found related generic-finiteness and alteration material, no exact live theorem.
- Exact declaration and node-ID searches in both Lean roots found no match.
- DAG search found `lem-per-generically-finite-quasifinite-over-dimension-one`,
  an identical older node. Its record explicitly says its module was deleted
  on 2026-10-20 as unreachable. The local module is absent;
  `scompile.py --source Sheaf.AlgebraicGeometry.Morphisms.GenericallyFiniteQuasiFiniteOverDimensionOne`
  independently returned "Module source unavailable". Its stale record cannot
  supply an existing declaration. The live node therefore receives a new module,
  using the established mathematical declaration name and all existing notions.
- The example `Sheaf.CategoryTheory.CompactObject` is now withdrawn; its node
  points to `WeilConjectures.CategoryTheory.CompactObject`, which was read for
  the current module/header/docstring convention.

No statement fault or dispute was found. The local Stacks source was read in
`literature/stacks-project/varieties.tex`, lines 3187–3274: its condition (1)
is precisely this item's hypothesis and conclusion.

## Second reading by NQ

The dispatcher requires a single worker and prohibits starting other agents;
this section records a second pass by the same worker, not an independent
reader. The maintainer supplies the independent delivery review.

Reread the node and theorem together: every object is bound, `g` is locally of
finite type, Noetherianity and dimension concern only the stalk at `s`, and
algebraicity is tested for every component and each of its generic points via
`g.residueFieldMap`. The conclusion covers exactly all `z` mapping to `s` using
`IsQuasiFiniteAtPoint`. The signature has no added global assumptions and no
strengthening to finite fibres. All variables and the universe are explicit,
`autoImplicit` is disabled, the only proof is `sorry`, and no definitions were
repeated. No mismatch was found; no statement change was made.

## Validation

Server compilation and prescribed delivery preflight results are recorded below.

- `scompile.py NQ lem-sfb-generically-finite-quasifinite-over-dimension-one <module>`:
  passed in sandbox module mode (7.9 s) and library module mode (9.8 s),
  with no errors or warnings.
- `deliver2.py NQ lem-sfb-generically-finite-quasifinite-over-dimension-one --no-push`:
  `OK (dry run): commit d59ee58e736 passes the preflight and compiles; nothing pushed`.
- The signature recorded in `lean.statement` is verbatim from the theorem keyword
  up to the assignment. The node differs from the read-only repository only in
  its `lean` field. All Lean lines are at most 100 characters.
