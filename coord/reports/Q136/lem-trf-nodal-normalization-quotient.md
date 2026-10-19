## Worker report

The module `Sheaf.AlgebraicGeometry.NodalNormalizationQuotient` states
`AlgebraicGeometry.Scheme.nodal_normalization_quotient`, with a single `sorry` proof.
It introduces no new definitions. The TeX statement is unchanged.

Source read: `literature/stacks-project/varieties.tex`, Tag 0C1R,
`lemma-prepare-delta-invariant`, statement and proof (especially (2), (4), (7), (9));
`curves.tex`, Tag 0CBW, `lemma-split-node`, and Tag 0C4A,
`lemma-2-branches-delta-1`, including the split Case I calculation.
The theorem docstring carries all five steps of the node's proof, including the
axis description, total fraction ring, integral closure, scalar action on the
quotient, and the global Euler characteristic calculation.

Hypotheses, objects, and clauses matched against the node:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The scheme over that field is `(B : Scheme.{u}) [B.Over (Spec (.of k))]`.
  Its structure morphism is consistently `B ↘ Spec (.of k)`.
- Properness is `[IsProper (B ↘ Spec (.of k))]`; it includes the finite-type
  requirement via universal closedness and quasi-compactness.
- Reducedness is `[IsReduced B]`; connectedness is `[ConnectedSpace B]`,
  including nonemptiness.
- Pure dimension one is `hpure`, quantifying over every irreducible component
  `Z ∈ irreducibleComponents B`, with `topologicalKrullDim Z = 1`.
- At every nonsmooth point, `hnodal` gives `Nonempty` of a ring equivalence from
  `AdicCompletion (IsLocalRing.maximalIdeal (B.presheaf.stalk x))
  (B.presheaf.stalk x)` to `MvPowerSeries (Fin 2) k` modulo the ideal spanned
  by `X 0 * X 1`. This is an isomorphism of rings, as in the node; no extra
  scalar-compatibility condition is imposed. The node's proof explicitly treats
  the possible twist of scalars.
- `B.reducedNormalizationComponent Z` is the reduced induced closed scheme of
  the component, already proved integral by the recorded normalization module.
  `B.reducedNormalization` is exactly the coproduct of these components'
  function-field normalizations. `B.fromReducedNormalization` is the induced
  canonical map. Thus the theorem does not replace the componentwise
  normalization by the normalization of an integral curve.
- `(N : Set B) (hN : N = {x | x ∉ (B ↘ Spec (.of k)).smoothLocus})` names
  exactly the nonsmooth locus. The conclusion `N.Finite` explicitly supplies
  its finiteness. No finiteness assumption or chosen enumeration is needed.
- `IsFinite B.fromReducedNormalization` supplies finiteness of the displayed
  normalization morphism.
- `Modules.unit B` is the structure sheaf and
  `(Modules.pushforward B.fromReducedNormalization).obj
  (Modules.unit B.reducedNormalization)` is its normalization pushforward.
  Both, and the existential quotient `Q`, are asserted coherent using the
  existing `RingedSpace.IsCoherent` definition.
- The first arrow is literally `SheafOfModules.unitToPushforwardObjUnit
  B.fromReducedNormalization.toRingCatSheafHom`, whose sections are the
  structure morphism of rings. The existential `q` and its composition-zero
  witness `hq` form a `ShortComplex`; its `ShortExact` clause asserts
  injectivity, middle exactness, and surjectivity. No arbitrary first arrow
  and no merely additive sheaf sequence is substituted.
- The existential family `i : N → (Spec (.of k) ⟶ B)` spells out the inclusions
  denoted `i_x` in the node. Each is a closed immersion, has singleton image
  `{x.val}`, and satisfies `i x ≫ (B ↘ Spec (.of k)) = 𝟙 _`. These identify the
  structural closed k-point inclusion: a point with structural residue field
  k has exactly this map over k. These are conclusion witnesses, not extra
  hypotheses or an arbitrary uncharacterized family of maps.
- The quotient description is `Nonempty (Q ≅ ∐ (fun x : N ↦
  (Modules.pushforward (i x)).obj (Modules.unit (Spec (.of k)))))`.
  The category is `B.Modules`. Its coproduct is the sheaf direct sum, and
  the structure sheaf on `Spec k` is precisely the module k in `i_{x,*}k`.
- The support clause is `{x | ¬ Subsingleton (Q.presheaf.stalk x)} ⊆ N`.
  It renders "supported on N" without strengthening it to equality.
- The numeric clause is `Q.eulerChar k = (N.ncard : ℤ)`. Here `N.ncard`
  renders e = |N|; the existing Euler characteristic is used, with the
  structural k-action determined by the displayed `B.Over` instance.

Dependency declarations read and used:

- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (the algebraically
  closed clause of `def-weil-algebraic-closure`).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`,
  imported through the normalization/scheme modules.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, inherited through
  scheme properties.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`
  with its commutative ring structure.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries` and its variables.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`:
  `AlgebraicGeometry.Scheme.normalization`, `Scheme.fromNormalization`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`:
  `AlgebraicGeometry.Scheme.Modules.eulerChar`.
- Added the already-landed `def-weil-pbc-reduced-normalization` to
  `stmt_deps`, as authorized by brief-stage2 §5. Its module
  `Sheaf.AlgebraicGeometry.ReducedNormalization` supplies
  `Scheme.reducedNormalizationComponent`, `Scheme.reducedNormalization`,
  and `Scheme.fromReducedNormalization`. The current published source was
  also read with `scompile.py --source` and agrees with the shared source.
- `Sheaf.AlgebraicGeometry.Coherent`: `RingedSpace.IsCoherent`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`: `Modules.unit`;
  Mathlib's `Modules.pushforward` and `SheafOfModules.unitToPushforwardObjUnit`
  give the canonical sheaf construction and map.
- The stated proof dependencies are imported privately:
  `Sheaf.RingTheory.PowerSeriesNormalDomain` (`PowerSeries.noetherian_normal_domain`)
  and `Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport`
  (`Scheme.Modules.eulerChar_zero_dim_support`). Their source signatures
  and docstrings were read. `lem-trf-normalization-singular-skyscraper` has
  no recorded Lean module in the shared node; its statement and proof role
  were read, and it is named in the proof docstring rather than imported
  from a nonexistent module.

Edge cases checked:

- Empty N: the direct sum is initial/zero; the theorem states a zero quotient
  and Euler characteristic zero. Smooth proper curves are included.
- Empty B: excluded exactly by the node's connectedness convention, since
  `ConnectedSpace` includes nonemptiness. No additional nonempty condition
  is silently assumed on N.
- A self-node on one irreducible component and a crossing of two components
  each contribute one summand; the index is the set of singular points,
  not the set of branches or pairs of components.
- Characteristic two is allowed. The argument uses the product uv, the
  idempotent, and the difference of constants, with no division by two.
- No branch order is fixed, and no canonical isomorphism Q with the direct
  sum is claimed; only existence is required.
- All universes and variables are explicitly bound; no auto-bound implicit
  or file-local notation/instance is used.

Searches performed (through the prescribed msearch wrapper where applicable):

- LeanFinder, `normalization quotient at split nodes exact sequence coherent sheaves`:
  eight generic normalization-map/diagram declarations, no nodal sheaf sequence.
- Loogle, `AdicCompletion, MvPowerSeries`: ten hits on the power-series/completion
  equivalence for polynomial algebras, no normalization quotient theorem.
- Mathlib grep, `normalization.*quotient`, subdirectory `AlgebraicGeometry`:
  zero hits.
- LeanSearch, `normalization exact sequence split nodal curve quotient skyscraper residue field`:
  eight hits on residue fields and generic normalization declarations, no exact match.
- Direct rg in Mathlib's `AlgebraicGeometry`, upstream `WeilConjectures/AlgebraicGeometry`,
  and `lean/Sheaf/AlgebraicGeometry`, query
  `nodal_normalization_quotient|normalization.*quotient|quotient.*normalization`:
  no theorem for this node; shared hits concern unrelated derived or scalar
  normalization comparisons.
- Direct rg for `lem-trf-nodal-normalization-quotient` throughout upstream
  `WeilConjectures` and the upstream name table: no existing declaration.
- Searches for `reducedNormalization`, `fromReducedNormalization`, and
  `nodal|Nodal|pureDim|PureDim` located the already-landed componentwise
  normalization and existing pure-dimensional/nodal interfaces. No notion
  has been copied or redefined.

No statement dispute or source fault was found. The module compiled cleanly
through the required `scompile.py` wrapper (sandbox and library-form checks,
2.2 seconds each). An initial compile identified missing public visibility
for `Modules.unit`; the explicit public import of the owning upstream module
fixed it. No errors or warnings remain.

## Second reading by Q136

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
