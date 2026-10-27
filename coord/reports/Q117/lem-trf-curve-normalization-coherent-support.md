## Worker report

Stage 2 delivery of `lem-trf-curve-normalization-coherent-support` by Q117.
The accepted Q146 stage-1 split is preserved verbatim. The node has no Lean
attachment on the live read clone, and coord/queue.tsv lists it in stage 2.
The explicit stage handoff in coord/brief-stage2.md §0 supersedes the inherited
stage-1 refusal: recording the statement does not reopen the reviewed split.
This packet repairs the maintainer return on immutable head d905fd29af05;
the correction is recorded below under "## Returned-delivery repair".

The module `Sheaf.AlgebraicGeometry.CurveNormalizationCoherentSupport` states
`AlgebraicGeometry.Scheme.curve_normalization_coherent_support`, with one `sorry`.
Its six-step docstring carries the accepted proof and its dependency names.
All five helper declarations are real constructions belonging to the same
normalization-quotient notion. No independent new notion or node is added.

The helpers are, in namespace `AlgebraicGeometry.Scheme`:

- `normalizationCoherentPushforward`: the existing `Modules.pushforward` of the
  structure module of `X.reducedNormalization`.
- `normalizationCoherentMap`: the existing canonical
  `SheafOfModules.unitToPushforwardObjUnit` for `X.fromReducedNormalization`.
- `normalizationCoherentQuotient`: the categorical `cokernel` of that map.
- `normalizationNormalLocus`: the set where the local ring satisfies
  `IsDomain` and `IsIntegrallyClosed`.
- `normalizationCoherentStalkQuotient`: the quotient of the actual direct-image
  module stalk by the range of the canonical structure-module stalk map.
  The structure-module stalk is the underlying module of the local ring A_x;
  the direct-image module stalk is the underlying A_x-module of C_x.
  Thus this is C_x/A_x, using the canonical scalar action and inclusion.

Hypotheses and clauses, matched individually to the Lean statement:

| Node | Lean |
| --- | --- |
| algebraically closed field k | `(k : Type u) [Field k] [IsAlgClosed k]` |
| k-scheme X | `(X : Scheme.{u}) [X.Over (Spec (.of k))]` |
| reduced | `[IsReduced X]` |
| finite type over k | `LocallyOfFiniteType` and `QuasiCompact` on `X ↘ Spec (.of k)` |
| every component has dimension one | `hpure`, quantifying over all `Z ∈ irreducibleComponents X`, with `topologicalKrullDim Z = 1` |
| componentwise normalization ν | the recorded `X.reducedNormalization` and `X.fromReducedNormalization` |
| A_x, C_x and N | `X.presheaf.stalk x`, the module stalk of `normalizationCoherentPushforward X`, and `normalizationNormalLocus X` |
| canonical injection and 0 → O_X → ν_*O → Q → 0 | `ShortExact` of `ShortComplex.mk (normalizationCoherentMap X) (cokernel.π ...) (cokernel.condition ...)`; this includes monicity, exactness and epimorphic last map |
| Q is the sheaf cokernel | definition of `normalizationCoherentQuotient X`, rather than an unconstrained existential sheaf |
| all three modules coherent | the three successive `RingedSpace.IsCoherent X.toRingedSpace ...` conjuncts |
| canonical Q_x = C_x/A_x for every x | `∃ e : normalizationCoherentStalkQuotient X x ≃ₗ[X.presheaf.stalk x] ...`; its equation on EVERY representative b says `e [b] = q_x b`. This determines e uniquely by surjectivity of the quotient projection |
| finite as A_x-module | `Module.Finite (X.presheaf.stalk x)` on Q_x |
| Q_x = 0 iff x ∈ N | `Subsingleton Q_x ↔ x ∈ normalizationNormalLocus X`; zero underlying module means subsingleton, not `IsZero` on a bare Type |
| N open and dense | `IsOpen (normalizationNormalLocus X) ∧ Dense (...)` |
| N exactly the smooth locus | for every x, membership iff `∃ U : X.Opens, x ∈ U ∧ Smooth (U.ι ≫ ...)`, the project convention for smoothness at a point |
| support equals X minus N | equality of `{x | ¬ Subsingleton Q_x}` with `(normalizationNormalLocus X)ᶜ` |
| support finite | `((normalizationNormalLocus X)ᶜ).Finite` together with that equality |
| every support point closed | `∀ x, x ∉ normalizationNormalLocus X → IsClosed ({x} : Set X)` |
| no component generic point in support | every `IsGenericPoint x Z` for an irreducible component Z belongs to N |
| every closed-point A_x is reduced | `_root_.IsReduced (X.presheaf.stalk x)` under `IsClosed {x}` |
| Noetherian | `IsNoetherianRing (X.presheaf.stalk x)` |
| Krull dimension one | `ringKrullDim (X.presheaf.stalk x) = 1` |
| essentially finite type over k | `RingHom.EssFiniteType` for the composite k → Γ(Spec k,⊤) → Γ(X,⊤) → A_x, using `ΓSpecIso.inv`, `appTop` and the germ at x |
| structural k → κ(x) an isomorphism | `∃ e : X.residueField x ≅ CommRingCat.of k`, with `Spec.map e.inv = X.fromSpecResidueField x ≫ ...`. By faithfulness of Spec this pins the inverse of e to the actual structural ring map |
| empty scheme allowed, Q = 0, support empty | no nonemptiness assumption anywhere; final conjunct `IsEmpty X → IsZero Q ∧ {x | ¬ Subsingleton Q_x} = ∅` |

Every universe and binder is explicit, with both autoImplicit options false.
The only common universe comes from the scheme morphism to Spec k and imposes
no extra size equality on a site. There are no let-bindings, private helpers,
local instances, hidden data choices, proofs besides `sorry`, or new axioms.

Statement dependencies read and used:

- def-weil-algebraic-closure: Mathlib.FieldTheory.IsAlgClosed.Basic, `IsAlgClosed`.
- def-pc-reduced-scheme: Mathlib.AlgebraicGeometry.Properties,
  `AlgebraicGeometry.IsReduced` (sectionwise definition and stalk instance).
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  `AlgebraicGeometry.LocallyOfFiniteType`, and Morphisms.QuasiCompact,
  `AlgebraicGeometry.QuasiCompact`.
- def-weil-irreducible-components: Mathlib.Topology.Irreducible,
  `irreducibleComponents`, maximal irreducible subsets.
- def-kun-topological-krull-dimension: Mathlib.Topology.KrullDimension,
  `topologicalKrullDim`, the chain-length dimension in `WithBot ℕ∞`.
- def-weil-pbc-reduced-normalization:
  Sheaf.AlgebraicGeometry.ReducedNormalization,
  `AlgebraicGeometry.Scheme.reducedNormalization`,
  `AlgebraicGeometry.Scheme.fromReducedNormalization`.
- def-weil-pbc-normal-ring: Mathlib.RingTheory.IntegralClosure.IntegrallyClosed,
  `IsDomain` and `IsIntegrallyClosed` inline, as prescribed by its record.
- pqf-def-coherent: WeilConjectures.AlgebraicGeometry.Coherent,
  `AlgebraicGeometry.RingedSpace.IsCoherent` for clause 3 (item lean.note below;
  the live Q25 dependency record is preserved).
- def-sbc-smooth-morphisms: Mathlib.AlgebraicGeometry.Morphisms.Smooth,
  `AlgebraicGeometry.Smooth` on the indicated open-neighbourhood composite.
- def-weil-pbc-essentially-finite-type-algebra:
  Mathlib.RingTheory.EssentialFiniteness,
  `RingHom.EssFiniteType` (the ring-map spelling of `Algebra.EssFiniteType`).

The public module-stalk interface is
WeilConjectures.Algebra.Homology.ModuleStalkFunctor,
`AlgebraicGeometry.RingedSpace.moduleStalkFunctor`.
The map comes from Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree,
`SheafOfModules.unitToPushforwardObjUnit`; its section formula is the original
ringed-space structure map, with no arbitrary adjunction choice.

Plain proof imports include every currently recorded proof-dependency module:
CoherentFiniteTypeLocallyNoetherian, FinitePushforwardCoherent,
CoherentKernelCokernelLocallyNoetherian, ModuleStalkExact,
EquidimensionalOpenLocalDimension, ClosedPointDimensionLocalRing,
Mathlib/RingTheory/Nullstellensatz, RegularLocalDimOneIffNormal,
Sheaf/AlgebraicGeometry/IsRegularScheme, AlgebraicGeometry/Regular,
Sheaf/AlgebraicGeometry/RegularNormalDecomposition, and
Mathlib/Topology/KrullDimension, under their recorded WeilConjectures or Sheaf
prefixes. Mathlib's KrullDimension.Zero provides the minimal-prime field leaf.
Mathlib Noetherian and scheme-sobriety leaves are already imported transitively.
The proof-only node `lem-trf-normalization-affine-stalk-closure` has no recorded
Lean statement yet; there is no module to import. No import of the downstream
`NormalizationSingularSkyscraper` is used and no dependency cycle is introduced.

Edge cases checked before writing and again against the final signature:
empty X (vacuous purity, empty normal locus dense in the empty space, zero Q),
a smooth curve or disjoint smooth curves (Q zero, N all of X), a nodal reducible
curve (normalization stalk has multiple branches and quotient nonzero at their
intersection), a cuspidal integral curve (one branch but nonnormal local ring),
generic points (field stalks, zero quotient), and a nonseparated curve such as
the doubled-origin line (no separated or proper hypothesis is added).
Dimension-zero components are correctly excluded by hpure; the empty scheme
is not excluded. No characteristic restriction is introduced.

Sources opened: literature/stacks-project/varieties.tex,
`lemma-prepare-delta-invariant` (Tag 0C1R, statement and proof) and
`lemma-dense-smooth-open-variety-over-perfect-field` (Tag 0B8X).
The source's Nagata case specializes to the reduced finite-type k-scheme here;
the accepted split supplies the algebraic normalization finiteness argument.
There is no statement correction and no STATEMENT-DISPUTED flag.

Existing-declaration searches (all through prescribed msearch.py, plus rg):

- LeanFinder: “For a reduced finite type pure curve over an algebraically closed
  field the normalization structure sheaf quotient is coherent and has finite
  support exactly at nonsmooth points.” Eight hits: scheme-morphism
  normalization and its generic ring properties, not this coherent quotient
  and its support. `ker_toNormalization` is a scheme-morphism kernel.
- LeanSearch: “The cokernel of the normalization structure sheaf inclusion of
  a reduced algebraic curve is coherent and vanishes exactly at normal points.”
  Eight hits: generic categorical cokernels and scheme normalizations;
  none is this statement.
- Loogle: `AlgebraicGeometry.Scheme.reducedNormalization,
  AlgebraicGeometry.RingedSpace.IsCoherent`: no hits; reducedNormalization is
  project-only, hence unknown to the remote Mathlib index.
- Mathlib grep: `normalization.*(cokernel|coherent|support)|[Cc]okernel.*[Nn]ormalization`
  in AlgebraicGeometry: one hit, Normalization.lean:342, support of a scheme
  morphism kernel. It does not state the module-cokernel result.
- rg of lean/WeilConjectures and lean/Sheaf for this node id and the planned
  theorem/helper names: no duplicate declaration. Searches for normalization
  plus quotient/coherent/support led to NormalizationSingularSkyscraper,
  NodalNormalizationQuotient, Curve/NormalizationMonoProperties, and related
  modules. These were read: the first is the larger downstream theorem with
  skyscraper/completion data, the second assumes nodal singularities and
  properness, and the third concerns constructible etale coefficient sheaves.
  None has exactly this node's statement or the canonical module-cokernel helpers.
- The componentwise normalization definition was found and read in the exact
  dependency module; reused without copying its construction.
- `normalLocus`, `normalizationNormalLocus`, `normalizationCoherentQuotient`,
  and `curve_normalization_coherent_support` searched in the project's two
  Lean roots; no prior matching declaration.

Validation: scompile.py compiled both its sandbox module and its actual module
name without errors or warnings (2.2 seconds each). The expected theorem proof
is the sole `sorry`; no definition contains postponed data.

## Returned-delivery repair

The maintainer returned immutable head `d905fd29af05` for H13/§1(B): rebinding
`pqf-def-coherent` would orphan the live Q25 interface's 16 Sheaf users.
Following the requested Q158 pattern, this repair removes
`dag/nodes/sec-abelian-varieties/pqf-def-coherent.json` from the delivery.
No dependency module or dependency-record change is delivered.

The item's `lean.note` now explains why its coherence conclusion uses the
existing upstream `AlgebraicGeometry.RingedSpace.IsCoherent` in
`WeilConjectures.AlgebraicGeometry.Coherent`: clause 3 of `pqf-def-coherent`
(Stacks 01BV) requires finite type and finite-type kernels of maps from finite
free modules on every open. The Q25 declaration
`AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType` renders only
quasi-coherence plus finite type. Both source definitions and their docstrings
were reread. The existing Q25 record and all its users are preserved.

The item node is compared with the current shared live node: only `lean`
differs. Its statement, dependencies and accepted six-step proof are unchanged.
The Lean module remains byte-for-byte unchanged from the returned packet;
its SHA256 is `ce0f3c6365cf423599731aa5fda361c3501cb1e874a17fd220e75e578255232c`.
The independent maintainer review already checked the mathematics clause by
clause against 0C1R and 0B8X, including the canonical stalk identification,
the structural residue-field map, and the empty-scheme case. The present
repair changes only delivery scope and the explanatory metadata.

The required initial dry run of the saved packet passed preflight and per-file
compilation at `59e96a63d25`, but still included the rejected dependency file.
The repaired packet is recompiled and dry-run before delivery.

## Second reading by Q117

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
