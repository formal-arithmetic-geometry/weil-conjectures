## Worker report

The module `Sheaf.AlgebraicGeometry.PureBaseChangeConstructibleImage` states
`AlgebraicGeometry.pure_base_change_constructible_image`, with proof `sorry`.
No definitions, new DAG nodes, or dependency repairs are needed. The item copy
changes only `lean`. No statement fault or STATEMENT-DISPUTED issue was found.

Source read: `literature/stacks-project/limits.tex`, Tag 0EY2,
`lemma-descend-dimension-d`, especially the proof defining the retrocompact
bounded-dimension open, taking its constructible complement, and proving image
containment by invariance of fibre dimension. The node makes the underlying
pure-fibre local-dimension and global-dimension comparisons explicit. The Lean
docstring follows all six proof steps and names their dependency nodes.

Hypothesis and clause correspondence:

- Schemes and morphism: `{X T : Scheme.{u}} (f : X ⟶ T)`.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the two
  conditions specified by def-weil-finite-type-morphism. Local finite
  presentation: `[LocallyOfFinitePresentation f]`. The fact that local finite
  presentation already implies local finite type does not remove the node's
  finite-type hypothesis, including its nonredundant quasi-compactness clause.
- Nonnegative integer dimension: `(d : ℕ)` includes zero.
- The point of the scheme-theoretic fibre corresponding to `x` is `f.asFiber x`,
  so `topologicalKrullDimAt (f.asFiber x)` is precisely the node's local fibre
  dimension, using the existing fibre homeomorphism and local dimension.
- The set U is inlined as
  `{x : X | topologicalKrullDimAt (f.asFiber x) < (d : WithBot ℕ∞)}`.
  This is exactly the node's integer bound `dim ≤ d - 1`: a local dimension at
  a point is a nonnegative integer or infinity. For a finite such value n,
  `n < d` is equivalent to `n ≤ (d : ℤ) - 1`; infinity satisfies neither bound.
  At d = 0 both conditions are false. This uses no natural truncated subtraction
  and is a notation-level equivalent formulation, not a statement correction.
- E is inlined as the set complement Uᶜ. The first three conjuncts are `IsOpen U`,
  `IsRetrocompact U`, and `Topology.IsConstructible Uᶜ`, respectively.
- The explicit endpoint is `(d = 0 → U = ∅ ∧ Uᶜ = Set.univ)`, expanded inline.
- Arbitrary base change: the final conjunct quantifies over every
  `(T' : Scheme.{u}) (g : T' ⟶ T)`, with no class assumptions on g. The universe
  u is arbitrary; using the common universe of the category of schemes adds no
  mathematical size restriction (schemes can be viewed in a common universe).
- X', p, f' are the canonical `pullback f g`, `pullback.fst f g`, and
  `pullback.snd f g`, not arbitrarily chosen maps.
- Pure nonempty fibres: `∀ t' : T', Nonempty ((pullback.snd f g).fiber t') →
  ((pullback.snd f g).fiber t').IsPureDimension d`. The `Nonempty` tests the
  underlying type of that scheme. It introduces no nonemptiness requirement on
  empty fibres and uses the dependency's pure-dimension definition verbatim.
- The pointwise displayed chain of equalities is a conjunction: for every
  `x' : ↥(pullback f g)`, the local dimension at `f'.asFiber x'` equals the local
  dimension at `f.asFiber (p x')`, and the latter equals `(d : WithBot ℕ∞)`.
- Image containment is `Set.range (pullback.fst f g) ⊆ Uᶜ`.
- The last conjunct is `∀ t' : T', topologicalKrullDim (f'.fiber t') ≤ d`,
  with the actual canonical f' expanded and the natural number cast to
  `WithBot ℕ∞`. No nonemptiness antecedent is placed on this conclusion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; its
  `locallyOfFiniteType_isStableUnderBaseChange` and pullback instances provide
  the recorded Mathlib match of lem-weil-pbc-lft-base-change for the proof plan.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`, `fiberHomeo`, and `asFiber`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.Topology.Constructible`: `IsRetrocompact`, `Topology.IsConstructible`.
  The dependency def-weil-constructible-subset has no lean record; its recorded
  Mathlib match is usable as required, and gives exactly these notions.
- Proof import `WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension`:
  `AlgebraicGeometry.topologicalKrullDimAt_eq_of_equidimensional_open`.
- Proof import `Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange`:
  `AlgebraicGeometry.fibre_dimension_after_base_change`.
- Proof import `Sheaf.AlgebraicGeometry.RetrocompactBoundedFibreDimension`:
  `AlgebraicGeometry.isOpen_and_isRetrocompact_localFibreDimension_le`.
- Proof import `WeilConjectures.Topology.DimensionSupremumLocalDimensions`:
  `topologicalKrullDim_eq_iSup_topologicalKrullDimAt`.

All statement-dependency modules are public imports; the remaining recorded
proof-dependency modules are ordinary imports. The source signatures and
associated docstrings were read, including the existing dimension theorem's
whole-space-open specialization and the actual fibre/base-change signatures.

Edge cases checked before writing:

- d = 0: at a point the local dimension is at least zero, so U is empty and E
  is the whole source. Empty fibres have dimension bottom and satisfy the bound.
- d = 1: the strict inequality selects exactly local dimension zero, rather
  than an erroneous truncated bound that could also include zero when d = 0.
- Empty X: both loci are empty; the d = 0 clause has E equal to the empty whole
  space, and there are no pullback points. Empty T' gives vacuous universal
  assertions. No point or fibre is artificially assumed to exist.
- Identity g is included. Arbitrary non-flat or non-finite-type g is included;
  there is no flatness, separation, properness, or finiteness assumption on g.
- Infinite dimension is excluded from U by the strict finite bound, as required.
  Empty fibres are not forced to have dimension d, only dimension at most d.

Searches actually run using `/home/ubuntu/weil-launcher-all/batch2/msearch.py`
with group Q39 and this item:

1. LeanFinder query: "For a finite type locally finitely presented scheme morphism
   the complement of the open locus of local fibre dimension less than d is
   constructible and contains every pure d dimensional base change".
   Result: eight hits, principally `Scheme.Hom.isConstructible_image`,
   `isLocallyConstructible_image`, `isConstructible_preimage`, and Chevalley
   theorems for spectra. These concern constructible images/preimages and do not
   state this fibre-dimension locus or its pure-base-change comparisons.
2. Loogle query:
   `AlgebraicGeometry.LocallyOfFinitePresentation, Topology.IsConstructible`.
   Result: one hit, `Scheme.Hom.isConstructible_image`, requiring a constructible
   input subset and qcqs target; this is not the node's statement.
3. Mathlib grep query: `localFibreDimension|pure.*base.*change|retrocompact`,
   subdirectory `AlgebraicGeometry`. Result: five hits, concerning retrocompact
   basic opens and constructible preimages in Affine, QuasiAffine, and
   FinitePresentation; no exact statement.
4. LeanSearch query: "For a locally finitely presented scheme morphism the high
   local fibre dimension locus is constructible and contains the image of any
   pure dimensional base change". Result: eight hits, constructible image,
   local finite presentation/type definitions and implications, proper morphisms,
   and local noetherianity; none is the combined statement.
5. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
   `localFibreDimension|localFiberDimension|pure_base_change|pureBaseChange|constructible.*[Dd]im|[Dd]im.*[Ll]ocus`,
   followed by the narrower algebraic-geometry search for
   `pure.*base.*change|base.*change.*pure|high.*[Ff]ibre|[Ff]ibre.*high|localFibreDimension`.
   Result: bounded-locus openness and retrocompactness dependencies, algebraic-space
   analogues, and unrelated curve/cohomology results; no theorem covering this item.
6. `grep -rn "lem-trf-pure-base-change-constructible-image" lean/WeilConjectures`:
   no matches. The exact proposed declaration name also had no existing match.

## Second reading by Q39

Re-read the node and completed signature clause by clause. The strict inequality
has the same integer predecessor semantics at d = 0 and at d > 0. The fibre-point
argument uses `asFiber`, so it measures dimension in the scheme-theoretic fibre,
not the local-ring dimension or the dimension in X. The equalities are quantified
over every point of X', and the all-fibres bound lies outside this point quantifier,
so it covers empty fibres as well. The openness, retrocompactness, constructibility,
and zero endpoint are outside the conditional on the pure base change. The
nonempty-fibre premise is an implication for each fibre; g has no added hypotheses.
The pure-dimension predicate and all other notions are the dependency declarations,
with no copied interface. The first compile found that the point binder needed the explicit carrier coercion
`↥(pullback f g)` to avoid elaborating a pullback in Type. This was corrected; no
mathematical mismatch was found and no statement changes were made.
This is a second pass by the assigned dispatcher worker; the maintainer supplies
the independent review, as specified in the assignment (no other agent was started).

Validation: prescribed `scompile.py Q39 lem-trf-pure-base-change-constructible-image`
accepted the delivered module as both a sandbox module (1.5 s) and the named
library module (1.4 s), under the default 60-second limit, with no errors or
unexpected warnings. The final source has one theorem and one `sorry`, explicit
universe u and `autoImplicit false`; every Lean line is at most 94 characters.
The node's recorded signature is verbatim and the only changed node field is lean.
