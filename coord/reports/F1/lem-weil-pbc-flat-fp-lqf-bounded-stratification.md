## Worker report

The module states `AlgebraicGeometry.Scheme.Hom.exists_flat_fp_lqf_bounded_stratification`.
It assumes a morphism `f : X ⟶ S` of schemes, with typeclass hypotheses `Flat f`,
`LocallyOfFinitePresentation f`, and `IsSeparated f`, plus the explicit hypotheses
`h_lqf : IsLocallyQuasiFinite f` and `h_bounded : HasUniversallyBoundedFibers f`.
It produces a natural-number bound `N` and sets `Z r : Set S`.  Each `Z r` for
`r ≤ N` is closed, `Z N = Set.univ`, and the chain is increasing.  The degree-r
stratum is rendered as `Z r \ (if r = 0 then ∅ else Z (r - 1))` when `r ≤ N`, and
as `∅` otherwise.  The statement asserts pairwise disjointness, coverage of `S`,
and for every `g : T ⟶ S` and `r : ℕ` the equivalence between
`(pullback.snd f g).IsFiniteLocallyFreeOfDegree r` and `Set.range g ⊆ Sᵣ`.

The finite-locally-free notion is the recorded source declaration
`AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree` in
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`; the fibre-bound notion is
`AlgebraicGeometry.Scheme.Hom.HasUniversallyBoundedFibers` from
`Sheaf.AlgebraicGeometry.FiberDegreeBound`; locally quasi-finite is
`AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite` from
`Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`.  Scheme, flatness, local finite
presentation, separatedness, and pullbacks use the Mathlib declarations recorded by
the dependency nodes (`AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Flat`,
`AlgebraicGeometry.LocallyOfFinitePresentation`, `AlgebraicGeometry.IsSeparated`,
and `CategoryTheory.Limits.pullback`).

Edge cases checked: `N = 0` uses the empty predecessor for degree zero; every
`r > N` has empty stratum; empty schemes and empty base changes are permitted; the
bound is a natural number, so no negative-degree case is introduced.

Searches: `rg` over `lean/Sheaf` and `WeilConjectures` for bounded stratification and
finite-locally-free stratification; `python3 .../msearch.py F1 ... leanfinder
"flat locally finitely presented locally quasi-finite bounded fibres stratification"`;
`... loogle "IsFiniteLocallyFreeOfDegree, IsLocallyQuasiFinite"`; and grep over
Mathlib algebraic-geometry morphism files.  No existing declaration of this lemma was
found; the dependency declarations above were used.

## Earlier second reading (a previous round; superseded)

The theorem binders match the node's flat, locally finitely presented, separated,
locally quasi-finite, and universally bounded hypotheses.  The natural-number `N`
and chain `Z` encode `Z_{-1}=∅` through the explicit empty predecessor in every
stratum, and `Z_N=S` through `Z N = Set.univ`.  The pairwise-disjoint and coverage
clauses render the partition, including empty strata above `N`; the final equivalence
uses the pullback projection and exactly the stated finite-locally-free degree
property.

## Second reading by F1

Read the delivered node, its nine statement dependencies, their recorded declarations,
and the complete source statement and proof of Stacks 07RY. The repository literature
checkout is absent on this machine; the same source is available in
`/home/ubuntu/c1-stacks-review/more-morphisms.tex:12761` and
`/home/ubuntu/c1-stacks-review/morphisms.tex:15302`. The local tags table maps 07RY
and 03J4 to the expected labels. The chapter introduction imposes no additional
Noetherian, base-field or characteristic assumptions.

Objects, hypotheses and conclusions, matched separately:

- Schemes X and S, and their morphism f: `{X S : Scheme.{u}} (f : X ⟶ S)`.
  Verdict: exact, arbitrary schemes, no affineness or finite-type assumption.
- Flat: `[Flat f]`. Opened Mathlib Morphisms/Flat.lean:42: the affine ring-map
  predicate is equivalent to flat stalk maps, as recorded by def-weil-flat-morphism.
  Verdict: exact.
- Locally finitely presented: `[LocallyOfFinitePresentation f]`. Opened Mathlib
  Morphisms/FinitePresentation.lean:45 and the dependency's affine-neighbourhood
  equivalence record. Verdict: exact; global finite presentation is not assumed.
- Separated: `[IsSeparated f]`. Opened Morphisms/Separated.lean:44: the diagonal
  is a closed immersion. This is the convention node's referenced notion. Exact.
- Locally quasi-finite: `h_lqf : IsLocallyQuasiFinite f`. Opened
  QuasiFiniteMorphism.lean: it quantifies over each point using affine neighbourhoods,
  Algebra.FiniteType and the recorded Algebra.IsQuasiFiniteAtPrime.
  Verdict: the Stacks 01TD notion, including finite type, not merely Mathlib's
  weaker same-sounding LocallyQuasiFinite.
- Universally bounded finite fibre degrees: `h_bounded : HasUniversallyBoundedFibers f`.
  Opened FiberDegreeBound.lean: this is `∃ n : ℕ, ∀ y, IsFinite
  (f.fiberToSpecResidueField y) ∧ (f.fiberToSpecResidueField y).finrankΓ ≤ n`.
  Opened Mathlib Fiber.lean and ResidueField.lean: the fibre is the pullback along
  Spec of the stalk residue field; its structure morphism is the second projection.
  Opened source FiberDegree.lean:81,92: ΓAlgebra uses the actual structure morphism
  and ΓSpecIso, and finrankΓ is the dimension of global sections over that field.
  Verdict: exact Stacks 03J4, with finiteness required explicitly (finrank alone
  would not exclude infinite-dimensional sections).
- Finite chain with terminal whole base: `∃ (N : ℕ) (Z : ℕ → Set S)`,
  `∀ r, r ≤ N → IsClosed (Z r)`, `Z N = Set.univ`, and
  `∀ r, r < N → Z r ⊆ Z (r + 1)`. Verdict: exact finite chain; values above N
  are immaterial. The existential bound follows the node's existential hypothesis;
  there is no independently supplied fixed n to preserve.
- Initial empty predecessor: in each stratum the predecessor is
  `if r = 0 then ∅ else Z (r - 1)`. Verdict: exactly Z_{-1}=∅ without
  natural-number subtraction mistakenly replacing it by Z 0.
- Strata: `if r ≤ N then Z r \ (if r = 0 then ∅ else Z (r - 1)) else ∅`.
  Verdict: exactly successive differences for r≤N, empty for r>N.
- Pairwise disjointness: `∀ r t, r ≠ t → ... Disjoint Sᵣ Sₜ`. Exact.
- Union whole base: `∀ s : S, ∃ r : ℕ, s ∈ ...`. Exact pointwise coverage.
- Every test scheme and morphism, and every nonnegative degree, after the choice
  of the chain: `∀ (T : Scheme.{u}) (g : T ⟶ S) (r : ℕ), ...`.
  Verdict: correct quantifier order, arbitrary morphisms rather than reduced or
  finite-type test schemes, with no extra typeclasses.
- Universal property: `(pullback.snd f g).IsFiniteLocallyFreeOfDegree r ↔
  Set.range g ⊆ Sᵣ`. Opened the recorded source FiberDegree.lean:778-794:
  IsFiniteLocallyFree extends finite, flat and locally finitely presented;
  the degree predicate additionally gives fibreDegree_eq at every target point.
  Its finite hypothesis supplies the affine instance required by fibreDegree.
  Opened Limits/Shapes/Pullback/HasPullback.lean:95-115: snd maps X×_S T to T.
  Verdict: exact degree and projection, both implications, image as a set.

Edge cases: N=0 has Z 0=S and the degree-zero stratum S. Empty X is allowed
and has degree-zero fibres. Empty S and empty T are allowed; on empty T finite
local freeness of every degree and inclusion of the empty image are compatible,
including r>N. Repeated closed sets yield empty strata, so no nonemptiness is
assumed. No characteristic or coefficient field is fixed. The universe u is
explicit and arbitrary; X,S,T are all objects of the same category Scheme.{u},
which is the setting of the chosen pullbacks and recorded predicates. There is
no independent smaller universe of tests and no unbound variable or universe.

Independent searches (different wording from the worker): LeanFinder query
"finite degree strata for separated flat quasi finite maps" returned eight
nearby morphism properties, no stratification theorem. Loogle query
"IsFiniteLocallyFreeOfDegree" returned no hits (identifier unknown to its index).
LeanSearch query "A flat finitely presented morphism with uniformly bounded
finite fibres admits closed degree strata" was unavailable (Internal Server
Error), so no verdict is inferred from it. rg across Mathlib algebraic geometry,
WeilConjectures and lean/Sheaf for `stratif.*(flat|bounded|degree)`,
`bounded.*stratif`, `stratify_flat`, `universallyBounded`, and the proposed full
name found only neighbouring fibre-bound definitions and lemmas, no existing
statement. No second definition is introduced; all dependency notions are used
from their recorded modules. No new nodes or dependency modules are needed.

Mismatches repaired: the theorem docstring summarized rather than carrying the
node's ten-step proof (H8). Expanded it with the actual maximal-degree argument,
étale splitting, shrinking, degree count, descent, induction on the reduced
closed complement, partition, and both universal-property implications, naming
the dependencies. Corrected an extra parenthesis in the module source tag,
removed unused named `if h` binders and an unused direct Finite import. The
mathematical statement is unchanged. Its node lean.statement was synchronized
verbatim with the file's signature. The single theorem still has proof `sorry`;
there are no definitions or auxiliary proofs. No statement_change is present.

Validation: remote scompile on the complete delivery module, followed by the
stage-2 delivery preflight dry run; no warnings other than allowed sorry notices.

## Reviewer fix (R-fls1149)

The delivered statement assumed `HasUniversallyBoundedFibers f` (an existential bound) and
concluded with an independent `∃ N`, so the length of the filtration was not tied to the bound
of the hypothesis (the node: "there is an integer n ... Then ... Z_n = S"), and the strata were
written with `let` binders and nested `if`s. Restated with the bound explicit,
`(n : ℕ) (hn : BoundsFiberDegrees f n)`, and in the spelling of the landed sibling
`exists_closed_stratification_of_flat_quasiFinite` (J1 11f04753c): `Z 0 = ∅` is the paper's
`Z_{-1}`, `Z (r + 1)` the paper's `Z_r`, all closed, `Monotone Z`, `Z (n + 1) = Set.univ`
(so the strata `Z (r + 1) \ Z r` are empty for `r > n`), strata written out in place,
pairwise disjoint with union `Set.univ`, and the universal property for every
`g : T ⟶ S` in `Scheme.{u}` and every `r`. Values of `Z` beyond index `n + 1` are forced to
`Set.univ` by monotonicity, which is no restriction.
