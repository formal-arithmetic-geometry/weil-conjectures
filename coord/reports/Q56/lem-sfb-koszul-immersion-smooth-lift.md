## Worker report

The module `Sheaf.AlgebraicGeometry.KoszulImmersionSmoothLift` states
`AlgebraicGeometry.koszulRegularImmersion_of_smooth_ambient`, with `sorry` as its
only proof. There are no new definitions or auxiliary theorems. I read the local
Stacks source `divisors.tex`, Tag 067S, and the definition and affine criterion in
Tags 063J and 063G. The source agrees with the node; no statement correction or
STATEMENT-DISPUTED flag is needed.

Hypotheses and conclusion, clause by clause:

- Schemes Z, P and S: `{Z P S : Scheme.{u}}`, with arbitrary explicit universe u.
- Morphisms i:Z→P, p:P→S, j:Z→S: the three explicit morphism binders.
- Compatibility p∘i=j: `(hcomm : i ≫ p = j)`; Lean composition reads left to right.
- Smoothness of p: `[Smooth p]`, the recorded Mathlib notion.
- Both i and j are immersions: `[IsImmersion i] [IsImmersion j]`. These are ordinary
  locally closed immersions, not globally closed immersions. The dependency's
  `mathlib_match.how` explicitly identifies this part with Mathlib's `IsImmersion`
  and `isImmersion_iff_exists`.
- Koszul regularity of j: `(hj : ∀ z : Z, IsKoszulRegularImmersionNear j z)`.
- Koszul regularity of i: `∀ z : Z, IsKoszulRegularImmersionNear i z`.
- Local meaning: the existing `IsKoszulRegularImmersionNear a z` provides an open
  source neighbourhood V containing z, an open target U, and a closed immersion
  V→U whose composite into the target equals the actual restriction of a. Its
  `CotangentPresentation.IsKoszulImmersion` clause says, near every source point,
  that an affine target open W has a finite tuple of Koszul-regular sections
  generating the actual kernel ideal. This is the node's local ideal condition,
  with no arbitrarily supplied ideal or map. Tags 063J and 063G identify this with
  Koszul regularity of the immersion. Source locality is explicit, rather than
  accidentally demanding the whole morphism be closed in each neighbourhood.
- Varying lengths: the chart existential `∃ (r : ℕ) (a : Fin r → Γ(P, W.1)), ...`
  is inside the point quantifier. Zero length is allowed.
- No Noetherian, separation, quasi-compactness or fixed-length condition occurs.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`, also
  `smooth_isStableUnderBaseChange` and the smooth-to-flat instance for the proof.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`. The ordinary immersion interface is
  `AlgebraicGeometry.IsImmersion` from `Mathlib.AlgebraicGeometry.Morphisms.Immersion`,
  made public by the near-point module; its `isImmersion_iff_exists` is the exact
  factorization recorded in def-weil-closed-immersion's mathlib_match.
- `WeilConjectures.RingTheory.KoszulRegularSequence`:
  `RingTheory.Sequence.IsKoszulRegular` (positive homology vanishing for the
  actual finite-tuple Koszul complex), used by the existing chart predicate.
- `Sheaf.AlgebraicGeometry.KoszulRegularImmersionNear`:
  `AlgebraicGeometry.IsKoszulRegularImmersionNear`. I read its entire definition
  and docstring and the underlying `CotangentPresentation.IsKoszulImmersion`
  definition in `Sheaf.AlgebraicGeometry.LciCotangentPresentation`.

The existing definition node `def-sfb-koszul-regular-immersion-near` is added to
stmt_deps under brief-stage2 §5 (a landed definition already carrying a Lean
record). It is reused without any new node or change to that dependency. The
original four dependencies and the entire mathematical statement are preserved.

Available proof dependencies have plain imports:

- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd` and `pullback.lift` (def-pc-fibre-product).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper.isStableUnderBaseChange`;
  the smooth clause of lem-pc-proper-base-change is already publicly imported
  through Smooth.
- `Sheaf.AlgebraicGeometry.SmoothSectionRegularImmersion`:
  `AlgebraicGeometry.smoothSection_regularImmersion`, with its full arbitrary-base
  immersion and regular affine-chart conclusion.
- `WeilConjectures.RingTheory.RegularSequenceKoszulRegular`:
  `RingTheory.Sequence.isKoszulRegularOn_of_isWeaklyRegular`,
  `RingTheory.Sequence.IsRegular.isKoszulRegularOn`, and
  `RingTheory.Sequence.IsRegular.isKoszulRegular`.

lem-pc-smooth-flat is Mathlib material in the imported Smooth module. The
flat-ascent/etale-descent and composition nodes currently have neither a Lean
record nor mathlib_match, so there is no module to import for these proof-only
prerequisites. Their node names and roles are retained in the five-step proof
docstring. They are not needed to type this statement, and no dependency wait or
unrelated theorem statement was introduced.

Edge cases checked mathematically before writing:

- Empty Z: both pointwise predicates are vacuous; no source point is chosen.
- Empty P or S: compatible maps force the corresponding empty-source cases;
  no Nonempty hypothesis is introduced.
- Empty equation tuple: the zero ideal on an open immersion is allowed, so an
  etale section and identity morphisms are covered, without positive codimension.
- A smooth zero section into affine space over a non-Noetherian ring is covered;
  no regularity or Noetherian property of the ambient ring is assumed.
- Disjoint components with distinct smooth relative dimensions and different
  tuple lengths are covered by the nested pointwise existentials.
- A nonclosed immersion remains allowed: no `[IsClosedImmersion i]` or
  `[IsClosedImmersion j]` hypothesis was substituted for ordinary immersion.
- Nonseparated smooth ambient schemes remain allowed. The local closed charts
  are used rather than a globally closed graph assumption.

Searches performed (the msearch calls are logged in searches.jsonl):

1. LeanFinder: `A Koszul regular immersion lifts to a Koszul regular immersion into
   a smooth ambient scheme`. Eight hits on Smooth, SmoothOfRelativeDimension,
   open-immersion smoothness and smooth affine charts; none states this theorem.
2. Loogle: `"IsKoszulRegular", "Smooth"`. Zero hits.
3. msearch grep: `KoszulRegular|koszul.regular|lift.*regular.*immersion` in
   Mathlib/AlgebraicGeometry. Zero hits.
4. Direct rg of Mathlib/AlgebraicGeometry with `KoszulRegular|koszul.regular`:
   zero hits. Direct rg of upstream and project AlgebraicGeometry with
   `KoszulRegularImmersion|IsKoszulRegular|koszulRegularImmersion|koszul.regular immersion`
   found the existing near-point predicate, closed-chart predicate and many
   closed-immersion duality statements, but no smooth-lift statement.
5. Direct rg of all lean/Sheaf with `KoszulRegular|koszul.regular`, and of upstream
   with the node id, found the same predicates and no exact theorem.
6. DAG search for `Koszul-regular immersion|Koszul regular immersion`, then reading
   def-sfb-koszul-regular-immersion-near, identified its usable landed declaration.
   `tools/blueprint_refs.py search 'Koszul-regular immersion'` returned zero matches.
7. LeanSearch: `If Z to S is a Koszul regular immersion and P to S is smooth,
   a compatible immersion Z to P is Koszul regular`. Eight hits on ordinary
   immersions, their composition/factorization and open-immersion smoothness;
   none states Koszul regularity of the lift.
8. Exact proposed declaration-name search across lean/Sheaf, lean/WeilConjectures
   and dag/lean_names_upstream.json returned no collision.

Validation: scompile.py compiled both its sandbox check and the actual library
module successfully (4.5 s and 25.3 s respectively), without errors or warnings.
Every universe and variable is explicitly bound; autoImplicit is disabled.

## Second reading by Q56

This is a separate checking pass by the same assigned worker, not a claim of an
independent agent review: the dispatcher explicitly forbids starting other agents,
and the maintainer's independent review follows delivery. I reopened the node,
the delivered Lean file, the near-point definition, its closed-chart definition,
and Stacks 067S/063J/063G for this pass.

The node's three schemes and three arrows occur with exactly the prescribed
sources and targets; hcomm is p∘i=j in Lean's composition order. Smooth p is the
recorded smoothness notion. Both explicit immersion hypotheses are present and
are neither replaced by closed immersion nor inferred from a stronger assumption.
The premise is pointwise Koszul regularity of j and the conclusion pointwise
Koszul regularity of i. The reused near predicate has the correct open source and
open target factorization, the equality to the actual restriction, the closed
immersion condition, and local finite Koszul-regular kernel generators. Its
quantifiers allow zero and varying lengths. There is no new global hypothesis,
fixed dimension, or nonempty condition. The arbitrary universe u is bound. The
five proof steps match the DAG: graph factorization, smooth base change and
section theorem, regular-to-Koszul conversion, flat ascent along p, composition.
No mismatch was found and no mathematical statement was changed.
