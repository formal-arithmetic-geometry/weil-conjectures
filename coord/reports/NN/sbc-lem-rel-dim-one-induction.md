## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeDimensionOneInduction` states
`AlgebraicGeometry.Etale.universalBaseChangeProperty_relativeDimensionOne_induction`,
with `sorry` as its whole proof. No definitions, helper nodes, or corrections are added.

Hypothesis and conclusion correspondence:

- Schemes and the morphism `f : X → S` are `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Affineness of the morphism is `[IsAffineHom f]`.
- Smoothness of relative dimension one is `[SmoothOfRelativeDimension 1 f]`, which
  includes smoothness and uses the exact dependency notion.
- Affineness of the source is `[IsAffine X]`; there is no assumption that `S` is affine.
- The positive integer coefficient parameter is `(n : ℕ) (hn : 0 < n)`.
  Positive integers and positive naturals give the same parameter domain.
- Invertibility on `S` is `(hinv : IsUnit (n : Γ(S, ⊤)))`.
- The nonnegative cohomological degree with `q ≥ 1` is `(q : ℕ) (hq : 1 ≤ q)`.
- Universal BC in every nonnegative degree at most `q - 1` is exactly
  `hprev : CumulativeUniversalBaseChangeProperty f n hn hinv (q - 1)`.
- The new universal degree-`q` conclusion is
  `UniversalBaseChangeProperty (ULift.{u + 1} (ZMod n)) f (q : ℤ)`.
- The final cumulative universal conclusion is the second conjunct
  `CumulativeUniversalBaseChangeProperty f n hn hinv q`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Affine`, `AlgebraicGeometry.IsAffineHom`:
  preimages of affine opens are affine opens.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.SmoothOfRelativeDimension`: the existing chart-based notion,
  identified with the node's fibre-dimension formulation by its recorded Stacks references.
- `Sheaf.AlgebraicGeometry.CumulativeUniversalBaseChangeProperty`,
  `AlgebraicGeometry.Etale.CumulativeUniversalBaseChangeProperty`: bounded forall over
  natural degrees of the recorded universal BC predicate.
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs` (publicly imported through
  the previous dependency), `AlgebraicGeometry.Etale.UniversalBaseChangeProperty`:
  every Cartesian base change, and then every qcqs horizontal side and coefficient sheaf.

Proof imports for the already recorded permanence declarations are
`Mathlib.AlgebraicGeometry.Morphisms.Etale`, `.Separated`, and
`Mathlib.AlgebraicGeometry.Limits` (including the finite coproduct clause of affine
permanence). The two remaining proof nodes `sbc-lem-bc-universal-test` and
`sbc-thm-universal-test-vanishing` have no recorded Lean declarations yet; they are named
in the proof docstring and supply no objects needed to state this theorem.

Edge cases checked: `q = 1` makes the hypothesis exactly universal BC in degree zero;
truncated natural subtraction is therefore harmless. `q = 0` is excluded by the node's
explicit hypothesis. `n = 1` retains the zero coefficient ring, with no nontriviality
hypothesis; `n = 0` is excluded as required. Empty affine source schemes are allowed;
relative dimension is vacuous there, just as in the recorded definition. The base may
be nonaffine. All schemes share the dependency universe `u`; the coefficient ring is
lifted to `u + 1`, matching its actual module-sheaf size convention. All variables and
universes are bound explicitly. There is no statement dispute.

Searches made:

- `msearch.py leanfinder`, query “Universal etale cohomology base change for an affine
  smooth relative curve induction on cohomological degree”: eight results about geometric
  etaleness and ring formal etaleness, no matching cohomological statement.
- `msearch.py loogle`, query `"UniversalBaseChangeProperty", "induction"`: zero hits.
- `msearch.py grep`, query `UniversalBaseChangeProperty|relDimOneInduction`: zero hits
  in Mathlib.
- `rg` in the upstream source and `lean/Sheaf`, including the node id and variants
  `rel_dim_one_induction|relDimOneInduction`: found the blueprint-tagged upstream
  cumulative theorem in `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction`.
  Its full docstring and signature were read. It is quantified over a general ring Λ
  annihilated by n, and assumes BC in all integer degrees at most q-1 (including negative
  degrees). It concludes the corresponding integer cumulative property. Thus its raw
  signature is not this node's positive-coefficient, nonnegative-degree statement.
  The new theorem specializes the existing BC predicates, without redefining any notion.
  The upstream negative-degree vanishing would bridge the two versions in stage 3.
- Read the full recorded signatures and docstrings in the affine and smooth Mathlib
  modules, the cumulative module, and the upstream BC definitions. Searched the project's
  statement modules: no existing theorem with the delivered exact statement was found.

Validation: the delivered module is checked separately by `scompile.py` on the server;
the dry run uses `deliver2.py --no-push`. No local Lean compiler or global build is used.


## Second reading by NN

Read independently against the DAG statement, its three statement dependencies,
the blueprint node source, and Stacks `etale-cohomology.tex`: the second proof of
`theorem-smooth-base-change` (0EYU), together with
`lemma-base-change-does-not-hold` (0F08). The Stacks proof fixes coefficients
annihilated by an invertible positive integer before reducing to an affine
smooth relative curve. The DAG explicitly fixes the nonnegative degree domain
through `sbc-def-base-change-property`. There is no ambient Noetherian, field,
nonempty, or characteristic assumption to add.

Object/hypothesis/conclusion checklist (each verdict: exact):

- Schemes X and S and morphism f: `{X S : Scheme.{u}} (f : X ⟶ S)`.
  The universe `u` is arbitrary and agrees with the recorded scheme and BC APIs.
- Affine morphism: `[IsAffineHom f]`. Read its actual Mathlib class, whose field
  says that preimages of affine opens are affine, matching
  `pqf-def-affine-morphism`.
- Smooth relative dimension one: `[SmoothOfRelativeDimension 1 f]`. Read the
  Mathlib class of standard smooth affine charts and its `smooth` lemma.
  This is the dependency's recorded notion, equivalent to the fibre dimension
  formulation by its Stacks 02G1/02G2 and 02H6 identification. It does not
  require an extra independently supplied smoothness instance.
- Affine source: `[IsAffine X]`; S remains an arbitrary scheme.
- Positive integer n: `(n : ℕ) (hn : 0 < n)`. Every integer at least one is
  represented, with no prime, nonzero-ring, or characteristic restriction.
- Invertibility on S: `(hinv : IsUnit (n : Γ(S, ⊤)))`, precisely the convention
  used by the coefficient and BC dependency; pullback preserves this condition.
- Integer degree q at least one: `(q : ℕ) (hq : 1 ≤ q)`. This represents
  exactly the positive integers in the node.
- Universal BC in each degree 0 through q-1: `hprev :
  CumulativeUniversalBaseChangeProperty f n hn hinv (q - 1)`. Opened the
  dependency module: its real body is `∀ r : ℕ, r ≤ q →
  UniversalBaseChangeProperty (ULift.{u + 1} (ZMod n)) f (r : ℤ)`.
  Opened upstream `Defs.lean`: the universal predicate quantifies over every
  Cartesian base change of f; the fixed-degree predicate then quantifies over
  every qcqs horizontal morphism, every Cartesian square and every module sheaf.
  Thus neither the outer universal quantifier nor the sheaf quantifier is lost.
- New degree-q universal BC: the first conjunct
  `UniversalBaseChangeProperty (ULift.{u + 1} (ZMod n)) f (q : ℤ)`.
  The lifted ring is the recorded Z/nZ coefficient convention, and the map is
  the existing `baseChangeHomologyMap`, not an unspecified isomorphism.
- Universal BC through q: the second conjunct
  `CumulativeUniversalBaseChangeProperty f n hn hinv q`. Both clauses of the
  node's conclusion are present, in the stated order, without extra clauses.

Edge cases: q=1 requires exactly degree zero in hprev; q=0 is explicitly
excluded by the source and node. Since q≥1, natural subtraction loses no
intended degree. n=1 includes the zero coefficient ring and its zero sheaves;
n=0 is excluded as required. Empty schemes and empty affine sources are not
excluded; the pointwise smooth-relative-dimension class is vacuous on the
empty source. There is no index set to restrict. Invertibility is the only
characteristic condition. All test schemes use the recorded arbitrary scheme
universe u; the coefficient ring and module sheaves use the dependency's u+1
convention. There is no extra equality of universes or unbound variable.

Independent searches: `msearch.py leanfinder` with “Affine smooth relative
dimension one morphism cohomological universal base change next degree” gave
eight geometric smoothness hits, no cohomological induction statement;
“Universal base change cumulative cohomology affine curve induction step” gave
eight unrelated Weierstrass base-change hits. `msearch.py loogle` with
`"BaseChangeProperty", "SmoothOfRelativeDimension"` gave zero hits.
`msearch.py grep` with `BaseChangeProperty|relativeDimensionOne_induction`
gave zero Mathlib hits. Direct rg searches of Mathlib's AlgebraicGeometry,
project lean/Sheaf and upstream WeilConjectures checked BC, curve induction,
`of_forall_lt`, and `forall_le_of_forall_le_sub_one` variants.
Read the whole upstream SmoothBaseChange/Induction.lean, including
`UniversalBaseChangeProperty.forall_le_of_forall_le_sub_one`. Its hypothesis
is a forall over all integer degrees ≤q-1 and an arbitrary annihilated ring;
it is not the node's bounded nonnegative hypothesis. The upstream
`of_forall_lt` also requires all negative degrees. They are useful stage-3
lemmas (negative vanishing bridges the interface), but neither is the exact
statement to record as existing. No second definition of a notion was added.

Read the proof-dependency records as well: smooth permanence uses the existing
Mathlib base-change stability and composition declarations; affine permanence
uses the existing affine base-change stability, affine-source lemma, separated
instance and finite-coproduct instance. Their source signatures match the
needed clauses. The two cohomological reduction/vanishing nodes have no
recorded declaration; they are proof dependencies only, so they introduce no
missing object into this signature. The module's proof docstring includes all
five DAG proof steps: failure datum, permanence, divisor invertibility,
vanishing contradiction, cumulative conclusion, with the horizontal map h in
the right role. The relevant statement/proof modules are imported as required.

No new definition nodes, dependency modules, statement corrections, hollow
definitions or proved helper theorems are present. The sole theorem proof is
`sorry`; module and declaration docstrings name the source and blueprint id.
Checked every binder and the verbatim node `lean.statement` against the file.
No mathematical or Lean mismatch was found; the module and node are unchanged.
Only this independent second-reading report was appended.

Validation: `scompile.py NN sbc-lem-rel-dim-one-induction
lean/Sheaf/AlgebraicGeometry/RelativeDimensionOneInduction.lean` passed on the
server, both sandbox and library checks (3.3 s and 3.6 s), without warnings.


## Maintainer search supplement (2026-10-15)

The immutable report above records LeanFinder, Loogle and grep, but omits the
LeanSearch kind required by coord/brief-stage2.md §1 (delivery-errors H4).
The independent maintainer reader supplied the missing attempt without changing
the worker's or NN second reader's account:

- Tool: lean-lsp MCP `lean_leansearch`.
- Exact query: “For an affine smooth morphism of relative dimension one with
  affine source, universal etale cohomology base change in all nonnegative
  degrees below q implies universal base change in degree q.”
- Actual result: `HTTP Error 500: Internal Server Error`; verdict: unavailable.
  This is not a successful search or evidence of no match.
- Independent `lean_loogle` query `"UniversalBaseChangeProperty"` returned
  `{"items": []}`. Direct rg searches of Mathlib AlgebraicGeometry, the project's
  lean/Sheaf and upstream WeilConjectures examined the node id, cumulative BC,
  relative-dimension-one induction and base-change/curve/induction variants.
  The upstream Induction.lean declarations were opened in full: their lower
  degree hypotheses range over all integers, unlike the delivered bounded
  natural-degree assumption. No exact existing statement was found.

Server-only reproducibility check of the immutable delivered file used
`scompile.py`'s `run_server` backend explicitly, since the current command-line
entry point first tries a local compiler. The server returned exit code 0:
`Sheaf/AlgebraicGeometry/RelativeDimensionOneInduction.lean: 2.9 s; nice 19;
2 threads; limit 60 s`, with no diagnostics. Its imported side dependencies
SmoothBaseChangeCoefficients, ChosenCartesianSquare, BaseChangeInverseImageIso
and CumulativeUniversalBaseChangeProperty also compiled separately (1.4, 1.5,
1.4 and 2.6 seconds). No local Lean compiler or global build was run.

The sole correction is this search/evidence supplement. All Lean text, the
node's statement and lean record, dependencies and the two original report
sections are preserved.
