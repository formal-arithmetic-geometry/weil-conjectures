## What changed

Completed the earlier sandbox attempt in four modules. The unchanged statement
`AlgebraicGeometry.Scheme.affine_support_iterated_cones` now follows from three finite-index
inductions: perfectness, support propagation, and the binomial restriction formula.
Its proof imports `ScalarConeStalkVanishing`, `RestrictedScalarConeSplit`, and
`BinomialShiftBiproduct` in addition to the existing `PerfectTwoOutOfThree`.
The latter's first implication is used with both perfect input terms equal to C_k.
All new imports in the item are proof-only imports. No existing signature, visibility,
definition, or target statement changes, and no other existing module is adapted.

`BinomialShiftBiproduct` constructs the Pascal bijection, proves injectivity and surjectivity,
constructs the sum-index biproduct isomorphism by inclusions and projections, and composes
with shift and reindexing isomorphisms. Its public theorem is completely proved.
The two geometric single-cone assertions are new named public statements with complete
proofs in words and matching nodes. They isolate steps 2 and 3 of the original argument;
neither restates the iterated theorem, and neither assumes the iterated conclusion.

All four modules compile through lcompile.py. The explicit axiom check for
`AlgebraicGeometry.Scheme.binomial_shift_biproduct` reports only `propext`,
`Classical.choice`, and `Quot.sound`. The main theorem still depends on the two listed
geometric holes (and on the pre-existing dependency closure of perfectness).

Edge cases checked: s=0 has no support witnesses and the restriction formula is the initial
binomial isomorphism. The proved Pascal bijection handles n=0, the left endpoint j=0,
the right endpoint j=n+1, and zero multiplicities. A unit scalar gives an acyclic cone;
an acyclic input gives an acyclic cone for any scalar. The restricted splitting statement
also applies to an empty finite family, a zero F, an empty U, and arbitrary integer shifts.
No affine, perfectness, or compactness condition is required for those single-cone facts.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.affine_support_iterated_cones`
(node `lem-sc-affine-support-iterated-cones`). This is a decomposition from two
strictly smaller geometric statements, not a sorry-free proof of the entire dependency
closure. Its combination of the parts is a complete Lean proof with no internal holes.

Additionally proved `AlgebraicGeometry.Scheme.binomial_shift_biproduct`
(node `lem-sc-binomial-shift-biproduct`), including all private helpers. It adds no hole.

Added and left exactly these two whole-theorem holes:

- `AlgebraicGeometry.Scheme.scalar_cone_stalk_vanishing`
  (node `lem-sc-scalar-cone-stalk-vanishing`, module `ScalarConeStalkVanishing`).
- `AlgebraicGeometry.Scheme.restricted_scalar_cone_split`
  (node `lem-sc-restricted-scalar-cone-split`, module `RestrictedScalarConeSplit`).

There is no sorry left in the item. Original holes closed: 1. New holes: 2.
The direct hole balance is therefore -1; this delivery records a decomposition rather
than claiming a net reduction of holes. No data is chosen from an unproved mere-existence
statement. All chosen isomorphisms are proof witnesses used to prove propositions.

## No longer needed

No original item import or original proof-dependency node is removed:
`PerfectTwoOutOfThree` is needed for the perfectness induction, and the four public imports
support the unchanged signature. The unit's route is retained.

Removed the unused public import `Sheaf.AlgebraicGeometry.PerfectComplex` from the new
`RestrictedScalarConeSplit` module of the earlier attempt; `DerivedGlobalScalar` supplies
its statement's derived categories and restriction functor. This eliminates that new
module's proposed dependency on `def-pc-perfect-complex`; the item still needs that node.
No pre-existing module is shown globally unreachable by this delivery. No separate
binomial-counting, zero-cone, or principal-open support modules are imported beyond
those explicitly listed: the counting is proved here, and the two geometric parts
are the remaining new items.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt had compiling Lean but no node files and no report, so it was not a
reviewable delivery. This completion supplies those records and updates the item's
`proof`, `proof_deps`, and `proof_origin` to agree with the actual code.

The original DAG treats the support and splitting arguments as elementary, but their
Lean glue is substantial: it includes exact stalks, compatibility of localized scalar
actions, linear shifts, and split distinguished triangles. Those precise single-cone
facts are the two remaining named tasks. Searches of WeilConjectures, Sheaf, the DAG,
and Mathlib found supporting general machinery, but no existing theorem with either
full single-cone signature. LeanSearch was attempted separately for all three new nodes
and returned Internal Server Error; that unavailability is recorded without a negative
search verdict. LeanFinder and source grep results are recorded for each node.

Sources were read at [Stacks 08EK](https://stacks.math.columbia.edu/tag/08EK),
[05QR](https://stacks.math.columbia.edu/tag/05QR),
[05QS](https://stacks.math.columbia.edu/tag/05QS), and
[05QT](https://stacks.math.columbia.edu/tag/05QT).
The new splitting docstring uses 05QT for its actual split-triangle assertion, after
rotation; 05QT does not itself state uniqueness of cones.

Source discrepancy: the displayed formula in 08EK has coefficients choose(s,j), but
starting at F plus F[1] and taking s zero cones gives coefficients choose(s+1,j).
Already at s=1 the source first computes F plus two copies of F[1] plus F[2], whereas
the later display would give only F plus F[1]. The project's existing statement has
the correct coefficients; it is preserved exactly. The source discrepancy does not
alter the unit statement or its route.

## New nodes

`lem-sc-scalar-cone-stalk-vanishing`: the two ways a single scalar cone becomes acyclic
at a point. Source: 08EK's support argument and the cone-of-isomorphism assertion 05QR.
This isolates support step 2 and supplies the induction's propagation case.

`lem-sc-restricted-scalar-cone-split`: one scalar cone restricts to input plus shifted
input when its restricted input is a finite sum of shifts annihilated by the scalar.
Source: 08EK and the split-triangle calculation 05QT, with 05QR/05QS explaining the
zero-map cone. This isolates the geometric part of step 3, without binomial counting.

`lem-sc-binomial-shift-biproduct`: the initial and successor identities for binomial
sums of shifts. Source: 08EK's binomial expansion, with the correct exponent counted
from the initial F plus F[1]. The entire new node is proved in Lean using Mathlib's
biproduct reindexing, shift addition, and Pascal's rule. No change records are needed.

## Second reading by Q1

1. Interface preservation — PASS. Compared the delivered item with the repository using
   diff, and separately compared the full existing theorem signature byte for byte:
   identical. Only its proof and three proof-only imports change. All other delivered
   modules and nodes are new. No target, existing definition, visibility or hypothesis
   changes; no change record or forced adaptation is needed.
2. Kernel and holes — PASS as a decomposition. Independently compiled all four files
   in import order through lcompile.py. Checked #print axioms in temporary copies of
   each module. binomial_shift_biproduct uses exactly propext, Classical.choice and
   Quot.sound. The main theorem and both single-cone lemmas additionally use sorryAx;
   no other axiom appears. The only two delivered sorries are the named public
   scalar_cone_stalk_vanishing and restricted_scalar_cone_split, each with its node
   and full docstring argument. No forbidden declaration or hollow definition occurs.
   Equiv.ofBijective uses fully proved bijectivity; the isomorphisms from open lemmas
   are used only as witnesses inside proposition proofs, never to define data.
3. Split statements — PASS. Checked both single-cone statements against their types
   and mathematical arguments. A unit germ is invertible on every stalk module,
   independent of affine or perfectness hypotheses; an acyclic input gives an acyclic
   cone. A zero scalar stays zero under integer shifts and finite biproducts; exact
   restriction preserves its triangle, and rotating gives a zero last map, to which
   the split-triangle lemma applies. Checked zero objects, empty schemes and opens,
   empty finite families, scalar zero, unit scalar and negative shifts. For s=0 the
   main support assertion is vacuous and its splitting assertion is the base formula;
   for s=1 multiplicities are 1,2,1. Read the Pascal bijection including n=0 and both
   endpoints. Each new hole is one local cone step, strictly smaller than the item.
   Independent searches with different wording found derived homology exactness,
   exact stalk machinery and exists_iso_binaryBiproduct_of_distTriang, but no complete
   single-cone theorem in Mathlib, WeilConjectures or Sheaf. Scalar restriction and
   stalk comparisons are substantial glue, so neither open theorem closes in a few
   minutes by an existing lemma.
4. Route and pruning — PASS. Read the three inductions from the top down and checked
   every application and the off-by-one binomial exponent. PerfectTwoOutOfThree remains
   used, so every old proof dependency is retained and No longer needed is complete.
   Public imports supply statement vocabulary; new proof dependencies in the item
   are plain imports. No auxiliary elementary module is imported unnecessarily.
   Inspected dag/units/sk-thm-picard-duality.json: its realized statement and steps
   contain no realization by this item, which is below the unit level. Its existing
   route and the perfectness/support/binomial argument are retained.
5. DAG agreement — PASS after repair. Compared every node lean.statement with its
   module signature after whitespace normalization; all four agree. The existing
   node changes only proof, proof_deps and proof_origin, and these name exactly the
   perfectness, support and restriction/binomial declarations the proof applies.
   Checked the new node sources, provenance, searches, created, blueprint, chapter,
   unit, status and Lean records. New holes have complete natural-language proofs.
   Corrected the cyclic misassignment of the original LeanSearch requests and two
   grep requests using searches.jsonl, then added independent supporting searches.

Second-reading changes: corrected new-node search records and added independently
verified search results; simplified the restricted_scalar_cone_split docstring to
rotation followed directly by Tag 05QT, naming the existing Mathlib splitting lemma
and the orientation of its isomorphism. No Lean signature or proof term changes.
The source coefficient discrepancy was independently verified in
[Stacks 08EK](https://stacks.math.columbia.edu/tag/08EK); the splitting argument was
checked against [Stacks 05QT](https://stacks.math.columbia.edu/tag/05QT), and unit-cone
vanishing against [Stacks 05QR](https://stacks.math.columbia.edu/tag/05QR).
Original holes closed: 1; holes added: 2; direct balance: -1. This delivery is a
reviewed decomposition, together with a fully proved binomial auxiliary theorem.
