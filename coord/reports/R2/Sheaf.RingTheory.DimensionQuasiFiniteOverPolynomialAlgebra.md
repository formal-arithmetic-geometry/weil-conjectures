## What changed

Proved `AlgebraicGeometry.topologicalKrullDim_spec_le_of_quasiFinite_over_mvPolynomial`
in `Sheaf.RingTheory.DimensionQuasiFiniteOverPolynomialAlgebra`, with its original signature
and public imports unchanged. The supplied map induces the local algebra structure; its
finite-type and quasi-finite hypotheses feed the existing local dimension inequality.
Both local dimensions are rewritten as heights. The contracted prime's height is bounded
by the global polynomial ring dimension, which Mathlib computes as `n`. The spectrum/ring
dimension equality and the supremum-of-heights criterion finish the proof.

Replaced the proof import `Sheaf.RingTheory.PolynomialRingMaximalLocalizationDimension`
by the proof import `Mathlib.RingTheory.KrullDimension.Polynomial`. The redundant
explicit `Mathlib.RingTheory.KrullDimension.Zero` import was removed on second reading:
Polynomial already publicly imports PID, which publicly imports Zero. Retained the proof import
`Sheaf.RingTheory.QuasiFiniteLocalDimension`. Updated the theorem docstring and its node's
`proof`, `proof_deps`, and `proof_origin`; no definition or statement changed.

Searches: Lean Finder found the height/localization and spectrum-dimension identities;
Loogle and grep confirmed `ringKrullDim_le_iff_height_le`. Read the Mathlib proofs and
searched both library roots for existing dimension comparisons. Read Stacks Tags
[00QG](https://stacks.math.columbia.edu/tag/00QG) and
[00OP](https://stacks.math.columbia.edu/tag/00OP) on their canonical pages; the local
literature copy is absent on this machine. The selected route stays below the unit level:
none of the removed dependencies occurs in `sk-thm-p1.realized`.

## Proved and sorry left

Closed the module's only hole:
`AlgebraicGeometry.topologicalKrullDim_spec_le_of_quasiFinite_over_mvPolynomial`
(node `lem-weil-pbc-dimension-quasi-finite-over-polynomial-algebra`).
Added zero holes and zero intermediate modules. No `sorry` remains in the delivered module.
This is a proof from existing declarations, not an assertion that its dependency closure
is sorry-free: it still uses `Algebra.ringKrullDim_le_of_isQuasiFiniteAtPrime`
(node `lem-weil-pbc-dimension-inequality-quasi-finite`) from
`Sheaf.RingTheory.QuasiFiniteLocalDimension`, whose existing proof is `sorry`.
That declaration was neither copied nor changed.

Local compilation passed without warnings. Edge cases are covered by the existing Mathlib
identities: `n = 0` computes the source dimension as zero, and the zero ring `T` has
no primes, so the universal height bound is vacuous and its spectrum dimension is bottom.
No nontriviality or injectivity assumption was added.

## No longer needed

Removed the direct import `Sheaf.RingTheory.PolynomialRingMaximalLocalizationDimension`
and the direct proof dependency
`lem-weil-pbc-polynomial-ring-maximal-localization-dimension`: bounding the polynomial
ring globally avoids computing the dimensions of its maximal localizations.

Removed direct proof dependency `lem-weil-pbc-proper-ideal-contained-in-maximal`
(Mathlib `Ideal.exists_le_maximal`): no maximal ideal is chosen.

Removed direct proof dependency `lem-weil-pbc-spec-irreducible-closed-subsets-primes`
(Mathlib `PrimeSpectrum.closure_singleton` and
`PrimeSpectrum.pointsEquivIrreducibleCloseds`): the already proved spectrum/ring dimension
identity replaces the explicit irreducible-closed-chain conversion.

Removed the direct proof edge to `def-kun-topological-krull-dimension`; it remains a
statement dependency and is encapsulated by the spectrum/ring dimension identity.

The localization/height node remains used. No claim is made that any removed module
becomes unreachable from all other targets; this delivery prunes the item's direct route.
No public statement import was removed.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The DAG's maximal-ideal detour was
unnecessary: the source local dimension bound follows directly from prime height at
most ring dimension and Mathlib's polynomial dimension computation. Its explicit final
prime-chain argument is already available as Mathlib's height criterion, including the
empty spectrum. No unit statement or realized unit step is bypassed.


## Second reading by R2

1. **Unchanged interface: PASS.** Compared the only delivered Lean module with the
   repository using `diff`; independently compared the existing theorem signature as
   literal text through `:= by`. It is byte-for-byte identical. The namespace, universes,
   visibility, public imports, definitions, and hypotheses are unchanged. No change record
   is needed. The only other delivered source file is the existing node's proof update.
2. **Proof and axioms: PASS.** Local compilation succeeded without warnings. No `sorry`
   remains in this module; no forbidden declaration or data construction was introduced.
   A scratch copy with `#print axioms` reports exactly `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The latter comes from the unchanged, explicitly reported
   `Algebra.ringKrullDim_le_of_isQuasiFiniteAtPrime`, not a new hole. The induced algebra
   and finite-type instances match the hypotheses' local instances. Reviewed the actual
   Mathlib height/localization and spectrum-dimension identities and polynomial theorem.
3. **Split-off statements: PASS (none).** No new declaration, node, or module is added.
   The existing local inequality is a strictly smaller part of this argument. Checked
   `n = 0` and the zero target ring: the field computation gives zero, and the height
   criterion is vacuous when there are no primes. There is no hidden nontriviality or
   injectivity assumption and no arbitrary witness chosen from an unproved theorem.
4. **Route and pruning: PASS after import cleanup.** Independently searched Lean Finder
   for dimension under finite-type maps with zero-dimensional fibres, and searched both
   library roots and Mathlib with dimension/quasi-finite and height terms. No direct
   proved ring inequality was found. Read the upstream scheme comparison: its equality
   theorem requires universally closed and surjective maps, which are absent here;
   its continuous-map comparison would require a separate fibre argument. The current
   local-height reduction is short and matches the existing planned local inequality.
   Checked all old proof dependencies against the report's pruning list. Checked
   `dag/units/sk-thm-p1.json`: no removed node is a realized statement or step, so the
   unit route is preserved. Removed the redundant proof import of KrullDimension.Zero,
   already transitively public through Polynomial and PID. Kept all public imports.
5. **DAG agreement: PASS.** Compared the node with its repository version: only `proof`,
   `proof_deps`, and `proof_origin` differ. The dependency list is exactly the union of
   the proof steps' uses. The localization-height, spectrum-dimension, and
   supremum-height nodes match the Mathlib declarations used; the polynomial calculation
   is an explicit specialization of the cited proved Mathlib theorem. The original node
   statement, source, unit, and Lean record are unchanged.

Second reading changed only the redundant proof import and this report; the proof and
node update were retained. Closed one existing hole, added zero holes, split off zero
statements. This does not certify a sorry-free dependency closure.
