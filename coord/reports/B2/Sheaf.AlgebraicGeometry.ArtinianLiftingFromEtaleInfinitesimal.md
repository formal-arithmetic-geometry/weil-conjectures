## What changed

Proved `AlgebraicGeometry.artinian_lifting_tests_of_etale_infinitesimal` in
`Sheaf.AlgebraicGeometry.ArtinianLiftingFromEtaleInfinitesimal`, preserving its signature
and every original public import. Added proof-only imports of
`Mathlib.RingTheory.HopkinsLevitzki` and
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`. The proof-only import
of `Sheaf.AlgebraicGeometry.FlatUnramifiedFormallyEtale` was already present.

Three proved private helpers establish the square-zero ring kernel, the corresponding
first-order thickening of spectra, and factorization of the Artinian test map through
an ideal power. The main proof constructs the pullback test map, invokes the existing
formal smoothness theorem, and verifies both projection equations. The node's proof
now describes this implementation. No statements, definitions, or other modules changed.

Read the item's node, all three dependency nodes and their Lean/Mathlib interfaces,
the unit record `sk-thm-p1`, and the proof of Stacks Tag 0A43 online (the local TeX
literature is not populated on this machine). This is the same infinitesimal lifting
argument, with the affine-chart computation expressed through the pullback ideal.
The node realizes no fixed unit statement or step; the unit's route is preserved.

Searches: Lean Finder for Artinian factorization found local-ring power bounds and
Artinian spectrum lemmas, but no scheme factorization theorem. Loogle `Module.length,
Ideal` returned length formulas, not a matching lifting result. The logged Mathlib
grep `IsFirstOrderThickening|liftSubscheme|subschemeLift` found no result. Direct library
search found the already-proved `Scheme.IdealSheafData.comap_pow`, which avoids
reimplementing affine chart glue.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.artinian_lifting_tests_of_etale_infinitesimal`
(node `lem-weil-pbc-etale-infinitesimal-artinian-tests`).
All three private helpers are completely proved. No `sorry` remains in the delivered
module; no holes or nodes were added.

The proof uses the existing named theorem
`AlgebraicGeometry.flat_unramified_formally_etale`
(node `lem-weil-pbc-flat-unramified-formally-etale`), whose own proof remains `sorry`
in the library. This is the intended existing proof dependency, not a new hole.
The theorem is closed relative to that dependency, not yet axiom-free globally.

The module compiles locally. The kernel proof only needs a local source ring and a
nontrivial target: its properness follows from the latter, rather than from
surjectivity. The factorization proof handles J = bottom and arbitrary non-Noetherian
S: only the Artinian test ring needs Noetherianity. It uses the exponent n+1, avoiding
any requirement that a chosen nilpotence exponent be positive. Empty Z cannot satisfy
hx. No new statement excludes any edge case of the original theorem.

## No longer needed

None. All three planned dependency nodes are used: unique primes, the Noetherian
component of the Artinian-ring theorem, and flat-unramified formal smoothness.
No original imports, nodes, or modules are pruned. The maximal-ideal computation on
an affine neighbourhood is replaced by a computation of the pulled-back ideal's
nilpotence on the affine test scheme; this requires no additional unfinished module.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. Mathlib's ideal-sheaf pullback powers theorem is absent
from Mathlib itself but already proved in the source library, so it is usable through
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`. The named flat-unramified
theorem's `FormallySmooth` conclusion must be given an explicit type when assigned to
a local `have`, to retain its implicit scheme parameters until application.

## Second reading by B2

1. Interface: compared the whole delivered module with the repository using `diff -u`,
   and checked the existing theorem signature byte for byte with a separate comparison.
   Verdict: unchanged. The scheme morphisms, closed immersion, ideal equality, all
   infinitesimal etaleness hypotheses, point condition, both Artinian local test rings,
   surjectivity, length-one kernel, commutative square, closed-point equation and both
   lift equations remain exactly those of the node. No definition, target statement,
   public import or other module changed; no change record is needed.
2. Proof: independently compiled the delivered file with `lcompile.py` (2.8 seconds,
   no errors or warnings) and the scratch copy with four `#print axioms` commands
   (3.4 seconds). Each private helper uses only `propext`, `Classical.choice`,
   `Quot.sound`; the main theorem additionally uses `sorryAx` through the already-open
   `flat_unramified_formally_etale`. Scanned for forbidden declarations and proof
   bypasses: none; no `sorry` occurs in the delivered file. Read `FormallySmooth` and
   `IsFirstOrderThickening` to check the precise lifting property. The factorization
   witness is constructed using an inverse of a proved isomorphism; no data is chosen
   from an unproved existence theorem. Verdict: a valid proof relative to the recorded
   existing dependency, closing one local hole and adding zero.
3. Split statements: none. Independently checked the three proved private helpers:
   a proper length-one kernel lies in its maximal-ideal annihilator; naturality of
   global sections transfers square-zero to the scheme kernel; full support on a
   one-point affine Artinian scheme gives a finitely generated nil ideal and hence
   a nilpotent pulled-back ideal. The exponent `n+1` handles an exponent zero;
   `J = bottom` is allowed, and no Noetherian hypothesis on the ambient scheme is
   introduced. Local rings are nontrivial, giving kernel properness. An empty `Z`
   makes the point hypothesis impossible. Verdict: no false, duplicate or circular
   split-off statement.
4. Route and pruning: read the dependency nodes, Mathlib interfaces and the unit's
   `realized` record, and independently read the factorization argument in
   [Stacks Tag 0A43](https://stacks.math.columbia.edu/tag/0A43). Searched Mathlib with
   the logged grep query `Etale.*lift|Smooth.*lift|formally.*smooth|length_eq_one|annihilator.*maximal`,
   inspected the Etale and Smooth scheme modules, and searched `lean/Sheaf` and
   `lean/WeilConjectures` for lifting and first-order-thickening results. The available
   Mathlib formal-smoothness results concern ring maps and stalks, not the needed
   scheme lifting property; no shorter existing direct proof was found. The proved
   source-library `comap_pow` is used rather than reproved. Each added import supplies
   a used result and is proof-only; original public imports expose notions in the
   unchanged signature. All three old proof-dependency nodes are used, so
   `No longer needed: None` is complete. This item is below the fixed unit steps;
   none of its three dependencies realizes a fixed step bypassed here. Verdict: the
   unit route is kept, with no modules or dependencies pruned.
5. Metadata: compared the old and delivered node records; only `proof` and
   `proof_origin` changed. Read each new proof step against the Lean helper and main
   proof; `proof_deps` is exactly the union of the steps' `uses`. Unique-prime facts,
   Artinian Noetherianity and the existing flat-unramified lifting theorem occur at
   the places described. No new nodes require metadata. Verdict: DAG agrees with Lean.

Changed in this second reading: corrected the report's inaccurate claim that the
flat-unramified import was newly added; it was already in the repository version.
No mathematical proof repair was needed.
