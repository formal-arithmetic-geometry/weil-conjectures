## What changed
Replaced the target's `sorry` by an explicit homogeneous cochain construction. Proved
joint continuity of the discrete Galois action using Krull-open algebraic stabilizers,
converted the multiplicative identity with `Units.ext`, and checked the alternating
homogeneous differential. Used Mathlib's concrete kernel isomorphism to construct the
cycle and prove its required evaluation. The construction is a local argument for an
abstract coefficient ring and representation, so elaboration does not repeatedly unfold
the concrete Galois representation. Existing signatures and docstrings are unchanged.
Added proof-only imports `Mathlib.FieldTheory.Galois.Profinite` and `Mathlib.Tactic.Abel`.
The transparency option is scoped to the existing theorem. No file-level linter change,
public import addition, new declaration, or change record is needed.

## Proved and sorry left
Closed `Field.exists_galoisUnits_cocycle_of_scalar_cocycle` (one of one original holes).
There are no remaining or added holes. The abandoned first-reader splits
`Field.additive_cocycle_condition` and
`Field.exists_homogeneous_cocycle_of_additive_cocycle` are not delivered: both arguments
are now proved locally, and their two proposed modules and nodes have been removed.
This is a proof with net one hole closed, not a decomposition.

## No longer needed
Removed the redundant direct import `Sheaf.FieldTheory.GaloisUnitsCohomology`: the public
import `Sheaf.FieldTheory.BrauerScalarDefect` already exposes it. Both original DAG proof
dependencies, `def-sc-brauer-scalar-defect` and `def-sc-galois-units-cohomology`, remain
used. No original dependency node or module is pruned from the target closure.
The proposed imports of `Sheaf.FieldTheory.GaloisUnitsCocycleRealization` and
`Sheaf.FieldTheory.GaloisUnitsAdditiveCocycle` have been removed together with those
unlanded modules. The delivered proof does not import the homogeneous-descent module.

## Where the brief, the DAG or earlier work was wrong
The first worker's homogeneous helper moved the whole realization problem to additive
notation without proving the construction. Its node and the additive helper's node also
copied the original target statement rather than stating their Lean conclusions. Their
inherited review fields did not certify these new statements. The first report's claim
that these were strictly simpler reductions was incorrect. Removed both splits.
The upstream library's public `Nonempty` cochain equivalence does not specify evaluation,
so it cannot prove this exact evaluation conclusion directly. Its private construction
and action-continuity proofs supplied the pattern for the complete local argument.
Searches using Loogle (`HomologicalComplex.cyclesMk`) and LeanFinder (continuous
representation kernel reconstruction from inhomogeneous cochains), plus `rg` on
`lean/Sheaf/FieldTheory` and `lean/WeilConjectures/FieldTheory`, found concrete kernels
and algebraic cohomology constructors, but no public continuous constructor with the
needed evaluation property. `cyclesMk` requires an abelian category, whereas the proof
here uses the kernel universal property in `TopModuleCat`.

## Second reading by M3
1. Compared the delivered module with the repository version. The sole existing theorem
signature is byte-for-byte identical, and its docstring is unchanged. No definition,
hypothesis, conclusion, visibility, or target statement changes. Verdict: pass.
2. Compiled the final file and a scratch copy with `#print axioms` through `lcompile.py`.
No `sorry`, axiom, unsafe declaration, opaque declaration, extern, implemented_by, or
hollow definition occurs in the delivered file. The coefficient cochain is explicit;
the cycle is obtained via the inverse of a proved kernel isomorphism, which determines
it uniquely by its inclusion. The scratch axiom check lists only `propext`, `Classical.choice`, and `Quot.sound`.
Verdict: pass.
3. Read both proposed split statements and searched alternatives with different queries.
Removed them and their malformed nodes. The local construction works for arbitrary
continuous two-cocycles, including the trivial group and nonnormalized constant
cocycles; it imposes no normalization or finite-range assumption. Verdict: pass.
4. Kept the original top-down homogeneous construction, using Mathlib's kernel API.
Removed every unused/redundant import. The original two proof-dependency nodes remain,
and `dag/units/sk-thm-br.json` and its realized fields are unchanged; no unit step is
bypassed. Verdict: pass.
5. Updated only the existing node's proof steps to describe continuity, the additive
identity, equivariance, differential calculation, kernel lift, and evaluation. Its
proof_deps, statement, source, proof_origin, chapter, and unit are retained. No new
nodes remain. Verdict: pass.
Second reading changed the attempted decomposition to a complete proof, removed both
new modules and nodes, removed the redundant direct import, eliminated file-level
linter changes and the unnecessary change record, and corrected the report and DAG.
