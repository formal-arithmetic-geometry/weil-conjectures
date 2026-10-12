## What changed

Proved `Algebra.Generators.principal_localization_naive_cotangent` in
`lean/Sheaf/AlgebraicGeometry/PrincipalLocalizationNaiveCotangent.lean`, with its entire
signature and visibility unchanged. Mathlib supplies the kernel equality, conormal splitting,
and the composition cotangent-space basis. The proof chooses the actual relation `fx-1`,
checks both specified inverse formulas, constructs a linear shear fixing the old summand,
and proves the commuting-square equation by naturality and the new coordinate calculation.
It then proves injectivity in both directions and constructs the cokernel equivalence from a
surjective quotient projection whose kernel is precisely the new differential's range.

Replaced the proof-only import of `Sheaf.RingTheory.KaehlerDifferentialsPolynomialExtension`
with `Mathlib.LinearAlgebra.Isomorphisms` for the quotient first isomorphism theorem. Updated
only `proof`, `proof_deps`, and `proof_origin` of the item's DAG node to reflect this route.
No definitions, public imports, target signatures, or other modules were changed.
Single-file launcher compilation passed without errors or warnings. A temporary `#print axioms`
check reported exactly `propext`, `Classical.choice`, and `Quot.sound`; the check line was then
removed. Text checks confirm the entire theorem signature is identical and all lines meet
the 100-character limit.
The existing declaration docstring describes the original plan; inline comments identify
where the Mathlib construction shortens that plan.

## Proved and sorry left

Closed the sole hole: `Algebra.Generators.principal_localization_naive_cotangent`
(node `lem-weil-pbc-principal-localization-naive-cotangent`).
All clauses are proved, including the generator formulas, differential compatibility,
injectivity equivalence, and cokernel equivalence. No holes remain in this module and no
holes or declarations were added elsewhere. This is a complete proof, not a decomposition.

## No longer needed

Removed import `Sheaf.RingTheory.KaehlerDifferentialsPolynomialExtension` and proof dependency
`lem-weil-pbc-kahler-differentials-polynomial-extension`. Neither its theorem
`KaehlerDifferential.exists_polynomial_extension_equiv` nor its finite-rank conclusion is
needed: Mathlib's `Algebra.Generators.CotangentSpace.compEquiv` gives the required splitting
for the actual polynomial presentations, already after scalar extension. This removes that
module from this item's imports; other items may still require it.

The coefficient-map kernel, localization quotient, and conormal injection leaves remain in
the DAG because the Mathlib kernel and conormal equivalence package those arguments. No
unit statement or realized unit step is bypassed. No other original import was removed.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement is correct. The earlier search report underestimated the available
Mathlib API: `CotangentSpace.compEquiv` supplies clause (2), and together with the existing
conormal equivalence, naturality, and a linear shear it also yields clause (3). The full
statement is not a single existing Mathlib lemma, but needs no new intermediate theory.

Searches: launcher Lean Finder query on composition polynomial-generator cotangent spaces;
launcher Loogle query `Algebra.Generators.CotangentSpace.compEquiv`; `rg` searches of
Mathlib's localization, Jacobi-Zariski, cotangent basis, quotient, and linear isomorphism
files, plus the local WeilConjectures and Sheaf trees. The implementation follows the
source proof recorded in the node and the checked Mathlib source; the referenced Stacks
TeX file is absent from this machine's literature directory.

The argument imposes no nonzero-ring, nonzero-g, finiteness, or nonempty-index hypothesis.
Unit cancellation works also when the localized ring is the zero ring. In particular `g=0`
and empty generator index types are covered by the same proof.

Delivery verification (2026-10-13): the previously reported launcher import and
Mathlib source-root failures were repaired externally. The prescribed command
`python3 /home/ubuntu/weil-launcher/deliver3.py Y2
Sheaf.AlgebraicGeometry.PrincipalLocalizationNaiveCotangent --no-push` now prints
`OK (dry run)`: compilation and preflight pass, with only the independent second
reading still to be supplied by the second reader. Nothing was pushed. No project
or launcher tool was modified, and no check was bypassed.

This retry also checked the retained proof against the repository: its theorem
signature is unchanged, it has no sorry tokens, every Lean line is at most 100
characters, and the node changes only `proof`, `proof_deps`, and `proof_origin`.

## Second reading by Y2

1. **Unchanged interface: PASS.** Read the full module and its `diff -u` against the
repository. The only changes are the proof-only import, two theorem-local elaboration
options, and the proof replacing `sorry`. Independently compared the entire theorem
signature byte for byte: identical. No definition, declaration visibility, public import,
or target statement changed; no change record is required.

2. **Kernel-checked proof: PASS.** Independently compiled the delivered module through
`lcompile.py` with no errors or warnings (17.7 seconds). Compiled a scratch copy with
`#print axioms Algebra.Generators.principal_localization_naive_cotangent` (22.4 seconds):
exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Checked the
source for forbidden tokens and holes: none. The relation `r` is explicitly `fx-1`,
not an arbitrary witness. The only chosen unit has prescribed value equal to the
image of `g`, so its inverse is uniquely determined; all equivalences are constructed
from proved Mathlib results and an explicit invertible linear shear.

3. **Split-off statements: PASS (none).** No new statements, modules, nodes, or holes
were introduced. Checked every clause of the original statement, including both
inverse formulas, the old-summand formula for `e0`, differential compatibility, both
injectivity directions, and the orientation of the quotient equivalence. The proof
uses only invertibility of the image of `g`, not nonzeroness. For `g=0` the localization
is the zero ring and cancellation by its unit remains valid; empty generator types
and an already invertible `g` introduce no exceptional case.

4. **Shortest route and pruning: PASS.** Read Mathlib's localization conormal
equivalence and its two inverse formulas, and the composition cotangent-space basis
equivalence, projection, and differential naturality in `JacobiZariski.lean`.
Independently searched Loogle for `CotangentSpace.compEquiv` and searched the local
Sheaf/WeilConjectures algebraic-geometry sources. The existing Mathlib splittings
are used directly, with no redundant intermediate statements. The public localization
import supplies the signature; the private isomorphism import supplies the quotient
first isomorphism theorem. The sole removed old proof dependency and import,
`lem-weil-pbc-kahler-differentials-polynomial-extension` /
`Sheaf.RingTheory.KaehlerDifferentialsPolynomialExtension`, is fully listed above.
Read `dag/units/sk-thm-p1.json` and searched all unit records: neither the removed
node nor this lower node is a realized unit statement or step. The unit's route stays
intact. The retained coefficient-kernel, localization-quotient, and conormal-injection
leaves are packaged inside the Mathlib theorems used, as the node explains.

5. **DAG fidelity: PASS.** Independently diffed the node: only `proof`, `proof_deps`,
and `proof_origin` changed. The union of the proof steps' `uses` equals `proof_deps`.
The six steps match the explicit relation, conormal splitting, differential-space
splitting, shear and naturality calculation, injectivity argument, and quotient-kernel
argument in Lean. Agent proof origin accurately records the Mathlib implementation
of the source argument. There are no new nodes to validate.

**Second-reader changes:** appended this independent review and its verification
evidence only. No mathematical or Lean repair was needed. The original docstring
remains an explicitly labelled eight-step stage-3 plan; the proof's inline comments
and updated node explain how Mathlib shortens its implementation.
