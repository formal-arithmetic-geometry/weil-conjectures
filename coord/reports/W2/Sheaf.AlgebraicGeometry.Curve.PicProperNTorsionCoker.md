## What changed

Simplified the proof of `AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker`
in `Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker`. It now composes the actual
Picard degree homomorphism with integer cast modulo n. Degree surjectivity supplies
a degree-z class M; degree-zero divisibility supplies an nth root R of L / M^n;
then (R*M)^n = L. This removes the product splitting, transport to a subtype,
and both uses of the inverse product equivalence. The first isomorphism theorem
completes the quotient calculation. Updated the existing node's proof and origin.
All signatures, visibility, imports, definitions and existing docstrings stay identical.
The existing docstring gives the valid splitting argument; the inline comment explains
that this implementation uses just its surjectivity part.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker`
(node `lem-sc-pic-proper-ntorsion-coker`) compiles with a complete proof.
The assigned baseline already contains no local sorry: holes closed 0; holes added 0;
local sorries left none; split-off statements none. This is a listed repair and proof
simplification, not new net hole progress. Existing dependency holes are not claimed
closed. The second reader’s explicit `#print axioms` reports `propext`,
`Classical.choice`, `Quot.sound`, and inherited `sorryAx`; this is a complete
local proof, not an axiom-clean proof of the full dependency closure. The unchanged field-cast assumption excludes n = 0; n = 1 is included and
both quotient and ZMod 1 are trivial. No new statement needs an edge-case check.

## No longer needed

The proof no longer uses `Scheme.exists_mulEquiv_prod_ker_picDegreeHom`, its
product equivalence, or the nth-power surjectivity theorem for the degree-kernel
subtype constructed locally in the previous proof. It also does not need the
Sheaf splitting wrapper `Scheme.Hom.exists_mulEquiv_prod_picZero` or its
module `Sheaf.AlgebraicGeometry.Curve.PicardDecomposition` (already absent
from the baseline imports). No import was removed in this delivery:
`WeilConjectures.AlgebraicGeometry.Curve.Picard` still supplies degree
surjectivity and the kernel identification. The decomposition node remains
recorded because its degree-surjectivity assertion is used, but its full splitting
conclusion is unnecessary here. The divisibility node remains needed. No module
is claimed globally unreachable. The curve-estimate unit's route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic brief says this module contains sorry; it is already fully proved.
`coord/repairs.txt` instead queues upstream duplicate review #1428. The proposed
replacement `Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient` and module
`WeilConjectures.AlgebraicGeometry.Curve.Jacobian` are absent from the supplied
repository. Searching `lean/WeilConjectures` and `lean/Sheaf` finds no replacement.
The earlier N2 report already records this mismatch. Deleting the public theorem
or repointing its caller to that absent declaration would break the library.
This delivery therefore preserves the interface and simplifies the existing proof;
the upstream duplicate request still requires reconciliation with the supplied revision.

Read the node, all six recorded dependency statements and attachments, the actual
source degree/splitting signatures, divisibility implementation, and unit realization.
LeanFinder returned eight unrelated class-group/elliptic-curve results; Loogle found
Mathlib's first isomorphism theorem; the launcher grep query returned no hits.
Direct rg found the available degree-surjectivity declaration and the sole cokernel
caller in PicProperNTorsion. No new dependency or node is needed.


## Second reading by W2

1. Compared the entire delivered module and existing node with the repository using
   `diff -u`. The only Lean difference is inside the body of
   `Scheme.Hom.pic_proper_ntorsion_coker`. Its signature, universe, visibility,
   imports and existing docstrings are byte-for-byte unchanged; there are no data
   definitions or other delivered modules. The node differs only in `proof` and
   `proof_origin`. Verdict: no accidental interface or target change.
2. Compiled the delivered file with the required `lcompile.py`: clean, 3.3 seconds.
   Searched its Lean sources for sorry and forbidden declarations: none.
   Compiled a scratch copy with explicit `#print axioms` for the cokernel theorem:
   only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The last is
   inherited through existing dependencies, not introduced by this proof.
   The witnesses M and R are local to a theorem proving `Nonempty`; no object is
   defined by arbitrary choice from an unproved existence theorem. Verdict: valid
   complete local proof, with the existing dependency holes honestly retained.
3. There are no split-off statements, new declarations, or new nodes. Checked the
   algebra in both kernel inclusions: nth powers map to zero in ZMod n; if degree
   is n*z, surjectivity supplies M of degree z, divisibility applies to L/M^n,
   and commutativity gives (R*M)^n = L. The field-cast assumption rules out n=0;
   n=1 makes the quotient and ZMod 1 trivial. Connectedness supplies nonemptiness,
   so the degree-surjectivity theorem's Nonempty assumption is available.
   Verdict: no disguised restatement, false auxiliary lemma, or new hole.
4. Read the source-library `picDegreeHom`, `coe_ker_picDegreeHom`,
   `surjective_picDegreeHom` and the full splitting theorem in Curve/Picard.lean,
   the degree-zero divisibility implementation, and the PicProperNTorsion caller.
   Independently searched for `nonempty_addEquiv_torsionBy_pic_and_quotient` and
   related Picard quotient names throughout lean/WeilConjectures and the relevant
   Sheaf files: the alleged upstream replacement is absent. Loogle confirmed
   Mathlib's `QuotientGroup.quotientKerEquivOfSurjective`; direct Mathlib search
   found the product-quotient API, which requires the unnecessary product route.
   Both proof-only imports are used; public imports provide signature vocabulary.
   No old proof dependency becomes wholly unused: decomposition still supplies
   its stated degree-surjectivity assertion. The unused full splitting is listed
   above; no module is claimed pruned. Checked `sk-thm-curveestimate.realized`:
   its proper-cohomology statement realization and route are preserved.
   Verdict: the direct degree argument is appropriate and no shorter available
   geometric theorem was found. The duplicate-review request remains unresolved
   for this supplied revision, as the first worker already reports.
5. Read all six old proof-dependency statements and Lean attachments. The smooth
   regularity and connected-regular integrality inputs provide the irreducibility
   needed for smooth relative dimension one. The decomposition statement explicitly
   includes degree surjectivity; `coe_ker_picDegreeHom` supplies the recorded
   degree-zero identification. The divisibility statement applies with exactly
   the original f, n and nonzero-cast hypothesis. The second node step records
   this divisibility use and the elementary kernel algebra followed by the first
   isomorphism theorem. The union of step uses equals `proof_deps`.
   Verdict: node metadata agrees with the proof and no new-node fields are needed.

Second reading changed only this report: added the explicit axiom limitation and
this point-by-point independent review. No Lean or node repair was necessary.
The blueprint literature files are absent on this machine; source comparison used
its imported DAG statement, the parent node, the unit record, and the available
Lean source and caller rather than claiming to read the missing literature file.
