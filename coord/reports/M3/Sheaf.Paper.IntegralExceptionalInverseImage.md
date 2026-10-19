## What changed

Filled eight of the twelve original proof holes without changing any existing declaration signature or definition. Added private categorical uniqueness helpers and proof-only imports of Mathlib.CategoryTheory.Adjunction.Unique and Mathlib.CategoryTheory.Preadditive.AdditiveFunctor. The preserved module compiled without warnings on the project server (22.2 seconds) on 2026-10-19.

## Proved and sorry left

Closed: WeilConjectures.integralExceptionalIdeal; WeilConjectures.integralExceptionalRingMap_comp; WeilConjectures.integralExceptionalCoordinates_comm; WeilConjectures.integralExceptionalCoordinates_laws; WeilConjectures.integralExceptionalCoordinatesInv_additive; WeilConjectures.integralExceptionalComparison_characterization; WeilConjectures.integralExceptionalSupport_characterization; WeilConjectures.integralExceptionalAdjoint_characterization.

Remaining original holes: WeilConjectures.integralExceptionalCoordinates_properties; WeilConjectures.integralExceptionalComparison_exists; WeilConjectures.integralExceptionalSupport_exists; WeilConjectures.integralExceptionalInverseImage_on_ctf. All belong to node def-pur-adic-exceptional-system-realization. No holes added; no split statements.

## No longer needed

None. Existing public imports remain necessary for the unchanged definitions and signatures. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The item node has an empty proof and proof_deps; the arguments are in the declaration docstrings. The generic system comparison theorem returns its own etale evaluation package, whereas integralExceptionalComparison_exists quantifies over an arbitrary package. Its use requires a package transport construction. The etale adjoint theorem is stated for the integer ring of a coefficient field in Type (u+1), whereas this item uses ULift of the integer ring of E in Type u; these rings are canonically isomorphic but not definitionally equal.

A first resumed compile request received no answer from the compile server within 188 seconds. The next request compiled the preserved module successfully in 22.2 seconds.

Resumed session, 2026-10-19: the required initial dry run succeeded with commit
bf1ca28fe4 (AUTO; compiles and passes preflight; nothing pushed). The item module
was then preserved unchanged. Four direct lcompile.py requests received no server
answer and returned exit 124 after 183, 185, 181 and 181 seconds. Two checked the
retained module and two checked scratchpad/CoordinatesProbe.lean. These are
transport/server-response failures, not Lean's 60-second file timeout. The probe
contains unverified candidate faithfulness and additivity proofs; it is outside
lean/ and is not part of a delivery. scratchpad/resume-notes.md records the API
findings and the remaining coordinate inverse construction. No additional holes
were closed or added in this resumed session; no delivery was pushed.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
