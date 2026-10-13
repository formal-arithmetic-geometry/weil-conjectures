## What changed

Proved `AlgebraicGeometry.Scheme.Modules.scalarInverseImageCompIso_coherence` with its original signature and definition of the composition comparison unchanged. Added two proved private helpers: `homEquiv_unique`, the generic uniqueness comparison's hom-equivalence formula; and `constant_homEquiv`, the unit formula for the existing constant-sheaf comparison.

The constant-unit calculation removes the constant-unit isomorphisms by naturality, then uses the composite constant-sheaf adjunction. Its two adjoints equal the constant adjunction unit. The coefficient calculation applies the inverse-image hom equivalence, uses `exists_scalarPullbackCoefficient` sectionwise, and finishes with the tensor-pullback comparison's inverse unit identity. This follows the existing two-step DAG plan, so no node changes are needed. No imports, public signatures, definitions, or other modules changed.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.Scheme.Modules.scalarInverseImageCompIso_coherence` (node `lem-sc-scalar-inverse-image-composition-coherence`). Both conjuncts are proved. Zero holes added; zero `sorry` declarations remain in the delivered module. This is a proof, not a decomposition. The existing imported theory's axioms are checked by the delivery tool.

## No longer needed

None. The sole existing public import, `Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`, supplies the statement's objects and the proof's normalized maps and adjunctions; it is still required. Both DAG steps still use `def-sc-field-linear-module-cohomology-operations`. No additional dependency modules or nodes were introduced.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction. All hypotheses and both conclusions stay identical. The proof cancels only isomorphisms, never elements or nonzero sections, so zero coefficients, empty schemes, identity arrows and arbitrary characteristic require no extra assumption.

The local literature checkout does not contain `literature/stacks-project/sheaves.tex`; read the official Stacks pages for Tags 008I and 0097 instead. Both prove the composition comparison by uniqueness of left adjoints. Library searches through msearch's leanfinder, loogle and grep found the generic uniqueness and constant-sheaf constructions, but no duplicate scalar coherence theorem. The final proof uses those constructions directly.

The two computations together need a declaration-local heartbeat budget of 600000; the reason is documented beside the option. Compilation remains below the single-file time limit. Earlier incomplete trial proofs and the rejected preliminary dry run have been replaced by the complete proof.

## Earlier second reading (a previous round; superseded)

1. PASS: Compared the sole delivered Lean module with the repository using `diff`.
   The existing definition body, public signature, visibility and import are byte-for-byte
   unchanged. Only two proved private helpers, local elaboration options and the completed
   theorem proof were added. No change record is needed.
2. PASS: Independently compiled the file through lcompile.py (26.8 seconds, no warnings).
   A scratch-copy `#print axioms` probe compiled in 24.3 seconds: the comparison definition
   uses only propext, Classical.choice and Quot.sound; the theorem additionally has sorryAx
   from existing imported theory. No sorry or prohibited declaration occurs in this module.
   The coefficient witness is fixed uniquely by its sectionwise adjunction formula, rather
   than chosen from an unconstrained existence statement.
3. PASS: No split-off statements, new nodes or new holes. Both private helpers are proved
   adjunction calculations. Read the coefficient characterization and its construction;
   neither equality assumes nonzero sections, nonempty schemes or special arrows.
4. PASS: Read both conjuncts top-down. The proof uses Mathlib adjunction uniqueness and
   naturality, then the imported coefficient characterization and tensor comparison unit
   identity. A fresh search of Mathlib's Adjunction/Unique.lean confirms the generic unit
   formula already used, with no direct replacement for the two scalar equations. Searches
   of both library roots found no public duplicate of these helpers or the target theorem.
   The sole public import supplies signature objects and is necessary; no old proof
   dependency is pruned. The unit sk-prop-av-cube and its realized record are unchanged;
   the argument stays below its unit route.
5. PASS: Read the item's node and sole proof dependency. Its two proof steps and
   proof_deps precisely describe the constant-adjunction and tensor-unit computations.
   No DAG update is required, and there are no new node records to check.

Second reading changed only this report; the Lean proof was accepted unchanged.

Delivery validation: the required dry run printed OK at commit 060fb686b7, review class
AUTO. Its all-declaration probe timed out at 60 seconds (the separate explicit axiom
probes above succeeded). Subsequent push attempts repeatedly stopped before pushing
with `COMPILE FAILED (local): timeout after 60 s`. The unchanged file's initial compile
and explicit axiom probe succeeded, but machine load rose from over 136 to 178.96,
with 127 Lean processes at the final check. A trial reducing one context-wide unfolding
also timed out and was reverted. No time limit or tool was modified, no Lean change
remains from this second reading, and no delivery was pushed.

## Second reading by S4

1. PASS: Independently diffed the sole delivered module against the repository and
   checked the existing theorem signature, comparison definition body and imports
   byte for byte with a script. All are unchanged. The only Lean additions are two
   proved private helpers, declaration-local options and the replacement proof.
   No change record or forced adaptation is needed.
2. PASS: Compiled the delivered file through lcompile.py in 29.7 seconds, without
   errors or warnings. No sorry, axiom, unsafe, opaque, extern, implemented_by or
   kernel-check bypass occurs in the delivered module. Read the imported coefficient
   characterization: its equations specify every component of the adjoint map, so
   injectivity of the hom equivalence uniquely determines the chosen coefficient.
   The tensor adjunction uses the existing constructed tensor-pullback functor.
3. PASS: No split-off statements, new nodes or new holes. The private helpers prove
   generic adjunction identities directly. Checked zero sections, empty schemes and
   identity arrows: only isomorphism cancellation and map equalities are used, with
   no nonzero, flatness, quasi-coherence or nonempty hypothesis.
4. PASS: Read the proof top-down and searched Mathlib Adjunction/Unique.lean using
   hom-equivalence and comparison keywords, and both library roots for the target
   and helpers. The generic Mathlib identities already used are the short route;
   no direct scalar coherence replacement was found. Similar private hom-equivalence
   helpers in ScalarUnitClassPullback and ScalarPullbackZeroGlobalSections are local
   conveniences, unavailable as imported API. The sole public import supplies the
   statement's objects and remains necessary. No old proof dependency is unused.
   Read dag/units/sk-prop-av-cube.json: its route and realized record are unchanged;
   this below-unit calculation does not replace any unit statement or step.
5. PASS: Read lem-sc-scalar-inverse-image-composition-coherence and the declarations
   of its sole proof dependency, FieldLinearModuleCohomologyOperations. Step 1 matches
   naturality, constant-sheaf comparison and adjunction uniqueness in the first
   conjunct. Step 2 matches the sectionwise coefficient characterization and inverse
   tensor-comparison unit identity in the second conjunct. Existing proof, proof_deps
   and proof_origin agree with the completed proof; no DAG edits are required.

This second reading accepted the Lean proof unchanged and appended this review.
The delivery closes scalarInverseImageCompIso_coherence, the sole original hole,
adds zero holes, and prunes no modules. The previous round's delivery failures are
historical; validation for this round is recorded below.

Current axiom verification: a scratch copy with explicit #print axioms for
scalarInverseImageCompIso, homEquiv_unique, constant_homEquiv and
scalarInverseImageCompIso_coherence compiled cleanly in 38.4 seconds. Every declaration
uses only propext, Classical.choice and Quot.sound; none uses sorryAx. This supersedes
the previous round's observation of sorryAx from then-open imported theory.

Delivery validation for this round: deliver3.py --no-push printed OK at commit
 de51f4e404, review class AUTO. The first run waited about 20 minutes for a shared
compile slot and was stopped; an unchanged retry passed. No compiler limit, tool or
Lean proof was modified.
