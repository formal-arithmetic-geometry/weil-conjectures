## What changed
Completed `FieldTheory.intersection_subfields_differentials_kernel` in
`Sheaf.FieldTheory.IntersectionSubfieldsDifferentialsKernel`, without changing its signature.
The nonempty case now restricts the p-basis to the finite support of a differential,
uses the subspace theorem to find one field preserving monomial independence, and
uses relative differential independence to force all coordinates to vanish.
The empty-index case proves all universal differentials vanish by the p-th power rule.
Three fully proved private helpers handle finite independence and scalar restriction.
Added the proof-only import `Mathlib.Algebra.CharP.Algebra` for a local characteristic
instance. Updated the item's proof plan to describe the contrapositive formulation.

## Proved and sorry left
Closed the one original hole:
`FieldTheory.intersection_subfields_differentials_kernel`
(node `lem-weil-pbc-intersection-subfields-differentials-kernel`).
No sorry remains in the item and no new hole was added. The three private helpers
`finite_independent_some_field`, `finite_independent_some_field'`, and
`independent_adjoin_of_subset` are fully proved.
The proof uses the existing stated dependencies and adds no upstream-hole claim.
Independent scratch-copy axiom checks show that the main theorem and each private
helper depend only on `propext`, `Classical.choice`, and `Quot.sound`, with no
`sorryAx` in the currently compiled import closure. This is a complete proof from
the existing DAG declarations, not a decomposition into new statements.
Single-file compilation succeeds without warnings and within the 60-second limit.
The proof includes empty index families and empty coordinate support.

## No longer needed
No existing proof dependency or module is pruned: all four original Sheaf imports
are used. Removed the earlier sandbox attempt's unused
`Mathlib.Data.Finsupp.Fintype` import. The exploratory
`Mathlib.Algebra.CharP.IntermediateField` import is also absent; a local characteristic
proof avoids introducing competing prime-field algebra instances.
No new nodes or modules are needed.

## Where the brief, the DAG or earlier work was wrong
The earlier attempt's tool failure used the wrong delivery-tool location. The required
wrapper exists at `/home/ubuntu/weil-launcher/deliver3.py`.
The earlier attempt left an inline sorry in the nonempty branch; this is now closed.
Direct definitional conversion of the directedness comparison across extended scalars
caused kernel timeouts: expanding the two containment proofs explicitly fixes it.
The mathematical plan was sound. The implementation applies the subspace lemma
contrapositively to obtain one field preserving finite independence, then applies the
p-independent differential lemma positively; it keeps the same dependencies and unit route.


## Second reading by A3
1. Compared the delivered module and node with the read-only repository using
   `diff`. The existing theorem signature is byte-for-byte identical (also checked
   mechanically), the local algebra instance is unchanged, and no public definition
   or statement changes. Only proofs, private helpers, a proof-only import, and the
   permitted node proof fields changed. Verdict: pass.
2. Independently compiled the module with `lcompile.py`: clean, about 12 seconds.
   Compiled a scratch copy with `#print axioms` for the main theorem and all three
   private helpers: only `propext`, `Classical.choice`, and `Quot.sound`, without
   `sorryAx`. Scanned for forbidden declarations/options and sorries: none. There
   are no new definitions choosing data from an unproved existence theorem.
   Verdict: pass.
3. No statements are split off and no new holes or public lemmas are introduced.
   Read each private helper: the finite independence lemma is the contrapositive
   of the existing subspace theorem, its finite-type version transports along an
   equivalence, and the adjunction helper uses `adjoin_le_iff` and scalar restriction.
   Checked the zero-dimensional family, empty support, and empty index family;
   all are covered. Searched Mathlib with the recorded grep query concerning
   independence over intermediate fields/adjunctions and intersections, and
   searched the project and upstream sources for related declarations. Found no
   shorter existing theorem replacing the reduction. Verdict: pass.
4. Read the proof from the differential-kernel conclusion downward and checked
   each of its four Sheaf imports against the declarations used. All four original
   proof dependencies remain used; no old dependency or module is omitted from
   `No longer needed`. The existing public imports support the signature and local
   algebra instance; the added characteristic import is proof-only. Read
   `dag/units/sk-thm-p1.json`: no recorded realization is bypassed or changed.
   Verdict: pass.
5. Compared the node's proof steps, their `uses` union, `proof_deps`, and
   `proof_origin` against the Lean: empty-index derivation argument, finite-relation
   subspace reduction, p-basis support monomials, and independent relative
   differentials match. All other node fields are unchanged. No new nodes need
   checking. Verdict: pass.

Second reading changed only this report: added the independent review and actual
axiom-check results. The Lean proof and DAG were already correct and are unchanged.
