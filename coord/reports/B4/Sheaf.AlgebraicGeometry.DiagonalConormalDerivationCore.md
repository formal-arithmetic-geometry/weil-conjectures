## What changed

Proved `AlgebraicGeometry.exists_diagonalConormalDerivation_core` in
`Sheaf.AlgebraicGeometry.DiagonalConormalDerivationCore` without changing its signature
or any existing public interface. Added the proof-only import
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf` for its proved sectionwise
kernel range and injectivity lemmas. All new constructions and supporting lemmas are
private and fully proved in the item module.

For each open U, the construction lifts the projection difference to the actual
kernel on W_U = p₁⁻¹(U) ∩ p₂⁻¹(U), applies the chosen tensor-pullback unit and restricts
to U. The kernel lift is unique by injectivity, and its existence is proved before
it is chosen; no data is chosen from an unproved existence statement. Addition and
restriction compatibility follow from that uniqueness. The product identity
p(ab) − q(ab) = p(a)(p(b) − q(b)) + q(b)(p(a) − q(a)), together with linearity of
the unit, gives Leibniz. Pullback commutativity gives base vanishing. The proved
`Scheme.Hom.derivationMk` packages these facts as a relative derivation.

Updated the item's DAG proof to this explicit construction, including the existing
adjunction node in `proof_deps`. The source read was Stacks Tag 08S2,
https://stacks.math.columbia.edu/tag/08S2, its global difference construction.
The unit record `sk-thm-picard-duality` has no realized node for this item; the
construction preserves the diagonal-conormal route.

Validation: the final single-file compilation is clean. A separate temporary
`#print axioms AlgebraicGeometry.exists_diagonalConormalDerivation_core` reported
exactly `propext`, `Classical.choice`, and `Quot.sound`. The temporary command has
been removed. The formula and construction work on every open, including the empty
open, and assume no separatedness, smoothness, or affine-chart hypothesis.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.exists_diagonalConormalDerivation_core`
(node `lem-sc-diagonal-conormal-derivation-core-exists`).

Added 0 holes. No `sorry` remains in the item module; no new modules or nodes are
introduced. This is a complete proof, not a decomposition.

## No longer needed

None. No existing imports were removed: all three original public imports occur in
the statement, and the new private import supplies the sectionwise kernel lemmas.
No original dependency node or module is pruned. The proof does not need an
independently formalized square-zero extension, affine conormal comparison, or
uniqueness theorem for normalized derivations; none was imported or introduced.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface fault was found. The original one-step plan hid
its construction behind a square-zero extension. The direct kernel construction
avoids that auxiliary object and proves every required property explicitly using
the existing tensor-pullback unit. The original proof-dependency list omitted the
adjunction node already used in the statement; the updated list includes it.

## Second reading by B4

1. Interface preservation: PASS. Read the complete repository/sandbox diff and
   mechanically compared the existing theorem signature byte for byte. Its name,
   binders, hypotheses, existential conclusion and normalized local formula are
   unchanged. All supporting declarations are private; no existing definition or
   public import changed. No change record or forced adaptation is needed.
2. Proof and trust: PASS. Independently compiled the delivered file cleanly using
   lcompile.py (6.9 s). Compiled a scratch copy with `#print axioms
   AlgebraicGeometry.exists_diagonalConormalDerivation_core` (7.1 s): exactly
   `propext`, `Classical.choice`, `Quot.sound`. Checked that the file has no sorry,
   axiom, unsafe, opaque, implemented_by or extern declaration, and no hollow
   definition. Kernel lifts are chosen only from the fully proved private
   existence theorem and are unique by the proved upstream injectivity lemma.
   The tensor-pullback adjunction is proved and its canonical unit is pinned in
   its statement. Read the sectionwise kernel lemmas and derivationMk constructor.
3. Split statements and edge cases: PASS. No statements or holes were split off,
   and no new public statements or nodes were introduced. Read every private
   helper proof: the kernel lift, unit/restriction maps, formula, scalar identity,
   Leibniz identity, restriction compatibility and base vanishing. They work for
   the empty open and zero sections as well as arbitrary opens; no separatedness,
   affine, smoothness or properness assumption enters. In the identity-morphism
   case the projection difference and its unique kernel lift are zero.
4. Route, reuse and pruning: PASS. Searched the library and Mathlib by the diagonal
   derivation and kernel/difference constructions, and independently queried
   LeanFinder for the conormal derivation construction. The hits supply general
   differential constructors or ring-level facts, not a shorter sheaf-level proof
   of this normalized formula. The direct kernel construction uses the existing
   sectionwise range and injectivity results and derivationMk; an affine
   comparison or normalized-derivation uniqueness would introduce unnecessary
   dependencies. All three public imports occur in the original statement, and
   the additional kernel-lemma import is correctly proof-only. Both original
   proof_deps remain used, so `No longer needed: None` is complete. Read the unit
   sk-thm-picard-duality: its realized statement and step lists do not name this
   item. The diagonal-conormal construction stays on its existing route. Read
   Stacks Tag 08S2 online and checked the sign s₂ − s₁ against its construction.
5. DAG consistency: PASS. The only changed node fields are proof, proof_deps and
   proof_origin. The dependency set equals the union of the proof steps' uses;
   the steps faithfully describe the actual kernel lifts, chosen unit, product
   identity and derivation constructor. The origin explicitly distinguishes the
   agent's direct kernel realization from the cited Stacks construction. No new
   nodes require validation.

Second reading changed only this report by adding the independent review and
validation evidence. No repair to the Lean proof or node was necessary. Closed
one original hole, added zero; this remains a complete proof.
