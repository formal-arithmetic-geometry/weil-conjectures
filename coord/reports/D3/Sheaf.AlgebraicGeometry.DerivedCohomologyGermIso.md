## What changed

Proved `AlgebraicGeometry.Etale.isIso_strictLocalCohomologyGermMap` with its
signature and docstring unchanged. Adapted the proved private local comparison
from `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf` to the public
canonical maps. The free-sheaf adjunction identifies sections with morphisms;
local lifts through cycles give surjectivity, and local boundary lifts give
null homotopies and injectivity. Transport through a K-injective representative
and the homology shift gives local bijectivity of the exact canonical map.
Mathlib `Point.W_isInvertedBy_presheafFiber` converts this to a stalk isomorphism.
Added proof-only imports of `DerivabilityStructureInjectives` and `Sites.EpiMono`.
Updated the existing node's proof route; no definitions or statements changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.isIso_strictLocalCohomologyGermMap`
(node `lem-weil-pbc-derived-cohomology-germ-isomorphism`).
No `sorry` remains in the item and no holes were added. All private helpers
are proved. This is a proof, not a decomposition into new statements.

## No longer needed

Removed the draft's redundant proof import
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`.
No original statement import was removed.
The planned explicit dependency `lem-weil-pbc-sheafification-geometric-stalk`
is replaced by Mathlib's direct inversion of locally bijective maps. It has no
separate Sheaf statement module to remove. The injective-representative leaf
remains used. No unit realization is bypassed and no other node is pruned.

## Where the brief, the DAG or earlier work was wrong

The previous draft was unchecked because two compiled imports were missing.
Unchanged copies of `StrictLocalNeighbourhoodGeometry` and
`StrictLocalCohomologyGerms` now compile through `lcompile.py`; they were used
only to populate the sandbox compile cache and removed from the delivery.
The draft's final inference needed reassociation to retain local bijectivity
of the composite comparison. Its proposed elementwise stalk-bijectivity lemma
also requested `LocallySmall.{v} S.Etale`, which was not available. The more
general skyscraper-adjunction theorem avoids this assumption.

Existing-source searches found no accessible public local-comparison lemma:
the argument in `AbelianHigherDirectImagePresheaf` is private. The existing
search log records semantic and name searches; a fresh grep confirmed the
more general Mathlib inversion theorem. No new statements were needed.

The static preflight conservatively flags the private proof-context commands
as an interface change. The record
`coord/changes/private-germ-comparison.md` explains their scope and unchanged
public interface. No dependent-module adaptation is required.

## Second reading by D3

1. Interface: PASS. Read the full module and its diff against the repository.
   The sole existing declaration's signature is byte-for-byte unchanged, as is
   its docstring. No existing definition or public import changed. The two
   added imports are proof-only; all added declarations are private, and their
   section variables end before the public theorem. The conservative context
   change is documented in `coord/changes/private-germ-comparison.md`.
2. Proof: PASS. Local compilation succeeded without errors or warnings.
   A scratch copy with `#print axioms
   AlgebraicGeometry.Etale.isIso_strictLocalCohomologyGermMap` reported exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
   There is no `sorry` or forbidden declaration in the delivered Lean file.
   Read the cycle lifting, boundary lifting, explicit null homotopy, and
   transport through the injective representative and homology shift.
   The representative is obtained from a proved existence theorem inside a
   proof; no data definition chooses an arbitrary unproved witness.
3. Split statements: PASS, vacuous. No statement is split off and no hole is
   added. The generic private local comparison covers the zero complex and
   every integer shift, including negative degrees; cycle surjectivity and
   exactness impose no unstated positivity or nonzero hypothesis.
4. Route and pruning: PASS. Rechecked the existing private comparison in
   `AbelianHigherDirectImagePresheaf`, the public canonical definitions, the
   injective-representative Mathlib leaf, and the direct Mathlib stalk
   inversion theorem. A fresh search using `homology.*locally`,
   `locally.*homology`, and `W_isInvertedBy_presheafFiber` found the direct
   inversion theorem, but no public local derived comparison to replace the
   private argument. Both added imports supply proof infrastructure; the
   original public import supplies the statement. The only old dependency
   omitted is `lem-weil-pbc-sheafification-geometric-stalk`, already recorded
   under No longer needed. The `sk-prop-h2` unit's realized fields are empty;
   no realized statement or step is removed or bypassed.
5. DAG: PASS. The existing node changes only its proof, proof_deps and
   proof_origin. Its single retained dependency is the proved injective
   representative used by the Lean argument; the remaining local and stalk
   steps are proved helpers and Mathlib infrastructure. No new nodes exist.

Second reading changed only this report: added the independent checks and
verdicts. No Lean proof, statement, definition, import, node or change-record
repair was necessary. Closed one original hole, added zero holes.
