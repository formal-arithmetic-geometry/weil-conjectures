## What changed

Proved `Algebra.exists_popescu_coefficient_step` with its signature unchanged.
The proof follows Stacks Tag 07FJ, ad (13): it clears a common denominator, captures
its positive power in an Artinian coefficient enlargement, obtains localized
injectivity from unit multiplication and positive powers of the given regular
sequence, applies Ogoma, captures a power of its factor in a second enlargement,
and composes the two essentially smooth extensions. The residue equations are
proved explicitly. The local Artinian quotient and characteristic instances are
constructed from Mathlib. All additional proof imports are nonpublic.

Added `Sheaf.RingTheory.PopescuLocalizedCoefficientRelation`, proving the first
paragraph of ad (13) directly from faithful-flat ideal contraction and ideal-product
expansion. Its proof handles an empty coefficient family and n=N. Private, proved
helpers in the original module handle unit multiplication, preceding-power ideals,
localization of their quotient, common denominators, and the k-algebra structure
on an enlargement. Updated the two node records to match the Lean route.

## Proved and sorry left

Closed the sole original hole: `Algebra.exists_popescu_coefficient_step`
(node `lem-weil-pbc-popescu-coefficient-step`).
Also proved `Algebra.exists_popescu_localized_coefficient_relation`
(node `lem-weil-pbc-popescu-localized-coefficient-relation`).
No sorry remains in either delivered module; no holes added. Existing imported
statements are used as stage 3 permits. This is one original hole closed, not a
hole-moving decomposition.

## No longer needed

Removed the direct proof import `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`
from the original module: faithful-flat contraction is used in the new localized
relation module, which imports it privately. No mathematical dependency has been
pruned from the overall proof: the flat-local and ideal-contraction nodes now occur
under the new relation node, and all remaining original proof dependencies are used.
No existing public imports removed or changed. The second reading also removed
the redundant public import `Mathlib.RingTheory.Ideal.Quotient.Operations` from the
new relation module. No modules of the original plan can be claimed globally
unreachable from this delivery.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The k-compatibility hypothesis of the original theorem
is retained but is unnecessary for its conclusion: the new rings get their k-algebra
structures through D, and the conclusion only asks that the composite ring map be g.
No statement or definition changed; no forced adaptations. The compiled cache
initially lacked ArtinianCoefficientEnlargement; the normal synchronization made it
available, without copying or changing another group's module.

## New nodes

`lem-weil-pbc-popescu-localized-coefficient-relation` isolates and proves only the
coefficient relation in the localization with residues in the original coefficient
ring. It asserts no denominator, kernel stabilization, or new coefficient ring;
thus it is strictly the first part of the argument. The source is Stacks Tag 07FJ,
ad (13), first paragraph. LeanFinder, Loogle, and grep searches are recorded; LeanSearch returned Internal Server Error
and is recorded as unavailable. The
unit's realized statement and proof steps are untouched; this is below the unit level.
No change records are needed.


## Second reading by F1

1. PASS: diffed the existing module against the repository and compared its complete
   theorem signature byte for byte. The signature, existing docstring, public imports,
   and definitions are unchanged. Only proofs, private proved helpers and private
   imports were added. The existing node changes only proof, proof_deps and proof_origin.
   No change record or forced adaptation is required.
2. PASS: compiled both delivered modules individually using lcompile.py. No sorry,
   axiom, unsafe, opaque, extern or implemented_by occurs in either source. Scratch
   #print axioms checks for both public theorems return exactly propext,
   Classical.choice and Quot.sound, without sorryAx. No data definition chooses an
   arbitrary witness from an unproved existence theorem.
3. PASS: the new localized relation is fully proved, not a remaining hole or a
   renamed copy of the item. It needs no regular sequence, enlargement, denominator,
   or kernel stabilization. Checked the correction argument when n=N (the coefficient
   ideal is the unit ideal), s=0 (all finite sums vanish), and i=0 in the main theorem
   (the preceding ideal is zero). Repeated grep, LeanFinder and Loogle searches using
   ideal-product expansion and power relations through quotients; results give only
   component lemmas already used. Searched the Sheaf and upstream library sources;
   no existing theorem provides the combined localized relation.
4. PASS, with import pruning: the proof starts with faithful-flat contraction and
   Mathlib ideal expansion, clears denominators, then uses the existing Artinian
   enlargement, regular-sequence powers, Ogoma and smooth composition declarations.
   Both old flat-local/contraction dependencies remain used through the new relation
   node; no old dependency is mathematically abandoned. Read sk-thm-p1.json realized:
   this item is below the unit level and bypasses no realized step. Removed the
   redundant public import Mathlib.RingTheory.Ideal.Quotient.Operations from the new
   module and recompiled successfully. Its signature prerequisites are already
   supplied by the remaining public imports.
5. PASS: checked both node proof steps and their dependency unions against the Lean
   argument. The new node has source, complete statement, searches, creation data,
   blueprint origin, chapter, unit, and a verbatim Lean declaration signature. The
   original node records the two enlargements, localized relation, powered regularity,
   Ogoma, Artinian quotient and composition used in the actual proof.

Second reading changed only the redundant public import in the new relation module
and this review record. One original hole closed, zero holes added; no split-off
statement remains sorry. No globally pruned module is claimed.
