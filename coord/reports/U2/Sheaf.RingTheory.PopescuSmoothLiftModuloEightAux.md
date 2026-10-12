## What changed

Proved `exists_popescu_smooth_lift_data` in
`Sheaf.RingTheory.PopescuSmoothLiftModuloEightAux` without changing its signature
or existing visibility. It now applies `Algebra.popescu_lifting` with π⁴,
proves the annihilator hypotheses directly, handles the two prime cases, and
constructs the compatible quotient map using `Ideal.Quotient.liftₐ`.
The only added import is the private proof import
`Sheaf.RingTheory.PopescuSmoothQuotientFactor`.

Added and fully proved `exists_popescu_smooth_quotient_factor` in that new
module. Its sole proof import is `Mathlib.Algebra.Category.Ring.FinitePresentation`.
It factors the original finitely presented R-algebra map directly into the
underlying filtered colimit of rings, rather than first constructing a finite
presentation of A/(π⁸). Private explicit equivalences with the under-category
of a lifted base handle the differing universes. The equivalences and the
restricted scalar structures are actual constructions, with no unproved data.

Updated the item's proof, proof dependencies and proof origin to match Lean;
added the node of the proved factorization lemma. No existing statements,
definitions, target declarations, or other modules were changed. The second
reader changed the proof-only PopescuLifting import from public to plain import.
The unit's realized statement and steps remain intact.

## Proved and sorry left

Closed the original hole in `exists_popescu_smooth_lift_data`
(node `lem-weil-pbc-popescu-smooth-lift-data`): 1 of 1 original holes closed.
Also proved `exists_popescu_smooth_quotient_factor`
(node `lem-weil-pbc-popescu-smooth-quotient-factor`). Both delivered modules
contain no sorry; zero holes added and zero split off.

The proof still uses the existing named theorem `Algebra.popescu_lifting`
(node `lem-weil-pbc-popescu-lifting`), whose proof remains sorry in the existing
library. This dependency was already part of the item and is not modified or
claimed as closed. The factorization helper uses Mathlib exclusively.

## No longer needed

No existing import edges, nodes or modules are removed. PopescuLifting is now
a plain proof import rather than a public import. Every existing import of
the item serves its unchanged statement or the lifting proof. All unused
experimental imports were removed before the final compile: the direct imports
of `Mathlib.RingTheory.Ideal.Quotient.Operations` and
`Mathlib.RingTheory.Spectrum.Prime.RingHom` from the item, and the direct imports
of `Mathlib.CategoryTheory.Limits.Constructions.Over.Connected`,
`Mathlib.CategoryTheory.Filtered.Connected`, and
`Mathlib.RingTheory.Ideal.Quotient.Operations` from the new module.
These were temporary sandbox imports, not baseline library imports.

The new helper does not need the finite-presentation base-change lemma:
it factors A directly over R into the underlying rings. This avoids adding
that dependency to this auxiliary argument. It does not claim that the
unchanged parent module has lost that dependency globally.

## Where the brief, the DAG or earlier work was wrong

The item's old DAG proof named only Popescu lifting and omitted the
finite-presentation factorization needed to choose its smooth input C.
The new proved helper supplies that step explicitly. Mathlib's existing
`commAlgCatEquivUnder` requires equal base and carrier universes, so it cannot
be applied directly to the item's universe-polymorphic diagram. The private
lifted-base equivalence solves this without changing any existing interface.

Checked Stacks Tag 07F5, fourth paragraph, and Mathlib's finite-presentation
factorization theorem and connected-colimit preservation. The new helper's
edge cases include ρ = 0, a unit ρ, and zero rings: none is excluded, and the
proof needs neither nonzerodivisors nor Noetherianity. In the main theorem,
primes containing π⁴ are obtained from the quotient spectrum, and no
nontriviality assumption is introduced.

The blueprint ancestor utility reports None for the item because its
created.item is a module name. The new node follows the existing parent
node's recorded ancestor and extends its via list instead of editing any
unowned blueprint fields.

Searches: LeanFinder located
`RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit`; Loogle found no
additional applicable annihilator statement; grep found no direct Popescu
quotient-factorization theorem. LeanSearch returned Internal Server Error,
recorded as unavailable. The blueprint search for smooth quotient factor
found no matching blueprint node.

## New nodes

`lem-weil-pbc-popescu-smooth-quotient-factor`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-popescu-smooth-quotient-factor.json`,
is realized by the fully proved theorem
`exists_popescu_smooth_quotient_factor`. It states only the preliminary smooth
factorization modulo ρ², without lifting an algebra to R or asserting
smoothness there. Its proof uses the existing Mathlib leaves for underlying
ring colimits and finite-presentation factorization. No new statement is left
for another worker. The second reading adds
coord/changes/PopescuSmoothLiftModuloEightAux-proof-import.md for the import
visibility correction required by the brief and preflight.

## Second reading by U2

1. Compared the existing module with the repository using diff and checked the
   original theorem signature byte for byte: unchanged. The existing node
   changes only proof, proof_deps and proof_origin. No existing definition is
   edited, and no target statement is changed. Verdict: pass.
2. Compiled both modules in import order and compiled separate scratch copies
   with #print axioms. The new factorization theorem uses only propext,
   Classical.choice and Quot.sound; the main theorem additionally uses sorryAx
   through the already-open Algebra.popescu_lifting. No delivered sorry,
   prohibited declaration or hollow definition occurs. The private functors and
   equivalence contain explicit data and proved laws. Extracting the lifting
   witness takes place only inside a theorem proof, never a data definition.
   Verdict: pass; one original hole closed, zero holes added.
3. No statement is split off with sorry. Read the new proved helper and its
   docstring: it is the strictly preliminary factorization through a diagram
   term, not a restatement of the lift. Checked zero rings, zero rho and unit
   rho: the filtered-colimit factorization applies without extra assumptions;
   a filtered category is nonempty even in the zero-ring case. Independently
   searched LeanFinder for regular-element annihilators, Loogle for the ring
   factorization theorem, and rg for smooth factorization in the library and
   upstream. The nearby nilpotent lifting and smooth-algebra descent statements
   solve different problems. No shorter exact theorem was found. Verdict: pass.
4. Read the proof from its conclusion down to the existing lifting theorem.
   Checked the power substitution, annihilator cancellation, quotient-spectrum
   prime cases and the equality obtained by applying psi to representatives.
   Read Mathlib's factorization theorem and the unit sk-thm-p1 realized fields;
   this auxiliary argument bypasses no realized unit step. The original sole
   proof dependency remains used, so no old node can be pruned. Corrected the
   sole import visibility fault: PopescuLifting is proof-only and now imported
   without public. All other imports serve the signatures or the new proof.
   Verdict: pass after that correction.
5. Checked both node statements against their Lean signatures, proof steps,
   dependency unions and origins. The new node supplies source, searches,
   provenance, chapter/unit and its complete Lean record. Its two Mathlib leaf
   dependencies match the actual colimit preservation and factorization.
   Verified the source's eighth-power and fourth-power reduction at
   https://stacks.math.columbia.edu/tag/07F5. Verdict: pass.

Changed only the visibility of the existing PopescuLifting import and this
report during second reading; retained the correct proof and node records.


The dry run required a change record for privatizing the existing public
import. Added coord/changes/PopescuSmoothLiftModuloEightAux-proof-import.md;
the sole direct importer already imports PopescuLifting and needs no change.
