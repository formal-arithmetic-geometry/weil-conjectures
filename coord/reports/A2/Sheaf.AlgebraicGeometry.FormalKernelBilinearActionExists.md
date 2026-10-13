## What changed

Replaced the proof of AlgebraicGeometry.formalKernel_bilinear_action_exists in
Sheaf.AlgebraicGeometry.FormalKernelBilinearActionExists by a complete Lean reduction.
Its signature, universe, visibility and public import are unchanged. The proof chooses
uniquely characterized output sections, proves restriction compatibility by uniqueness,
and proves all four bilinear identities using simultaneous local lifts, the representative
formula, injectivity of the kernel inclusion and sheaf separation. LinearMap.mk₂ then
constructs the bilinear maps. The existing private formal_transition_epi, kernel_inclusion_injective, local_lift
and local_lifts_three helpers are reused from FormalKernelBilinearActionAssociative
through a proof-only import all. The four duplicate declarations have been removed.
Scalar restriction and section separation remain proved private helpers; there are
no private holes. Elaboration options are scoped to individual declarations.

Added Sheaf.AlgebraicGeometry.FormalKernelProductSection, containing the single named
remaining step: unique existence of a product section for two fixed inputs, determined
by all local representative equations. It does not assert a map, any linearity, or
compatibility between different input pairs. Its docstring gives the quotient induction,
independence of representatives, gluing and uniqueness argument. The choice in the
upper proof is from unique existence, so its output is determined up to equality.

The repaired proof-only imports are FormalKernelProductSection and
import all FormalKernelBilinearActionAssociative. The latter exposes the existing
private helpers to this proof without changing their visibility in their own module.
The associativity theorem itself is not applied. The import-direction check confirms
that this introduces no cycle. Both delivered modules compile without errors or warnings. No definition,
existing statement or other module is adapted. Updated the item's proof route in its
node and added the new node.

Sources read: Stacks tags 087Z and 0EHN online (the TeX clone listed in literature/LIST.md
is not present in this read-only checkout). The new section construction makes explicit
the local multiplication implicit in 087Z. The unit sk-thm-p1 was read: this is below
its realized statements and steps and does not bypass or modify any unit route.

## Proved and sorry left

Closed the original hole in AlgebraicGeometry.formalKernel_bilinear_action_exists
(node lem-weil-pbc-formal-kernel-bilinear-action-exists). The item's module has no sorry.
Added one hole: AlgebraicGeometry.formalKernel_product_section_existsUnique in
Sheaf.AlgebraicGeometry.FormalKernelProductSection
(node lem-weil-pbc-formal-kernel-product-section), whose proof is exactly `:= by sorry`.
This is a decomposition: one upper hole closed, one strictly narrower fixed-section
construction added, net zero holes. Bilinearity and restriction compatibility are now
proved and will not be obligations of the next worker.

The new statement was checked mathematically at m=n=0 (the kernel inclusion is identity),
n=0 (I^0 F=F), m=0 (ordinary scalar action modulo I), I=0 (all positive ideal pieces
vanish and the tower is constant), I=O_X (the formal levels vanish), zero modules and
empty opens. No global surjectivity on arbitrary opens is required anywhere. All data
chosen from the unproved step are uniquely determined by its statement.

## No longer needed

Removed four imports from the returned sandbox version:
WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification,
Mathlib.CategoryTheory.Sites.Abelian, Mathlib.Algebra.Category.Grp.Abelian and
Mathlib.Algebra.Category.Grp.EpiMono. They supported the removed duplicate lifting
proofs and are unnecessary when reusing the existing helpers. These removals do not
claim that the modules leave the targets closure.

The original module had only its public FormalKernelGradedPieces import, which
is needed and retained. No originally imported module is removed. The direct proof edge
to lem-weil-pbc-ideal-module-product-stalk is replaced by the new product-section node;
the stalk theorem remains needed by that node and is not claimed as pruned. The
coherent-formal-module, graded-pieces and sheaf-of-modules definition nodes remain needed.
No whole module or node is claimed to leave the targets' closure.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or source error was found. The original proof plan's definitions
and stalk formulas do not themselves state existence of the fixed product section:
iterated quotient comparison, representative independence and gluing still need a proof.
That portion is isolated in the new theorem, while the linearity and naturality portion
is implemented in Lean. The returned delivery incorrectly duplicated four private helper statements already
proved in FormalKernelBilinearActionAssociative. The repair removes all four and imports
that module with import all to reuse them. The actual associativity result is not used.
Its node is recorded as a proof dependency solely to account for its helper declarations. The blueprint ancestor tool returned None for this recently created item's
module-valued created.item, so the new node preserves the ancestor thm-weil-pbc-finite-etale-lifting explicitly recorded in the item's existing blueprint.from field.

Searches: LeanFinder returned filtration and adic-completion results, with no sheaf-level
product-section theorem. Loogle found LinearMap.mk₂ for the final assembly. LeanSearch
was tried and returned Internal Server Error, recorded as unavailable. Text search covered
both library roots, the formal kernel modules and Mathlib's quotient bilinear file;
blueprint search for kernel product section returned no matches.

## New nodes

lem-weil-pbc-formal-kernel-product-section, in
 dag/nodes/sec-proper-base-change/lem-weil-pbc-formal-kernel-product-section.json,
states unique existence for one product section and only that step. Its source, complete
proof, inherited chapter and unit, ancestor, searches and verbatim Lean statement are
recorded. It is strictly narrower than the item's bilinear-family existence: the actual
upper Lean proof supplies the four linear laws, restriction compatibility and packaging.
No change record is needed because no existing signature or definition changes.

The independent reading below concerns the returned version, before this repair.
A new independent reading must check the repaired imports and helper reuse.

## Earlier second reading (a previous round; superseded)

1. Compared the complete existing module with the repository using diff and checked
   the original theorem signature byte for byte. The signature, universe, visibility,
   definitions and public import are unchanged. Only proof-private helpers, proof-only
   imports and the proof/docstring change. The existing node differs only in proof,
   proof_deps and proof_origin. There are no forced adaptations or interface changes.
   Verdict: pass.
2. Compiled both delivered modules in import order with lcompile.py: 3.0 seconds for
   FormalKernelProductSection and 13.1 seconds for FormalKernelBilinearActionExists,
   no errors or warnings. Read every helper and the entire upper proof. The sole sorry
   is the named product-section theorem with its complete proof docstring; no definition
   or private helper contains a hole. Scratch copies with #print axioms for both public
   theorems report exactly propext, Classical.choice, Quot.sound and sorryAx. There are
   no forbidden declarations or implementation mechanisms. Verdict: pass, conditional
   on the explicitly reported lower hole, not an axiom-free completed proof.
3. Read Stacks tags 087Z and 0EHN online and the definitions of the quotient, the
   formal-system conditions and the kernel pieces. The new theorem isolates existence
   and uniqueness for fixed inputs; it supplies neither bilinearity nor a natural family
   of maps. Those properties are genuinely derived in the upper proof using epis,
   simultaneous local lifts, kernel injectivity and sheaf separation. On stalks, iterated
   quotient reduction has kernel I^(n+1)F; a lift of K_n belongs to I^nF for n>0.
   Multiplication then lands in I^(m+n)F, and both changes of representative are killed
   by I^(m+n+1). This verifies the stated gluing and uniqueness argument. Checked m=n=0,
   m=0, n=0, I=0, I=O_X, zero modules and empty opens; no global section surjectivity
   is assumed. The uniquely determined choice obeys the prohibition on arbitrary
   witnesses. Fresh LeanFinder search for existence and uniqueness from compatible
   quotient representatives found general sheaf gluing lemmas only. Loogle search for
   TopCat.Sheaf.existsUnique_gluing confirmed that generic lemma, which does not supply
   the compatible products; a separate SheafOfModules/Epi query was unavailable under
   load. Text search of formal-system modules, upstream module files and Mathlib's
   quotient bilinear file found no replacement product-section theorem. The remaining
   construction requires quotient comparison and descent, not a few-minute closure.
   Verdict: true, needed, strictly narrower decomposition; one hole closed and one added.
4. Checked the top-down reduction, each import's role, the old proof_deps and the
   realized statement and steps of dag/units/sk-thm-p1.json. Generic gluing and quotient
   bilinear lemmas do not bypass the missing construction. All added imports are plain
   proof imports; the existing public graded-pieces import remains needed by the
   signature. The report names the replaced direct ideal-module-product-stalk edge;
   that theorem remains a dependency of the new lower node, so no module is claimed
   pruned. No realized unit statement or step is bypassed or altered. Verdict: pass.
5. Checked both nodes against the Lean and compared the new node's Lean statement
   verbatim. The upper route records unique selection, naturality, local lifting and
   the four linear laws actually proved. The new node has its source, proof steps,
   dependency union, searches, created record, blueprint ancestor, chapter, unit and
   Lean record. Its stalk dependency is available through the public imports of
   CoherentFormalModule. Verdict: pass.

Second reading changed only this report: added the independent checks, fresh search
results and explicit conditional-proof verdict. No Lean or node repair was necessary.


## Second reading by A2

1. Compared the delivered existing module and node with the read-only repository by
   diff. Also checked the complete theorem signature byte for byte with a string
   comparison: identical. The existing public import, universe and visibility are
   retained. There are no changed definitions or adapted modules. The existing node
   changes only proof, proof_deps and proof_origin. Verdict: pass.
2. Read the complete repaired proof and the reused private helpers in
   FormalKernelBilinearActionAssociative. Compiled both delivery modules in import
   order through lcompile.py (2.4 and 10.7 seconds), with no errors or warnings.
   Scratch copies of the repaired files print the axioms of both public theorems:
   propext, Classical.choice, Quot.sound and sorryAx only. The sole textual sorry is
   the named public product-section theorem; no private helper or definition has a
   hole, and there are no forbidden declarations. Verdict: pass as a decomposition,
   conditional on the explicitly recorded lower hole, not a completed axiom-free proof.
3. Independently read the definitions of coherent formal modules, quotient projections
   and kernel pieces, and Stacks tags 087Z and 0EHN online. Iterated adjacent quotients
   identify the transition kernel with the indicated ideal power. At stalks, the
   coefficient-times-lift product lies in the correct kernel, and changing either
   representative gives a product killed by I^(m+n+1). Local preimages thus glue
   uniquely. Checked m=n=0, either degree zero, I=0, I=O_X, zero modules and empty
   opens. The choice is determined up to equality by unique existence. The lower
   theorem constructs only one fixed product section: linearity and naturality are
   genuinely derived in the upper proof, so it does not merely rename the item.
   Fresh LeanFinder query "descend multiplication of local quotient lifts to a unique
   sheaf section" returned general unique-gluing lemmas; fresh Loogle query
   TopCat.Sheaf.existsUnique_gluing confirmed the packaging lemma. Text searches for
   existsUnique gluing, product sections and bilinear descent in both library roots
   and Mathlib found no construction replacing this lower theorem. Closing it needs
   quotient comparison and representative independence, beyond a few-minute repair.
   Verdict: true, needed and strictly narrower; one upper hole closed, one hole added.
4. Checked every import and the actual top-down reduction. The two added imports are
   proof-only; import all is necessary for the already proved private transition,
   simultaneous-lifting and injectivity helpers. The associativity theorem itself is
   never applied and the import introduces no cycle. The old direct stalk-product
   dependency is replaced but remains below the product-section node; all other old
   dependencies remain. The report's No longer needed section accounts for this and
   claims no closure pruning. Read sk-thm-p1.json, including every realized statement
   and step: this below-unit reduction bypasses none. Verdict: pass.
5. Compared the two node records with the Lean declarations and proof. The existing
   route correctly records unique selection, restriction compatibility, local lifts,
   sectionwise injectivity, separation and the four linear laws. Its associativity
   node edge accounts specifically for proved private helpers. The new node contains
   its source, complete proof steps, dependency union, search records, creation record,
   inherited chapter/unit, blueprint ancestor and verbatim Lean statement. Verdict:
   pass.

This second reading changed only report.md, adding this independent review of the
repaired version. No Lean or node repair was needed. The delivery remains a net-zero
hole decomposition, with no module pruned.
