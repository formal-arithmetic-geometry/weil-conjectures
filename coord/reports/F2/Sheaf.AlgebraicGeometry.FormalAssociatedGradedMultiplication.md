## What changed

Proved `AlgebraicGeometry.formalAssociatedGraded_multiplication_exists` with its original
signature and original public import. Added three proof-only imports for fully proved helpers:
`Sheaf.AlgebraicGeometry.FormalAssociatedGradedAffineMultiplication` and
`Sheaf.AlgebraicGeometry.AffineBilinearExtension`, and
`Sheaf.AlgebraicGeometry.FormalPolynomialPowerLifts`. The last import supplies the
existing general `formalPolynomial_power_injective` theorem. The affine construction imports the existing affine ideal-product theorem and the unit
quasi-coherence theorem; the main file reuses its proved range/product helpers and the existing public power-injectivity theorem.

Repair of the landing return at head `7c354f468`: removed the new private declaration
`AlgebraicGeometry.power_qc`, which duplicated the existing private
`AlgebraicGeometry.idealSheafPower_quasicoherent` in `CoherentFormalModule`.
That existing declaration is private and cannot be imported by name. Both projection
proofs now use the already imported public theorem
`Scheme.Modules.ideal_times_quasiCoherent_affine_sections` directly for positive powers
and `SheafOfModules.isQuasicoherent_unit` for degree zero. No duplicate named theorem
is retained, and no visibility or interface of an existing module is changed.

The affine construction proves the power projection kernel formula, constructs the unique
product lift, and uses Mathlib `LinearMap.liftQ₂` plus the surjective first-isomorphism theorem
to descend through both quotient projections. Naturality is checked on representatives using
affine projection surjectivity. The general affine-basis extension helper proves overlap
compatibility on affine refinements, glues sections, and proves both linearities and naturality
by separatedness. The main theorem separately glues unique product lifts through the monic
power inclusion and proves the global representative identity on the affine basis.

No existing definitions or statement interfaces changed. No other holder's module was adapted.
The original unit route stays intact. Choices in the proof are determined by injective power
inclusions or by all affine restrictions and sheaf separatedness; no arbitrary object is defined
from a mere existence theorem. The source tags were read online because the local Stacks TeX
files named by the inherited node are absent on this machine.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.formalAssociatedGraded_multiplication_exists`
(node `lem-weil-pbc-formal-associated-graded-multiplication`).

Also fully proved the new public helpers `AlgebraicGeometry.affineBilinear_extension`
(node `lem-weil-pbc-affine-bilinear-extension`) and
`AlgebraicGeometry.formalAssociatedGraded_affine_multiplication_exists`
(node `lem-weil-pbc-formal-associated-graded-affine-multiplication`). All local and shared helpers
are fully proved. There are no remaining or added `sorry`s; zero holes split off.

All three delivered modules compiled together without warnings. `#print axioms` for each of
the three public theorems reported exactly `propext`, `Classical.choice`, and `Quot.sound`;
there is no transitive proof hole in these theorems. The edge cases use the same formal proof:
degree zero is handled explicitly by the identity power inclusion, the empty open by the
sheaf gluing axiom on its affine cover, and zero/unit ideals by ordinary ideal power arithmetic.
Intersections of affine opens are never assumed affine; equality on them is checked on affine
refinements. This needs no separation or quasi-separatedness hypothesis.

## No longer needed

No original import was removed, and both original planned dependency nodes remain used:
`lem-weil-pbc-ideal-times-quasi-coherent-affine-sections` and
`def-weil-sheaf-of-modules-category`. Removed the redundant proof-only import `Mathlib.LinearAlgebra.Isomorphisms`
from the new affine helper during second reading; its first-isomorphism declarations
are already available through the retained imports. Removed the main file's proof-only imports
`Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections` and
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`: their use
is now confined to the affine construction, whose proved helpers the main file imports.
The duplicate helper `AlgebraicGeometry.power_qc` is removed entirely; both callers
reuse existing public declarations. Its removal needs no extra module import.
Current second reading also removes the redundant new declarations `AlgebraicGeometry.app_restrict`
and `AlgebraicGeometry.power_injective`: callers use Mathlib
`PresheafOfModules.naturality_apply` and the existing
`AlgebraicGeometry.formalPolynomial_power_injective` directly. The latter requires a
plain proof-only import of `FormalPolynomialPowerLifts` in both callers; its polynomial
evaluation theorem and finite-generation hypotheses are not used.
The remaining imports are used. No node
or module is claimed pruned from the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The current return identified a duplicate power quasi-coherence declaration.
Its named replacement in `CoherentFormalModule` is private, so direct use from another
module is impossible. The existing public affine ideal-product theorem already supplies
quasi-coherence of every positive power, and the unit theorem supplies power zero.
The repair deletes the duplicate and uses those existing results at both callers.
The earlier second-reading section below is an inherited review of the prior delivery.
The final `Second reading by F2` section reviews and repairs the current version.

Earlier repair of the returned delivery: the affine extension and parent contained identical
private `sections_eq_of_affine` helpers. Keep the proved helper once, expose it in the
new affine extension module, and reuse it through the parent's existing proof-only import.
Also share the proved `app_restrict`, `power_injective`, `power_affine_range` and
`power_affine_product` helpers from the new affine construction module, removing their
repeated parent proofs. These helper declarations were introduced by this delivery;
no pre-existing library signature or visibility changes. No mathematical error or
statement change was needed. Second reading found and removed
one redundant proof-only Mathlib import. The original plan works, but its two
steps require explicit quotient-kernel transport and affine-basis gluing. Both are now proved.
LeanSearch was unavailable (Internal Server Error); this is recorded without treating it as
absence evidence. Loogle, LeanFinder, Mathlib source searches and library searches supplied
the quotient and gluing tools. The blueprint ancestor helper returns None because the inherited
created.item chain contains module names; the new nodes preserve the parent's recorded nearest
blueprint ancestor `thm-weil-pbc-finite-etale-lifting` and insert the parent in their via chains.

## New nodes

`lem-weil-pbc-formal-associated-graded-affine-multiplication` records the proved affine-only
construction in `lean/Sheaf/AlgebraicGeometry/FormalAssociatedGradedAffineMultiplication.lean`.
It includes bilinearity, naturality between affine opens, and the identity for any product lift.
It is strictly an affine part of the original argument and contains no proof hole.

`lem-weil-pbc-affine-bilinear-extension` records the proved general affine-basis extension
in `lean/Sheaf/AlgebraicGeometry/AffineBilinearExtension.lean`. It applies to arbitrary module
sheaves, not just quasi-coherent graded pieces, and uses only the module sheaf axiom and the
affine basis. It contains no proof hole. No change record is necessary because no existing
statement, definition or public import changed.


## Earlier second reading (a previous round; superseded)

1. PASS: Compared the main module with the repository using `diff` and checked its
   existing theorem signature byte for byte. The signature and original public import
   are unchanged. Both additional modules are new; no existing definition, target,
   visibility, or other holder's module is changed. No change record is required.
2. PASS: Independently compiled all three delivered modules in import order with
   `lcompile.py --all`, without errors or warnings. Searched their sources for forbidden
   declarations and proof holes: none. Scratch copies printed axioms for all eight
   public helper/main declarations, each showing only `propext`, `Classical.choice`,
   and `Quot.sound`. The delivery tool additionally probes private declarations.
   All choices come from proved existence statements: product lifts are unique by
   injectivity, quotient pairings are determined by surjective projections, and glued
   sections are determined by their affine restrictions. There is no hollow definition.
3. PASS: No statement is split off with `sorry`. Read both new theorem signatures,
   docstrings and nodes against their proofs. The affine theorem is the representative
   quotient construction, strictly a part of the original argument; the extension
   theorem is the independent general sheaf-gluing step. Degree zero uses the identity
   inclusion explicitly. Zero and unit ideals satisfy the same power/kernel identities;
   empty opens satisfy the sheaf cover and uniqueness arguments. Affine intersections
   are checked on affine refinements, never assumed affine. Repeated independent
   searches with the query "A pairing of module sheaves defined on a topological basis
   glues to a sectionwise bilinear map" (LeanFinder), `"quotKerEquivOfSurjective"`
   (Loogle), and local searches for bilinear maps, basis extension, ideal powers and
   section equality. Found no duplicate or direct replacement. The existing tensor
   universal property requires operations on all opens, and the sheafification
   bilinear extension concerns sheafification on one site, not affine-basis extension.
4. PASS: Read the proof from the main reduction down through affine quotient descent
   and sheaf gluing. It uses Mathlib `liftQ₂`, the first isomorphism theorem and the
   sheaf gluing/separatedness API. The retained imports support the signatures or
   actual proof steps; every proof-only import is plain `import`. Both original
   dependency nodes remain used, so `No longer needed` omits neither original node.
   Inspected `dag/units/sk-thm-p1.json`: none of this delivery's three nodes realizes
   the unit statement or a fixed step; its `realized` route is unchanged. No module
   is claimed pruned from the targets' closure.
5. PASS: Compared the existing node: only `proof`, `proof_deps`, and `proof_origin`
   change. Checked both new nodes' verbatim Lean signatures, dependency-step unions,
   source, searches, status, creation, blueprint ancestry, chapter and unit fields.
   Their proofs match the affine algebra and affine-basis gluing in the Lean files.
   The main node records both new proved dependencies and preserves the two original
   dependencies used for power calculations and the sheaf axiom.

Changes by this second reader: appended this independent review and recorded fresh
searches in the sandbox search log. No Lean or node repair was necessary. The earlier
repair/pruning history above describes the received sandbox, not changes made in this
reading. Closed one original hole, added zero holes, left zero holes; no decomposition.


## Second reading by F2

1. PASS after repair. Compared every delivered module with the repository. Only the
   parent module already exists. Its existing theorem signature is byte-for-byte
   identical, checked independently with the declaration parser, and its original
   public import is unchanged. Both other modules are new. No existing definition,
   visibility, target, or other holder's module was changed; no change record is needed.
   The two declarations removed in this reading were introduced only by this delivery.
2. PASS. Independently compiled all three repaired modules in import order with
   `lcompile.py --all`, without errors or warnings. Read the sources and scanned for
   sorry, axiom, unsafe, opaque, implemented_by and extern: no forbidden code or holes.
   Fresh scratch copies printed axioms for all six retained public declarations; each
   reported only propext, Classical.choice and Quot.sound. The delivery tool also
   checks private declarations. Product lifts are uniquely determined by injective
   inclusions, quotient pairings by surjective projections, and glued values by their
   affine restrictions. No data come from an unproved existence statement.
3. PASS after removing duplicates. No theorem is split off with sorry. Read the affine
   quotient theorem, extension theorem, their docstrings, and their nodes against the
   Lean proofs. The kernel calculation maps I times the power module into I^(n+1)
   and uses injectivity for the converse; liftQ₂ annihilates both kernels separately.
   Degree zero uses the identity inclusion. Zero/unit ideals satisfy the same ideal
   equations, and the empty open is handled by sheaf gluing and separatedness. Overlaps
   are compared on affine refinements, without an affine-intersection assumption.
   Fresh LeanFinder search for a compatible pairing on basic opens found sheafification
   scalar constructions, not this basis-extension statement. Fresh Loogle search for
   naturality_apply identified the exact existing naturality lemma. Fresh Mathlib grep
   for bilinear|pairing in Topology/Sheaves found no replacement. Local searches in both
   library roots and upstream found formalPolynomial_power_injective, which already
   proves a strictly more general version of the proposed new power_injective helper.
   Removed both duplicate helpers and reused the existing results at every caller.
4. PASS. Read downward from the main theorem through the affine quotient construction
   and the affine-basis extension. The proof uses the shortest existing quotient APIs,
   liftQ₂ and quotKerEquivOfSurjective, then the sheaf gluing/separatedness APIs.
   Read Stacks 087Z, 01I8, 01IC and 0072 online: the first uses the associated graded
   algebra without expanding this construction; the others give affine tensor/exact
   quotient descriptions and the sheaf equalizer axiom. The current Lean construction
   needs no Noetherian assumption, finite generation, or separation. Proof-only imports
   are plain imports, including the reused injectivity lemma's module. Both original
   proof_deps remain genuinely used, so none is missing from No longer needed.
   Checked sk-thm-p1.json: none of these nodes realizes a fixed unit statement or step;
   the unit route is unchanged. No module is claimed pruned from the target closure.
5. PASS after updating proof descriptions. Checked all three node signatures verbatim,
   and checked proof_deps against the union of step uses. The existing node changes
   only proof, proof_deps and proof_origin. The new nodes contain source, searches,
   creation, status, blueprint ancestry, chapter, unit and complete Lean records.
   Updated the affine and parent proof descriptions/origins to name the reused public
   injectivity and Mathlib naturality results. The elementary monicity specialization
   uses the existing helper directly, not the polynomial-evaluation theorem or its proof.
   The old quasi-coherence-helper repair is also present: positive powers use the public
   affine product theorem, and degree zero uses isQuasicoherent_unit.

Changes by this second reader: removed the new duplicate app_restrict and power_injective
helpers, replaced all their uses by existing declarations, added the necessary plain
FormalPolynomialPowerLifts imports, adjusted the affected rewrites for the existing
presheaf API, and updated the two proof records and this report. No mathematical or
statement correction was needed. Closed one original hole, added zero holes, left zero
holes; zero statements split off, no decomposition, and no closure-pruning claim.


Dry-run repair: preflight treated a newly added `open PresheafOfModules` command
in the existing parent module as a visible command change. Removed that command
and used fully qualified theorem names instead, preserving the original command
interface. No change record or interface change is needed.
