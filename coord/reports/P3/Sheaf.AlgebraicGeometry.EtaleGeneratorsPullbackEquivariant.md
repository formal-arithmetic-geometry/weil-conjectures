## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.Modules.etale_generators_pullback_equivariant`
by a compiling local-to-global proof. Set σ = eT.inv ≫ ρ. The assumed action equation heT
and cancellation of the sheaf isomorphism prove equivariance on unit images. Represent
a pair of inverse-image sections on one common base-changed object, use naturality of
eT and σ and restriction compatibility of both actions, then apply separatedness of
the target generator sheaf. The original signature and every target remain unchanged.

Added `Sheaf.AlgebraicGeometry.EtaleInverseImageJointRepresentatives`, proved in Lean:
finite-limit preservation gives a product section, the locally surjective sheafification
unit gives a covering sieve, and the existing Kan-representative theorem gives common
representatives. The abelian/set comparison is taken only from
`EtaleInverseImageAbelianLiftHom`, with its unit equation derived from its hom-set
equation. Thus no ring-lift or operation-transport theorem is needed.

Added `Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackUnitMap` for the remaining geometric
construction of ρ and its equation on adjunction-unit sections. This is strictly the
construction and unit-section portion of the original argument. It neither involves
T', eT, or heT nor asserts equivariance on arbitrary inverse-image sections.

The complete sandbox compiles in import order. No new sorry occurs in a definition or
inside the main proof. New module statements were checked on empty schemes and empty
section sets: the product argument requires both input sections, and the image sieve
covers even on an empty object; pulling back an isomorphism also works over the zero ring.
The node copies record the actual proof and its dependencies. The unit record has no
realized node bindings for this item; the Picard/Kummer naturality route is retained.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.etale_generators_pullback_equivariant`
(node `lem-sc-etale-generators-pullback-equivariant`). Its proof is complete from the
named lower theorem; the result remains dependent on sorry and is a decomposition,
not an axiom-free proof of the geometric result.

New theorem proved without a new hole:
`AlgebraicGeometry.etaleInverseImage_joint_representatives`
(node `lem-sc-etale-inverse-image-joint-representatives`). The private product-section
helper is also proved. This uses the existing abelian-comparison theorem, which is
still sorry in the repository; no copy or new hole for that theorem is added.

Exactly one added hole remains:
`AlgebraicGeometry.Scheme.Modules.exists_etale_generators_pullback_unit_map`
(node `lem-sc-etale-generators-pullback-unit-map`), whose proof is exactly `:= by sorry`.
It carries the geometric construction and complete proof in words in its docstring.

Holes closed: 1. Holes added: 1. Net textual hole change: 0 (decomposition).
No sorry remains in the item's module.

## No longer needed

Removed the redundant direct proof import
`WeilConjectures.CategoryTheory.Sites.Torsor` from the item: the torsor API is already
publicly imported by `EtaleIsoTorsor`, which the statement needs. The node
`def-sc-gm-torsor` remains necessary as a statement dependency and for the geometric
construction; its removal from the parent's direct proof_deps does not prune it globally.

No original mathematical dependency is claimed globally pruned: module tensor pullback,
generator torsors, and inverse-image adjunctions remain required by the statements or the
unit-map construction. The new joint-representative proof avoids
`EtaleInverseImageAlgebraicStructures`, `EtaleInverseImageAbelianLiftOperations`,
`EtaleInverseImageRingLift`, `EtaleInverseImageSectionDescription`, and
`EtaleInverseImageLocalSheafification` as direct proof imports. It uses the narrower
`EtaleInverseImageAbelianLiftHom`, `EtaleInverseImageKanRepresentative`, and Mathlib's
locally surjective sheafification unit instead. These avoided modules were not original
imports, so this is not a claimed removal from the targets' closure.

The old direct proof dependencies `def-pc-module-pullback`, `def-sc-gm-torsor`, and
`def-weil-pbc-inverse-image` are all removed from the item's direct `proof_deps`:
the actual proof instead cites the two new intermediate theorems. All three remain
needed through their statements and the unit-map node; none is globally pruned.

## Where the brief, the DAG or earlier work was wrong

The node's definitions alone do not expose a sheaf map pulling back generator torsors;
the geometric map and its unit-section equation therefore need a separate theorem.
The original informal common-refinement assertion is made precise and proved via the
inverse image of a product. No false statement, signature change, or tool workaround
was required. The quoted Stacks sources are not present in this read-only clone's
literature directory; their exact tags were read on the official Stacks site.

## New nodes

`lem-sc-etale-generators-pullback-unit-map` records the remaining construction and unit
identity in `Sheaf.AlgebraicGeometry.EtaleGeneratorsPullbackUnitMap`, from Stacks Tags
040E and 0097 and the original node's first two steps and unit-section part of step 3.
One named theorem, one remaining sorry.

`lem-sc-etale-inverse-image-joint-representatives` records the proved simultaneous
representation lemma in `Sheaf.AlgebraicGeometry.EtaleInverseImageJointRepresentatives`,
from Stacks Tags 09XN and 00YV. No new sorry. It records the existing abelian comparison
and Kan-representative dependencies and the Mathlib product/sheafification argument.
No change record is needed: no existing statement, definition, or public import changed.

## Second reading by P3

1. PASS: compared the item with the repository using `diff`. Its existing theorem
signature and docstring are byte for byte unchanged; its public imports are unchanged.
The two other delivered modules are new, with no existing interface to overwrite.
No definitions or target statements changed, so no change record is required.

2. PASS: compiled all three modules in import order with `lcompile.py`, without errors
or warnings. Scratch copies with `#print axioms` for all three public theorems report
only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The last is expected:
the unit-map theorem is open and the joint-representative theorem uses the existing
open abelian comparison. There is exactly one textual sorry, in the named unit-map
theorem. There are no data definitions or forbidden declarations in this delivery.
The witnesses are eliminated within proofs of propositions; no data is defined by
choosing an arbitrary witness of an unproved existence theorem.

3. PASS: read the new statements, their docstrings and nodes. The unit-map theorem
contains the geometric map and only its unit-section equation; it omits T', eT, heT
and global equivariance, so it is a strictly smaller part of the original argument.
The representative theorem handles arbitrary G and F via a preserved binary product,
locally surjective sheafification and the existing Kan theorem. Empty source or target
schemes and absent sections create no counterexample: hypotheses supply the pair,
and an empty test scheme admits an empty covering. Identity base change reduces to
the expected generator map and local representatives. Checked Stacks 040E, 0097,
09XN and 00YV on the official site; these support the stated constructions.
Repeated searches with different words using msearch leanfinder, loogle and grep:
Mathlib has the free-module pullback and product/image-sieve ingredients, but no
combined generator-torsor map or mixed simultaneous representation theorem. Searched
lean/ for etaleIsoTorsor, common representatives and generator pullbacks; no duplicate.
Closing the remaining geometric construction requires its naturality and comparison
with tensor pullback, not a short application of the search results.

4. PASS: read the main proof from its conclusion down. It cancels eT on unit sections,
represents a and eT.inv(t) over the same object, rewrites both actions through
restriction, and applies separatedness. The product route reuses the narrower
abelian hom comparison rather than introducing operation-transport holes. The old
Torsor import was redundant via EtaleIsoTorsor. All original proof dependencies are
now explicitly accounted for under No longer needed; no globally pruned module is
claimed. Read sk-prop-ext-invariance.json: realized has no bindings for this item,
and the Picard/Kummer route remains intact.

5. PASS after metadata repair: node proof steps and proof_deps match the Lean argument.
New nodes have source, searches, created, blueprint, chapter, unit and lean records.
Changed both new lean.statement fields from single-line renderings to exact verbatim
signatures. No mathematical statement was altered. The report correctly counts one
old hole closed and one added hole: decomposition, zero net textual hole reduction.

Second reading changed only the two verbatim node-signature records and this report
(explicit old dependency accounting and review); the compiling Lean proofs were kept.
