## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.CoherentOpenMapTensorExtension` by a
complete Lean proof from a strictly smaller section-extension theorem. The original signature
and every existing public import stay identical. Proof imports provide coherence-to-finite-
presentation, quasi-coherence of internal Hom, section extension, and tensor-Hom restriction.
The second reader reuses the existing proved finite-presentation helper in
CoherentStalkMapExtends (`import all` is proof-only), removing the duplicated local proof.

Added two modules, one statement in each:
`Sheaf.AlgebraicGeometry.QuasicoherentOpenSectionIdealExtension` states only the
structure-module section-extension part of 01YB, for an arbitrary quasi-coherent E.
`Sheaf.AlgebraicGeometry.TensorHomRestrictionScalar` proves the entirely formal tensor-Hom
restriction calculation, for any A, H and F on any scheme, without coherence or ideal powers.
The latter is proved by cancelling the restriction tensor comparison and evaluating pure
tensors; the scalar action, left unitor and overFunctorEquiv transport are checked in Lean.
Updated the item's proof route and dependency list; new nodes record each new module.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.coherent_open_map_tensor_extension`
(node `lem-pc-coherent-open-map-tensor-extension`), the only original hole.
Also proved: `AlgebraicGeometry.Scheme.Modules.tensorHom_restriction_of_local_scalar`
(node `lem-pc-tensor-hom-restriction-scalar`). The existing private helper
`AlgebraicGeometry.isFinitePresentation_of_coherent` is reused and introduces no hole.

Added and left: `AlgebraicGeometry.Scheme.Modules.quasicoherent_open_section_ideal_extension`
(node `lem-pc-quasicoherent-open-section-ideal-extension`), exactly `:= by sorry`.
No sorry remains in the item's module or the tensor-Hom compatibility module.
This is a decomposition: one upper hole closed and one strictly smaller lower hole added;
no net hole reduction is claimed. The lower statement handles only extension of one section,
with no coherent source, tensor product, local morphism, or tensor-Hom transport.
Its source and full proof in words are in its docstring and DAG node.

## No longer needed

Original imports removed: none. All four original imports occur in the unchanged statement
or supply its tensor structure. The second reader replaces the parent
CoherentFiniteTypeLocallyNoetherian proof import with CoherentStalkMapExtends to reuse its
proved helper. The former remains a transitive dependency. TensorHomRestrictionScalar now
publicly imports only TensorProduct, HomModule and Modules.Sheaf; TensorHomAdjunction is
imported only for the parent proof. No module can be claimed globally pruned by this delivery.

The parent theorem no longer directly uses
`lem-weil-pbc-module-finite-type-submodule-extension`,
`lem-weil-pbc-noetherian-acc-quasi-coherent`,
`lem-weil-pbc-sections-over-quasi-compact-open`,
`lem-weil-pbc-sections-annihilated-by-ideal`,
`lem-weil-pbc-coherent-artin-rees`,
`lem-weil-pbc-quasi-coherent-ideal-zero-set-affine`, and
`lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`.
The parent also no longer directly uses `pqf-lem-coherent-ft-locnoeth`: its finite-presentation
construction is reused from the existing stalk-map module.
These nodes are still required by the smaller section-extension node or the reused helper,
so they are relocated
proof dependencies, not pruned work. Their modules are not imported into the parent without
use. No kernel-of-multiplication or descent-through-image lemma is needed in this argument.

## Where the brief, the DAG or earlier work was wrong

The listed dependencies do not expose the structure-module case of 01YB as a single theorem:
SectionsOverQuasiCompactOpen exposes annihilator quotients, whereas this proof needs an
unquotiented map into E. The stabilization and Artin-Rees argument is recorded explicitly
in the new section-extension node instead of treating the quotient statement as direct
surjectivity into E. The tensor-Hom theorem supplies a linear equivalence and its evaluation
formula, but not the scheme restriction equation; that compatibility is now proved.

The existing full CoherentHomsOverOpen module cannot be used as a shortcut: import_direction.py
reports that it already reaches this item, so importing it here would close a cycle.
The blueprint ancestor tool reports None for this item's module-valued creation chain;
new nodes retain the item's explicit blueprint ancestor `lem-pc-coherent-hi` and extend its
existing via chain. The unit record has no realized node bindings; its statement and route
are unchanged. Mathlib searches found localization and tensor-functor tools, no exact match;
LeanSearch returned an HTTP internal-server error, recorded as unavailable.

Edge cases: section extension uses zero maps on the empty open and for a zero section or
zero target; the zero ideal has empty complement and admits a positive power; the unit ideal
admits exponent zero. The compatibility proof has no nonempty-open or nonzero-module
hypothesis and includes all these cases. Arbitrary existential witnesses occur only within
propositional theorem proofs, never as data of a definition.

## New nodes

`lem-pc-quasicoherent-open-section-ideal-extension`: the unquotiented ideal-power extension
of a quasi-coherent open section (01YB, first part). Its proof uses finite-type submodule
extension, coherent ACC, annihilators, Artin-Rees and the existing sections comparison.

`lem-pc-tensor-hom-restriction-scalar`: the scalar evaluation/restriction step (01CN and
01YB, tensor-Hom paragraph), fully proved. Its section hypotheses are local on every
smaller open, so it does not assume that section tensors on U generate the tensor sheaf.
No statement or definition changed; no forced adaptation or change record is needed.

## Second reading by E3

1. Interface preservation: PASS. Compared the parent module with the repository by
   diff, then compared its theorem signature byte for byte through the assignment.
   The signature, original docstring and four original public imports are unchanged.
   No existing definition or target is changed; there are no adaptations or change records.
2. Proof and trust: PASS as a decomposition. All three files compiled with no warnings.
   The only delivered sorry is the named section-extension theorem, listed above.
   There are no axioms, unsafe declarations, opaque declarations, extern attributes,
   implemented_by attributes, hollow definitions or arbitrary witness definitions.
   Scratch #print axioms checks gave only propext, Classical.choice and Quot.sound for
   tensorHom_restriction_of_local_scalar. The parent and section-extension theorem also
   use sorryAx, as expected from the still-open lower theorem. No claim of an axiom-free
   proof of the parent or a positive net hole reduction is made.
3. New statements: PASS. Read the full declarations and natural-language arguments.
   Checked the section-extension argument against Stacks Tag 01YB
   (https://stacks.math.columbia.edu/tag/01YB), first part: coherent reduction, stabilized
   torsion, Artin-Rees and the quotient section comparison. This is strictly the
   structure-module section case; the parent genuinely adds finite presentation,
   quasi-coherence of internal Hom, tensor-Hom transposition and restriction transport.
   It is not the parent under a new name. Empty U, zero section/module, zero ideal
   (positive exponent), unit ideal (exponent zero) and n=0 agree with the statements.
   The restriction theorem is formal and proved, with local sections on every smaller
   open rather than an assumption that global pure tensors generate.
   Independent LeanFinder queries used "Hom from powers of a coherent ideal surjects
   onto sections on its open complement" and "Restriction of tensor evaluation equals
   a scalar multiple of a sheaf morphism"; results were localization, presheaf tensor
   and scalar-restriction lemmas, with no exact extension/compatibility theorem.
   Loogle for SheafOfModules.homObj was unavailable for that project identifier.
   Grep and rg searches in Mathlib, upstream modules and lean/ found no usable duplicate
   of either new statement. The full CoherentHomsOverOpen shortcut is cyclic, confirmed
   with import_direction.py. The section-extension hole is not a short formal consequence
   of SectionsOverQuasiCompactOpen: its surjectivity has annihilator-quotient targets.
4. Route and pruning: PASS after repairs. Reviewed the pure tensor restriction argument
   from its conclusion downward and the parent conjugation and map-preimage cancellation.
   Removed the duplicated finite-presentation construction in favour of the existing
   proved private helper in CoherentStalkMapExtends, accessed by a proof-only import all;
   import_direction.py permits this import. Replaced TensorHomRestrictionScalar's public
   TensorHomAdjunction import by the TensorProduct and HomModule imports its signature
   needs, and imported adjunction only for the parent proof. The report now names every
   old proof dependency no longer directly used, including pqf-lem-coherent-ft-locnoeth.
   They remain lower-plan or transitive dependencies; no globally pruned module is claimed.
   Read dag/units/sk-thm-picard-coherence.json: its realized lists are empty and its
   statement and proof steps are unchanged; no unit route is bypassed.
5. DAG agreement: PASS. Checked the parent changes are only proof and proof_deps;
   proof_origin is retained. Updated its first step to name the reused stalk-map module's
   finite-presentation helper and its dependency node. Each proof_deps list is exactly
   the union of its proof steps' uses. Both new nodes have source, complete argument,
   search records, split status, creation record, blueprint ancestry, chapter/unit and
   verbatim Lean signatures; their statements match the files.

Second reading changed the duplicated finite-presentation proof and its DAG dependency,
the visibility and location of the adjunction import, and this report. The original proof's
mathematical reduction and its single true lower hole are retained. The initial parent
compile took 50.9 seconds, then exceeded 60 seconds after import cleanup; reusing the existing
helper brought the repaired parent to 26.0 seconds (25.0 seconds with the axiom print).
