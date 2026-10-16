## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.inverseImageModule_preservesFlat`
with a complete Lean reduction, without changing its signature.

Added `Sheaf.CategoryTheory.InternalSectionModuleFlat`, with a fully proved
`CategoryTheory.InternalAbelianSheafModule.flat_iff_sectionModule`. The proof
constructs both directions of the tensor comparison, verifies their inverse
identities and naturality, and transports exactness through the existing section
module equivalence. This is the first step of the assigned node's plan, now proved.

The assigned module constructs the concrete set-valued inverse image, its right
adjoint and its finite-limit preservation. It applies the already proved
`SheafOfModules.isFlat_algebraicInverseImageOfUniverses`, transports flatness
through the source equivalence unit and a module isomorphism, then uses the reverse
tensor-flatness comparison. A local, proved helper transports the local finite
relation criterion through an arbitrary module isomorphism.

Added `Sheaf.Paper.SectionModuleAlgebraicInverseImage` for the remaining structural
identification of the internal inverse image with the algebraic inverse image.
Its statement fixes the actual Kan-extension/sheafification set inverse image,
and contains no flatness hypothesis or conclusion. The coefficient and module
universes are explicitly `u + 1`. This module also contains concrete, sorry-free
private constructions `pullbackForgetIso`, `sectionRingPullbackIso`, and
`sectionModulePullbackIso`, together with `pullbackForgetIso_unit_hom`. The latter
proves that the comparison commutes with the set and abelian adjunction units,
using the Kan-extension and sheafification comparison equations. The proved
helpers `pullback_add_graph` and `pullback_zero_graph` show that this comparison
preserves arbitrary addition and zero graphs. The new
`pushforward_section_mul`, `pushforward_section_one`, and
`pushforward_section_smul` prove that the pointwise ring/module operations of
pushforward agree with the operations at the corresponding site object.
`sectionRingMap`, `pushforwardSectionRingHom`, and
`inverseImageSectionRingUnit` construct the ring homomorphism on sections given
by the adjunction unit and inverse coefficient map. The proved
`sectionRingPullbackIso_unit` identifies its values with the transpose of the
concrete underlying ring comparison. The proved
`sectionRingPullbackIso_transpose` extends this to any test sheaf.
`sectionRingPullback_add_graph`, `sectionRingPullback_mul_graph`, and
`sectionRingPullback_nat_graph` establish the ring operation graphs; the latter
includes zero and one.

Single-file compilation and compilation of the three sandbox modules in import
order were used during development. The new private module-sheafification lift
has an explicit identity-scalar
comparison and a proved unit/naturality API; using that API prevents
repeated expansion of the internal tensor coequalizer while checking naturality.
No existing definitions, target signatures,
or consumer modules were changed. Both new nodes and the assigned node's proof
route are recorded in the delivery.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.inverseImageModule_preservesFlat` (one original hole).
The assigned module now has zero holes.

Fully proved the new theorem
`CategoryTheory.InternalAbelianSheafModule.flat_iff_sectionModule`, including all
its private tensor and exactness helpers. This module has zero holes.

Added one hole:
`AlgebraicGeometry.ProEtale.exists_sectionModuleAlgebraicInverseImage`, node
`lem-c2-proetale-section-module-algebraic-inverse-image`. It remains exactly
`by sorry` in its own module. The delivery is a decomposition: one original hole
closed, one strictly structural hole added, net zero holes; it is not a complete
proof of inverse-image flatness from the standard axioms.

What remains for that theorem is assembly of the structure and verification of
the module operation graph equations after the source section-equivalence
counit. The four ring fields now follow directly from the proved ring graph
lemmas by evaluation (use natural constants zero and one). The generic
`pullback_add_graph` and `pullback_zero_graph` prove the additive step for abelian
inverse image; compose them with the linear source-equivalence counit and the
ULift identifications to fill module addition and zero. For scalar action,
transpose through the set adjunction as in the proved ring graph lemmas. Use
`Adjunction.mapModAdjunction_unit_app_hom` and the linearity of the lifted
module-adjunction unit; the proved `pushforward_section_smul` identifies its
pointwise scalar action. Restriction along rho cancels the inverse coefficient
map in `inverseImageSectionRingUnit`. Finally compose with the linear
section-equivalence counit, choose exactly the constructed module functor, and
use its identity comparison isomorphism. All comparison data, unit compatibility,
ring graphs, and generic additive graphs compile without sorry. Finite-limit
preservation, the tensor comparison and algebraic inverse-image flatness are
already proved. No unfinished scratch declaration is included in the delivery.

The new statements were checked on zero rings/modules and empty sites: all
constructions use universal properties and finite-limit diagrams, without a
nonzero section or a nonempty cover assumption. No arbitrary object is defined
by choosing a witness of the remaining theorem; it is used only inside a proof.

## No longer needed

Removed the direct proof import
`Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`, replacing it by
`Sheaf.CategoryTheory.InternalSectionModuleFlat`. The equivalence remains a
transitive dependency and is used by the tensor proof.

Removed the direct import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses` and the
assigned node's direct dependency edge to
`lem-weil-pbc-flat-local-relations-universes`. Its role is handled by the existing
`FlatAlgebraicInverseImageOfUniverses` proof. This module remains a transitive
dependency of that proof, so no module is claimed pruned from the target closure.

The equational criterion remains directly used for flatness under module
isomorphism. No blueprint unit statement or realized proof step is bypassed.
The structural comparison uses adjunction-unit transposition, so it does not
need a separate tensor-monoidality theorem for the underlying-set comparison.
No such theorem or node was imported or added.

No whole module is withdrawn or deleted. No module is pruned from the target closure.

## Where the brief, the DAG or earlier work was wrong

The assigned node's plan correctly suggested the internal/section tensor
comparison, but did not provide it as a Lean declaration. That comparison has now
been constructed and proved. The plan also requires compatibility of internal
inverse image with the algebraic inverse-image presentation; the section-module
equivalence alone does not provide this. The remaining new theorem isolates
precisely that structural task, rather than restating flatness preservation.

The read-only local source snapshot initially lacked the assigned module and its
node, although they were present in the published compiled library. The original
source and node were recovered by a read-only read from the meeting repository.
No repository file was written or git operation performed by the worker.

The initial recovery dry run was refused by the delivery tool's budget guard:
it treats this recovery as a fresh 120-minute session and accepts a remaining
split-off only after minute 72, despite the brief's 40-minute recovery request.
The budget file and guard were left unchanged. During recovery, the main proof's
new global command context was removed, preserving the original interface;
the two new nodes received actual LeanSearch search records; and the concrete
comparison and unit proofs above were completed.

## New nodes

`lem-c2-internal-section-module-flatness` records the proved tensor and flatness
comparison in `Sheaf.CategoryTheory.InternalSectionModuleFlat`. Its proof uses
the existing internal/section equivalence and the existing definition of
site-flatness, with explicit universal-property glue proved in the new module.

`lem-c2-proetale-section-module-algebraic-inverse-image` records the remaining
geometric algebraic-operations identification in
`Sheaf.Paper.SectionModuleAlgebraicInverseImage`. It is strictly a structural part
of the argument and does not assert flatness. Its docstring and node describe the
full construction and operation verification needed for a subsequent proof.

No definition or statement repair was made, so no change record is needed.

## Second reading by C2

1. **Signatures and accidental changes.** Compared the assigned module with the
   repository version byte for byte at every existing declaration. The target
   theorem signature is unchanged; the two additional modules contain only new
   declarations and no consumer module is adapted. Verdict: pass.

2. **Proof and axioms.** Compiled all three sandbox modules in import order with
   `lcompile.py`. The target and the tensor-comparison theorem contain no
   `sorry`; the only remaining hole is the separately named structural theorem
   `exists_sectionModuleAlgebraicInverseImage`. Axiom inspection gives only
   `propext`, `Classical.choice`, and `Quot.sound` for the proved declarations;
   the target depends on the explicitly reported structural `sorryAx`. No
   forbidden declarations or hollow definitions occur. Verdict: pass.

3. **Split-off statements.** Checked both new nodes against the Lean
   declarations, searched the library and Mathlib for duplicates, and checked
   zero/empty cases. `flat_iff_sectionModule` is a proved equivalence and the
   structural inverse-image theorem is a strictly smaller identification with
   no flatness conclusion; its docstring and DAG node state the proof and source.
   Verdict: pass.

4. **Pruning and route.** The proof follows the unit route through the explicit
   internal/section tensor comparison, concrete set inverse image, algebraic
   inverse-image flatness theorem, and transport across isomorphisms. Removed
   only the obsolete direct local-relations import and dependency edge; retained
   the equational criterion and all transitive modules. Verdict: pass.

5. **DAG agreement.** Matched the target node's proof steps and dependencies to
   the imports and theorem applications, and matched both new nodes' statements,
   proof metadata, Lean records, chapter, and unit. Verdict: pass.

Changed during second reading: appended this review only; no Lean proof,
statement, definition, node, or import required repair.
