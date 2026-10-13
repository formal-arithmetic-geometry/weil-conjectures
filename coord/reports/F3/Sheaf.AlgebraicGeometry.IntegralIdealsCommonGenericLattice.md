## What changed

Repaired the landing-tool return about six duplicated helper statements. Removed
`local_clear_denominators`, `local_kill_denominators`,
`local_isQuasicoherent_pushforward`, `local_isFiniteType_over`,
`local_isCoherent_pushforward_of_isFinite`, and `local_isCoherent_unit`
from both new modules `CoherentPushforwardIdeal` and `CommonGenericLatticeMaps`.
Their names and statement copies no longer occur in the delivery.

Both modules now import the shared new module `FinitePushforwardFiniteType`.
Its proved theorem `isQuasicoherent_and_isFiniteType_pushforward_of_isFinite`
works on arbitrary schemes, without either Noetherianity hypothesis. It imports
and uses the existing `isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated`
instead of reproducing the affine quasi-coherence theorem or its denominator wrappers.
The restriction-of-generators construction occurs once inside its proof. Finite sections
follow by the existing affine criterion and `Module.Finite.trans`. This is a mathematical
generalization of the finite-type part of finite coherent pushforward, rather than a
renaming of the existing coherent-pushforward statement.

The two coherence arguments apply this shared result and the existing
`isCoherent_iff_isQuasicoherent_and_isFiniteType` criterion. Coherence of structure
modules follows directly from existing invertibility, finite-presentation and
quasi-coherence results. The kernel construction and generic stalk proofs are unchanged.
The original item's statement, visibility and public imports are unchanged. No existing
module other than the item is adapted, and no change record is required.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.Scheme.Modules.integral_ideals_common_generic_lattice`.

The delivery also contains complete proofs of these new declarations:

- `AlgebraicGeometry.Scheme.Modules.coherent_pushforward_ideal`, node
  `lem-pc-r2-coherent-pushforward-ideal`;
- `AlgebraicGeometry.Scheme.Modules.exists_common_generic_lattice_maps`, node
  `lem-pc-r2-common-generic-lattice-maps`;
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_and_isFiniteType_pushforward_of_isFinite`,
  node `lem-pc-f3-finite-pushforward-finite-type`.

No delivered declaration contains `sorry`; no new hole is added or split off.
The proof uses existing library statements, some with inherited proof holes, so this
reports closure of the local hole, not completion of the target's entire import closure.
All four modules compile in dependency order without warnings, each within 60 seconds.
The data are categorical kernels and their canonical inclusions or lifts. No object is
chosen from a mere unproved existence statement.

The generalization is valid for empty schemes, zero modules, and non-Noetherian affine
bases: a finite module over a finite algebra is finite over the base ring independently
of Noetherianity. The ideal coherence proof includes zero and unit ideals. The lattice
proof excludes zero ideals by its exact hypotheses and includes unit ideals. On the
spectrum of a field its maps are the full-ideal generic isomorphisms.

## No longer needed

Second reading also removed the redundant public import
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` from
`FinitePushforwardFiniteType`: its required finite-type declarations are already
publicly imported by `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`.

Removed the proof-only imports `Mathlib.AlgebraicGeometry.Morphisms.Finite` and
`Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine` from both coherence/lattice
helper modules. The finite morphism facts are supplied by the shared helper, and the
affine criterion is used only there. Both modules retain `QuasicoherentKernel` for
its existing structure-module quasi-coherence theorem. The six duplicated private
helper declarations listed above are removed from both modules.

No public import of the original item is removed. Its original seven proof-plan
interfaces are accounted for as follows:

- `lem-pc-closed-immersion-coherent-cohomology`: its broad interface is bypassed by
  finite-type pushforward and the coherence criterion.
- `lem-weil-pbc-quasi-coherent-module-kernel`: its separate ideal quasi-coherence
  argument is bypassed by coherent kernel closure; its module remains needed for
  the structure-module theorem.
- `lem-weil-pbc-finite-pushforward-coherent`: its cyclic module is not imported;
  the finite-type subargument is generalized in the shared new module, which uses
  the existing acyclic qcqs pushforward theorem.
- `lem-weil-pbc-coherent-kernel-cokernel-locnoeth`: retained in both helper proofs.
- `lem-weil-pbc-integral-scheme-ideal-generic-stalk`: retained in the lattice proof.
- `lem-weil-pbc-module-stalk-exact`: retained in the lattice proof.
- `lem-weil-pbc-closed-pushforward-stalks`: retained in the lattice proof.

No whole-library module is shown to be unreachable. The two helper nodes now refer
to the shared finite-type node instead of directly to the affine finite-type criterion;
the criterion remains needed inside that node. The unit
`sk-thm-picard-coherence` has empty realized fields; its intersection-comparison route
is retained and no realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned version copied six existing helper statements into each of two modules.
Making those copies private did not justify proving the same facts again. The repair
removes them, reuses the existing acyclic qcqs pushforward theorem, and proves a shared
finite-type generalization with genuinely weaker geometric hypotheses. The landing
checker now accepts each new module without duplicate-statement findings.

The existing `FinitePushforwardCoherent` module still cannot be imported here:
`import_direction.py may` confirms that it reaches this item and would close a cycle.
No tool or existing dependent module was changed to bypass this check. The new shared
module does not import higher cohomology or the cyclic coherence module.

New Lean Finder, Loogle and Mathlib grep searches are recorded in `searches.jsonl` and
the new node. LeanSearch was also queried and returned an Internal Server Error; its
unavailability is recorded without claiming a successful search. They found no exact Mathlib theorem for finite-type pushforward. The
existing library's qcqs pushforward and affine finite-type criterion supply its main
steps. The source argument was checked in Stacks Tags 01Y6 and 01LC: the finite
scalar-restriction argument of 01Y6 needs no Noetherian hypothesis, while 01LC provides
quasi-coherence. The source of the kernel intersection remains Tag 01YH.

The earlier report's second-reading section described the returned duplicated proofs.
It has been removed so the independent reader can review this repair afresh.

## New nodes

`lem-pc-r2-coherent-pushforward-ideal` records the proved coherence subargument.
Its proof now uses the shared finite-type result, the coherence criterion and coherent
kernel closure. Its statement and Lean signature are unchanged from the returned version.

`lem-pc-r2-common-generic-lattice-maps` records the proved comparison-kernel construction
and its generic-stalk isomorphisms. Only its coherence dependencies change to use the
shared finite-type result; the generic/stalk steps and statement are unchanged.

`lem-pc-f3-finite-pushforward-finite-type` records the new proved generalization on
arbitrary schemes, the acyclic existing qcqs theorem, restriction of finite generators,
finite scalar restriction and the affine criterion. Its Lean signature is copied verbatim,
its searches are actual recorded queries, and its node records the source and each step.

The original item's node still records assembly from the two proved subarguments.


## Second reading by F3

1. Compared every delivered module with the repository. Only the original item
   exists there; its diff adds two plain proof-only imports and replaces its one
   proof. Its theorem signature is byte-for-byte identical, as are its existing
   docstring, visibility and public imports. The other three modules are new.
   No definition, target statement or existing interface is changed, and no
   forced adaptation or change record is needed. Verdict: pass.

2. Read all four Lean modules and compiled them in import order with lcompile.py.
   After the import cleanup, runtimes were 32.5, 7.8, 11.0 and 2.5 seconds, with
   no errors or warnings. A lexical check found no sorry or forbidden axiom,
   unsafe, opaque, implemented_by, extern or skipKernelTC in delivered Lean.
   The kernel L, its inclusion d and the canonical kernel lift b are concrete
   constructions. The local-generators witness is extracted from Mathlib's
   proved finite-type characterization, not from an open existence theorem.
   The finite-type theorem axiom probe shows only propext, Classical.choice
   and Quot.sound, with no sorryAx. The other three public theorem probes show
   those same axioms and inherited sorryAx. This closes the item's local hole; it does
   not assert that its imported statements are all proved. Verdict: pass.

3. There are no split-off holes. Read each of the three new proved statements,
   its complete docstring argument and its node. Finite-type pushforward is
   valid without Noetherian assumptions: over A -> B finite, a finite B-module
   is finite over A; the qcqs pushforward theorem gives quasi-coherence. Empty
   schemes and zero modules cause no exception. Coherent ideal pushforward
   includes zero and unit ideals. For the lattice, the exact nonzero hypotheses
   imply both generic ideal inclusions are invertible; on Spec of a field they
   are full ideals. The kernel construction supplies their actual intersection,
   and stalk exactness and natural closed-pushforward comparisons transfer the
   two isomorphisms. Read Stacks Tags [01YH](https://stacks.math.columbia.edu/tag/01YH),
   [01Y6](https://stacks.math.columbia.edu/tag/01Y6) and
   [01LC](https://stacks.math.columbia.edu/tag/01LC); the non-Noetherian statement
   is the proved generalization of the scalar-restriction argument of 01Y6.
   Independent rg searches in lean/Sheaf and the upstream module sources,
   plus recorded Lean Finder, Loogle and Mathlib grep searches with different
   wording, found no accessible shorter replacement. Existing restriction
   helpers are private; FinitePushforwardCoherent would introduce the reported
   import cycle. Each new theorem proves a strict subargument or a reusable
   generalization and has a complete proof, rather than moving a hole.
   Verdict: pass.

4. Checked the original seven proof_deps individually against the new route.
   The report's No longer needed section accounts for each: the broad closed
   cohomology and cyclic finite-coherence interfaces are bypassed; the separate
   ideal quasi-coherence argument is unused, while its module still supplies
   structure-module quasi-coherence; coherent kernels, generic ideal stalks,
   stalk exactness and closed-pushforward stalk naturality remain in use.
   No whole-library module is claimed pruned. The unit record
   dag/units/sk-thm-picard-coherence.json has empty realized fields and is
   unchanged; the intersection comparison route is preserved. All retained
   public imports in the new modules provide notions in their statements.
   Removed the redundant Generators public import from the finite-type module,
   since Quasicoherent already publicly supplies it. Verdict: pass after cleanup.

5. Compared the existing node fields: only proof, proof_deps and proof_origin
   change. All four lean.statement records occur verbatim in their modules,
   and each proof_deps is exactly the union of its steps' uses. Read the node
   proofs against the actual kernel, scalar-tower and stalk calculations;
   the two target dependencies are the proved subarguments used by the tuple
   assembly. New nodes have source, chapter/unit, creation, blueprint, actual
   recorded searches and Lean records. No signature record was weakened.
   Verdict: pass.

Second-reading changes: removed one redundant public import, added independent
search records and a four-theorem scratch axiom probe, and wrote this review.
No mathematical proof or statement needed repair. Holes closed remain one;
holes added remain zero.
