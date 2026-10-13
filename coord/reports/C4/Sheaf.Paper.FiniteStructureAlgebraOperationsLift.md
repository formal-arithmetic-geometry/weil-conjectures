## What changed

Corrected `AlgebraicGeometry.finite_structure_algebra_operations_lift`'s `hc` to the
inverse of `Scheme.Modules.tensorPullbackCompositionIso`, the explicit mate built from
the same pinned adjunctions used in its conclusion. Its conclusion is unchanged. This
repairs the existing statement dispute. The corrected normalization argument is at
the end of the argument list so obsolete callers fail promptly at their argument
boundary rather than expanding the conflicting comparison formulas. The public import of
`TensorPullbackCompositionIso` supplies the definition used in the corrected signature.
No target signature or definition is changed.

The theorem now has a complete Lean proof from the algebra-construction part and a
proved general adjoint-transition theorem. Functoriality and naturality transport
`hψ` across `e.hom`; ring-hom extensionality and the adjoint section formula give the
transition equality. Local irreducibility attributes stop needless unfolding of the
explicit tensor-pullback construction during elaboration.

Added `FiniteStructureAlgebraAdjointsConstruct`, containing only algebra construction
and the section formula, without the transition equality. Added
`FiniteStructureAdjointTransitions`, whose theorem is fully proved: the mate unit equation,
base-change adjoint formula, unit naturality, and naturality of pushforward composition
produce a module equation. Evaluation on sections and uniqueness of open-poset morphisms
identify its transport with `appLE`. This general theorem needs neither properness,
coherence, finiteness, cartesianness nor invertibility of the module maps. Its explicit
`finiteStructureAdjoint` definition contains no postponed data.

`FiniteStructureAlgebraLift` is a forced adaptation with its entire existing signature,
visibility, docstring and imports preserved. Its original application uses the now-invalid
bare-comparison `hc`. The proof is reopened as the existing named theorem hole and marked
`STATEMENT-DISPUTED`; no unproved normalization assertion is used to preserve the proof.
See `coord/changes/finite-structure-algebra-canonical-comparison.md`.

Searched with Lean Finder, Loogle and grep; LeanSearch returned Internal Server Error. Also read the original dependency interfaces,
Mathlib's adjunction mates, the new explicit composition comparison, the unit route
`sk-thm-p1`, and Stacks 09ZT, 088E and 0CYS online. No shorter sheaf-algebra construction
was found. The unit's statement and realized steps stay unchanged.

## Proved and sorry left

The corrected `AlgebraicGeometry.finite_structure_algebra_operations_lift` has no direct
hole. Its proof is a decomposition, not a proof of the former disputed signature.

`AlgebraicGeometry.Scheme.Modules.finiteStructureAdjoint_transitions`
(`lem-weil-pbc-finite-structure-adjoint-transitions`) is proved without `sorry`.

One new hole is split off:
`AlgebraicGeometry.finite_structure_algebra_adjoints_construct`
(`lem-weil-pbc-finite-structure-algebra-adjoints-construct`). It is strictly the algebra
construction and section formula; the transition assertion is omitted and is proved
separately. Its docstring includes the source, the proper-support unit construction,
tensor-power coherence, full-faithfulness lifting, checking the identities, building the
ring sheaf and adjoint maps, and empty/zero edge cases.

One existing hole is reopened by the forced adaptation:
`AlgebraicGeometry.finite_structure_algebra_lift`
(`lem-weil-pbc-finite-structure-algebra-lift`). The unchanged caller still has the disputed
old comparison hypothesis; it requires a later interface correction propagated through
its own callers. Keeping its old proof would require the very unsupported normalization
this delivery repairs. Closed one assigned hole, added one split hole and reopened one
existing caller hole; net hole change is +1, not net proof progress.

There are no other holes in this delivery. In particular neither `finiteStructureAdjoint`
nor any other definition selects data from an unproved existence statement.

## No longer needed

Removed these direct proof imports from the assigned module and moved their planned uses
to the algebra-construction item:

- `Sheaf.AlgebraicGeometry.GrothendieckExistence`
- `Sheaf.AlgebraicGeometry.ModuleSupportProperOverBase`
- `Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections`
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`
- `Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
- `Sheaf.AlgebraicGeometry.ModulePullbackTensor`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`

The assigned module imports the two new parts instead. Its old public TensorPullback
import is replaced by the public TensorPullbackCompositionIso import, which reexports
the same tensor-pullback API. The arbitrary `Nonempty` comparison no longer appears in
its signature or proof. No original proof-dependency node is globally pruned: the
algebra-construction item still needs them. No unit statement or step is bypassed.
The same direct public dependencies of the original conclusion stay available.

The original node’s direct proof dependencies replaced by the two new parts are:

- `lem-weil-pbc-module-support-proper-over-base`
- `def-sbc-closed-immersion-ideal-sheaf`
- `lem-weil-pbc-quasi-coherent-tensor-product-affine-sections`
- `lem-weil-pbc-quasi-coherent-finite-type-affine`
- `pqf-lem-coherent-ft-locnoeth`
- `lem-weil-pbc-quasi-coherent-module-cokernel-image`
- `lem-weil-pbc-module-pullback-tensor`
- `lem-weil-pbc-module-tensor-symmetric-monoidal`
- `lem-weil-pbc-affine-pushforward-base-change`
- `prop-weil-pbc-grothendieck-existence`
- `def-weil-pbc-comm-algebra-sheaf`
- `def-pc-module-pullback`

They remain prerequisites of the construction split; this removes no module from the
targets’ import closure. “No longer needed” here describes the assigned proof’s direct
dependencies, not global pruning.

## Where the brief, the DAG or earlier work was wrong

The existing marker correctly identified a real interface error. The node called `c`
canonical, but `hc` fixed it to a choice from bare `Nonempty`, which cannot retain
compatibility with the section-formula adjunction. Proof irrelevance means that unfolding
the proof of `nonempty_tensorPullbackComp` cannot recover the witness it constructed.
Natural module isomorphisms may differ by signs; such differences need not preserve the
unit. No equality with the explicit canonical mate is available or asserted here.

The current repository already has `TensorPullbackCompositionIso`, so the repair now
uses that transparent definition. The new transition proof checks its unit equation by
`unit_conjugateEquiv_symm`; it does not assume it in a new hole. At the beginning this
new module was absent from the last green compiled cache; it became available on refresh.
The brief's rule to wait rather than duplicate landed interfaces was respected.

GrothendieckExistence also still states its full-faithfulness clause using the old bare
comparison. The new algebra-construction item follows the source full-faithfulness proof
for the canonical comparison; its worker must repair that interface or use the supported
completion Hom theorem underneath it. It must not assert an equality between the old
choice and the explicit mate. That further interface repair is outside this delivery.

The caller still assumes the unnormalized choice, and this delivery cannot soundly prove
that hypothesis implies the repaired one. Its forced proof reopening is explicit. The
change record names the only direct declaration user; the 194 transitive import users
retain their interfaces through that caller. No error in the Stacks source or unit route
is alleged.

## New nodes

`lem-weil-pbc-finite-structure-algebra-adjoints-construct` is the source's algebra
construction, separated from transition compatibility. Its module is
`Sheaf.Paper.FiniteStructureAlgebraAdjointsConstruct`; its statement omits the entire
transition clause. Its named hole is the remaining proper-support algebra construction.

`lem-weil-pbc-finite-structure-adjoint-transitions` is a general adjunction calculation
used for the final transition clause. Its module is
`Sheaf.Paper.FiniteStructureAdjointTransitions`; its theorem is fully proved.

The original node's route, `proof_deps` and Lean statement are updated. Its
`statement_change` records the canonical-comparison correction, source and sole citer.
The change record is `coord/changes/finite-structure-algebra-canonical-comparison.md`.

## Forced adaptations

### Sheaf.Paper.FiniteStructureAlgebraLift

The original module compiled against the baseline. Against the delivered corrected
module it failed at its original application:

```text
Application type mismatch: The argument hc has type
  ∀ n, c n = (Classical.choice ...).symm ≪≫ eqToIso ...
of sort Prop but is expected to have type ℕ → Scheme
in finite_structure_algebra_operations_lift A I X f i hi hp c hc.
```

A direct copy of the original caller was independently compiled with lcompile.py against
the sandbox overlay; the same error occurred at line 137. The following rcases failed
because the obsolete application has no well-typed result. This evidence is retained in
`scratchpad/caller-corrected-interface.log`.

Changed the original proof at lines 135 onward to `:= by sorry`, and added only the
statement-dispute comment. All existing signatures, visibility and imports stay identical.
The comparison correction makes the original application unusable. Reordering its
arguments would not repair the substantive problem: its old hc does not provide the new
normalization. Keeping the rest of the proof would require a local sorry at the application,
forbidden by the stage-3 contract. The theorem remains the named existing hole with its
original source and proof docstring. Its adapted module compiles. The change record names
it as unclaimed and explains these necessary changes.

## Second reading by C4

1. Compared both existing delivered modules with the repository using diff. The only
   existing signature change is the declared, recorded canonical-comparison correction
   and relocation of hc in finite_structure_algebra_operations_lift. Its conclusion
   is unchanged. The forced caller retains its signature, visibility, imports and
   docstring byte for byte. No target or definition changes. Verdict: pass as a
   recorded intermediate-statement repair, not a proof-only delivery.
2. Read the complete construction, transition and operations modules and the caller
   adaptation. The only direct holes are the named construction theorem and reopened
   caller. There are no forbidden declarations or hollow definitions. The explicit
   finiteStructureAdjoint uses the adjunction theorem’s explicit sectionwise unit formula, which
   determines the unit used downstream; it does not use bare existence of an
   adjunction. Read TensorPullbackAdjunction to check this normalization. Local
   compilation and the delivery tool's declaration-axiom probe are required to pass
   before this second reading is delivered. Verdict: the transition calculation is a
   real proof; the operations theorem is a decomposition with an open construction.
3. Checked the split against Stacks 09ZT, 088E and 0CYS and read its full docstring and
   node. Tensor powers and the proper supporting quotient permit full-faithfulness
   lifting; faithfulness checks the ring laws. Tested I=0, the zero module, empty
   schemes and empty opens: no extra nonzero or nonempty hypothesis is needed. The
   omitted transition conclusion is independently established by the general theorem,
   so the split is strictly part of the argument rather than a renamed restatement.
   Fresh LeanFinder search for “full faithful formal completion lifts algebra objects
   multiplication unit” found ring-completion maps only. Loogle confirmed the actual
   adjunction naturality component; grep and rg found no existing sheaf-algebra lift.
   Verdict: true, needed split; no quick closure found.
4. Read the proof top down: construction gives B,e,b and their formula; naturality
   transports hψ; the general adjunction calculation proves the transition equation;
   ring-hom extensionality finishes. The new public transition import in the
   construction module is necessary for finiteStructureAdjoint in its signature.
   Other new proof-only imports are plain import. The old planned construction
   dependencies remain only in the construction module. Read sk-thm-p1.realized;
   none of its nodes or steps is removed or bypassed. Verdict: pass; no globally
   pruned module.
5. Checked the original node's new proof steps and dependency union against the Lean
   proof, and both new nodes' statements, source, searches, creation/blueprint fields
   and Lean records. The construction node preserves the remaining plan; the general
   node describes the mate-unit, base-change and section calculations implemented
   by the proof. The change record identifies the sole direct caller, the preserved
   transitive interfaces and the forced reopening. Verdict: pass.

Second reading changed only this report: explicitly enumerated every replaced old
direct proof-dependency node and documented the five checks. No sound Lean proof was
rewritten. This delivery is an interface repair and decomposition, with net +1 hole,
not a claim to have proved the original disputed statement.

The separate scratch #print axioms check compiled successfully. finiteStructureAdjoint
and finiteStructureAdjoint_transitions use exactly propext, Classical.choice and
Quot.sound. The construction, operations theorem and reopened caller additionally
use sorryAx, as expected from their named open construction/caller holes. The scratch
file was removed from the delivery. Evidence: scratchpad/second-reading-axioms.log.

## Forced adaptations

### Sheaf.Paper.FiniteStructureAlgebraLift
Original against changed dependencies failed:
```
/tmp/forced-adaptation-gmyk9it6/lean/Sheaf/Paper/FiniteStructureAlgebraLift.lean:137:63: error: Application type mismatch: The argument
  hc
has type
  ∀ (n : ℕ), c n = (Classical.choice ⋯).symm ≪≫ eqToIso ⋯
of sort `Prop` but is expected to have type
  ℕ → Scheme
of sort `Type (u + 1)` in the application
  finite_structure_algebra_operations_lift A I X f i hi hp c hc
/tmp/forced-adaptation-gmyk9it6/lean/Sheaf/Paper/FiniteStructureAlgebraLift.lean:136:9: error: Tactic `rcases` failed: `x✝ : ?m.1063` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-gmyk9it6/.lbuild) [7.9 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
