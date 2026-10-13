## What changed

Proved `AlgebraicGeometry.coherentFormalModule_affine_spec_transport` in
`Sheaf.AlgebraicGeometry.CoherentFormalModuleAffineSpecTransport`, with its existing
signature and public imports unchanged. Added the proof-only import
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine` for the proved affine
ideal-extension formulas. `FormalSystemsPullback` supplies both transport functors;
their underlying functor equations are retained to assemble the comparison.

The private, fully proved helper `affineSectionsIso` compares sections of arbitrary
module sheaves. Forward pushforward is inverse to backward pushforward; uniqueness
of left adjoints therefore compares forward pushforward with backward tensor
pullback. The top-ring equation and `restrictScalarsComp'` give the required linear
section comparison. Whiskering supplies all transition and morphism compatibility.
The node proof and dependencies now describe this route.

Validation: the complete module compiled without warnings with `lcompile.py`.
The second reading replaced three expensive definitional composition checks by
`Functor.whiskeringRight_obj_comp`; this reduced local compilation from roughly
50–60 seconds (including timeouts under load) to 7.7 seconds.
The proof uses no nonzero-ring, nonempty-open, or proper-ideal assumption; the
empty affine open and the zero and unit ideals use the same functorial formulas.
The declared statement was compared verbatim with the repository original.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.coherentFormalModule_affine_spec_transport`
(node `lem-weil-pbc-formal-affine-spec-transport`).
No sorry remains in the delivered module, and no holes or new nodes were added.
This is a proof from existing dependencies, not a decomposition into new holes.
It retains the existing dependency on `exists_formalSystemsPullback`.

## No longer needed

None: no original import or proof-dependency node was removed. Both public imports
are needed by the statement; both proof imports are used by the proof.
The planned `restrictAppIso` calculation is replaced by pushforward and adjoint
uniqueness, but no separate module or node for that calculation was imported.
`CoherentFormalModulesIsoEquivalence` was searched but is not imported: its
existential equivalence does not expose the underlying functor needed here.
The unit's statement and realized steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original plan omitted a named dependency for the
already proved affine ideal-extension formulas; the node now cites
`lem-pc-ideal-sheaf-comap-affine-extension`. The section comparison can be obtained
from the tensor adjunction (`nonempty_tensorPullbackAdjunction`, recorded by `def-pc-module-pullback`) and sectionwise
pushforward, avoiding explicit restriction-section transport.

Searches: launcher LeanFinder returned module-section isomorphism and pushforward
comparison tools; Loogle returned `restrictAppIso` and its scalar compatibility
lemmas; launcher grep and local rg found the proved affine ideal-extension module
and `coherentFormalModules_iso_equivalence`. The latter was read and its construction
used while retaining the forward-functor equation. No exact section-compatible
formal-module equivalence was found.

The local Stacks source file named by the node is absent on this machine. Read the
[087W](https://stacks.math.columbia.edu/tag/087W) affine correspondence and the
[087X](https://stacks.math.columbia.edu/tag/087X) affine reduction on the official
pages. This proof supplies the transport used by that affine reduction and does
not change its route or introduce completion arguments.


## Second reading by N3

1. Compared the entire delivered module and node with the repository versions.
   The existing theorem signature is byte for byte identical, including its local
   Noetherian-ring instance, both existential conclusions, and all hypotheses.
   No existing definition, visibility, or public import changed. The extra affine
   ideal-extension import is proof-only. Verdict: unchanged mathematical interface.
2. Compiled the whole delivered module locally without warnings. Checked for
   `sorry`, axioms, unsafe/opaque declarations and implementation overrides: none.
   In a scratch copy, `#print axioms` for the private `affineSectionsIso` and the
   target theorem returned exactly `propext`, `Classical.choice`, `Quot.sound`.
   Separate checks of `exists_formalSystemsPullback` and the tensor-pullback
   adjunction returned the same permitted axioms. The helper constructs its
   isomorphism from proved pushforward comparisons and the proved adjunction;
   there is no data chosen from an unproved mere-existence theorem. The formal
   transport functors are specified on objects and maps by their equations with
   fully faithful inclusions. Verdict: a kernel-checked proof, with no remaining
   `sorryAx` dependency in the checked compiled environment.
3. No statements were split off, no nodes were added, and no new holes exist.
   Read the private section comparison and checked inverse directions, scalar-map
   composition, and naturality. The argument applies to every module sheaf and
   assumes neither a nonzero ring nor a proper ideal, so the empty affine open and
   the zero and unit ideals require no exception. Rechecked Mathlib's adjoint
   uniqueness with launcher Loogle under `leftAdjointUniq` and searched the local
   library for section/pullback comparisons. The existing formal-module transport
   equivalence lacks the required underlying-functor equation; applying it alone
   cannot supply this section comparison. Verdict: no duplicate split or false
   edge-case claim.
4. Read the imported affine ideal-extension formulas, formal-system pullback
   theorem, tensor adjunction and identity/composition comparisons, and the
   existing `coherentFormalModules_iso_equivalence` proof. The transport follows
   the existing plan; adjoint uniqueness provides the shorter section comparison.
   Each import is used by the statement or proof. All old proof-dependency nodes
   remain used, so `No longer needed: None` is complete. Read the unit
   `dag/units/sk-thm-p1.json` and its realized statement and steps: this item is
   below those fixed steps, and no unit route is bypassed or edited. Verdict: the
   proof is pruned and the unit route is preserved.
5. Compared the node's three proof steps, dependency union and proof origin with
   the actual Lean construction. Both newly cited dependency nodes already exist:
   the affine-extension module supplies the ideal calculation, and the module
   pullback node records the tensor adjunction. The declaration and statement
   records remain unchanged. Verdict: the DAG agrees with Lean.

Changed only proof glue: replaced the three `rfl` proofs of whiskering-composition
identities by congruence of Mathlib's `Functor.whiskeringRight_obj_comp`, avoiding
large definitional unfolding. Updated the node's proof text and this report to
record that repair. No statement, definition, import, hole count, or unit changed
in the second reading.
