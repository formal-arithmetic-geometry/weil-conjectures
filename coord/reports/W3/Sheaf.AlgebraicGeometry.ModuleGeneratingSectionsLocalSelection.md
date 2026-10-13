## What changed

The statement and visibility of
`AlgebraicGeometry.Scheme.Modules.exists_finset_generatingSections_near_point`
are unchanged. Its proof now first lifts a finite free generating map locally,
then factors that finite free map through finitely many of the original basis
indices. Restriction preserves the epimorphic composite, and `epi_of_epi_fac`
proves that the resulting finite-support map is epi.

Added the proof-only imports `Sheaf.AlgebraicGeometry.ModuleFiniteFreeLocalLift`
and `Sheaf.AlgebraicGeometry.ModuleFiniteFreeLocalSupport`. Each new module states
one strictly separate part of the original argument. Updated the original node's
proof, proof dependencies and proof origin to match the composition in Lean.
The unit `sk-thm-p1` and all its realized statement/step nodes are unchanged.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_finset_generatingSections_near_point`
(node `lem-weil-pbc-module-generating-sections-local-selection`).
There are no sorries left in the item's module.

Added these two named holes:

- `AlgebraicGeometry.Scheme.Modules.exists_finite_free_local_lift`
  (node `lem-weil-pbc-module-finite-free-local-lift`). Its source sheaf is
  arbitrary, and its conclusion produces no finite support or subset of the
  specified generators: it handles finite-generator local lifting alone.
- `AlgebraicGeometry.Scheme.Modules.exists_finite_free_local_support`
  (node `lem-weil-pbc-module-finite-free-local-support`). It factors an arbitrary
  finite free source map to a free sheaf locally, without any epimorphism or
  finite type target assumption.

This is a decomposition, not a net proof gain: one hole closed, two holes added,
net -1. The proof combining these separate parts is complete Lean, using map
composition, the factorization equality, preservation of epimorphisms under open
restriction, and the epi right-factor criterion.

## No longer needed

No original import was removed and no module is claimed pruned. These old direct
proof dependencies are replaced by the two intermediate nodes in the item's proof:

- `def-weil-pbc-module-finite-type-presentation`;
- `lem-weil-pbc-ringed-space-module-exactness-local-lifting`;
- `lem-weil-pbc-module-stalk-filtered-colimit`.

All three remain in the intermediate proof plans. The restriction-colimit node
remains a direct dependency. No realized unit step is bypassed.

The new modules import only the public APIs their signatures use instead of the
broader `Coherent` module. The local lift imports the planned local-exactness
module privately; the local support imports the planned stalk-colimit module
privately. These proof-plan imports are retained for the named open theorems.

## Where the brief, the DAG or earlier work was wrong

No false statement or source error was found. The extra attempt to prove the
local-lifting intermediate transported finite generators through the iterated
slice equivalence, then drafted the finite-family lift. The complete experiment
exceeded the 60-second compiler limit, so it is excluded from the delivery; the
intermediate is left as exactly `:= by sorry`. The original single proof step
bundled local lifting and finite support without interfaces for those separate
arguments. The existing local-lifting and stalk-colimit declarations do not
provide those composed interfaces directly; the new statements isolate them.

Mathlib searches read `GeneratingSections.lean`, `Free.lean`, and
`PushforwardContinuous.lean`; `GeneratingSections.ofEpi` maps generators forward
but does not locally lift them. `freeMap` describes basis maps but does not
assert finite support for a local morphism. LeanFinder and Loogle yielded these
partial APIs, and grep gave no matching local-support result. LeanSearch was
unavailable (Internal Server Error), recorded as unavailable rather than as
absence. Full-blueprint searches for finite free local lift/support gave no
matching blueprint statement.

Read Stacks Tags 01B8, 01BB and 01AH online: the local argument follows their
finite-generator lifting, colimit capture, and stalk-colimit descriptions.
Edge cases checked: zero finite free rank permits the empty support and the
unique zero-source map; empty basis type gives a zero target free sheaf;
empty K or U has no point to which the respective statement applies. No
quasi-coherence, compactness or finite presentation was added.

## New nodes

`lem-weil-pbc-module-finite-free-local-lift` is stated in
`lean/Sheaf/AlgebraicGeometry/ModuleFiniteFreeLocalLift.lean` and records local
lifting of finite type generators through an arbitrary epimorphism, with its
complete proof in words and source Stacks 01B5/01B8.

`lem-weil-pbc-module-finite-free-local-support` is stated in
`lean/Sheaf/AlgebraicGeometry/ModuleFiniteFreeLocalSupport.lean` and records local
finite basis support of a finite free map, with its complete proof in words
and source Stacks 01BB/01AH. Both nodes inherit the item's chapter and unit,
and point to the same blueprint ancestor through the item's node.

No interface change record or forced adaptation is needed.

## Second reading by W3

1. Compared the original module with the repository using diff, and compared
   the existing theorem's text from `theorem` through the signature byte for
   byte. PASS after removing one accidental extra space before `:=`.
   Hypotheses, conclusion, universe, visibility, and original docstring are
   unchanged. The other two modules are new. No definition, target statement,
   or module held by another group is edited; no interface change record is needed.
2. Read the composition proof: local lifting gives an epi composite, finite
   support gives the factorization, open restriction preserves the epi, and
   `epi_of_epi_fac` gives the desired right factor. All three delivered modules
   compile locally without warnings. Only the two named new theorems have
   `sorry`; no data definition or forbidden declaration is added. A scratch
   copy checks the axioms of all three declarations: exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. The original theorem is
   conditional on the two open statements, not a completed axiom-free proof.
3. PASS on mathematical truth and strict decomposition. The lift lemma handles
   an arbitrary source and chooses no basis support; the support lemma handles
   an arbitrary finite-free map and assumes neither epi nor finite type of its
   target. Neither restates the item. Checked zero rank, empty index type, empty
   opens, and arbitrary non-quasi-coherent sheaves. The source arguments in
   Stacks 01B8, 01BB (local paragraph only), and 01AH support the docstring proofs.
   Independently searched using finite collections lifting through an epi,
   factorization through a finite subcoproduct, `freeHomEquiv`, and local support
   via LeanFinder, Loogle, msearch grep, and rg in both library roots and Mathlib.
   `FiniteFreeConstantLocalLift` is for etale constant coefficient sheaves, not
   these structure-module sheaves. `ModuleFiniteTypeImageExtension` has a private
   finite-section lift, but does not state this restricted finite-free result.
   Mathlib's `isColimitFiniteSubproductsCocone` supplies the first categorical
   step of the support proof, not the remaining local factorization; recorded
   this partial match in its node. No split statement closes in a few minutes
   from these APIs: finite intersections, section representatives, and slice
   equivalences still need a Lean argument.
4. PASS on route: the item uses the two intermediate theorems with a real
   categorical composition proof. All original direct dependencies omitted
   from its new `proof_deps` are now explicitly listed under No longer needed,
   with their retained intermediate uses. No module is claimed pruned.
   Read `dag/units/sk-thm-p1.json` and its realized statement/step nodes: the
   local module argument is below those steps and bypasses none of them.
   Narrowed the public imports of both new modules and added the private
   imports for their open proof plans. The original public import is preserved.
5. PASS on metadata: every lean.statement matches its theorem signature, every
   proof_deps equals the union of the proof-step uses, and the item's proof
   records the actual lifting, factorization, restriction and epi cancellation.
   Its only changed node fields are proof, proof_deps and proof_origin. Both new
   nodes have source, complete proof steps, searches, creation, blueprint,
   chapter/unit, status split and Lean records. Removed the support node's
   extraneous finite-type statement dependency, since it assumes no finite type.

Second reading changed signature whitespace, new-module imports, the support
node's statement-dependency list and partial Mathlib search record, and report
pruning/review details. The proof bodies and the two named remaining holes are
unchanged. This remains one original hole closed and two strictly separate
holes added, net -1, a decomposition rather than a net proof gain.
