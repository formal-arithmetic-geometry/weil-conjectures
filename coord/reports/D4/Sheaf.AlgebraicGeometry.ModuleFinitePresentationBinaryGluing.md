## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Scheme.Modules.exists_finitePresentation_binary_gluing`
with the concrete pullback `binarySubmodule` and its first projection. The existing
`binarySubmodule_restrictions` theorem needs neither monicity nor quasi-coherence,
so it applies to the replacement map without extra hypotheses. Transport finite
presentation through its two restriction isomorphisms. A proved private helper
`finitePresentation_binary_local` supplies locality on the union using the
source library's `IsFinitePresentation.of_coversTop` and
`isFinitePresentation_pushforward_of_isLeftAdjoint`. Its slice equivalence and
cover proof follow the already proved `ModuleBinaryLocalProperties` implementation,
with finite presentation in place of finite type.

The statement, universe, visibility, and existing docstrings are unchanged.
The public import of `Coherent` is unchanged. The proof imports
`ModuleSubmoduleBinaryGluingProperties` and the source-library `Quasicoherent` module.
The DAG proof and its dependencies now describe this concrete route.

Read the gluing paragraph of Stacks 01PI and the object/morphism gluing argument
of 00AK online (the literature sources are not installed in this clone).
The pullback restricts to the given modules even when an open is empty, the
opens coincide, or they are disjoint. The overlap hypothesis is used only for
the restriction on W; the identification on V is unconditional. The local
cover argument uses point membership in the union, with no compactness or
quasi-separatedness. The target node is below the unit's realized statements
and steps, so this changes no unit route.

Searches: LeanFinder for locality of finite presentation returned the predicates
and local data; Loogle for `SheafOfModules.IsFinitePresentation` returned its
class and witnesses; grep of both library roots found the proved source-library
locality and transport lemmas and the recently landed concrete pullback
restriction theorem. Both new proof-import directions were checked and are acyclic.

## Proved and sorry left

Closed one original hole with a complete, compiled proof term:
`AlgebraicGeometry.Scheme.Modules.exists_finitePresentation_binary_gluing`
(node `lem-weil-pbc-module-finite-presentation-binary-gluing`).
Added zero holes. No sorry remains in the delivered module; the private locality
helper is completely proved. The reused construction and restriction modules,
and the source-library locality module, contain no sorry.

## No longer needed

Removed proof import `Sheaf.Topology.GlueSheavesOfModules`.
This proof no longer directly needs `lem-weil-pbc-glue-sheaves-of-modules`
(`Sheaf.Topology.GlueSheavesOfModules`), or the planned open-immersion restriction
lemma `lem-weil-pbc-module-restriction-open-immersion-colimits`
(`Mathlib.AlgebraicGeometry.Modules.Sheaf.restrictFunctor/restrictAdjunction`).
The latter Mathlib module remains transitively public through the unchanged
statement import; no claim of global unreachability is made.
The generic descent branch, including `lem-weil-pbc-module-object-open-descent`
(`Sheaf.Topology.ModuleObjectOpenDescent`), is unnecessary for this item's proof.
The definitions of module sheaves and finite presentation remain needed.
No affine replacement, affine sections, or finite-type submodule gluing theorem
is imported or used; only its separate concrete construction and restriction
properties are reused.

## Where the brief, the DAG or earlier work was wrong

The planned generic object and morphism descent is valid but unnecessary:
the concrete pullback restriction theorem already supplies both required local
identifications without a monomorphism hypothesis. The existing theorem's
"submodule" naming does not impose monicity on the construction or its
restriction properties. No statement correction or forced adaptation was needed.

The original retry failed because three existing dependency modules were missing from
this machine's compiled snapshot. Their unchanged source files were initially included in the
sandbox solely to compile the dependency overlay with lcompile.py. The second reader
removed these copies after the shared snapshot acquired their compiled modules.
They did not change the repository sources. The first worker compiled the overlay
and target successfully.
All declaration axiom probes passed. The dry run printed OK (commit 7b3f8a2f79),
with no push. The static interface check requires a record for the additional local
open command: `coord/changes/finite-presentation-binary-gluing-proof-interface.md`.
The independent second reading is recorded below.


## Second reading by D4

1. Compared all four sandbox modules against the repository. The three dependency
   overlay modules are byte-for-byte identical. The item's existing theorem signature,
   universe, visibility and docstring are byte-for-byte unchanged. Only its proof,
   private locality helper, proof imports and local open command differ. Verdict: pass.
2. Read the complete proof and the concrete pullback definitions and restriction
   properties. There is no arbitrary witness chosen from an unproved existence theorem.
   No delivered Lean file contains sorry, axiom, unsafe, opaque, implemented_by or extern.
   Compilation and axiom validation are checked below and by deliver3.py. Verdict:
   the argument is a proof, subject to those compiler checks.
3. No statements are split off and no holes are added. The fully proved private
   locality helper is exactly the required two-open finite-presentation locality fact.
   Empty opens, equal opens and disjoint opens satisfy both the restriction and cover
   arguments without additional hypotheses. Verdict: pass; no new node is required.
4. Searched the library with finite-presentation/locality/restriction terminology.
   The existing source-library locality and equivalence-transport lemmas are already
   used; no shorter binary restriction locality theorem was found. Both new imports
   serve only the proof and are plain imports. The report lists both old proof_deps
   removed, and the extra generic descent branch. The item is absent from all realized
   entries of sk-thm-p1, whose statement and steps are unchanged. Verdict: pass.
5. Compared the node JSON: only proof, proof_deps and proof_origin change. They describe
   the concrete pullback, its two restriction isomorphisms, transport of finite
   presentation and the two-open cover. Their uses union equals proof_deps. All other
   node fields are unchanged. Verdict: pass.

Second reading removed the three byte-identical dependency overlay source files,
now present in the refreshed shared compiled snapshot, after the second-restriction
overlay compile timed out twice. They are not part of the delivery. Updated this
report to record the independent review; no Lean proof repair was needed. One original hole closed, zero added, zero split off.
