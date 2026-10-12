## What changed
Replaced the invalid saved attempt with a canonical germ construction. The original
statement and docstring are unchanged. Two new modules isolate injectivity of the
terminal germ and identification of its image with the invariant subgroup. The second reader proved injectivity directly. The
main module constructs an additive homomorphism, restricts it to invariants, proves
it bijective from those statements, and constructs its additive equivalence.
Naturality is proved from Mathlib germ naturality and naturality of i inverse.
No arbitrary family of equivalences or false naturality statement is used.

## Proved and sorry left
Closed the original hole in
`AlgebraicGeometry.Scheme.etaleGlobalSections_galoisInvariants` by decomposition.
The second reader also closed
`AlgebraicGeometry.Scheme.etaleGlobalSections_galoisInvariants_injective`,
node `aux-etale-global-sections-injective`, by a complete separatedness proof.
One added hole remains:
- `AlgebraicGeometry.Scheme.etaleGlobalSections_galoisInvariants_image`,
  node `aux-etale-global-sections-image`.
No holes remain in the original module or the injectivity module. Relative to
the repository this is one original hole closed and one new hole added (net
zero), a decomposition rather than a fully sorry-free comparison. Relative to
the first worker's saved attempt, the second reading closed one auxiliary hole.

## No longer needed
Removed the original proof import `Sheaf.AlgebraicGeometry.AbelianSheavesGModules`
and its dependency node `lem-exc-abelian-sheaves-gmodules`: the direct germ proof
uses the supplied E and i rather than constructing another equivalence.
Removed the original proof import `Sheaf.FieldTheory.GaloisAutomorphismExtension`
from the main module, but its node `lem-exc-galois-automorphism-extension` remains
needed below the new image theorem; this is not global pruning of that node.
Discarded the invalid saved nodes `aux-etale-global-sections-pointwise` and
`aux-etale-global-sections-naturality`, and the duplicate saved Lean files.
No unit statement or unit step is bypassed; the assigned node is not a realized
unit statement or step in `dag/units/sk-thm-br.json`.

## Where the brief, the DAG or earlier work was wrong
The saved naturality assertion for arbitrary additive equivalences was false.
Different signs on two isomorphic constant integer sheaves give a counterexample.
The repair fixes the forward map to be the canonical terminal germ transported
by i inverse, so naturality follows from actual natural transformations.
The saved new statements also lacked complete proof docstrings and were placed
in the original module rather than separate modules; both problems are repaired.
The local Stacks source is absent; Tag 04JM was read at
https://stacks.math.columbia.edu/tag/04JM, including its direct descent proof.

## New nodes
`aux-etale-global-sections-injective`, in
`Sheaf.AlgebraicGeometry.EtaleGlobalSectionsGaloisInjective`, isolates uniqueness
of global sections with the same germ, proved mathematically by separatedness
for a nonempty etale covering of Spec K. This statement is valid even for the
zero sheaf and requires no nonzero-section hypothesis.

`aux-etale-global-sections-image`, in
`Sheaf.AlgebraicGeometry.EtaleGlobalSectionsGaloisImage`, isolates existence of
descent and invariance of the canonical terminal germ. The finite Galois cover
argument works with transcendental Omega and with a trivial Galois group.
Each new module has one named theorem with its source, complete proof in words,
and exact signature recorded in its node. No change record is required because
no existing interface or statement has changed.

## Second reading by A2

1. Compared the existing module and node with the repository using diff. The
   original theorem signature and docstring are byte-for-byte unchanged. The
   only existing node fields changed are proof, proof_deps, and proof_origin.
   The auxiliary injectivity signature is new and now omits the unnecessary hi
   assumption. No existing definition, target, or public import changed. PASS.
2. Compiled all three delivered modules with lcompile.py. Injectivity now has
   a complete proof; only the named image theorem has sorry. There are no new
   definitions, arbitrary witness constructions, or forbidden declarations.
   AddEquiv.ofBijective uses the explicitly constructed canonical germ map;
   its inverse is uniquely determined by bijectivity. Axiom probes check the
   standard three axioms and the remaining sorryAx. PASS.
3. Checked both geometric claims against Stacks Tag 04JM's direct proof and
   tested zero sheaves, separably closed K, trivial Galois groups, and
   transcendental Omega. Injectivity is independent of action compatibility.
   The image claim is genuine descent, not a restatement of the natural additive
   equivalence. Independent leanfinder, loogle, grep, and repository searches
   found no applicable exact theorem. The nearby fieldSections_stalkInvariants
   and exists_fieldSection_of_invariant_germ assume Algebra.IsAlgebraic K Omega
   and thus do not prove this general statement. PASS.
4. The canonical forward map makes naturality follow directly from germ and
   i inverse naturality. Closed injectivity via Mathlib's filtered colimit
   equality criterion and sheaf separatedness. Removed unused abelian-sheaf
   equivalence imports from both auxiliaries and the automorphism-extension
   import from injectivity; extension remains needed by the image proof plan.
   The old proof_deps are fully accounted for above. sk-thm-br.json realized
   fields are unchanged, and this node is not a realized statement or step.
   PASS.
5. Read all three node records against the final Lean. The main proof_deps
   name precisely its two auxiliary theorems. Injectivity has no DAG proof
   dependencies and now records the complete formal argument and its updated
   signature. Image retains the automorphism-extension dependency and a named
   whole-proof hole with a source and full mathematical proof docstring. PASS.

Changes by this reader: proved injectivity, removed its unnecessary hi binder,
pruned unused auxiliary imports, synchronized its node and this report. No
change record is required because the only changed signature belongs to a new
auxiliary declaration of this delivery.
