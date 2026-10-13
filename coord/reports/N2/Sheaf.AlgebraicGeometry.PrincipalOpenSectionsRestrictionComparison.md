## What changed

Proved `AlgebraicGeometry.principalOpenSections_restriction_quasiIso_iff`. Added a private natural isomorphism between the two section functors after forgetting module scalars, using the canonical equality between an open and the underlying open of its topological restriction. Transported this isomorphism to cochain complexes and used Mathlib's quasi-isomorphism preservation and reflection under additive exact forgetful functors.

## Proved and sorry left

Closed one existing hole: `AlgebraicGeometry.principalOpenSections_restriction_quasiIso_iff` (node `lem-sc-principal-open-sections-restriction-comparison`). Added zero holes and split off zero statements. No `sorry` remains in the delivered module. This is a proof, not a decomposition.

## No longer needed

No proof-dependency imports were removed. The proof uses `Mathlib.Algebra.Homology.QuasiIso` in addition to the existing section and global-sections modules. No DAG nodes were pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan describes the comparison informally; its naturality and scalar-forgetting steps require an explicit functor isomorphism and transport through `mapHomologicalComplexCompIso`, which are supplied in the proof.


## Second reading by N2

1. Compared the only delivered Lean module against the repository with `diff -u` and checked the existing theorem signature byte for byte: identical. Its docstring is also unchanged. Changes are confined to its proof, a private fully constructed natural isomorphism, local elaboration options, and the proof-only `import Mathlib.Algebra.Homology.QuasiIso`. No existing definition, statement, visibility, or public import changed; no change record is required. Verdict: pass.

2. Compiled the delivered module with `lcompile.py`: no errors or warnings (50.9 seconds). Compiled a scratch copy with `#print axioms` for both `principalOpenSections_restriction_quasiIso_iff` and `sectionsForgetIso`: each uses exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` (52.6 seconds). Scanned the delivered Lean source for forbidden declarations and holes: none. The private isomorphism constructs its components from presheaf functoriality and a proved equality of opens; it chooses no witness from an unproved existence theorem. Verdict: pass.

3. There are no split-off statements or new public statements, modules, or nodes. Checked the private comparison for an arbitrary open: equality with the underlying open of the terminal object is pointwise and remains valid for the empty open. Thus g = 0, g = 1, the zero ring, and zero complexes require no additional assumptions. Naturality is precisely presheaf-module naturality. Independent `msearch.py grep` for `quasiIso_map_iff_of_preservesHomology|overEquiv.*[Ss]ection|[Ss]ection.*overEquiv` found the generic Mathlib quasi-isomorphism API already used, with no exact section-functor comparison. Read Mathlib's `restrictAppIso` and `overMapCompOverEquiv`: they concern the other open-immersion restriction presentation, so using them here adds transport rather than shortens this direct component construction. Verdict: pass.

4. Read the proof from its conclusion downward: it reduces the iff to an arrow isomorphism of underlying additive complexes and Mathlib preservation/reflection of homology. The private comparison supplies only the missing natural identification. Both original imports are required by the public statement (`affineOpenSections` and ringed-space `globalSectionsFunctor`), and the added homology import is proof-only. Both old proof dependencies remain used, so `## No longer needed` is complete. Read `dag/units/sk-thm-picard-duality.json`: this item is below its unit route; no realized field, unit statement, or unit step is changed or bypassed. Verdict: pass.

5. Compared the delivered and repository node records. Only `proof` and `proof_origin` differ; `proof_deps` retains precisely the two section-definition nodes used in Lean. The first proof step describes the equality of opens and naturality construction; the second describes complex composition isomorphisms, arrow transport, and Mathlib reflection. The Lean attachment and mathematical statement remain unchanged. No new-node requirements apply. Verdict: pass.

Second reading changed only this report: made the closed/added-hole accounting explicit and recorded the five review checks. No Lean or node repair was necessary.
