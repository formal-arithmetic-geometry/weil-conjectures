## What changed

Proved AlgebraicGeometry.Etale.epi_constantModulePushforwardComparison without changing its
signature. Its proof constructs an explicit fiber preimage from a stage representative,
using colimit.ι_desc_assoc, hι, and cancellation of the isomorphisms eK and e. The existing
jointly conservative left-exact geometric fiber family detects epimorphisms.

Added Sheaf.AlgebraicGeometry.ConstantModuleLimitFiberDescent: individual germs descend to
stages. This is the geometric descent step, not the original Epi statement under a new name:
it has no K, eK, hK, c, e, hι, colimit, or comparison-desc morphism. The original theorem's
categorical combination of descent, coprojections, and isomorphisms is fully proved in Lean.

Both modules compile without warnings through lcompile.py --all. Sources read online:
[Stacks 09Z1](https://stacks.math.columbia.edu/tag/09Z1) and
[Stacks 09Z6](https://stacks.math.columbia.edu/tag/09Z6). The local literature tex is absent.

## Proved and sorry left

Closed the named hole AlgebraicGeometry.Etale.epi_constantModulePushforwardComparison
by a reduction to the new descent theorem. This is a decomposition, not an
axiom-free proof: one hole closed and one hole added, net zero holes closed.

One new sorry remains: AlgebraicGeometry.Etale.exists_constantModule_limit_fiber_rep,
node lem-weil-pbc-constant-module-limit-fiber-descent. Its docstring and node describe
reindexing, constant pullback identifications, affine-neighborhood continuity, and the
canonical-map/coefficient identifications. Edge cases checked: singleton diagrams reduce
to an invertible projection; the zero module has only the zero germ; an empty base has no
points. Empty index categories are excluded by cofilteredness. No ring/module finiteness
hypothesis was added.

## No longer needed

Removed direct proof imports from the item:
- Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem
- Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful

HigherDirectImageLimitSystem (sbc-lem-higher-direct-image-limit) is still needed by the
new germ-descent node. Reindexing (lem-weil-pbc-filtered-category-exists-directed-final),
constant pullback (lemma-constructible-pullback-constant), and connected constant colimits
(lem-weil-pbc-colimit-constant-connected-diagram) likewise remain under that node.
The direct-image definition and constant-module-map definition remain needed by signatures.

The preservation-of-colimits theorem
lem-weil-pbc-module-sheaves-colimits-forgetful / ModuleSheavesColimitsForgetful is not used
by this branch: we construct the module colimit preimage directly from the stage germ,
so no module-to-abelian sheaf colimit comparison is required. This does not assert the
module is globally unreachable from other targets. No unit statement or realized unit
step is removed. The geometric-stalk criterion is an existing proved generic tool.

## Where the brief, the DAG or earlier work was wrong

The old plan's module-sheaf colimit-forgetful theorem is stated for SheafOfModules over a
ring sheaf, whereas this item uses Sheaf valued in ModuleCat of a fixed ring. It is not an
immediately applicable API. The germ-representative route avoids needing that adaptation.
The existing degree-p continuity theorem uses directed preorders and derived abelian
images; coefficient, degree-zero, and reindexing identifications are still part of the
new descent lemma's proof obligation. Its theorem statement is not claimed to supply a
representative on its own without those identifications.

The target's hK hypothesis is unnecessary for the categorical combination once stage
germ descent is available, but its signature is preserved. The unit sk-thm-p1 realized
statements/steps are preserved: this is a refinement strictly below that unit level.

## New nodes

lem-weil-pbc-constant-module-limit-fiber-descent, in
lean/Sheaf/AlgebraicGeometry/ConstantModuleLimitFiberDescent.lean, states the surjectivity
argument's affine-neighborhood/germ descent step independently of the categorical colimit
comparison. Mathlib semantic, type-pattern, and grep searches found no exact match;
the existing higher-image fiber descent theorem has different derived-system inputs.
The parent node's proof/proof_deps/proof_origin now follow the actual Lean combination.
No definition or statement changes and no change records.

## Second reading by N2

1. Compared the complete item module with the repository version. The signature of
   AlgebraicGeometry.Etale.epi_constantModulePushforwardComparison is byte-for-byte
   unchanged, including hK, both qcqs assumptions, the limit hypothesis and hι.
   No existing definition was edited. The existing node changes only proof,
   proof_deps and proof_origin. Verdict: no accidental statement change.
2. Compiled both modules locally in import order without errors or warnings.
   Read the stage preimage construction: colimit.ι_desc_assoc and hι give hcomp,
   the fiber of eK.inv supplies the colimit element, inv_hom_id cancels eK,
   and injectivity of the fiber of e.hom gives the required equality. The
   conservative geometric-point family and epi_of_epi_map supply epimorphism
   detection; the required exactness instances elaborate. Only the named new
   descent theorem contains sorry; no definitions, axioms or unsafe declarations
   were added. Axiom probes show propext, Classical.choice, Quot.sound and sorryAx.
   Verdict: correct conditional reduction, with the stated remaining hole.
3. Read Stacks 09Z1 and 09Z6 online. 09Z1 has exactly affine transitions and qcqs
   stage/limit structure maps, without finiteness of coefficients. 09Z6 uses its
   constant-sheaf specialization in the finite approximation paragraph; its
   Noetherian/finite hypotheses are not imported into this general specialization.
   The new theorem isolates germ descent, without K, its transitions, cocone or
   colimit morphism. It is a strictly smaller geometric obligation; the complete
   categorical passage to an epi is supplied above it. For a singleton index the
   limit projection is invertible; for the zero module the germ is zero and any
   stage exists by cofiltered nonemptiness; for empty X there is no point s. An
   empty Y gives the zero target germ. Repeated searches using stalk surjectivity,
   sheafFiber/Surjective and fiber representatives found only generic fiber
   representatives and structure-sheaf limit continuity, not this etale statement.
   Read HigherDirectImageLimitSystem: it is a derived abelian-system theorem over
   a directed preorder; its degree-zero and coefficient identifications are still
   needed, so this hole cannot be closed by directly applying its declaration.
   Verdict: true, needed descent obligation; no quick closure or duplicate found.
4. The proof uses the shortest categorical route once descent is isolated. Public
   imports in the new module provide constantModulePushforwardMap and the fiber
   occurring in its signature; the remaining imports are private proof dependencies
   for its recorded plan (continuity, reindexing and constant colimits). Every old
   proof dependency removed from the parent is accounted for: direct image and
   functoriality remain in signature imports; reindexing, constant pullback, constant
   colimits and higher-image continuity remain below descent; module-sheaf colimit
   forgetfulness is unused. The old private Defs imports are supplied by the public
   functoriality import. Read sk-thm-p1.realized: none of its statement or step
   realizations is removed or bypassed. Verdict: route and pruning are consistent.
5. Matched the parent node's two steps to the Lean preimage and cancellation proof.
   Matched the new node's full verbatim Lean statement and all geometric hypotheses,
   source, creation, blueprint and search fields. Its proof_deps are the union of
   its uses and the parent depends on descent and geometric conservativity.
   Verdict: nodes agree with the conditional proof and remaining obligation.

Changed the progress description to explicitly report a decomposition (net zero),
and clarified the new descent docstring/node: use the stated continuity isomorphism
and filtered-colimit fiber representatives, rather than claiming the theorem's proof
itself supplies representatives. No Lean proof or signature needed repair.
