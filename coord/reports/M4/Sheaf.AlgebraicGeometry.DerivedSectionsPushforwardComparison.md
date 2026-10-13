## What changed

Proved AlgebraicGeometry.derivedSectionsPushforwardComparison in
Sheaf.AlgebraicGeometry.DerivedSectionsPushforwardComparison without changing its
statement, universes, public imports, or definitions. Added two fully proved private
categorical helpers: unit_isIso_comp_of_exact (exact postcomposition transports
invertibility of a derived unit) and derivedSectionsCompositionOfAcyclic (composition
from acyclicity using right-derived uniqueness).

The proof uses the existing
AlgebraicGeometry.isIso_directImage_globalSections_unit_on_kInjective, transports
its module-valued unit through exact forgetting to abelian groups, uses the
definitional underived section identity, and whiskers the resulting natural
isomorphism by exact derived restriction. The auxiliary module derived category is
chosen standard locally; the four derived-category universes in the theorem remain
independent. Added proof imports Mathlib.Algebra.Category.ModuleCat.AB,
Sheaf.AlgebraicGeometry.DirectImageGlobalSectionsKInjectiveAcyclic, and
WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory.
Updated the existing node's proof, proof_deps, and proof_origin to match this route.

Validation: the final module compiles with lcompile.py in 11.5 seconds without
warnings. Both private helpers are proved. Identity morphisms, empty opens, and
zero complexes require no additional assumptions: the underived identity is
reflexivity and the argument applies uniformly to every K-injective complex.

## Proved and sorry left

Closed one hole: AlgebraicGeometry.derivedSectionsPushforwardComparison
(node lem-pc-derived-sections-pushforward-comparison). No sorry remains in the item;
no new holes, nodes, or modules are added. This is a proof from existing library
declarations, not a decomposition into new unproved statements. The delivery dry
run supplies the axiom probe and mechanical checks.

## No longer needed

Removed direct proof imports Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
and Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition. The former
remains available through the unchanged public imports and is still used for the
underived/derived direct-image definitions; it is not globally pruned.

The proof no longer directly requires
lem-pc-ringed-spaces-derived-direct-image-composition
(Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition), nor
 def-weil-locally-ringed-space-morphism as a separate proof dependency. It does not
construct maps to the integer-valued one-point ringed space or import any new
point-comparison module. The existing global-sections acyclicity declaration
encapsulates the needed point argument. Its own transitive prerequisites remain
needed; no claim is made that they leave the targets' entire import closure.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is mathematically valid but unnecessarily requires a new
explicit comparison with the integer-valued point. The existing module-valued
acyclicity API plus exact forgetting already provides the composition criterion.
The original theorem docstring is retained as the source proof plan; the delivered
node records the Lean route. The unit's statement and route are unchanged.

The cited Stacks source files are absent in this remote checkout. Their tags were
read on the official Stacks site; no literature files were changed.

## Second reading by M4

1. Compared the delivered module with the repository version. The theorem signature, universes, definitions, and public imports are unchanged; only proof imports, private helpers, and the target proof differ.

2. Compiled the module with `lcompile.py`; it succeeds without errors or warnings. The target proof contains no `sorry`, and no prohibited declarations or hollow definitions were added.

3. Checked the two private helpers and the target proof route. The helpers are strictly intermediate categorical reductions, and the target statement is proved directly from existing acyclicity and derived-functor uniqueness declarations; no split-off statements or new nodes were added.

4. Reviewed pruning and dependencies. The proof uses exact forgetting, module-valued global-sections acyclicity, and right-derived uniqueness; the removed direct-image composition imports are no longer needed. The unit route remains represented by the existing node and its realized unit.

5. Checked the DAG node against the Lean proof. Its statement is unchanged, and `proof`, `proof_deps`, and `proof_origin` describe the implemented route. Edge cases such as identity maps, empty opens, and zero complexes are covered uniformly by the categorical argument.

Changed after second reading: added this review record only; no Lean statements, definitions, or proof content required repair.
