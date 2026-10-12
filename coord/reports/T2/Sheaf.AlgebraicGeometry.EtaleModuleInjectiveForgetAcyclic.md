## What changed

Proved `AlgebraicGeometry.Scheme.isZero_rightDerived_globalSections_forget_of_injective`
in `Sheaf.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic`, with its signature unchanged.
Added four proof-only imports: `Sheaf.AlgebraicGeometry.ModuleSheafConstantRingEquivalence`,
`Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic`,
`Sheaf.AlgebraicGeometry.EtaleCechVanishingCriterion`, and
`Sheaf.AlgebraicGeometry.EtaleSiteCechComplexComparison`.

The proof follows all four original steps. The equivalence sends G to an injective ring-sheaf
module I. Ringed-site Čech vanishing and the comparison of chosen-product and categorical Čech
complexes supply the hypothesis of the étale vanishing criterion. Use all objects and all
coverings (a covering refines itself by identities), then evaluate at the terminal object.
The natural isomorphism between Γ and terminal evaluation is derived explicitly by deriving
its two inverse maps, using Mathlib's composition and identity laws. Finally transport along
the underlying-abelian component of the equivalence. No additional universe lift or hypothesis
is introduced. The argument covers n=0, the empty scheme and the zero ring as well.

Updated the item's node proof and proof_deps to record the exact existing declarations used.
The unit `sk-prop-h2` has no realized statement or step at this node; its route is unchanged.
Local single-file compilation passed without warnings. No library build was run.

## Proved and sorry left

Proved the item's sole original sorry:
`AlgebraicGeometry.Scheme.isZero_rightDerived_globalSections_forget_of_injective`
(node `lem-weil-pbc-etale-module-injective-forget-acyclic`).
No sorry remains in this module; no new theorem, module, or sorry was added.

The proof uses these existing declarations that are still sorry in their own modules:
`AlgebraicGeometry.moduleSheaf_constantRing_equivalence`
(`lem-weil-pbc-module-sheaf-constant-ring-equivalence`),
`CategoryTheory.injective_module_cech_cohomology_isZero`
(`lem-weil-pbc-ringed-site-injective-module-cech-acyclic`),
`AlgebraicGeometry.Scheme.nonempty_etale_siteCech_complex_iso`
(`lem-weil-pbc-etale-site-cech-complex-comparison`), and
`AlgebraicGeometry.Scheme.isZero_rightDerived_etale_of_cech_vanishing`
(`lem-weil-pbc-cech-vanishing-criterion`). They are the next proof items, not new obligations
in this delivery. Thus the transitive proof still depends on sorry; this delivery closes the
local declaration from the project's named statements, as required by stage 3.

## No longer needed

None. Every added proof import is used. The original public import remains unchanged.
Every original proof dependency is retained; no original node or module is pruned.
The existing `Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic` theorem was considered
but not imported: its coefficients are `R : Type u` lifted to Type (u+1), whereas this item
allows arbitrary Λ : Type (u+1). The general constant-ring equivalence avoids that restriction.

## Where the brief, the DAG or earlier work was wrong

The original DAG omitted the named constant-ring equivalence and the Čech-construction
comparison needed to express its first two steps in Lean. Both already exist, so they are
now explicit proof dependencies. No mathematical statement was changed or disputed.
The file initially did not import its stated proof dependencies; the delivery adds the
proof-only imports it actually uses. Terminal sheafSections requires its Additive instance
transported from Γ before deriving the natural isomorphism.

The cited Stacks source is not present in this clone's literature directory. This delivery
uses the existing statements and their complete proof docstrings and introduces no new
source-dependent assertion or remaining lemma.

## Second reading by T2

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are unchanged byte for byte; only proof-only imports and the proof body differ. Verdict: pass.

2. Compiled the module with `lcompile.py`; it compiles without errors or warnings. There are no `sorry`s, axioms, unsafe declarations, or hollow definitions. The proof uses only the existing named intermediate theorems, whose remaining `sorry`s are recorded above. Verdict: pass.

3. Checked the route against Mathlib and the existing Sheaf declarations. The proof uses the constant-ring equivalence, injective module Cech vanishing, the etale Cech comparison, and the etale Cech vanishing criterion; no duplicate split-off statement or weakened hypothesis was introduced. Verdict: pass.

4. The proof follows the unit route and is pruned to the imports actually used. No original proof dependency or module is removed, so there is nothing to prune. Verdict: pass.

5. Compared the node proof and `proof_deps` with the Lean proof. They list the exact declarations used, and the unit `sk-prop-h2` route remains unchanged. Verdict: pass.

Changed only the proof imports, proof body, and corresponding node proof metadata; no statement or definition was changed.
