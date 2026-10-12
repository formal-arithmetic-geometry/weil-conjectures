## What changed

Replaced the sorry in `AlgebraicGeometry.ModuleExtensionByZeroStalkInside` by a complete
Lean reduction to two distinct intermediate theorems, each in a new module:

- `ModuleExtensionByZeroStalkMorphism`: construction of the natural linear morphism
  induced by the chosen unit, including its formula on germs, without invertibility.
- `ModuleExtensionByZeroUnitIsIso`: invertibility of the chosen unit as a morphism of
  sheaves of modules, without any stalk comparison or natural stalk isomorphism.

The combining proof identifies the additive map underlying the first morphism with
(stalk of the unit) followed by Mathlib's additive restriction-stalk isomorphism.
It proves this equality on germs using `stalk_hom_ext` and
`restrictStalkIso_hom_eq_germ`. The second theorem makes this composite invertible.
The forgetful functor from modules to abelian groups reflects isomorphisms, and
`NatIso.isIso_of_isIso_app` then upgrades the morphism to the required natural
isomorphism with exactly the original germ formula. The original signature and
visibility are unchanged. The existing node's proof and proof dependencies now
record this route.

Both remaining statements were checked against Stacks `sheaves.tex`, label
`lemma-j-shriek-modules` (Tag 00A7), clauses (2)-(4), and `sites-modules.tex`, label
`lemma-extension-by-zero` (Tag 03DI). The source text was read from the local
literature mirror. The unit lemma uses the canonical single-summand calculation
on opens inside W and uniqueness of left adjoints; it does not use this item's
stalk isomorphism. The construction lemma uses only linearity and functoriality
of the unit, followed by restriction of stalks; it does not use the unit lemma.

Searches: LeanFinder found the scheme-specific `Scheme.Modules.restrictStalkNatIso`
and Mathlib's additive `PresheafedSpace.restrictStalkIso`. Loogle returned the
restriction-stalk germ formulas. Grep found only scheme-specific comparisons,
not an arbitrary-ringed-space linear comparison. LeanSearch returned HTTP 500;
that search is recorded as unavailable. Blueprint searches for extension by zero,
stalk morphisms and unit isomorphisms found no exact existing statement for these
two interfaces. The unit's `realized` record is empty, so this reduction bypasses
no realized unit step.

Edge cases: W empty has no point for the stalk construction, while its module-sheaf
category is trivial for the unit assertion. W equal to X uses the same single-summand
calculation. The zero sheaf and zero stalk ring require no nonzero assumption.
The unit is arbitrary among the adjunctions of the specified functors: uniqueness
of left adjoints transports invertibility to the actual chosen unit, so neither
new statement silently assumes a canonical choice.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.ModuleExtensionByZeroStalkInside`
(node `lem-sc-module-extension-by-zero-stalk-maps-inside`). There are no sorries left
in the item's module.

Added exactly two named holes:

- `AlgebraicGeometry.exists_moduleExtensionByZero_stalk_morphism`
  (`lem-sc-module-extension-by-zero-stalk-morphism`).
- `AlgebraicGeometry.moduleExtensionByZero_unit_isIso`
  (`lem-sc-module-extension-by-zero-unit-isiso`).

This is a decomposition: one hole closed and two holes added, not an unconditional
sorry-free proof and not a net reduction in holes. The remaining lemmas separate
construction/linearity from invertibility; neither restates the original theorem.
All three delivered modules compile cleanly with `lcompile.py --all`.

## No longer needed

Removed the proof import `Sheaf.Topology.AbelianOpenExtensionByZeroStalks` and removed
`lem-sc-topological-extension-by-zero-stalks` from this node's proof dependencies.
This proof does not compare module extension by zero with abelian extension by zero.
It uses Mathlib's additive restriction-stalk comparison instead. Also removed `def-weil-presheaf-modules-sheafification` from the item’s direct
`proof_deps`: its construction is still used transitively by the new unit lemma and
in the statement, but the combining proof calls no sheafification theorem directly.
No other original import was removed. The definition dependencies for extension presheaves,
sheafification and module stalks remain necessary in the new lemmas and statements.
This does not claim that the removed module is unreachable from all other targets.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original DAG paragraph combines the construction,
linearity, naturality and invertibility of the stalk comparison into one step.
Its imported abelian extension comparison does not identify the underlying abelian
module extension or account directly for the arbitrary chosen unit. The new route
separates these obligations and gives complete Lean glue between them.

`nonempty_openExtensionRestrictionIso` already states an abstract restriction/extension
isomorphism, but its proof imports `ModuleExtensionByZeroStalkMaps` and uses this very
item. Importing it here would create an import cycle; it is not an independent
shortcut for the chosen-unit assertion. The new unit lemma explicitly calls for
an independent proof using the single-summand calculation.

A scratch attempt to construct the scalar-transport comparison directly ran into
expensive unfolding of the module structures under `sheafOfModulesEquivOver`.
No definitions or signatures were changed, and scratch files are not delivered.

## New nodes

`lem-sc-module-extension-by-zero-stalk-morphism` states the unit-induced natural
linear stalk morphism and its germ equation, without invertibility. Its source
and complete proof in words are recorded in its node and declaration docstring.
It is in `Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkMorphism`.

`lem-sc-module-extension-by-zero-unit-isiso` states invertibility of the actual
chosen extension/restriction unit for each module sheaf. Its proof plan is the
single-summand calculation on opens inside W, compatibility of sheafification
with restriction, and comparison of adjunctions. It is in
`Sheaf.Algebra.Homology.ModuleExtensionByZeroUnitIsIso`.

No change record or forced adaptation is needed: no existing interface changed.

## Second reading by J3

1. Compared every delivered module against the repository. The two helper modules
   are new; the existing theorem signature and visibility are byte for byte unchanged.
   No existing definition, target or other module was changed. Restored the existing
   theorem docstring, which the first worker had rewritten. Verdict: pass.
2. Compiled all three modules locally in import order. Only the two named helper
   theorems contain `sorry`; neither a definition nor an anonymous proof does. No
   forbidden declaration or attribute occurs. Checked `#print axioms` in a scratch
   module for all three declarations: only `propext`, `Classical.choice`, `Quot.sound`
   and `sorryAx`. The combining proof is conditional on the two reported holes.
   The existential stalk map is uniquely determined by the germ equation (every
   stalk element is a germ); the proof extracts it locally and introduces no
   definition choosing an arbitrary existence witness. Verdict: pass.
3. Read both new statements and their complete docstring proofs against the local
   Stacks source, Sheaves `lemma-j-shriek-modules` and Modules on Sites
   `lemma-extension-by-zero`. The scalar direction is the inverse ring comparison,
   as required. Checked the empty open, total open, zero module and zero ring; no
   extra hypothesis is required. The unit lemma concerns invertibility on sheaves;
   the morphism lemma only constructs the natural linear map. Both are strictly
   separate parts of the original argument. Searched again with full faithfulness,
   adjunction-unit invertibility, and scalar/stalk restriction terminology, using
   LeanFinder, Loogle, Mathlib grep and repository `rg`. The general fully faithful
   left-adjoint criterion lacks the necessary independent full-faithfulness instance.
   No independent exact duplicate or closure in a few minutes was found. Verdict: pass.
4. Read the reduction from its target downwards. Germ extensionality identifies
   the additive map; the unit lemma and reflection of isomorphisms supply precisely
   the remaining invertibility. All added proof imports are plain imports. The
   original public imports support the statements. The existing
   `nonempty_openExtensionRestrictionIso` imports the current item through
   `ModuleExtensionByZeroStalkMaps`, so using it would be circular. Compared all old
   direct `proof_deps` and corrected the pruning report to mention the removed
   sheafification dependency as well as the abelian extension comparison. The unit
   `sk-thm-picard-duality` has empty `realized.statement` and `realized.steps[0]`; no
   realized route is bypassed or changed. Verdict: pass.
5. Compared node records with the Lean signatures and reduction. The new nodes
   include sources, proof steps, dependency unions, searches, provenance, blueprint,
   creation and Lean records. The existing node changes only its proof route and
   provenance. Added the independent second-reader unit searches to its new node.
   Verdict: pass.

Second reading changed documentation only: restored the existing theorem docstring,
completed the list of removed direct proof dependencies, and recorded additional
unit-lemma searches. No proof or statement required repair. This remains a
decomposition: one original hole closed, two helper holes added (net minus one).
