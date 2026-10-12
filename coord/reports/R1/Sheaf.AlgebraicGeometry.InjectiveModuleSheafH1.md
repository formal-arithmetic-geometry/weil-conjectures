## What changed

Replaced the sorry in `Sheaf.AlgebraicGeometry.InjectiveModuleSheafH1` by a complete
Lean proof from first Čech vanishing and the existing étale section-lifting theorem.
For each abelian short exact sequence with kernel the underlying sheaf, the proof
chooses all covering families as the cofinal system and explicitly refines a family
by itself using identity arrows. The proved source-library theorem
`CategoryTheory.Sheaf.subsingleton_H_one_of_surjective` then closes global H¹.
The original declaration and all its binders and universes are unchanged.

Added one module, `Sheaf.AlgebraicGeometry.InjectiveEtaleModuleCechH1`, exposing only
the degree-one Čech vanishing needed here. Its source is Stacks 03FC, as used by
03FD. Its docstring and node explain the constant-ring module equivalence, the free
Čech complex argument and the comparison of the two Čech models. Updated the item's
DAG proof and dependencies to agree with the Lean argument. All new proof imports
in the original module are non-public.

Both sandbox modules compile together through `lcompile.py --all` with no errors
or warnings. The new module's imports were reduced to the Mathlib ingredients its
statement needs. The sources read online were Stacks tags 03FC, 03FD and 03F8; the
local literature clone does not include their TeX files.

## Proved and sorry left

Proved/reduced:
`AlgebraicGeometry.Etale.subsingleton_H_one_of_injective_module_sheaf`
(node `lem-weil-pbc-henselian-finite-pushforward-h1-injective-vanishing`): no sorry
remains in its module. This is a proof from named open dependencies, not a claim
that its transitive axiom closure is already sorry-free.

The delivery leaves exactly one sorry, in the new public theorem
`AlgebraicGeometry.Scheme.isZero_cech_H_one_of_injective_module_sheaf`
(node `lem-weil-pbc-injective-etale-module-cech-h1`). Its conclusion concerns the
covering's Čech complex, rather than Ext or global H¹, so it is strictly a step of
the argument. The existing open section-lifting dependency is
`AlgebraicGeometry.Scheme.surjective_sections_of_cech_h1_vanishing`
(node `lem-weil-pbc-ses-cech-h1-surjective`); it is imported, not changed.

Edge cases checked mathematically: the zero sheaf and the zero coefficient ring
have zero cochains; the identity covering has alternating zero/identity
differentials and zero positive homology; an empty covering can cover only an
empty étale object, and its positive cochain groups are zero. Infinite coverings
are retained: indices have universe u+1 and cochains are categorical products,
with no finite-subcover assumption. Coefficients such as Z/pZ are allowed; the
argument never asserts that the underlying abelian sheaf is injective.

## No longer needed

The proof no longer uses `lem-weil-pbc-injective-module-abelian-acyclic` or its
module `Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic`. Its general
positive-degree right-derived evaluation conclusion, the constant-ring module
conversion at that interface, and the derived-evaluation/Ext comparison are not
needed to prove this degree-one theorem. The original module had no proof-only
imports to remove; its public import is preserved.

The trial import `Sheaf.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic` was
removed; its node `lem-sc-injective-module-abelian-acyclic-zariski` is not needed.
The trial Ext-isomorphism proof import was also removed. No terminal H'/H
comparison or universe-lifting comparison theorem is introduced.

The new Čech node still uses the generic ringed-site Čech theorem and its free
complex/injective-presheaf argument. These nodes are not pruned. No unit-realizing
statement or step is bypassed: this is a local degree-one reduction below the
unit `sk-thm-p1`; that unit's `realized` nodes are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original node already identifies the interface gaps accurately: its sole
planned dependency has R : Type u and a SheafOfModules input, but this item has
Λ : Type (u+1) and a ModuleCat-valued sheaf, and the dependency's conclusion is
right-derived evaluation rather than Ext. It cannot be applied directly.

The general ringed-site abelian acyclicity theorem fixes the coefficient issue
only when the coefficient universe equals the morphism universe. Here Y.Etale
has morphisms in Type u while values are in Type (u+1). Its H' interface therefore
also does not match. The existing generic SiteCech section-lifting theorem fixes
values to a universe containing the object's universe (Type (u+2) here), whereas
the existing étale version is a direct match and is used.

The existing ringed-site Čech theorem uses SheafOfModules and SiteCechComplex;
the new node is the focused interface bridge to ModuleCat sheaves and Mathlib's
cechComplexFunctor, not a second definition of any mathematical notion.
Searches completed with LeanFinder, Loogle and grep; LeanSearch returned an
Internal Server Error, recorded without a verdict. No process workaround was used.

## New nodes

`lem-weil-pbc-injective-etale-module-cech-h1` is the first Čech vanishing step of
03FC in the exact universes and Čech model used by the existing étale section
surjectivity theorem. Its proof plan uses
`lem-weil-pbc-ringed-site-injective-module-cech-acyclic` as a generic ringed-site
tool from `sk-thm-curveestimate` (the source is the same 03FC). The constant-ring
action and complex comparison are described explicitly. The node and module
contain the matching full Lean signature. No change record is needed because no
existing statement or definition changes.

## Second reading by R1

1. **Statements unchanged.** Compared `InjectiveModuleSheafH1.lean` with the repository version: the existing theorem signature is byte-for-byte unchanged. The new Čech theorem has a standalone signature matching its DAG node, with no changes to target statements.

2. **Proof and axioms.** Compiled both sandbox modules with `lcompile.py --all`; compilation succeeds without errors or warnings. The only remaining `sorry` is the named split-off theorem `AlgebraicGeometry.Scheme.isZero_cech_H_one_of_injective_module_sheaf`; no forbidden declarations or hollow definitions occur. The proved theorem uses only the imported open dependencies, so its transitive axiom closure is pending those dependencies as documented.

3. **Split-off statement.** Checked the new theorem's edge cases (zero sheaf and ring, identity and empty coverings, and arbitrary infinite index sets). Its conclusion is the degree-one Čech homology vanishing needed by the parent proof and is strictly narrower than the parent global H¹ statement. It is not duplicated in the existing library; the node, docstring, source, and Lean signature agree.

4. **Pruning and route.** The parent proof uses the existing section-surjectivity theorem and the new Čech interface theorem, then applies `Sheaf.subsingleton_H_one_of_surjective`. The obsolete abelian-acyclic and Ext-comparison route and its proof-only imports are removed. The unit `sk-thm-p1` route and realized nodes remain intact.

5. **DAG agreement.** Updated node proof steps and `proof_deps` describe exactly the Lean route. The new node records its source, proof plan, Lean declaration, chapter, unit, and split status. No change record is required because existing declarations and definitions are unchanged.

I changed only this report section after the initial delivery review; no Lean proof or statement required repair.
