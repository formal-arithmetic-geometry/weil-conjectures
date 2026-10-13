## What changed

`scalar_abelian_pullback_square` is reduced through a canonical comparison characterized by its adjunction equation, rather than an arbitrary comparison satisfying only the unit equation. The degree-zero identity follows by applying `Ext.mk₀` to its sheaf-map identity. The coefficient equality follows by cancelling the inverse comparison component and applying injectivity of the abelian adjunction.

The new module `ScalarStructureCoefficientAdjunct` proves `scalar_structure_coefficient_adjunct` from `exists_scalarPullbackCoefficient` and `tensorPullbackObjUnitToUnit_isIso`: scalar adjunction naturality, sectionwise extensionality, and the tensor adjunction unit equation supply the entire proof. `ScalarForgetPullbackAdjunction` isolates the canonical comparison and integer-generator calculation in a separate module.

The existing theorem and all its binders are unchanged. Both new imports in the item are proof-only imports. The refreshed compiled snapshot supplies `ScalarAbelianExtFactorization`; its temporary source copy has been removed from the delivery. Local irreducibility of `scalarAbelianUnitClass` and `scalarInverseImage` avoids expensive unfolding without changing their definitions or other modules.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.scalar_abelian_pullback_square` (node `new-sc-scalar-abelian-pullback-square`). This is a decomposition, not a sorry-free proof of the whole comparison.

Added and proved without a direct hole: `AlgebraicGeometry.Scheme.scalar_structure_coefficient_adjunct` (node `new-sc-scalar-structure-coefficient-adjunct`).

One new hole: `AlgebraicGeometry.Scheme.scalar_forget_pullback_adjunction` (node `new-sc-scalar-forget-pullback-adjunction`). No holes remain directly in the item's module. One original hole closed and one lower hole added; net zero holes. The remaining theorem contains neither the structure coefficient equation nor the original combined conclusion.

## No longer needed

No existing imports or dependency modules are pruned. The earlier attempt's `scalar_abelian_pullback_square_unit` and `scalar_abelian_pullback_square_coefficient` are discarded: neither is needed, and neither had a DAG node. In particular the coefficient calculation needs no new unproved compatibility theorem.

## Where the brief, the DAG or earlier work was wrong

The saved attempt left two new holes in the original module without corresponding nodes or independent modules, and its coefficient obligation assumed only unit compatibility of an arbitrary comparison. This repair characterizes the canonical comparison by its adjunction, which is exactly the information needed for the coefficient calculation. The saved dependency copy also predated the repository's completed factorization proof; it has been replaced with the unchanged current source. The compiled snapshot initially lacked that dependency; after it refreshed, the temporary dependency source copy was removed. During this session the launcher added a compile-slot queue to lcompile.py to reduce host contention; queue waiting is outside the per-file compilation limit. No target signature or unit route is changed.

The source adjunction is [Stacks Tag 0096](https://stacks.math.columbia.edu/tag/0096); the functorial cohomology construction is [Tag 01F7](https://stacks.math.columbia.edu/tag/01F7). Both official pages were read. New statements were checked on the empty scheme, zero sheaves, identity morphisms, and arbitrary characteristic. Their arguments use neither nonempty opens nor a choice of an arbitrary existence witness.

## New nodes

`new-sc-scalar-forget-pullback-adjunction`, module `Sheaf.AlgebraicGeometry.ScalarForgetPullbackAdjunction`: existence of the canonical natural comparison, its adjunction characterization for arbitrary scalar sheaves, and its integer-unit sheaf-map equation. The structure coefficient assertion is excluded. Its natural-language proof describes the canonical adjunct, its stalkwise isomorphism, and evaluation on the integer generator.

`new-sc-scalar-structure-coefficient-adjunct`, module `Sheaf.AlgebraicGeometry.ScalarStructureCoefficientAdjunct`: the forgotten scalar adjunct of the tensor-unit coefficient is the original structure-sheaf morphism. Its proof is complete Lean. The parent's proof and proof dependencies now describe the implemented degree-zero Ext and adjunction calculations.

Change record: `coord/changes/scalar-abelian-pullback-local-transparency.md` records the file-local elaboration attributes required by the conservative preflight command-change check. No existing signature, exported attribute, or other module is changed.

## Second reading by S4

1. **Visible changes:** Compared the delivered module with the repository version. The theorem and all existing declarations have byte-for-byte identical signatures; only proof-only imports, local elaboration attributes, and proof terms changed. The existing DAG node statement and dependencies were restored exactly from the repository; the two added nodes match their new declarations.

2. **Proof and axioms:** Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds without errors or warnings. The item has no direct `sorry`; the only remaining hole is the named `scalar_forget_pullback_adjunction`, documented with its DAG node. No forbidden declaration or hollow definition was introduced. The proof uses the documented existing open dependency closure.

3. **Statements:** Checked the split statements against the implementations and edge cases described in their docstrings (empty schemes, zero sheaves, identity maps, and arbitrary characteristic). `scalar_structure_coefficient_adjunct` is proved completely; `scalar_forget_pullback_adjunction` is a strictly smaller prerequisite and does not restate the parent target.

4. **Pruning and route:** The parent proof follows the unit route through the canonical comparison, degree-zero Ext calculation, and coefficient adjunct. The two added imports are proof-only. No existing dependency module can be removed, and the discarded attempted lemmas are not delivered or referenced.

5. **DAG/report consistency:** The parent node’s proof, proof dependencies, and proof origin now match the Lean proof. New nodes include source, proof text, dependencies, Lean records, and the required split status. The unit route remains unchanged.

Changed during second reading: restored the existing node’s full `lean.statement` and `stmt_deps` verbatim, and added this review section. No Lean code or theorem statement was otherwise changed.
