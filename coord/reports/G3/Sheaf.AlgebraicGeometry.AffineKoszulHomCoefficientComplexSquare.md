## What changed

The original theorem `AlgebraicGeometry.affine_koszul_hom_coefficient_complex_square`
now has a complete Lean proof, with its signature unchanged. It substitutes `hH`,
applies the general Hom-to-single coefficient square, applies the affine
signed-dual coefficient square, and composes their two pairs of isomorphisms.
The last equality follows by associativity and the two square equalities.

Three new modules provide the steps. `SignedSheafDualCoefficientMap` constructs
postcomposition on the signed dual, proving its chain-map identity by linearity
and `homObjMap_comp_homObjMap`. `HomComplexToSingleCoefficientSquare` proves the
general coefficient naturality theorem. Its private helper retains the explicit
component formula from the existing Hom-to-single projection construction.
The projection map formula then proves naturality by complex extensionality.
`AffineKoszulSignedDualCoefficientSquare` states the remaining finite-free
localization comparison, with a full proof in words and its source.

All changes are in the sandbox. The existing definition and theorem interfaces
are unchanged; no forced adaptations or change records are required.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.affine_koszul_hom_coefficient_complex_square`
(node `lem-sc-affine-koszul-hom-coefficient-complex-square`).

New theorems fully proved:
`CategoryTheory.signedSheafDualCoefficientMap_comm` and
`CategoryTheory.homComplex_to_single_coefficient_square`. The private helper
`CategoryTheory.homComplex_to_single_components` and its two elementary private
lemmas are also fully proved. The coefficient-map definition contains no hole.

One hole added and left:
`AlgebraicGeometry.affine_koszul_signed_dual_coefficient_square`
(node `new-g3-affine-koszul-signed-dual-coefficient-square`). This is the
finite-free affine part of the argument, after the product-Hom-to-single
calculation has been proved separately. It assumes no regularity and has a
complete coordinate/localization proof in its docstring. Its edge cases were
checked in that proof: negative degrees, n=0, degrees above n, zero rings,
I=top, and empty charts.

This is a decomposition, not a net reduction in holes: one original hole
closed and one smaller hole added. The item's module itself contains no sorry.

## No longer needed

Removed the direct proof imports `Sheaf.Algebra.Homology.HomComplexToSingle`
and `Mathlib.LinearAlgebra.ExteriorPower.Basis` from the item's module;
replaced them with the two coefficient-square proof imports.
`HomComplexToSingle` remains an indirect dependency providing the signed-dual
construction. The exterior-power basis remains part of the affine comparison's
mathematical plan. Thus no previously required DAG node or whole module is
claimed pruned from the targets' closure. The original public statement imports
are retained. The new affine statement module needs no proof import while its
finite-free comparison remains a named hole.

Old proof-dependency accounting: `lem-sc-hom-complex-to-single` is no longer
applied by name: its existence conclusion does not specify compatible components.
Its module stays transitively imported for the signed-dual definition, while the
new proved helper retains the projection formula needed for naturality.
`lem-weil-pbc-exterior-power-free-basis` is not used by the item's composition
proof, but stays in the remaining affine lemma's plan.
`new-j3-koszul-quotient-coefficient-complex` stays as a statement/definition
dependency: the displayed coefficient morphism and both dual complexes use it.
None of these three nodes or their modules is pruned from the target closure.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies prove the Hom-to-single comparison and the Koszul
coefficient morphism, but their signatures do not supply the coefficient
naturality square for sheafification. The existing finite-free dual comparison
only treats structure-sheaf coefficients and does not assert quotient
naturality. The new affine signed-dual statement isolates exactly that missing
part. The product-Hom coefficient naturality is now proved directly from the
existing projection specification, rather than assumed from existence of two
unrelated isomorphisms. No mathematical error or disputed statement was found.

The unit record `sk-thm-picard-duality` has no realized node covering this local
calculation, so this decomposition preserves the unit route.

## New nodes

`new-g3-signed-sheaf-dual-coefficient-map`: the explicit postcomposition morphism
on signed dual complexes, with its proved chain-map identity.

`new-g3-hom-to-single-coefficient-square`: the fully proved general product-Hom
comparison square for any coefficient morphism of module sheaves.

`new-g3-affine-koszul-signed-dual-coefficient-square`: the remaining finite-free
affine coordinate comparison and quotient compatibility. Its source is Stacks
Tag 0BQZ's displayed coefficient map and Tag 01HV's functorial localization.
All three nodes are in `dag/nodes/sec-picard-framework/`; searches are recorded
from the sandbox search log. The original node's proof and proof dependencies
now follow the actual composition proof.

## Second reading by G3

1. PASS: compared every delivered module with the repository. Only the item
   existed there; its theorem signature and docstring are byte-for-byte unchanged.
   Its public imports are unchanged. The three new modules introduce the reported
   declarations; no existing definition, statement, visibility or target changes.
2. PASS: all four modules compile individually in dependency order with lcompile.py,
   without errors or warnings. The only textual hole is the reported public named
   affine signed-dual theorem. There are no forbidden declarations or holed
   definitions. Explicit scratch #print axioms checks show only propext,
   Classical.choice and Quot.sound for the coefficient-map definition, its
   commutation theorem, the general coefficient square and its component helper.
   The affine hole and the item's composed theorem also use sorryAx, as expected.
   Product projections are selected from their universal-property specification;
   their data are determined up to the product isomorphism used in the proof.
3. PASS: the remaining affine square is the finite-free coordinate part alone,
   after the general product-Hom naturality has been proved. It is strictly a part
   of the original argument, not a renamed whole theorem. Checked n=0 (degree-zero
   coefficient reduction), k>n (empty exterior basis), negative degrees and the
   -1 boundary (zero source), zero rings, I=top and empty charts. No regularity or
   relation between I and f is required. The docstring explains localization,
   differential signs and postcomposition, and the node matches its statement.
   Independent msearch leanfinder, loogle (Basis.constr) and grep queries, together
   with rg over Sheaf and the upstream internal-Hom sources, found coordinate
   ingredients but no full coefficient square. AffineFiniteFreeDualNaturality and
   AffineFiniteFreeDualComplexComparison only handle structure-sheaf targets;
   FiniteFreeInternalHomExact has private coefficient-natural finite-sum helpers,
   not a sheafified Koszul coefficient square. Closing the remaining full square
   requires additional coordinate and extension work rather than a quick application.
   Checked the cited Stacks 0BQZ coefficient map, 01HV localization functoriality
   and 0A8X Hom differential against the proof in words.
4. PASS: reviewed the proof from its target downwards. Substitution, the proved
   Hom-to-single coefficient square and the remaining affine square compose to
   precisely the target. Public imports supply statement/definition dependencies;
   the two new item proof imports are plain imports. The copied private product
   argument is needed to retain components, which the existing existential iso
   theorem does not expose. No shorter available full argument was found. Added
   explicit accounting of every old proof_deps entry under No longer needed.
   The unit sk-thm-picard-duality has empty realized statement/step lists; no unit
   route has been bypassed. This remains one hole closed and one hole added,
   a decomposition with zero net reduction, and no closure pruning.
5. PASS: checked the four node records against declarations and proof steps:
   original fields outside proof/proof_deps/proof_origin are unchanged; new nodes
   have source, complete statement, dependency union, searches, origin, creation,
   blueprint, chapter/unit and verbatim Lean signatures. The coefficient-map node
   records its actual construction and named commutation proof. No node change is
   needed.

Second reading changed only report.md: completed the old dependency accounting
and added this independent review. No Lean proof or statement repairs were needed.
