/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Chartwise étale permanence for algebraic spaces

Source: Stacks Project, Properties of Spaces, Tags 03FR, 03FT, 03FU and 03FV;
Topologies on Algebraic Spaces, Tag 041F(1)--(3)
(blueprint: lem-trf-space-chartwise-etale-permanence).

We reuse `IsChartwiseEtale` from the enlarged-site module. Covering families are written
as the conjunction of chartwise étaleness and `IsJointlySurjective`, so no representability
condition is imposed on a covering map. All pullbacks are the actual sheaf pullbacks
bundled by `enlargedFibreProduct`.
-/

@[expose] public section

set_option autoImplicit false

universe u w v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Chartwise étaleness agrees with representable étaleness for scheme sources, contains
identities, is closed under composition and arbitrary base change, and satisfies cancellation
between two objects étale over a common base. Étale covering families (the two displayed
conjuncts) contain singleton isomorphisms and are closed under composition and base change.
Source: Stacks, Tags 03FR, 03FT, 03FU, 03FV and 041F(1)--(3)
(blueprint: lem-trf-space-chartwise-etale-permanence).

Proof, following the ten steps of the node:
1. Every map from a scheme to an algebraic space is representable: its scheme tests are
   pullbacks of the representable diagonal along the product of the two test schemes
   [def-trf-algebraic-space, def-pc-fibre-product].
2. For representable étale maps, successive scheme tests give composition and base change.
   Scheme étaleness is stable under both operations; isomorphisms are open immersions,
   hence étale. Surjectivity is likewise preserved [lem-weil-pbc-etale-composition-cancellation,
   def-weil-open-immersion, lem-trf-surjective-morphism-composition,
   lem-weil-pbc-surjective-base-change, lem-weil-pbc-etale-scheme-base-change].
3. For a scheme source, test chartwise étaleness on its identity. Conversely compose a
   representable étale map with each scheme chart, using step 2.
4. If a scheme-source map becomes representable étale after a surjective étale scheme
   cover, test over any scheme. Step 1 represents both pullbacks by schemes; the projection
   between them is surjective étale. Apply [lem-trf-etale-descent-through-source-cover].
5. Identity and composition follow directly by applying the chartwise condition to a
   scheme chart, once or twice. Isomorphisms follow from step 2.
6. For base change, pull back an atlas of the original source. For any scheme chart of the
   fibre product, pull back this atlas again. The result is a scheme surjective étale over
   the chart and representable étale over the new target. Descend by step 4. Reassociation
   identifies the two pullbacks section by section; closure is
   [lem-trf-space-fibre-products-etale-covers].
7. For schemes étale over a common algebraic space, the graph into their fibre product is
   a section of an étale projection. Scheme cancellation makes this section étale; scheme
   composition makes the original map étale [lem-weil-pbc-etale-composition-cancellation].
8. To cancel for arbitrary spaces, pull back a scheme chart of the source along an atlas
   of the target. Step 7 makes its map to that atlas étale, step 2 gives representable
   étaleness of the composite, and step 4 descends it to the original source chart.
9. An isomorphism lifts field-valued sections by its inverse. For composite coverings,
   lift a section after a field extension to the first family, then after a further
   extension to the second. The composite embedding supplies the required lift
   [def-trf-algebraic-space-jointly-surjective-family].
10. After arbitrary base change, step 6 gives chartwise étaleness. Lift the image of a
   field-valued section through the original cover after extension. The compatible pair
   gives a section of the actual sheaf fibre product and thus joint surjectivity. Empty
   covering families cause no exception: their hypotheses exclude target field sections. -/
theorem chartwise_etale_permanence {S : Scheme.{u}} :
    (∀ (T : Over S) (Y : AlgebraicSpace S) (f : schemeSpace T ⟶ Y),
      IsChartwiseEtale f ↔ IsEtale f.hom.hom) ∧
    (∀ X : AlgebraicSpace S, IsChartwiseEtale (𝟙 X)) ∧
    (∀ (X Y Z : AlgebraicSpace S) (f : X ⟶ Y) (g : Y ⟶ Z),
      IsChartwiseEtale f → IsChartwiseEtale g → IsChartwiseEtale (f ≫ g)) ∧
    (∀ (X Y Z : AlgebraicSpace S) (f : X ⟶ Z) (g : Y ⟶ Z),
      IsChartwiseEtale f → IsChartwiseEtale (enlargedFibreProductFst g f)) ∧
    (∀ (X Y Z : AlgebraicSpace S) (g : X ⟶ Z) (h : Y ⟶ Z) (f : X ⟶ Y),
      IsChartwiseEtale g → IsChartwiseEtale h → f ≫ h = g → IsChartwiseEtale f) ∧
    (∀ (X Y : AlgebraicSpace S) (e : X ≅ Y),
      IsChartwiseEtale e.hom ∧
        IsJointlySurjective (fun _ : Unit ↦ e.hom.hom.hom)) ∧
    (∀ (I : Type w) (J : I → Type v) (X : AlgebraicSpace S)
      (Xᵢ : I → AlgebraicSpace S) (Xᵢⱼ : ∀ i : I, J i → AlgebraicSpace S)
      (f : ∀ i : I, Xᵢ i ⟶ X) (g : ∀ (i : I) (j : J i), Xᵢⱼ i j ⟶ Xᵢ i),
      ((∀ i : I, IsChartwiseEtale (f i)) ∧
        IsJointlySurjective (fun i : I ↦ (f i).hom.hom)) →
      (∀ i : I, (∀ j : J i, IsChartwiseEtale (g i j)) ∧
        IsJointlySurjective (fun j : J i ↦ (g i j).hom.hom)) →
      (∀ a : Sigma J, IsChartwiseEtale (g a.1 a.2 ≫ f a.1)) ∧
        IsJointlySurjective (fun a : Sigma J ↦ (g a.1 a.2 ≫ f a.1).hom.hom)) ∧
    (∀ (I : Type w) (X X' : AlgebraicSpace S) (Xᵢ : I → AlgebraicSpace S)
      (f : ∀ i : I, Xᵢ i ⟶ X) (g : X' ⟶ X),
      ((∀ i : I, IsChartwiseEtale (f i)) ∧
        IsJointlySurjective (fun i : I ↦ (f i).hom.hom)) →
      (∀ i : I, IsChartwiseEtale (enlargedFibreProductFst g (f i))) ∧
        IsJointlySurjective
          (fun i : I ↦ (enlargedFibreProductFst g (f i)).hom.hom)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
