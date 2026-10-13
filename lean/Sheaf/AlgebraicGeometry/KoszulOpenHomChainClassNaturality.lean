/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.KoszulOpenHomChainRepresentatives


/-! # Naturality of the explicit Koszul stage class

Source: Stacks Project, Tags 08DC, 08DD, 08D1 and 09M1.
(blueprint: lem-sc-koszul-open-hom-chain-class-naturality).
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The explicit stage-to-derived-sections class commutes with postcomposition.
Source: Stacks Project, Tag 08D1, functoriality in the coefficient complex;
Tag 08DC, Equation 36.9.4.1, and Tag 08DD.
(blueprint: lem-sc-koszul-open-hom-chain-class-naturality).
Proof: The tilde/sections adjunction transpose of s followed by t is the transpose
of s postcomposed with the top-sections chain map of t. The Hom cycle of that
composite is postcomposition of the Hom cycle of s. Postcomposition commutes
with the signed Hom differential and hence with cycles, homology projections,
and homologyFunctorFactors. Transport through koszulCechHomObjIso gives the
same stage map. On each ordered wedge, t commutes with restriction to the
principal intersection and with division by the product of the f_j: the map
is A-linear and the localized denominator is invertible. It also commutes with
the integer totalization sign. Thus the explicit Cech cocones are natural.
The colimit injections commute with these stage maps by the colimit cocone law.
Finally the Cech-to-derived-sections comparison is natural (compute it after a
K-injective resolution and use its defining comparison equation). Apply Q and
H^0 and use preservation of composition to obtain the displayed equality.
No quasi-coherence is needed for naturality. Empty covers, zero rings, zero
maps and zero complexes yield the same equality of zero classes. -/
theorem koszulOpenHom_chain_class_naturality
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} A)]
    (L F : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (e : ℕ) (s : koszulOpenSheafComplex A r f e ⟶ L) (t : L ⟶ F) :
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
    let G := (affineOpenSections A (koszulOpen A r f)).rightDerivedFunctor
    H.map (G.map (DerivedCategory.Q.map t))
      (H.map (koszulCechDerivedComparison A r f L)
        (H.map (DerivedCategory.Q.map (colimit.ι
          (koszulCechHomDiagram A r f
            (((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj L)) e))
          (koszulOpenHomStageClass A r f L e s))) =
    H.map (koszulCechDerivedComparison A r f F)
      (H.map (DerivedCategory.Q.map (colimit.ι
        (koszulCechHomDiagram A r f
          (((affineOpenSections A ⊤).mapHomologicalComplex (.up ℤ)).obj F)) e))
        (koszulOpenHomStageClass A r f F e (s ≫ t))) := by sorry

end AlgebraicGeometry
