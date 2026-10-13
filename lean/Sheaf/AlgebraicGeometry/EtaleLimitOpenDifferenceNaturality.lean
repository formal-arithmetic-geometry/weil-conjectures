/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.AlgebraicGeometry.EtaleLimitOpenCohomologyCoconeDegree
public import Sheaf.AlgebraicGeometry.EtaleOpenCohomologyMaps

/-! # Difference of restrictions on the actual open cohomology groups

Source: Stacks Project, Tags 0A50, 01F7 and 09YQ.
(blueprint: lem-weil-pbc-etale-limit-open-difference-naturality).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar openCohomologyRestriction cohomologyMap
  tailOpenCohomologyMapDegree tailOpenCohomologyLegDegree

set_option backward.isDefEq.respectTransparency true

/-- Difference of restrictions commutes with canonical transitions and cone legs.

Source: Stacks Project, Tag 0A50 (difference map), Tag 01F7 (pullback functoriality),
Tag 09YQ (restricted coherent-system maps).
(blueprint: lem-weil-pbc-etale-limit-open-difference-naturality).

Proof: Construct the two additive maps by subtracting the restrictions composed
with the two product projections. Their displayed value equations determine them
uniquely by additive-map extensionality. Apply nested-open restriction naturality
to the inclusions U∩V ≤ U and
U∩V ≤ V after inverse image to each stage. The restricted transition squares
commute by the definition of tailStageOpenMap; their coefficient maps are
openSquareCoefficient. In each term compose pullback naturality with naturality
of restriction in the coefficient morphism φ. The inverse-image composition
comparisons cancel, giving restriction followed by tailOpenCohomologyMapDegree
on the intersection. Subtract the two equalities and use additivity of that
intersection map. For the cone legs repeat this calculation with c.π at j and
the coefficient morphism (eG j).inv ≫ L.ι.app j; the cone equation identifies
the inverse-image opens with the supplied limit opens. Subtraction gives the
second formula. No cover or coefficient identity/composition laws are needed.
If an open is empty or U=V, the same additive identities apply. -/
theorem tailOpenDifference_naturality
    (X : Scheme.{u}) (U V : X.Opens)
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (L : Cocone G) (q : ℕ) (i₀ : I) (g₀ : D.obj (op i₀) ⟶ X)
    :
    ∃ (d : ∀ j : Set.Ici i₀,
      (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ U j).ι).obj
        (F j.val)) q ×
       Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ V j).ι).obj
        (F j.val)) q) →+
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ (U ⊓ V) j).ι).obj
        (F j.val)) q)
    (dL : (Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
        ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ U).ι).obj L.pt) q ×
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
        ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ V).ι).obj L.pt) q) →+
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
        ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ (U ⊓ V)).ι).obj L.pt) q),
    (∀ j x, d j x =
      openCohomologyRestriction (X := D.obj (op j.val))
        (A := tailStageOpen D g₀ (U ⊓ V) j) (B := tailStageOpen D g₀ U j)
        ((D.map (homOfLE j.property).op ≫ g₀).preimage_mono
          (inf_le_left : U ⊓ V ≤ U)) (F j.val) q x.1 -
      openCohomologyRestriction (X := D.obj (op j.val))
        (A := tailStageOpen D g₀ (U ⊓ V) j) (B := tailStageOpen D g₀ V j)
        ((D.map (homOfLE j.property).op ≫ g₀).preimage_mono
          (inf_le_right : U ⊓ V ≤ V)) (F j.val) q x.2) ∧
    (∀ x, dL x =
      openCohomologyRestriction (X := c.pt)
        (A := (c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ (U ⊓ V))
        (B := (c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ U)
        ((c.π.app (op i₀) ≫ g₀).preimage_mono (inf_le_left : U ⊓ V ≤ U)) L.pt q x.1 -
      openCohomologyRestriction (X := c.pt)
        (A := (c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ (U ⊓ V))
        (B := (c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ V)
        ((c.π.app (op i₀) ≫ g₀).preimage_mono (inf_le_right : U ⊓ V ≤ V)) L.pt q x.2) ∧
    (∀ (j k : Set.Ici i₀) (f : j ⟶ k)
      (x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
        (tailStageOpen D (X := X) (i₀ := i₀) g₀ U j).ι).obj (F j.val)) q)
      (y : Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
        (tailStageOpen D (X := X) (i₀ := i₀) g₀ V j).ι).obj (F j.val)) q),
      d k ((tailOpenCohomologyMapDegree D (X := X) (i₀ := i₀) g₀ U F φ q f).hom x,
        (tailOpenCohomologyMapDegree D (X := X) (i₀ := i₀) g₀ V F φ q f).hom y) =
      (tailOpenCohomologyMapDegree D (X := X) (i₀ := i₀) g₀ (U ⊓ V) F φ q f).hom (d j (x, y))) ∧
    (∀ (j : Set.Ici i₀)
      (x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
        (tailStageOpen D (X := X) (i₀ := i₀) g₀ U j).ι).obj (F j.val)) q)
      (y : Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
        (tailStageOpen D (X := X) (i₀ := i₀) g₀ V j).ι).obj (F j.val)) q),
      dL ((tailOpenCohomologyLegDegree D c (X := X) (i₀ := i₀) g₀ U F G eG L q j).hom x,
        (tailOpenCohomologyLegDegree D c (X := X) (i₀ := i₀) g₀ V F G eG L q j).hom y) =
      (tailOpenCohomologyLegDegree D c (X := X) (i₀ := i₀) g₀ (U ⊓ V) F G eG L q j).hom
        (d j (x, y))) := by sorry

end AlgebraicGeometry.Etale
