/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.LocalizingExceptionalAdjoint
/-! Formal full-subcategory restriction subclaim for det-existence-restriction.
Source: det-existence-restriction proof, final adjunction paragraph
(blueprint: det-existence-restriction-adjunction). -/
@[expose] public section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option maxHeartbeats 2000000 in
-- The dependent full-subcategory lifts require extra elaboration reductions.
/-- Restrict the adjunction along the two fully faithful inclusions. The identity
comparison isomorphisms preserve the ambient Hom equivalence by the unit formula.
Source: det-existence-restriction, final paragraph
(blueprint: det-existence-restriction-adjunction). -/
theorem det_existence_restriction_adjunction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (c : Compactification.BoundaryCompactification f.left)
    (h : ∀ K, localizingClosureProEtale Λ X.left K → localizingClosureProEtale Λ Y.left
      ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
    (G : (localizingClosureProEtale Λ Y.left).FullSubcategory ⥤
      (localizingClosureProEtale Λ X.left).FullSubcategory)
    (adj : localizingLowerShriek Λ c.obj.obj h ⊣ G)
    (hF : ∀ M : (ObjectProperty.inverseImage
        (constantModelBoundedConstructible Λ X.left ⊓ DerivedCategory.finiteTorAmplitude _)
        (localizingClosureProEtale Λ X.left).ι).FullSubcategory,
      (constantModelBoundedConstructible Λ Y.left ⊓ DerivedCategory.finiteTorAmplitude _)
        (((localizingLowerShriek Λ c.obj.obj h).obj M.obj).obj))
    (hG : ∀ K : (ObjectProperty.inverseImage
        (constantModelBoundedConstructible Λ Y.left ⊓ DerivedCategory.finiteTorAmplitude _)
        (localizingClosureProEtale Λ Y.left).ι).FullSubcategory,
      (constantModelBoundedConstructible Λ X.left ⊓ DerivedCategory.finiteTorAmplitude _)
        (G.obj K.obj).obj) :
    ∃ adjSmall :
      (ObjectProperty.inverseImage
        (constantModelBoundedConstructible Λ Y.left ⊓ DerivedCategory.finiteTorAmplitude _)
        (localizingClosureProEtale Λ Y.left).ι).lift
          ((ObjectProperty.inverseImage
            (constantModelBoundedConstructible Λ X.left ⊓ DerivedCategory.finiteTorAmplitude _)
            (localizingClosureProEtale Λ X.left).ι).ι ⋙
              localizingLowerShriek Λ c.obj.obj h) hF ⊣
        (ObjectProperty.inverseImage
          (constantModelBoundedConstructible Λ X.left ⊓ DerivedCategory.finiteTorAmplitude _)
          (localizingClosureProEtale Λ X.left).ι).lift
          ((ObjectProperty.inverseImage
            (constantModelBoundedConstructible Λ Y.left ⊓ DerivedCategory.finiteTorAmplitude _)
            (localizingClosureProEtale Λ Y.left).ι).ι ⋙ G) hG,
      ∀ (M : (ObjectProperty.inverseImage
        (constantModelBoundedConstructible Λ X.left ⊓ DerivedCategory.finiteTorAmplitude _)
        (localizingClosureProEtale Λ X.left).ι).FullSubcategory)
      (K : (ObjectProperty.inverseImage
        (constantModelBoundedConstructible Λ Y.left ⊓ DerivedCategory.finiteTorAmplitude _)
        (localizingClosureProEtale Λ Y.left).ι).FullSubcategory)
      (a : (localizingLowerShriek Λ c.obj.obj h).obj M.obj ⟶ K.obj),
      (adjSmall.homEquiv M K (ObjectProperty.homMk a)).hom = adj.homEquiv M.obj K.obj a := by
  let PX := ObjectProperty.inverseImage
    (constantModelBoundedConstructible Λ X.left ⊓
      DerivedCategory.finiteTorAmplitude _)
    (localizingClosureProEtale Λ X.left).ι
  let PY := ObjectProperty.inverseImage
    (constantModelBoundedConstructible Λ Y.left ⊓
      DerivedCategory.finiteTorAmplitude _)
    (localizingClosureProEtale Λ Y.left).ι
  let Ls := PY.lift (PX.ι ⋙ localizingLowerShriek Λ c.obj.obj h) hF
  let Rs := PX.lift (PY.ι ⋙ G) hG
  let adjSmall : Ls ⊣ Rs := adj.restrictFullyFaithful
      PX.fullyFaithfulι PY.fullyFaithfulι (Iso.refl _) (Iso.refl _)
  refine ⟨adjSmall, ?_⟩
  intro M K a
  dsimp only [adjSmall]
  rw [Adjunction.restrictFullyFaithful_homEquiv_apply]
  change adj.unit.app M.obj ≫ G.map (𝟙 _) ≫ G.map a ≫ 𝟙 _ = _
  rw [G.map_id]
  erw [Category.comp_id, Category.id_comp]
  exact (adj.homEquiv_unit M.obj K.obj a).symm
end AlgebraicGeometry.ProEtale.CondensedRing
