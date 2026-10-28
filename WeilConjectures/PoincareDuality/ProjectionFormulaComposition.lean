/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ExchangeFormalism.ProjectionComposition
public import WeilConjectures.PoincareDuality.ProjectionFormulaOpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompositionTriangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeFormalism

/-!

# The exceptional projection morphism and the composition of lower shrieks

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- see the implementation notes of `WeilConjectures.TraceFormula.KunnethVerdierOpen`
attribute [local instance 2000] MonoidalCategory.toMonoidalCategoryStruct

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

set_option hygiene false in
/-- The condensed field `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj.{u} ℓ

/-- The formalism `boundedConstructibleExchangeFormalism`, for `ℚ̄_ℓ`-sheaves. -/
local notation "𝔽" => boundedConstructibleExchangeFormalism ℓ k

/-- The categories of the exchange formalism of bounded constructible `ℚ̄_ℓ`-sheaves are
monoidal. -/
noncomputable instance boundedConstructibleExchangeFormalism.monoidalCategory
    (X : SepFinType k) : MonoidalCategory ((𝔽).obj X) :=
  monoidalCategory_boundedConstructible X.obj

/-- The pullbacks of the exchange formalism of bounded constructible `ℚ̄_ℓ`-sheaves are
monoidal. -/
noncomputable instance boundedConstructibleExchangeFormalism.monoidal_pb {X Y : SepFinType k}
    (f : X ⟶ Y) : ((𝔽).pb f).Monoidal :=
  monoidal_boundedConstructibleUpperStar ℓ f.hom

/-- The projection comparisons of the extensions by zero of the exchange formalism of bounded
constructible `ℚ̄_ℓ`-sheaves are isomorphisms. -/
instance boundedConstructibleExchangeFormalism.isIso_projectionComparison {X Y : SepFinType k}
    (j : X ⟶ Y) [Fact (SepFinType.openImmersion j)] (K : (𝔽).obj X) (N : (𝔽).obj Y) :
    IsIso (((𝔽).shAdj j).projectionComparison K N) :=
  isIso_boundedConstructibleOpenImmersionProjectionComparison ℓ j.hom K N

/-- The category structures of the exchange formalism of bounded constructible `ℚ̄_ℓ`-sheaves. -/
lemma boundedConstructibleExchangeFormalism_category (X : SepFinType k) :
    (𝔽).category X = ObjectProperty.FullSubcategory.category _ :=
  rfl

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] {f : X ⟶ Y}

/-- The composition isomorphism of the pullbacks of a compactification in the exchange formalism
is that of the bounded constructible pullbacks. -/
lemma boundedConstructibleExchangeFormalism_pbComp'_compactification
    (c : Compactification f.left) :
    (𝔽).pbComp' (SepFinType.homMk c.overI) (SepFinType.homMk c.overG) (SepFinType.homMk f)
        (ObjectProperty.hom_ext _ c.overI_overG) =
      eqToIso (congrArg (boundedConstructibleUpperStar _ ℓ) c.overI_overG.symm) ≪≫
        boundedConstructibleUpperStarComp _ ℓ c.overI c.overG :=
  rfl

/-- The exceptional projection morphism of a compactification on bounded constructible
`ℚ̄_ℓ`-complexes is the exceptional projection morphism of the factorization in the exchange
formalism. -/
lemma homMk_exceptionalProjectionMorphismOfCompactification_eq_shriekProjection
    (c : Compactification f.left) (K : Dᵇc(X.left)⟦𝐐⟧) (B : Dᵇc(Y.left)⟦𝐐⟧) :
    ObjectProperty.homMk
        (X := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj K ⊗ B)
        (Y := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj
          (K ⊗ (boundedConstructibleUpperStar _ ℓ f).obj B))
        (exceptionalProjectionMorphismOfCompactification _ c K.obj B.obj) =
      (𝔽).shriekProjection (SepFinType.homMk c.overI) (SepFinType.homMk c.overG)
        (SepFinType.homMk f) (ObjectProperty.hom_ext _ c.overI_overG) K B := by
  rw [homMk_exceptionalProjectionMorphismOfCompactification_eq ℓ c K B _
    (ι_map_eqToIso_trans_upperStarComp_inv_app_compactification ℓ c B)]
  unfold ExchangeFormalism.shriekProjection
  refine congrArg₂ (· ≫ ·) rfl (congrArg _ (congrArg₂ (· ≫ ·) rfl ?_))
  exact congrArg (fun e : boundedConstructibleUpperStar _ ℓ f ≅
      boundedConstructibleUpperStar _ ℓ c.overG ⋙ boundedConstructibleUpperStar _ ℓ c.overI ↦
        (boundedConstructibleOpenImmersionLowerShriek _ ℓ c.overI).map (K ◁ e.inv.app B))
    (boundedConstructibleExchangeFormalism_pbComp'_compactification ℓ c).symm


/-- The composition isomorphisms of the pullbacks of bounded constructible `ℚ̄_ℓ`-complexes are
compatible with the comultiplications, in the exchange formalism. -/
lemma boundedConstructibleExchangeFormalism_δ_pbComp {X Y Z : SepFinType k} (f : X ⟶ Y)
    (g : Y ⟶ Z) (M N : (𝔽).obj Z) :
    Functor.OplaxMonoidal.δ ((𝔽).pb (f ≫ g)) M N ≫
        (((𝔽).pbComp f g).hom.app M ⊗ₘ ((𝔽).pbComp f g).hom.app N) =
      ((𝔽).pbComp f g).hom.app (M ⊗ N) ≫
        ((𝔽).pb f).map (Functor.OplaxMonoidal.δ ((𝔽).pb g) M N) ≫
          Functor.OplaxMonoidal.δ ((𝔽).pb f) (((𝔽).pb g).obj M) (((𝔽).pb g).obj N) :=
  boundedConstructibleUpperStarComp_hom_app_tensor_δ ℓ f.hom g.hom M N

section Triangle

variable {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] {g : Y ⟶ Z}

/-- The composition isomorphism of a triangle of compactifications intertwines the exceptional
projection morphisms of the exchange formalism. -/
lemma triangleShriekTriangle_compIso_hom_app_whiskerRight_comp_shriekProjection
    (T : Compactification.Triangle f.left g.left) (K : Dᵇc(X.left)⟦𝐐⟧) (B : Dᵇc(Z.left)⟦𝐐⟧) :
    haveI := isIso_baseChange_triangleShriekTriangle ℓ T
    haveI := isIso_exchange_triangleShriekTriangle ℓ T
    ((𝔽).compIso (triangleShriekTriangle T)).hom.app K ▷ B ≫
        (𝔽).shriekProjection (triangleShriekTriangle T).i (triangleShriekTriangle T).p
          (SepFinType.homMk f ≫ SepFinType.homMk g)
          (ObjectProperty.hom_ext _ (Compactification.Triangle.overCfg T).overI_overG) K B ≫
        ((𝔽).shriek (triangleShriekTriangle T).i (triangleShriekTriangle T).p).map
          (K ◁ ((𝔽).pbComp (SepFinType.homMk f) (SepFinType.homMk g)).hom.app B) =
      (𝔽).shriekProjection (triangleShriekTriangle T).i₂ (triangleShriekTriangle T).p₂
          (SepFinType.homMk g) (ObjectProperty.hom_ext _ T.cg.overI_overG)
          (((𝔽).shriek (triangleShriekTriangle T).i₁ (triangleShriekTriangle T).p₁).obj K) B ≫
        ((𝔽).shriek (triangleShriekTriangle T).i₂ (triangleShriekTriangle T).p₂).map
          ((𝔽).shriekProjection (triangleShriekTriangle T).i₁ (triangleShriekTriangle T).p₁
            (SepFinType.homMk f) (ObjectProperty.hom_ext _ T.cf.overI_overG) K
            (((𝔽).pb (SepFinType.homMk g)).obj B)) ≫
        ((𝔽).compIso (triangleShriekTriangle T)).hom.app
          (K ⊗ ((𝔽).pb (SepFinType.homMk f)).obj (((𝔽).pb (SepFinType.homMk g)).obj B)) :=
  haveI := isIso_baseChange_triangleShriekTriangle ℓ T
  haveI := isIso_exchange_triangleShriekTriangle ℓ T
  (𝔽).compIso_hom_app_whiskerRight_comp_shriekProjection
    (boundedConstructibleExchangeFormalism_δ_pbComp ℓ) (triangleShriekTriangle T) _ _ _ K B

end Triangle


section Composite

variable {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] {g : Y ⟶ Z}

/-- The composition isomorphism of the pullbacks of a compactification of a composite in the
exchange formalism is that of the bounded constructible pullbacks. -/
lemma boundedConstructibleExchangeFormalism_pbComp'_compactification_comp
    (c : Compactification (f ≫ g).left) :
    (𝔽).pbComp' (SepFinType.homMk c.overI) (SepFinType.homMk c.overG)
        (SepFinType.homMk f ≫ SepFinType.homMk g) (ObjectProperty.hom_ext _ c.overI_overG) =
      eqToIso (congrArg (boundedConstructibleUpperStar _ ℓ) c.overI_overG.symm) ≪≫
        boundedConstructibleUpperStarComp _ ℓ c.overI c.overG :=
  rfl

/-- `homMk_exceptionalProjectionMorphismOfCompactification_eq_shriekProjection` for a
compactification of a composite `f ≫ g`, written with the composite `homMk f ≫ homMk g` in the
exchange formalism. -/
lemma homMk_exceptionalProjectionMorphismOfCompactification_eq_shriekProjection_comp
    (c : Compactification (f ≫ g).left) (K : Dᵇc(X.left)⟦𝐐⟧) (B : Dᵇc(Z.left)⟦𝐐⟧) :
    ObjectProperty.homMk
        (X := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj K ⊗ B)
        (Y := (boundedConstructibleLowerShriekOfCompactification ℓ c).obj
          (K ⊗ (boundedConstructibleUpperStar _ ℓ (f ≫ g)).obj B))
        (exceptionalProjectionMorphismOfCompactification _ c K.obj B.obj) =
      (𝔽).shriekProjection (SepFinType.homMk c.overI) (SepFinType.homMk c.overG)
        (SepFinType.homMk f ≫ SepFinType.homMk g) (ObjectProperty.hom_ext _ c.overI_overG) K B := by
  rw [homMk_exceptionalProjectionMorphismOfCompactification_eq ℓ c K B _
    (ι_map_eqToIso_trans_upperStarComp_inv_app_compactification ℓ c B)]
  unfold ExchangeFormalism.shriekProjection
  refine congrArg₂ (· ≫ ·) rfl (congrArg _ (congrArg₂ (· ≫ ·) rfl ?_))
  exact congrArg (fun e : boundedConstructibleUpperStar _ ℓ (f ≫ g) ≅
      boundedConstructibleUpperStar _ ℓ c.overG ⋙ boundedConstructibleUpperStar _ ℓ c.overI ↦
        (boundedConstructibleOpenImmersionLowerShriek _ ℓ c.overI).map (K ◁ e.inv.app B))
    (boundedConstructibleExchangeFormalism_pbComp'_compactification_comp ℓ c).symm


/-- The composition isomorphisms of the pullbacks in the exchange formalism are those of the
bounded constructible pullbacks. -/
lemma boundedConstructibleExchangeFormalism_pbComp_homMk (f : X ⟶ Y) (g : Y ⟶ Z) :
    (𝔽).pbComp (SepFinType.homMk f) (SepFinType.homMk g) =
      boundedConstructibleUpperStarComp _ ℓ f g :=
  rfl

end Composite

end AlgebraicGeometry.ProEtale.CondensedRing
