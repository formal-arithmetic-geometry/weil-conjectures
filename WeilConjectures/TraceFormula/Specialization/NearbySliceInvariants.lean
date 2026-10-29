/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyCartesianModel

/-!

# The change of geometric generic fibre and the unit of `Lg^* ⊣ Rg_*`

Let `φ : M ⟶ N` be a morphism of models and `φ.toCartesian : M ⟶ φ.cartesianModel` the change of
geometric
generic fibre of its cartesian factorization (`NearbyCyclesModel.Hom.toCartesian`): the identity on
total spaces, and `g = φ.toCartesian.generic : 𝒳_η̄ ⟶ 𝒴_η̄ ×_𝒴 𝒳` on geometric generic fibres. Its
pullback exchange is, up to isomorphisms, `Li^* Rj'_*` applied to the unit `G ⟶ Rg_* Lg^* G` of the
adjunction `Lg^* ⊣ Rg_*`. We prove that it is a split monomorphism at `C` as soon as this unit is a
split monomorphism at `G = Lε'^* C`
(`NearbyCyclesModel.Hom.isSplitMono_toCart_pullbackExchange_app_of_isSplitMono_unit`). For the
coordinate slices of the affine space this reduces the `toCart` hypothesis of
`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_cart'` to the splitting
of the unit of the change of geometric generic fibre
(`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_unit`).

The abstract input (`Adjunction.isSplitMono_mateEquiv_app_of_isSplitMono_unit`) is a statement
about mates: for adjunctions `L_N ⊣ R_N`, `L_M ⊣ R_M`, `L_G ⊣ R_G`, a functor `T ≅ 𝟭` and an
isomorphism `θ : T ⋙ L_M ≅ L_N ⋙ L_G`, the mate `R_N ⋙ T ⟶ L_G ⋙ R_M` of `θ` is a split
monomorphism at `y` as soon as the unit of `L_G ⊣ R_G` is.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {D E F : Type*} [Category D] [Category E] [Category F]
  {LN : D ⥤ E} {RN : E ⥤ D} {LM : D ⥤ F} {RM : F ⥤ D} {LG : E ⥤ F} {RG : F ⥤ E}
  (adjN : LN ⊣ RN) (adjM : LM ⊣ RM) (adjG : LG ⊣ RG) {T : D ⥤ D}

/-- For a natural isomorphism `e : T ≅ 𝟭`, the components `e_{T x}` and `T(e_x)` agree. -/
lemma _root_.CategoryTheory.Iso.hom_app_obj_eq_map_hom_app (e : T ≅ 𝟭 D) (x : D) :
    e.hom.app (T.obj x) = T.map (e.hom.app x) := by
  rw [← cancel_mono (e.hom.app x)]
  exact (e.hom.naturality (e.hom.app x)).symm

/-- **The mate of an isomorphism `T ⋙ L_M ≅ L_N ⋙ L_G` with `T ≅ 𝟭` against the unit of
`L_G ⊣ R_G`**: the mate `β : R_N ⋙ T ⟶ L_G ⋙ R_M` of `θ`, followed by the comparison
`κ : R_M ⟶ R_N R_G`, is `e ∘ R_N(η_G)`. -/
lemma mateEquiv_app_comp_eq (e : T ≅ 𝟭 D) (θ : T ⋙ LM ⟶ LN ⋙ LG) [IsIso θ] (y : E) :
    (mateEquiv adjN adjM (TwoSquare.mk _ _ _ _ θ)).natTrans.app y ≫
        (adjN.unit.app (RM.obj (LG.obj y)) ≫ RN.map (adjG.unit.app (LN.obj (RM.obj (LG.obj y))) ≫
          RG.map ((inv (Functor.whiskerRight e.inv LM ≫ θ)).app (RM.obj (LG.obj y)) ≫
            adjM.counit.app (LG.obj y)))) =
      e.hom.app (RN.obj y) ≫ RN.map (adjG.unit.app y) := by
  set φ : LN ⋙ LG ⟶ LM := inv (Functor.whiskerRight e.inv LM ≫ θ) with hφ
  apply (adjN.homEquiv _ _).symm.injective
  apply (adjG.homEquiv _ _).symm.injective
  simp only [Functor.comp_obj, Functor.id_obj, mateEquiv_apply, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp, Functor.map_comp,
    Category.assoc, homEquiv_counit, counit_naturality, counit_naturality_assoc,
    left_triangle_components_assoc, left_triangle_components]
  have key : φ.app (T.obj (RN.obj y)) ≫ θ.app (RN.obj y) =
      LG.map (LN.map (e.hom.app (RN.obj y))) := by
    have h1 : ∀ w, φ.app w = inv (θ.app w) ≫ LM.map (e.hom.app w) := fun w ↦ by
      rw [hφ]
      simp
    rw [h1, Category.assoc, Iso.hom_app_obj_eq_map_hom_app]
    erw [θ.naturality (e.hom.app (RN.obj y))]
    simp
  have hnat := φ.naturality (adjM.unit.app (T.obj (RN.obj y)) ≫ RM.map (θ.app (RN.obj y)) ≫
    RM.map (LG.map (adjN.counit.app y)))
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at hnat
  erw [reassoc_of% hnat]
  erw [adjM.counit_naturality (LG.map (adjN.counit.app y))]
  erw [reassoc_of% (adjM.counit_naturality (θ.app (RN.obj y))),
    adjM.left_triangle_components_assoc, reassoc_of% key]

/-- **Splitting the mate by the unit**: for adjunctions `L_N ⊣ R_N`, `L_M ⊣ R_M`, `L_G ⊣ R_G`, a
natural isomorphism `T ≅ 𝟭` and an isomorphism `θ : T ⋙ L_M ⟶ L_N ⋙ L_G`, the mate
`R_N ⋙ T ⟶ L_G ⋙ R_M` of `θ` is a split monomorphism at `y` as soon as the unit
`y ⟶ R_G L_G y` is. -/
lemma isSplitMono_mateEquiv_app_of_isSplitMono_unit (e : T ≅ 𝟭 D) (θ : T ⋙ LM ⟶ LN ⋙ LG)
    [IsIso θ] (y : E) [IsSplitMono (adjG.unit.app y)] :
    IsSplitMono ((mateEquiv adjN adjM (TwoSquare.mk _ _ _ _ θ)).natTrans.app y) :=
  IsSplitMono.mk' ⟨(adjN.unit.app (RM.obj (LG.obj y)) ≫
    RN.map (adjG.unit.app (LN.obj (RM.obj (LG.obj y))) ≫
      RG.map ((inv (Functor.whiskerRight e.inv LM ≫ θ)).app (RM.obj (LG.obj y)) ≫
        adjM.counit.app (LG.obj y)))) ≫ RN.map (retraction (adjG.unit.app y)) ≫
      e.inv.app (RN.obj y), by
    rw [← Category.assoc, mateEquiv_app_comp_eq adjN adjM adjG e θ y, Category.assoc,
      ← RN.map_comp_assoc,
      IsSplitMono.id, RN.map_id, Category.id_comp, Iso.hom_inv_id_app]; rfl⟩

end CategoryTheory.Adjunction

/-- The shape of the pullback exchange of nearby cycles: a composite
`θ_i(E R_N c) ≫ I_M(β(E c) ≫ R_M(θ_ε c))` with `θ_i`, `θ_ε` isomorphisms is a split monomorphism
as soon as `β(E c)` is. -/
lemma CategoryTheory.isSplitMono_app_whiskerLeft_comp_whiskerRight
    {C₀ C₁ C₂ C₂' C₃ C₄ C₅ C₆ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₂'] [Category C₃] [Category C₄]
    [Category C₅] [Category C₆] (EN : C₀ ⥤ C₁) (RN : C₁ ⥤ C₂) (IM : C₂' ⥤ C₃) (RM : C₄ ⥤ C₂')
    {IN : C₂ ⥤ C₅} {Fp : C₅ ⥤ C₃} {T : C₂ ⥤ C₂'} {LG : C₁ ⥤ C₄} {F : C₀ ⥤ C₆} {EM : C₆ ⥤ C₄}
    (θi : IN ⋙ Fp ⟶ T ⋙ IM) (β : RN ⋙ T ⟶ LG ⋙ RM) (θε : EN ⋙ LG ⟶ F ⋙ EM) (c : C₀)
    (hi : IsIso θi) (hε : IsIso θε) (h : IsSplitMono (β.app (EN.obj c))) :
    IsSplitMono (NatTrans.app (Functor.whiskerLeft (EN ⋙ RN) θi ≫
      Functor.whiskerRight (Functor.whiskerLeft EN β ≫ Functor.whiskerRight θε RM) IM :
        (EN ⋙ RN ⋙ IN) ⋙ Fp ⟶ F ⋙ EM ⋙ RM ⋙ IM) c) := by
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- A composite `a ≫ F(b ≫ c)` with `a`, `c` isomorphisms and `b` a split monomorphism is a split
monomorphism. -/
lemma CategoryTheory.isSplitMono_comp_map_comp {C D : Type*} [Category C] [Category D] {x : D}
    {y z w : C} (F : C ⥤ D) (a : x ⟶ F.obj y) (b : y ⟶ z) (c : z ⟶ w) (ha : IsIso a)
    (hb : IsSplitMono b) (hc : IsIso c) : IsSplitMono (a ≫ F.map (b ≫ c)) :=
  inferInstance

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel.Hom

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} (φ : M.Hom N f f')

/-- The pullback exchange of a morphism of models `ψ` is a split monomorphism at `C` as soon as the
base change morphism `Lt^* Rj_{N*} ⟶ Rj_{M*} Lg^*` of its square of geometric generic fibres (the
mate of the pullback comparison) is a split monomorphism at `Lε_N^* C`: the other two factors are
isomorphisms. -/
theorem isSplitMono_pullbackExchange_app_of_isSplitMono_mate (ψ : M.Hom N f f')
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (h : IsSplitMono ((mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j)
      (pullbackSquareComparison Λ ψ.commSq_j).hom).natTrans.app ((L((N.ε)^*⟦Λ⟧)).obj C))) :
    IsSplitMono ((ψ.pullbackExchange Λ).app C) := by
  have key := isSplitMono_app_whiskerLeft_comp_whiskerRight (L((N.ε)^*⟦Λ⟧)) R((N.j)_*⟦Λ⟧)
    L((M.i)^*⟦Λ⟧) R((M.j)_*⟦Λ⟧) (pullbackSquareComparison Λ ψ.commSq_i).hom
    (mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j)
      (pullbackSquareComparison Λ ψ.commSq_j).hom).natTrans
    (pullbackSquareComparison Λ ψ.commSq_ε).hom C inferInstance inferInstance h
  unfold pullbackExchange
  exact_mod_proofs key

/-- **The change of geometric generic fibre is split by the unit**: the pullback exchange of
`φ.toCartesian` is a split monomorphism at `C` as soon as the unit `G ⟶ Rg_* Lg^* G` of the
adjunction
`Lg^* ⊣ Rg_*` of the morphism `g = φ.toCartesian.generic : 𝒳_η̄ ⟶ 𝒴_η̄ ×_𝒴 𝒳` of geometric generic
fibres is a split monomorphism at `G = Lε'^* C`. -/
theorem isSplitMono_toCart_pullbackExchange_app_of_isSplitMono_unit
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (h : IsSplitMono ((derivedUpperStarLowerStarAdjunction Λ φ.toCartesian.generic).unit.app
      ((L((φ.cartesianModel.ε)^*⟦Λ⟧)).obj C))) :
    IsSplitMono ((φ.toCartesian.pullbackExchange Λ).app C) := by
  have e : L((φ.toCartesian.total)^*⟦Λ⟧) ≅ 𝟭 _ := by
    rw [toCartesian_total]
    exact leftDerivedUpperStarId Λ _
  exact φ.toCartesian.isSplitMono_pullbackExchange_app_of_isSplitMono_mate Λ C
    (Adjunction.isSplitMono_mateEquiv_app_of_isSplitMono_unit
      (derivedUpperStarLowerStarAdjunction Λ φ.cartesianModel.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j)
      (derivedUpperStarLowerStarAdjunction Λ φ.toCartesian.generic) e
      (pullbackSquareComparison Λ φ.toCartesian.commSq_j).hom
        ((L((φ.cartesianModel.ε)^*⟦Λ⟧)).obj C))

end NearbyCyclesModel.Hom

namespace NearbyCyclesModel

variable {k' : Type u} [Field k'] {ℓ : ℕ} [Fact ℓ.Prime]

/-- **The slice exchange from the unit of the change of geometric generic fibre,
`ℚ̄_ℓ`-coefficients**: for a complex `B` on `𝔸ⁿ⁺¹_S`, the pullback exchange of the morphism of
models over the coordinate slice `hᵢ` is a split monomorphism at `B` provided
* the pullback exchange of the cartesian part `fromCart` is invertible at `B`, and
* the unit `G ⟶ Rg_* Lg^* G` of the change of geometric generic fibre
  `g : 𝔸ⁿ_{K⟦t⟧} ×_{K⟦t⟧} Spec Ω_K ⟶ 𝔸ⁿ_{K⟦t⟧} ×_S Spec Ω` is a split monomorphism at the
  restriction `G` of `B`. -/
theorem isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_unit (n : ℕ) (i : Fin (n + 1))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (affineSpaceModel k' (n + 1)).total))}
    (hfrom : IsIso (((affineSpaceSliceHom k' n i).fromCartesian.pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app B))
    (hunit : IsSplitMono ((derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ)
      (affineSpaceSliceHom k' n i).toCartesian.generic).unit.app
        ((L(((affineSpaceSliceHom k' n i).cartesianModel.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
          B))) :
    IsSplitMono (((affineSpaceSliceHom k' n i).pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app B) := by
  refine isSplitMono_pullbackExchange_app_affineSpaceSliceHom_of_cart' n i hfrom ?_
  have key := Hom.isSplitMono_toCart_pullbackExchange_app_of_isSplitMono_unit
    (Profinite.padicAlgClRingObj ℓ) (affineSpaceSliceHom k' n i)
  clear hfrom
  revert B
  exact_mod_proofs key

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
