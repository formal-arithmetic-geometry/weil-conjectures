/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars

/-!

# The finite-coefficient comparison commutes with pushforward

Let `T` be a finite discrete commutative ring and `g : X ⟶ Y` a morphism of schemes. The
equivalence `ProEtale.finiteCoefficientModEquivalence` identifies module objects over
`Λ_X = p_X^* T̲` with pro-étale sheaves of `T`-modules on `X`, keeping the underlying abelian
sheaf. This file shows that it commutes with the pushforward `g_*`:

* on the module-object side, `(g)_*⟦T̲⟧` is the pushforward of abelian sheaves with `Λ_Y` acting
  through the coefficient morphism `η_g : Λ_Y ⟶ g_* Λ_X`;
* on the `ModuleCat` side, `ProEtale.lowerStar (ModuleCat (ULift T)) g` is the pushforward of
  sheaves of `T`-modules.

The underlying abelian sheaves agree definitionally; it remains to compare the actions of
`t ∈ T`. By `ProEtale.finiteCoefficientModEquivalence_smul` both are actions of the constant
global section `t` of the coefficient ring, and `η_g` sends the constant section `t` of `Λ_Y`
to the image under `g_*` of the constant section `t` of `Λ_X`
(`ProEtale.upperStarFromPoint_section_comp_condensedPushforwardHom`).

## Main definitions and results

* `CategoryTheory.Mod.globalSmul_mapMod_obj`: a lax monoidal functor `F` sends the action of a
  global section `σ` on a module object to the action of the global section `ε ≫ F σ`.
* `CategoryTheory.Equivalence.preservesKInjectiveComplexes_functor`: an additive equivalence of
  abelian categories preserves K-injective complexes.
* `ProEtale.finiteCoefficientModLowerStarIso`: the natural isomorphism
  `Φ_X ⋙ g_* ≅ g_*⟦T̲⟧ ⋙ Φ_Y`, for `Φ = finiteCoefficientModEquivalence`.
* `ProEtale.finiteCoefficientDerivedLowerStarIso`: its derived version
  `D(Φ_X) ⋙ Rg_* ≅ Rg_*⟦T̲⟧ ⋙ D(Φ_Y)`.
* `CategoryTheory.Adjunction.leftAdjointCompEquivalenceIso`: a commutation of right adjoints
  with equivalences induces the conjugate commutation of the left adjoints. Hence the pullback
  versions `ProEtale.finiteCoefficientModUpperStarIso`,
  `ProEtale.finiteCoefficientDerivedUpperStarIso`, and the extension by zero versions
  `ProEtale.finiteCoefficientModOpenImmersionLowerShriekIso`,
  `ProEtale.finiteCoefficientDerivedOpenImmersionLowerShriekIso`.

## Sorried input

`ProEtale.finiteCoefficientDerivedUpperStarIso` uses the derived adjunction
`ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`, which depends on the sorried
`ProEtale.CondensedRing.preservesKFlatComplexes_mapMod_upperStar`. The other declarations are
sorry-free.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite Functor.LaxMonoidal

open scoped CategoryTheory.Obj CategoryTheory.Functor

/-! ### Global sections acting through a lax monoidal functor -/

namespace CategoryTheory.Mod

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  (F : C ⥤ D) [F.LaxMonoidal] {A : C} [MonObj A]

/-- A lax monoidal functor `F` sends the action of a global section `σ` of `A` on an `A`-module
object `M` to the action of the global section `ε ≫ F σ` of `F A` on the `F A`-module `F M`. -/
lemma globalSmul_mapMod_obj (σ : 𝟙_ C ⟶ A) (M : Mod C A) :
    globalSmul (ε F ≫ F.map σ) ((F.mapMod A).obj M) = F.map (globalSmul σ M) := by
  rw [globalSmul, globalSmul, comp_whiskerRight, Category.assoc, F.map_comp, F.map_comp,
    ← left_unitality_inv, Category.assoc, Category.assoc, ← μ_natural_left_assoc]
  rfl

end CategoryTheory.Mod

/-! ### Equivalences preserve K-injective complexes -/

namespace CategoryTheory.Equivalence

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D] (e : C ≌ D)
  [e.functor.Additive]

/-- An additive equivalence of abelian categories preserves K-injective complexes: it is right
adjoint to the exact functor `e.inverse`. -/
instance preservesKInjectiveComplexes_functor : e.functor.PreservesKInjectiveComplexes :=
  have : e.symm.functor.Additive := inferInstanceAs e.inverse.Additive
  e.symm.toAdjunction.preservesKInjectiveComplexes

end CategoryTheory.Equivalence

/-! ### Transporting a commutation of right adjoints to the left adjoints -/

namespace CategoryTheory.Adjunction

variable {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']
  (eC : C ≌ C') (eD : D ≌ D') {L : D ⥤ C} {R : C ⥤ D} {L' : D' ⥤ C'} {R' : C' ⥤ D'}

/-- Given equivalences `eC : C ≌ C'`, `eD : D ≌ D'` and adjunctions `L ⊣ R`, `L' ⊣ R'`, an
isomorphism `eC ⋙ R' ≅ R ⋙ eD` of right adjoints induces the conjugate isomorphism
`eD ⋙ L' ≅ L ⋙ eC` of left adjoints. -/
noncomputable def leftAdjointCompEquivalenceIso (adj : L ⊣ R) (adj' : L' ⊣ R')
    (i : eC.functor ⋙ R' ≅ R ⋙ eD.functor) : eD.functor ⋙ L' ≅ L ⋙ eC.functor :=
  (conjugateIsoEquiv (adj.comp eC.toAdjunction) (eD.toAdjunction.comp adj')).symm
    (Iso.inverseCompIso (Iso.isoCompInverse i.symm ≪≫ Functor.associator _ _ _))

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale

open Scheme

/-! ### The coefficient morphism `η_g` on constant global sections -/

section Sections

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) {X Y : Scheme.{u}}
  (g : X ⟶ Y)

/-- The coefficient morphism `η_g : Λ_Y ⟶ g_* Λ_X` sends the image `ε ≫ p_Y^* s` of a global
section `s` of `Λ` to the image under `g_*` of the image `ε ≫ p_X^* s` of `s`. -/
@[reassoc]
lemma upperStarFromPoint_section_comp_condensedPushforwardHom
    (s : 𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ) :
    ε (upperStarFromPoint Y) ≫ (upperStarFromPoint Y).map s ≫ condensedPushforwardHom Λ g =
      ε (g)_*[Ab.{u + 1}] ≫
        (g)_*[Ab.{u + 1}].map (ε (upperStarFromPoint X) ≫ (upperStarFromPoint X).map s) := by
  let adj := ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} g
  let α := (upperStarFromPointComp g).hom
  have hα := α.naturality s
  have hε := NatTrans.IsMonoidal.unit (τ := α)
  rw [condensedPushforwardHom, ← adj.unit_app_unit_comp_map_η, Category.assoc,
    ← Functor.map_comp, Adjunction.unitAlgHom, ← adj.unit_naturality_assoc,
    ← adj.unit_naturality_assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  rw [← hε, Functor.LaxMonoidal.comp_ε, Category.assoc, Category.assoc, Functor.Monoidal.η_ε_assoc,
    ← hα]
  rfl

variable [MonObj Λ]

open CondensedRing in
/-- The action of the image `ε ≫ p_Y^* s` of a global section `s` of `Λ` on the pushforward
`g_* M` of a module object is the pushforward of the action of `ε ≫ p_X^* s` on `M`. -/
lemma globalSmul_lowerStar_obj (s : 𝟙_ (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ⟶ Λ)
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    Mod.globalSmul (ε (upperStarFromPoint Y) ≫ (upperStarFromPoint Y).map s) ((g)_*⟦Λ⟧.obj M) =
      (g)_*[Ab.{u + 1}].map
        (Mod.globalSmul (ε (upperStarFromPoint X) ≫ (upperStarFromPoint X).map s) M) := by
  refine (Mod.globalSmul_comap (condensedPushforwardHom Λ g) _
    (((g)_*[Ab.{u + 1}].mapMod _).obj M)).trans ?_
  rw [Category.assoc,
    upperStarFromPoint_section_comp_condensedPushforwardHom, Mod.globalSmul_mapMod_obj]

end Sections

/-! ### The comparison for finite coefficients -/

section FiniteCoefficient

open CondensedRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T] {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The sections over `b` of `g_* Φ_X(M)` and of `Φ_Y(g_*⟦T̲⟧ M)`, for
`Φ = finiteCoefficientModEquivalence`, are the same abelian group, with the same action of `T`. -/
noncomputable def finiteCoefficientModLowerStarLinearEquiv
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)) (b : Y.ProEtᵒᵖ) :
    ((g)_*[ModuleCat.{u + 1} (ULift.{u + 1} T)].obj
        ((finiteCoefficientModEquivalence X T).functor.obj M)).obj.obj b ≃ₗ[ULift.{u + 1} T]
      ((finiteCoefficientModEquivalence Y T).functor.obj
        ((g)_*⟦Profinite.continuousMapRingObj T⟧.obj M)).obj.obj b where
  toFun y := y
  invFun y := y
  map_add' _ _ := rfl
  map_smul' r y := by
    obtain ⟨t⟩ := r
    have h₁ := finiteCoefficientModEquivalence_smul X T M
      (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).obj b.unop)) t
    have h₂ := finiteCoefficientModEquivalence_smul Y T
      ((g)_*⟦Profinite.continuousMapRingObj T⟧.obj M) b t
    have h₃ := globalSmul_lowerStar_obj (Profinite.continuousMapRingObj T) g
      (Profinite.continuousMapConstRingHom.{u} T t).hom M
    have h₄ := h₁ y
    have h₅ := h₂ y
    have h₆ := congrArg (fun φ ↦ φ.hom.app b y) h₃
    exact h₄.trans (h₆.symm.trans h₅.symm)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The finite-coefficient comparison commutes with pushforward**: for
`Φ = finiteCoefficientModEquivalence`, `Φ_X ⋙ g_* ≅ g_*⟦T̲⟧ ⋙ Φ_Y`. The underlying abelian
sheaves agree, and so do the actions of `T` (`finiteCoefficientModLowerStarLinearEquiv`). -/
noncomputable def finiteCoefficientModLowerStarIso :
    (finiteCoefficientModEquivalence X T).functor ⋙ (g)_*[ModuleCat.{u + 1} (ULift.{u + 1} T)] ≅
      (g)_*⟦Profinite.continuousMapRingObj T⟧ ⋙ (finiteCoefficientModEquivalence Y T).functor :=
  NatIso.ofComponents (fun M ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun b ↦ (finiteCoefficientModLowerStarLinearEquiv T g M b).toModuleIso)
      fun _ ↦ rfl)) fun _ ↦ rfl

/-- **The derived finite-coefficient comparison commutes with pushforward**: for
`Φ = finiteCoefficientDerivedEquivalence`, `Φ_X ⋙ Rg_* ≅ Rg_*⟦T̲⟧ ⋙ Φ_Y`. Since `Φ_X` is an
exact equivalence, it preserves K-injective complexes and `D(Φ_X) ⋙ Rg_* ≅ R(Φ_X ⋙ g_*)`; since
`Φ_Y` is exact, `R(g_*⟦T̲⟧ ⋙ Φ_Y) ≅ Rg_*⟦T̲⟧ ⋙ D(Φ_Y)`; the two right derived functors are
identified by `finiteCoefficientModLowerStarIso`. -/
noncomputable def finiteCoefficientDerivedLowerStarIso :
    (finiteCoefficientDerivedEquivalence X T).functor ⋙
        R((g)_*[ModuleCat.{u + 1} (ULift.{u + 1} T)]) ≅
      R((g)_*⟦Profinite.continuousMapRingObj T⟧) ⋙
        (finiteCoefficientDerivedEquivalence Y T).functor :=
  (Functor.mapDerivedCategoryCompRightDerivedFunctorIso
      (finiteCoefficientModEquivalence X T).functor _).symm ≪≫
    Functor.rightDerivedFunctorNatIso (finiteCoefficientModLowerStarIso T g) ≪≫
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso _
      (finiteCoefficientModEquivalence Y T).functor

/-! ### Pullback and extension by zero -/

/-- **The finite-coefficient comparison commutes with pullback**: `Φ_Y ⋙ g^* ≅ g^*⟦T̲⟧ ⋙ Φ_X`,
the conjugate of `finiteCoefficientModLowerStarIso` along the adjunctions `g^* ⊣ g_*`. -/
noncomputable def finiteCoefficientModUpperStarIso :
    (finiteCoefficientModEquivalence Y T).functor ⋙ (g)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)] ≅
      (g)^*⟦Profinite.continuousMapRingObj T⟧ ⋙ (finiteCoefficientModEquivalence X T).functor :=
  Adjunction.leftAdjointCompEquivalenceIso _ _
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.continuousMapRingObj T) g)
    (ProEtale.upperStarLowerStarAdjunction _ g) (finiteCoefficientModLowerStarIso T g)

/-- **The derived finite-coefficient comparison commutes with pullback**:
`Φ_Y ⋙ Lg^* ≅ Lg^*⟦T̲⟧ ⋙ Φ_X`, the conjugate of `finiteCoefficientDerivedLowerStarIso` along the
derived adjunctions `Lg^* ⊣ Rg_*`. -/
noncomputable def finiteCoefficientDerivedUpperStarIso :
    (finiteCoefficientDerivedEquivalence Y T).functor ⋙
        L((g)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)]) ≅
      L((g)^*⟦Profinite.continuousMapRingObj T⟧) ⋙
        (finiteCoefficientDerivedEquivalence X T).functor :=
  Adjunction.leftAdjointCompEquivalenceIso _ _
    (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj T) g)
    (ProEtale.derivedUpperStarLowerStarAdjunction _ g) (finiteCoefficientDerivedLowerStarIso T g)

/-- **The finite-coefficient comparison commutes with extension by zero** along an open
immersion `j`: `Φ_U ⋙ j_! ≅ j_!⟦T̲⟧ ⋙ Φ_X`, the conjugate of `finiteCoefficientModUpperStarIso`
along the adjunctions `j_! ⊣ j^*`. -/
noncomputable def finiteCoefficientModOpenImmersionLowerShriekIso {U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    (finiteCoefficientModEquivalence U T).functor ⋙
        (j)_!open[ModuleCat.{u + 1} (ULift.{u + 1} T)] ≅
      (j)_!open⟦Profinite.continuousMapRingObj T⟧ ⋙
        (finiteCoefficientModEquivalence X T).functor :=
  Adjunction.leftAdjointCompEquivalenceIso _ _
    (CondensedRing.openImmersionLowerShriekUpperStarAdjunction
      (Profinite.continuousMapRingObj T) j)
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction _ j)
    (finiteCoefficientModUpperStarIso T j)

/-- **The derived finite-coefficient comparison commutes with extension by zero** along an open
immersion `j`: `Φ_U ⋙ Dj_! ≅ Dj_!⟦T̲⟧ ⋙ Φ_X`, both extensions by zero being exact. -/
noncomputable def finiteCoefficientDerivedOpenImmersionLowerShriekIso {U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (finiteCoefficientDerivedEquivalence U T).functor ⋙
        D((j)_!open[ModuleCat.{u + 1} (ULift.{u + 1} T)]) ≅
      D((j)_!open⟦Profinite.continuousMapRingObj T⟧) ⋙
        (finiteCoefficientDerivedEquivalence X T).functor :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (finiteCoefficientModOpenImmersionLowerShriekIso T j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

end FiniteCoefficient

end AlgebraicGeometry.ProEtale
