/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.Sites.FlatLocalRelations
public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicSheafPadicIntExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.Adic.Constructible
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleComparison

/-!
# Underlying abelian sheaves of derived direct images of `ℓ`-adic sheaves

For a morphism of schemes `f : X ⟶ Y`, taking underlying abelian sheaves (forgetting the
`ℚ̄_ℓ,X`-module structure and then the `ℚ̄_ℓ`-vector space structure,
`AlgebraicGeometry.ProEtale.AdicSheaf.toAb`) commutes with the derived direct images:
for an `ℓ`-adic sheaf `F` on `X_proét`,
```
Hᵠ(Rf_* F[0])_ab ≅ Hᵠ(Rf_* F_ab[0]),
```
the left hand side computed in `D(AdicSheaf l Y)` with `(f)_*ᵃ[l].rightDerivedFunctor`, the right
hand side in the derived category of abelian sheaves on `Y_proét`
(`AlgebraicGeometry.ProEtale.toAbHomologyRightDerivedAdicLowerStarIso`). The same holds for the
underlying sheaves of `ℚ̄_ℓ`-modules
(`AlgebraicGeometry.ProEtale.forgetHomologyRightDerivedAdicLowerStarIso`).

The point is that **the underlying abelian sheaf of an injective `ℓ`-adic sheaf is injective**.
Both forgetful functors have exact left adjoints:

* the free `ℚ̄_ℓ,X`-module functor `G ↦ ℚ̄_ℓ,X ⊗ G` on sheaves of `ℚ̄_ℓ`-modules is exact,
  because every sheaf of vector spaces over a field is flat
  (`CategoryTheory.Sheaf.flat_of_field`, from the relation criterion of
  `WeilConjectures.CategoryTheory.Sites.FlatLocalRelations`), so that the forgetful functor
  from modules over a flat ring object preserves injectives
  (`CategoryTheory.Mod.preservesInjectiveObjects_forget`);
* the sheafified free `ℚ̄_ℓ`-module functor `A ↦ (ℚ̄_ℓ ⊗[ℤ] A)^#` on abelian sheaves is exact,
  `ℚ̄_ℓ` being flat over `ℤ`.

Hence the forgetful functors are exact, commute with `f_*` on the nose and send injectives to
injectives, which makes the base change morphisms of derived functors invertible
(`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic`). Since
`AdicSheaf.toAb` reflects isomorphisms, lisse sheaves can then be detected through morphisms
inducing isomorphisms of underlying abelian sheaves
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.of_isIso_toAb_map`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

namespace CategoryTheory

namespace Mod

variable {C : Type*} [Category* C] [MonoidalCategory C] (A : C) [MonObj A]

/-- If tensoring with `A` preserves monomorphisms, so does the free `A`-module functor
`X ↦ A ⊗ X`. -/
lemma preservesMonomorphisms_free [(tensorLeft A).PreservesMonomorphisms] :
    (free A).PreservesMonomorphisms where
  preserves {X Y} f _ := by
    have : Mono ((forget (D := C) A).map ((free A).map f)) :=
      (tensorLeft A).map_mono f
    exact (forget (D := C) A).mono_of_mono_map this

/-- If tensoring with `A` preserves monomorphisms, the forgetful functor from `A`-modules
preserves injective objects, being right adjoint to the free module functor. -/
lemma preservesInjectiveObjects_forget [(tensorLeft A).PreservesMonomorphisms] :
    (forget (D := C) A).PreservesInjectiveObjects :=
  have := preservesMonomorphisms_free A
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (freeForgetAdjunction A)

end Mod

section Field

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  {K : Type (u + 1)} [Field K]

/-- **Relations between sections of a presheaf of vector spaces are trivial**: over a field,
every module is flat, so the equational criterion for flatness holds globally. -/
lemma Presheaf.hasLocallyTrivialRelations_of_field (P : Cᵒᵖ ⥤ ModuleCat.{u + 1} K) :
    Presheaf.HasLocallyTrivialRelations J P := by
  intro V s q y e he
  classical
  let f : (Fin q → K) →ₗ[K] (Fin s → K) := Matrix.vecMulLinear e
  let x : (Fin s → K) →ₗ[K] P.obj (op V) := Fintype.linearCombination K y
  have hxf : x ∘ₗ f = 0 := by
    refine LinearMap.pi_ext' fun l ↦ LinearMap.ext_ring ?_
    simpa [x, f, Fintype.linearCombination_apply, Matrix.vecMul, dotProduct,
      Pi.single_apply] using he l
  obtain ⟨k, a, z, hxa, haf⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxf
  refine ⟨⊤, J.top_mem V, fun W g _ ↦ ⟨k, Matrix.of fun j m ↦ a (Pi.single j 1) m,
    fun m ↦ P.map g.op (z (Finsupp.single m 1)), ?_, fun j ↦ ?_⟩⟩
  · ext l m
    have h := congrArg (fun w ↦ w m) (LinearMap.congr_fun haf (Pi.single l 1))
    have hf : f (Pi.single l 1) = ∑ j, e l j • Pi.single j 1 := by
      ext i
      simp [f, Pi.single_apply, Matrix.vecMul, dotProduct]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply,
      Finsupp.coe_zero, Pi.zero_apply, hf, map_sum, map_smul, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_apply, Matrix.zero_apply, ← h]
    rfl
  · have hy : y j = ∑ m, a (Pi.single j 1) m • z (Finsupp.single m 1) := by
      have h1 : y j = x (Pi.single j 1) := by
        simp [x, Fintype.linearCombination_apply, Pi.single_apply]
      rw [h1, hxa, LinearMap.comp_apply]
      conv_lhs => rw [← Finsupp.univ_sum_single (a (Pi.single j 1))]
      simp only [map_sum]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      rw [← map_smul, Finsupp.smul_single, smul_eq_mul, _root_.mul_one]
    rw [hy, map_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [map_smul]
    rfl

variable [EssentiallySmall.{u + 1} C]

/-- **Every sheaf of vector spaces is flat**, its relations being trivial
(`CategoryTheory.Presheaf.hasLocallyTrivialRelations_of_field`). -/
lemma Sheaf.flat_of_field (F : Sheaf J (ModuleCat.{u + 1} K)) : ObjectProperty.flat F :=
  ObjectProperty.prop_of_iso _ (asIso ((sheafificationAdjunction J _).counit.app F))
    (Presheaf.flat_presheafToSheaf_obj_of_hasLocallyTrivialRelations
      (Presheaf.hasLocallyTrivialRelations_of_field J F.obj))

/-- Tensoring with a sheaf of vector spaces preserves monomorphisms. -/
instance Sheaf.preservesMonomorphisms_tensorLeft_of_field (F : Sheaf J (ModuleCat.{u + 1} K)) :
    (tensorLeft F).PreservesMonomorphisms :=
  have : PreservesFiniteLimits (tensorLeft F) := (Sheaf.flat_of_field J F).tensorLeft.1
  inferInstance

end Field

/-- Postcomposition with a functor preserving monomorphisms preserves monomorphisms of
presheaves. -/
lemma Functor.preservesMonomorphisms_whiskeringRight_obj {C D E : Type*} [Category* C]
    [Category* D] [Category* E] [HasPullbacks D] (F : D ⥤ E) [F.PreservesMonomorphisms] :
    ((Functor.whiskeringRight C D E).obj F).PreservesMonomorphisms where
  preserves α _ := by
    have (X : C) : Mono ((((Functor.whiskeringRight C D E).obj F).map α).app X) :=
      F.map_mono (α.app X)
    exact NatTrans.mono_of_mono_app _

end CategoryTheory

namespace ModuleCat

/-- The free `R`-module functor `M ↦ R ⊗[ℤ] M` preserves monomorphisms when `R` is flat over
`ℤ`. -/
instance preservesMonomorphisms_extendScalarsAb (R : Type*) [CommRing R] [Module.Flat ℤ R] :
    (extendScalarsAb R).PreservesMonomorphisms where
  preserves f hf := by
    rw [AddCommGrpCat.mono_iff_injective] at hf
    rw [ModuleCat.mono_iff_injective]
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := R) f.hom.toIntLinearMap hf

end ModuleCat

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (l : ℕ) [Fact l.Prime]

/-- The underlying sheaf of `ℚ̄_ℓ`-modules of an injective `ℓ`-adic sheaf is injective: the free
`ℚ̄_ℓ,X`-module functor is exact, every sheaf of `ℚ̄_ℓ`-vector spaces being flat. -/
instance preservesInjectiveObjects_adicSheafForget (X : Scheme.{u}) :
    (AdicSheaf.forget (l := l) X).PreservesInjectiveObjects :=
  Mod.preservesInjectiveObjects_forget _

/-- The sheafified free `ℚ̄_ℓ`-module functor on abelian sheaves preserves monomorphisms, `ℚ̄_ℓ`
being flat over `ℤ`. -/
instance preservesMonomorphisms_weilCoefficientsFree (X : Scheme.{u}) :
    (weilCoefficientsFree X l).PreservesMonomorphisms := by
  have := Functor.preservesMonomorphisms_whiskeringRight_obj (C := X.ProEtᵒᵖ)
    (ModuleCat.extendScalarsAb (ULift.{u + 1} (PadicAlgCl l)))
  exact inferInstanceAs (Sheaf.composeAndSheafify _ _).PreservesMonomorphisms

/-- The underlying abelian sheaf of an injective sheaf of `ℚ̄_ℓ`-modules is injective. -/
instance preservesInjectiveObjects_weilCoefficientsForgetAb (X : Scheme.{u}) :
    (weilCoefficientsForgetAb l X).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (weilCoefficientsFreeAdjunction X l)

/-- The underlying abelian sheaf of an `ℓ`-adic sheaf on `X_proét`: forget the
`ℚ̄_ℓ,X`-module structure, then the `ℚ̄_ℓ`-vector space structure. -/
noncomputable abbrev AdicSheaf.toAb (X : Scheme.{u}) :
    AdicSheaf l X ⥤ Sheaf (ProEt.topology X) Ab.{u + 1} :=
  AdicSheaf.forget X ⋙ weilCoefficientsForgetAb l X

/-- The underlying abelian sheaf of an injective `ℓ`-adic sheaf is injective. -/
instance (X : Scheme.{u}) : (AdicSheaf.toAb l X).PreservesInjectiveObjects := by
  unfold AdicSheaf.toAb
  infer_instance

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The pushforward of `ℓ`-adic sheaves commutes with taking underlying abelian sheaves. -/
noncomputable def adicLowerStarCompToAbIso :
    (f)_*ᵃ[l] ⋙ AdicSheaf.toAb l Y ≅ AdicSheaf.toAb l X ⋙ (f)_*[Ab.{u + 1}] :=
  Iso.refl _

/-- The base change morphism `(R⁺f_* K)_ab ⟶ R⁺f_*(K_ab)` comparing the derived pushforward
of `ℓ`-adic sheaves with that of the underlying abelian sheaves, on `D⁺`. -/
noncomputable def rightDerivedAdicLowerStarToAb :
    ((f)_*ᵃ[l]).rightDerivedFunctorPlus ⋙ (AdicSheaf.toAb l Y).mapDerivedCategoryPlus ⟶
      (AdicSheaf.toAb l X).mapDerivedCategoryPlus ⋙
        ((f)_*[Ab.{u + 1}]).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusBaseChange (adicLowerStarCompToAbIso l f).hom

/-- The comparison `(R⁺f_* K)_ab ⟶ R⁺f_*(K_ab)` is an isomorphism, the underlying abelian
sheaves of injective `ℓ`-adic sheaves being injective. -/
instance isIso_rightDerivedAdicLowerStarToAb : IsIso (rightDerivedAdicLowerStarToAb l f) :=
  Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic _
    fun _ _ ↦ Functor.rightAcyclic_of_injective _

/-- **Higher direct images of `ℓ`-adic sheaves have the higher direct images of the underlying
abelian sheaves as underlying abelian sheaves**: `(Rᵠf_* F)_ab ≅ Rᵠf_*(F_ab)` for the classical
right derived functors. -/
noncomputable def rightDerivedAdicLowerStarToAbIso (q : ℕ) :
    ((f)_*ᵃ[l]).rightDerived q ⋙ AdicSheaf.toAb l Y ≅
      AdicSheaf.toAb l X ⋙ ((f)_*[Ab.{u + 1}]).rightDerived q :=
  have : IsIso (Functor.rightDerivedBaseChange (adicLowerStarCompToAbIso l f).hom q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro G
    rw [Functor.rightDerivedBaseChange_app]
    have : IsIso (Functor.rightDerivedFunctorPlusBaseChange (adicLowerStarCompToAbIso l f).hom) :=
      isIso_rightDerivedAdicLowerStarToAb l f
    infer_instance
  asIso (Functor.rightDerivedBaseChange (adicLowerStarCompToAbIso l f).hom q)

/-! ### The underlying sheaves of `ℚ̄_ℓ`-modules -/

/-! ### Detecting isomorphisms and lisse sheaves on underlying abelian sheaves -/

/-- A morphism of `ℓ`-adic sheaves is an isomorphism as soon as it is one on underlying abelian
sheaves. -/
instance (X : Scheme.{u}) : (AdicSheaf.toAb l X).ReflectsIsomorphisms := by
  unfold AdicSheaf.toAb
  infer_instance

end AlgebraicGeometry.ProEtale
