module

public import WeilConjectures.AlgebraicGeometry.Modules.Vanishing
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyTrivial

@[expose] public section

universe v₁ u₁ u

open CategoryTheory MonoidalCategory Opposite TensorProduct TopologicalSpace
open Functor.LaxMonoidal Functor.OplaxMonoidal

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R : Sheaf J CommRingCat.{u}}

/-- The forgetful functor from sheaves of `R`-modules to presheaves of modules over the
underlying presheaf of rings of `R`, spelled so that the monoidal structure on presheaves of
modules is found by instance resolution. This is the right adjoint of
`SheafOfModules.sheafification`. -/
noncomputable abbrev forgetRestrict :
    SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)

/-- The forgetful functor to presheaves of modules is lax monoidal, being right adjoint to the
monoidal sheafification functor. -/
noncomputable instance : (forgetRestrict (R := R)).LaxMonoidal :=
  Adjunction.rightAdjointLaxMonoidal (F := sheafification R) (G := forgetRestrict)
    (PresheafOfModules.sheafificationAdjunction (𝟙 _))

variable (F G : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))

set_option maxHeartbeats 1000000 in
-- unfolding the lax monoidal structure of the right adjoint is expensive
/-- **The comparison morphism `SheafOfModules.tensorPresheafHom` is the tensorator of the lax
monoidal forgetful functor** to presheaves of modules. All its coherences are therefore those of
a lax monoidal functor. -/
theorem mu_eq_tensorPresheafHom : μ (forgetRestrict (R := R)) F G = tensorPresheafHom F G := by
  rw [Adjunction.rightAdjointLaxMonoidal_μ]
  rfl

/-- The unit comparison of the lax monoidal forgetful functor is the unit of the sheafification
adjunction at the tensor unit: the tensor unit of the category of sheaves of modules is by
construction the sheafification of the tensor unit of presheaves of modules. -/
theorem epsilon_forgetRestrict :
    ε (forgetRestrict (R := R)) =
      (PresheafOfModules.sheafificationAdjunction
          (R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) (𝟙 _)).unit.app
        (𝟙_ (PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}))) := rfl

set_option maxHeartbeats 1000000 in
-- identifying the two spellings of the sheafification adjunction is expensive
/-- **The unit comparison of the forgetful functor identifies the tensor unit with the structure
sheaf**: composing it with the isomorphism `SheafOfModules.tensorUnitIso` gives the identity of
the tensor unit of presheaves of modules. -/
theorem epsilon_forgetRestrict_comp_map_tensorUnitIso :
    ε (forgetRestrict (R := R)) ≫ forgetRestrict.map (tensorUnitIso R).hom = 𝟙 _ := by
  rw [epsilon_forgetRestrict]
  refine (Adjunction.homEquiv_unit _ _ _ _).symm.trans ?_
  rw [PresheafOfModules.sheafificationAdjunction_homEquiv_apply]
  exact (PresheafOfModules.sheafificationHomEquiv _).apply_symm_apply _

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The unit global section of the tensor unit of `X.Modules` over an open subset `U`, the
section corresponding to `1 : Γ(X, U)`. -/
noncomputable def unitSection (X : Scheme.{u}) (U : X.Opens) : Γ(𝟙_ X.Modules, U) :=
  ((ε (SheafOfModules.forgetRestrict (R := X.sheaf))).app (op U)).hom (1 : Γ(X, U))

variable (F : X.Modules)

/-- The product of a section of `F` and a section of `G` over an open subset `U`, as a section of
`F ⊗ G` over `U`: the image of `t ⊗ₜ g` under the tensorator of the lax monoidal forgetful
functor to presheaves of modules. -/
noncomputable def tensorMk {F G : X.Modules} (U : X.Opens) (t : Γ(F, U)) (g : Γ(G, U)) :
    Γ(F ⊗ G, U) :=
  ((μ (SheafOfModules.forgetRestrict (R := X.sheaf)) F G).app (op U)).hom (t ⊗ₜ[Γ(X, U)] g)

/-- **The inverse of the right unitor multiplies by the unit section.** -/
theorem app_rightUnitor_inv (U : X.Opens) (t : Γ(F, U)) :
    Hom.app (ρ_ F).inv U t = tensorMk U t (unitSection X U) :=
  (congrArg (fun φ ↦ (φ.app (op U)).hom t)
    (right_unitality_inv (F := SheafOfModules.forgetRestrict (R := X.sheaf)) F)).symm

/-- **Whiskering acts on the second factor of a product of sections.** -/
theorem app_whiskerLeft {M N : X.Modules} (ψ : M ⟶ N) (U : X.Opens) (t : Γ(F, U)) (m : Γ(M, U)) :
    Hom.app (F ◁ ψ) U (tensorMk U t m) = tensorMk U t (Hom.app ψ U m) :=
  (congrArg (fun φ ↦ (φ.app (op U)).hom (t ⊗ₜ[Γ(X, U)] m))
    (μ_natural_right (SheafOfModules.forgetRestrict (R := X.sheaf)) F ψ)).symm

/-- **The unit section corresponds to the unit global function** under the identification of the
tensor unit of `X.Modules` with the structure sheaf. -/
theorem app_tensorUnitIsoUnit_hom_unitSection (U : X.Opens) :
    Hom.app (tensorUnitIsoUnit X).hom U (unitSection X U) = (1 : Γ(X, U)) :=
  congrArg (fun φ ↦ (φ.app (op U)).hom (1 : Γ(X, U)))
    (SheafOfModules.epsilon_forgetRestrict_comp_map_tensorUnitIso (R := X.sheaf))

/-- **Multiplication by a global section `s` of a sheaf of modules `L`**, as a morphism
`F ⟶ F ⊗ L` of sheaves of `𝒪ₓ`-modules: the section `s` is a morphism `𝒪ₓ ⟶ L`, and the
morphism below is obtained by tensoring it on the right of `F` and composing with the right
unitor. On sections it is `t ↦ t ⊗ s`, see
`AlgebraicGeometry.Scheme.Modules.app_mulSection`. -/
noncomputable def mulSection (F : X.Modules) {L : X.Modules} (s : Γ(L, ⊤)) : F ⟶ F ⊗ L :=
  (ρ_ F).inv ≫ F ◁ ((tensorUnitIsoUnit X).hom ≫ homOfSectionTop L s)

/-- **Multiplication by a global section is `t ↦ t ⊗ s` on sections.** -/
theorem app_mulSection {L : X.Modules} (s : Γ(L, ⊤)) (U : X.Opens) (t : Γ(F, U)) :
    Hom.app (mulSection F s) U t = tensorMk U t (L.presheaf.map U.leTop.op s) := by
  rw [mulSection, Hom.comp_app, ConcreteCategory.comp_apply, app_rightUnitor_inv,
    app_whiskerLeft, Hom.comp_app, ConcreteCategory.comp_apply,
    app_tensorUnitIsoUnit_hom_unitSection]
  congr 1
  have h := Hom.naturality_apply (homOfSectionTop L s) U.leTop (oneSection X ⊤)
  rw [map_oneSection, homOfSectionTop_app_top] at h
  simpa [oneSection] using h

end AlgebraicGeometry.Scheme.Modules
