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

/-- The tensorator of the lax monoidal forgetful functor is locally bijective: the tensor product
of sheaves of modules is the sheafification of the sectionwise tensor product. -/
lemma w_toPresheaf_map_mu :
    J.W ((PresheafOfModules.toPresheaf _).map (μ (forgetRestrict (R := R)) F G)) := by
  rw [mu_eq_tensorPresheafHom]
  exact w_toPresheaf_map_tensorPresheafHom F G

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

/-- **A product of sections that vanishes, vanishes locally in the sectionwise tensor product**:
if `t ⊗ g` is zero as a section of `F ⊗ G` over `U`, then around every point of `U` there is an
open subset on which the restrictions of `t` and `g` have zero tensor product already in
`Γ(F, V) ⊗ Γ(G, V)`. -/
theorem exists_restrict_tmul_eq_zero {F G : X.Modules} {U : X.Opens} (t : Γ(F, U)) (g : Γ(G, U))
    (h : tensorMk U t g = 0) {x : X} (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      F.presheaf.map (homOfLE hVU).op t ⊗ₜ[Γ(X, V)] G.presheaf.map (homOfLE hVU).op g = 0 := by
  have := (SheafOfModules.w_toPresheaf_map_mu (R := X.sheaf) F G).isLocallyInjective
  have hz : ((PresheafOfModules.toPresheaf _).map
      (μ (SheafOfModules.forgetRestrict (R := X.sheaf)) F G)).app (op U)
        (t ⊗ₜ[Γ(X, U)] g) =
      ((PresheafOfModules.toPresheaf _).map
      (μ (SheafOfModules.forgetRestrict (R := X.sheaf)) F G)).app (op U) 0 := by
    rw [map_zero]
    exact h
  obtain ⟨V, f, hf, hxV⟩ :=
    Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X) _ _ _ hz x hx
  refine ⟨V, f.le, hxV, ?_⟩
  have hf' : _ = _ := hf
  rw [map_zero] at hf'
  exact hf'

/-- **A trivialising section generates the sections over every smaller open subset.** If
multiplication by `m : Γ(L, W)` is an isomorphism `𝒪_W ≅ L|_W`, then for every open `V ≤ W`
multiplication by the restriction of `m` is a bijection of `Γ(X, V)` onto `Γ(L, V)`. -/
theorem bijective_smulSection {L : X.Modules} {W : X.Opens} (m : Γ(L, W))
    [IsIso (unitSmulRestrictHom m)] {V : X.Opens} (hV : V ≤ W) :
    Function.Bijective (smulSection m V hV) := by
  have hiso : IsIso (smulRestrictHom m) := by
    have h : smulRestrictHom m = (restrictUnitIso W.ι).hom ≫ unitSmulRestrictHom m := by
      rw [unitSmulRestrictHom, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [h]
    infer_instance
  obtain ⟨V', rfl⟩ : ∃ V' : W.toScheme.Opens, W.ι ''ᵁ V' = V :=
    ⟨W.ι ⁻¹ᵁ V, by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.2 hV]⟩
  exact ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation W.toScheme.ringCatSheaf (op V')).map (smulRestrictHom m))

end AlgebraicGeometry.Scheme.Modules
