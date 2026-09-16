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
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧ ∀ (V' : X.Opens) (hV' : V' ≤ V),
      F.presheaf.map (homOfLE (hV'.trans hVU)).op t ⊗ₜ[Γ(X, V')]
        G.presheaf.map (homOfLE (hV'.trans hVU)).op g = 0 := by
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
  refine ⟨V, f.le, hxV, fun V' hV' ↦ ?_⟩
  have hf' : _ = _ := (Presheaf.equalizerSieve _ _).downward_closed hf (homOfLE hV')
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

section Trivialisation

variable {L : X.Modules} {W : X.Opens}

/-- **A trivialising section generates every stalk over the trivialising open.** -/
theorem span_germ_eq_top (m : Γ(L, W)) [IsIso (unitSmulRestrictHom m)] {x : X} (hx : x ∈ W) :
    Submodule.span (X.presheaf.stalk x) {L.presheaf.germ W x hx m} = ⊤ := by
  refine eq_top_iff.2 fun y _ ↦ ?_
  obtain ⟨V, hxV, t, rfl⟩ := L.presheaf.exists_germ_eq y
  have hxV' : x ∈ V ⊓ W := ⟨hxV, hx⟩
  rw [← L.presheaf.germ_res_apply (homOfLE (inf_le_left : V ⊓ W ≤ V)) x hxV' t]
  obtain ⟨r, hr⟩ := (bijective_smulSection m (V := V ⊓ W) inf_le_right).2
    (L.presheaf.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op t)
  rw [← hr]
  change L.presheaf.germ (V ⊓ W) x hxV' (r • L.presheaf.map (homOfLE inf_le_right).op m) ∈ _
  rw [germ_smul L x hxV' r, L.presheaf.germ_res_apply]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- **A trivialising section is a free generator of every stalk over the trivialising open**:
no nonzero element of the local ring kills it. -/
theorem eq_zero_of_smul_germ_eq_zero (m : Γ(L, W)) [IsIso (unitSmulRestrictHom m)]
    {x : X} (hx : x ∈ W) {z : X.presheaf.stalk x} (hz : z • L.presheaf.germ W x hx m = 0) :
    z = 0 := by
  obtain ⟨V, hxV, r, rfl⟩ := X.presheaf.exists_germ_eq z
  have hxV' : x ∈ V ⊓ W := ⟨hxV, hx⟩
  rw [← X.presheaf.germ_res_apply (homOfLE (inf_le_left : V ⊓ W ≤ V)) x hxV' r] at hz ⊢
  rw [← L.presheaf.germ_res_apply (homOfLE (inf_le_right : V ⊓ W ≤ W)) x hxV' m,
    ← germ_smul L x hxV'] at hz
  obtain ⟨V'', hxV'', i, i', hzz⟩ :=
    L.presheaf.germ_eq (U := V ⊓ W) (V := V ⊓ W) x hxV' hxV' _ 0 (by simpa using hz)
  rw [map_zero, Scheme.Modules.map_smul] at hzz
  have hreg : smulSection m V'' (i.le.trans inf_le_right)
      (X.presheaf.map i.op (X.presheaf.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op r)) = 0 := by
    rw [smulSection]
    simp only [AddMonoidHom.mk'_apply]
    rw [← hzz]
    congr 1
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    congr 2
  have := (bijective_smulSection m (V := V'') (i.le.trans inf_le_right)).1
    (hreg.trans (map_zero _).symm)
  rw [← X.presheaf.germ_res_apply i x hxV'' _, this, map_zero]

/-- **The bridge between vanishing and basic open subsets.** If `s` restricts to `g • m` on a
trivialising open `W`, then `s` vanishes at a point of `W` exactly when that point lies outside
the basic open subset of `g`.

This identifies `AlgebraicGeometry.Scheme.Modules.VanishesAt` for an invertible sheaf with the
hypothesis of
`AlgebraicGeometry.Scheme.Modules.isSMulRegular_iff_associatedPoints_subset_basicOpen`, and
generalises `AlgebraicGeometry.Scheme.Modules.vanishesAt_structureModules_iff`. -/
theorem vanishesAt_iff_notMem_basicOpen (m : Γ(L, W)) [IsIso (unitSmulRestrictHom m)]
    (s : Γ(L, ⊤)) (g : Γ(X, W)) (hg : L.presheaf.map W.leTop.op s = g • m)
    {x : X} (hx : x ∈ W) :
    L.VanishesAt s x ↔ x ∉ X.basicOpen g := by
  have he : L.presheaf.germ ⊤ x trivial s
      = X.presheaf.germ W x hx g • L.presheaf.germ W x hx m := by
    rw [← L.presheaf.germ_res_apply W.leTop x hx s, hg, germ_smul L x hx]
  have hne : L.presheaf.germ W x hx m ≠ 0 := fun h0 ↦
    one_ne_zero (eq_zero_of_smul_germ_eq_zero m hx (by rw [h0, smul_zero]))
  have hnt : Nontrivial (L.presheaf.stalk x) := nontrivial_of_ne _ _ hne
  have hfin : Module.Finite (X.presheaf.stalk x) (L.presheaf.stalk x) :=
    ⟨span_germ_eq_top m hx ▸ Submodule.fg_span_singleton _⟩
  rw [vanishesAt_iff, he, Scheme.mem_basicOpen X g x hx]
  constructor
  · intro h hu
    obtain ⟨u, hu⟩ := hu
    have hmem := Submodule.smul_mem (IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
      (⊤ : Submodule (X.presheaf.stalk x) (L.presheaf.stalk x)))
      ((u⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) h
    rw [smul_smul, ← hu, Units.inv_mul, one_smul] at hmem
    have hspan : Submodule.span (X.presheaf.stalk x) {L.presheaf.germ W x hx m} ≤
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) • ⊤ :=
      Submodule.span_le.2 (Set.singleton_subset_iff.2 hmem)
    rw [span_germ_eq_top m hx] at hspan
    exact absurd (le_antisymm le_top hspan)
      (Submodule.ideal_smul_top_lt_top (R := X.presheaf.stalk x)
        (M := L.presheaf.stalk x)
        (I := IsLocalRing.maximalIdeal (X.presheaf.stalk x)) le_rfl).ne
  · intro h
    exact Submodule.smul_mem_smul
      ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 h)) Submodule.mem_top

end Trivialisation

end AlgebraicGeometry.Scheme.Modules
