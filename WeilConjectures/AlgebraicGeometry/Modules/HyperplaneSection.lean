/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Coherent
public import WeilConjectures.AlgebraicGeometry.Modules.Dimension
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyTrivial
public import WeilConjectures.AlgebraicGeometry.Modules.Vanishing

/-!
# The hyperplane exact sequence

A global section `s` of a sheaf of `𝒪ₓ`-modules `L` is a morphism `𝒪ₓ ⟶ L`, and tensoring it
on the right of a sheaf of modules `F` gives **multiplication by `s`**, a morphism
`F ⟶ F ⊗ L` (`AlgebraicGeometry.Scheme.Modules.mulSection`). This file proves that, for `L`
invertible and `F` quasi-coherent on a locally Noetherian scheme, this morphism is a
monomorphism exactly when `s` vanishes at no associated point of `F`, and assembles the
resulting short exact sequence

```
0 ⟶ F ⟶ F ⊗ L ⟶ G ⟶ 0
```

whose cokernel `G` is supported inside the support of `F` and avoids every generic point of an
irreducible component of that support.

## The tensor product on sections

The tensor product of sheaves of modules is the *sheafification* of the sectionwise tensor
product, so a section of `F ⊗ G` over an open subset is only locally a sum of products of
sections. The comparison map is the tensorator of the lax monoidal forgetful functor from sheaves
of modules to presheaves of modules, which is lax monoidal because it is right adjoint to the
monoidal sheafification functor; `SheafOfModules.mu_eq_tensorPresheafHom` identifies it with
`SheafOfModules.tensorPresheafHom`, so all its coherences — naturality and unitality — are those
of a lax monoidal functor. This is what makes `AlgebraicGeometry.Scheme.Modules.mulSection`,
defined by the monoidal formula, computable on sections as `t ↦ t ⊗ s`
(`AlgebraicGeometry.Scheme.Modules.app_mulSection`), and the tensorator is locally bijective, so
a product of sections that vanishes does so already in the sectionwise tensor product over a
small enough open subset.

## The criterion

The case `L = 𝒪ₓ` of the criterion is
`AlgebraicGeometry.Scheme.Modules.isSMulRegular_iff_associatedPoints_subset_basicOpen`, which
says that a global function acts injectively on a quasi-coherent sheaf over a Noetherian affine
open exactly when its zero locus misses the associated points there. The general case follows by
trivialising `L`: near any point there is an open `W` and a section `m` of `L` over `W` such that
multiplication by `m` is an isomorphism `𝒪_W ≅ L|_W`
(`SheafOfModules.Invertible.exists_isIso_unitSmulRestrictHom`), and then `s|_W = g • m` for a
unique global function `g` on `W`. The bridge between the two spellings of vanishing is
`AlgebraicGeometry.Scheme.Modules.vanishesAt_iff_notMem_basicOpen`: on `W`, the section `s`
vanishes at a point exactly where `g` does.

## Main results

- `AlgebraicGeometry.Scheme.Modules.mulSection`: **multiplication by a global section** of `L`,
  as a morphism `F ⟶ F ⊗ L`, with `AlgebraicGeometry.Scheme.Modules.app_mulSection` computing it
  on sections.
- `AlgebraicGeometry.Scheme.Modules.vanishesAt_iff_notMem_basicOpen`: vanishing of a section of
  an invertible sheaf is, in a trivialisation, the complement of a basic open subset.
- `AlgebraicGeometry.Scheme.Modules.coheight_le_one_of_minimal_vanishesAt`: **Krull's principal
  ideal theorem for a section of a line bundle**, every irreducible component of the zero locus
  of a global section of an invertible sheaf on a locally Noetherian scheme has codimension at
  most one. This is `AlgebraicGeometry.coheight_le_one_of_minimal_notMem_basicOpen` read through
  the trivialisation.
- `AlgebraicGeometry.Scheme.Modules.mono_mulSection_iff`: **the nonzerodivisor criterion**,
  multiplication by `s` is a monomorphism `F ⟶ F ⊗ L` if and only if `s` vanishes at no
  associated point of `F`.
- `AlgebraicGeometry.Scheme.Modules.support_cokernel_mulSection`: **the support of the cokernel
  is `Supp F ∩ Z(s)`**, the intersection of the support of `F` with the zero locus of `s`.
- `AlgebraicGeometry.Scheme.Modules.exists_shortExact_tensor_of_forall_not_vanishesAt`: **the
  hyperplane exact sequence**, with the support conditions on its cokernel.
- `AlgebraicGeometry.Scheme.Modules.exists_shortExact_supportDim_add_one_le`:
  **`lem:deg-general-hyperplane`**, the hyperplane exact sequence attached to a globally
  generated line bundle on a scheme over an infinite field, with the drop of the dimension of
  the support.

## Blueprint

This file contributes `lem:deg-general-hyperplane` of
`curve_estimates/28_degree_of_the_isogeny.tex`, assembling it from the genericity half — the
production of a section avoiding the associated points, which is
`WeilConjectures/AlgebraicGeometry/Modules/Vanishing.lean` — and the exact sequence proved
here.

## TODO

- Identify the cokernel `G` with `(F ⊗ L)|_D`, where `D` is the zero scheme of `s`. This is the
  geometric description of the sequence; its support is already computed here, as
  `AlgebraicGeometry.Scheme.Modules.support_cokernel_mulSection`.
-/

@[expose] public section

universe v₁ u₁ u

open CategoryTheory Limits MonoidalCategory Opposite TensorProduct TopologicalSpace
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

@[simp]
lemma tensorMk_zero_left {G : X.Modules} (U : X.Opens) (l : Γ(G, U)) :
    tensorMk (F := F) U 0 l = 0 := by
  have h : (0 : Γ(F, U)) ⊗ₜ[Γ(X, U)] l = 0 := TensorProduct.zero_tmul _ l
  rw [tensorMk, h, map_zero]

lemma tensorMk_add_left {G : X.Modules} (U : X.Opens) (t t' : Γ(F, U)) (l : Γ(G, U)) :
    tensorMk U (t + t') l = tensorMk U t l + tensorMk U t' l := by
  have h : (t + t') ⊗ₜ[Γ(X, U)] l = t ⊗ₜ[Γ(X, U)] l + t' ⊗ₜ[Γ(X, U)] l :=
    TensorProduct.add_tmul t t' l
  rw [tensorMk, tensorMk, tensorMk, h, map_add]

lemma tensorMk_smul_left {G : X.Modules} (U : X.Opens) (r : Γ(X, U)) (t : Γ(F, U)) (l : Γ(G, U)) :
    tensorMk U (r • t) l = r • tensorMk U t l := by
  have h : (r • t) ⊗ₜ[Γ(X, U)] l = r • (t ⊗ₜ[Γ(X, U)] l) := TensorProduct.smul_tmul' r t l
  rw [tensorMk, tensorMk, h]
  exact LinearMap.map_smul _ r _

lemma tensorMk_smul_right {G : X.Modules} (U : X.Opens) (r : Γ(X, U)) (t : Γ(F, U))
    (l : Γ(G, U)) : tensorMk U t (r • l) = r • tensorMk U t l := by
  have h : t ⊗ₜ[Γ(X, U)] (r • l) = r • (t ⊗ₜ[Γ(X, U)] l) := TensorProduct.tmul_smul r t l
  rw [tensorMk, tensorMk, h]
  exact LinearMap.map_smul _ r _

lemma map_tensorMk {G : X.Modules} {U V : X.Opens} (i : V ⟶ U) (t : Γ(F, U)) (l : Γ(G, U)) :
    (F ⊗ G).presheaf.map i.op (tensorMk U t l) =
      tensorMk V (F.presheaf.map i.op t) (G.presheaf.map i.op l) := by
  have h := PresheafOfModules.naturality_apply
    (μ (SheafOfModules.forgetRestrict (R := X.sheaf)) F G) i.op (t ⊗ₜ[Γ(X, U)] l)
  exact h.symm

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

/-- **A section of an invertible sheaf is a function times a trivialising section.** If
multiplication by `m : Γ(L, W)` is an isomorphism `𝒪_W ≅ L|_W`, then every section `t` of `L`
over `W` is `g • m` for some function `g` on `W`. -/
theorem exists_eq_smul (m : Γ(L, W)) [IsIso (unitSmulRestrictHom m)] (t : Γ(L, W)) :
    ∃ g : Γ(X, W), t = g • m := by
  obtain ⟨g, hg⟩ := (bijective_smulSection m le_rfl).2 t
  refine ⟨g, ?_⟩
  rw [← hg, smulSection_self]

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
    rw [smulSection_apply, ← hzz]
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


/-- **Krull's principal ideal theorem for a section of a line bundle.** Let `s` be a global
section of an invertible sheaf `L` on a locally Noetherian scheme `X`, and let `z` be a point at
which `s` vanishes such that the only point where `s` vanishes generalizing to `z` is `z` itself
— that is, `z` is the generic point of an irreducible component of the zero locus of `s`. Then
`z` has codimension at most one in `X`.

Trivialising `L` on an open neighbourhood `W` of `z` writes `s|_W` as `g • m` for a function `g`
on `W` with the same zero locus, by
`AlgebraicGeometry.Scheme.Modules.vanishesAt_iff_notMem_basicOpen`, and the statement becomes
`AlgebraicGeometry.coheight_le_one_of_minimal_notMem_basicOpen`. -/
theorem coheight_le_one_of_minimal_vanishesAt [IsLocallyNoetherian X] (hL : L.Invertible)
    (s : Γ(L, ⊤)) {z : X} (hz : L.VanishesAt s z)
    (hmin : ∀ y, L.VanishesAt s y → y ⤳ z → y = z) :
    Order.coheight z ≤ 1 := by
  obtain ⟨V, hzV, m, hm⟩ := hL.exists_isIso_unitSmulRestrictHom z
  have : IsIso (unitSmulRestrictHom m) := hm
  obtain ⟨g, hgV⟩ := exists_eq_smul m (L.presheaf.map V.leTop.op s)
  exact coheight_le_one_of_minimal_notMem_basicOpen g hzV
    ((vanishesAt_iff_notMem_basicOpen m s g hgV hzV).1 hz)
    fun y hyV hy hyz ↦ hmin y ((vanishesAt_iff_notMem_basicOpen m s g hgV hyV).2 hy) hyz

/-- **Multiplication by a trivialising section, as a linear equivalence on sections.** -/
noncomputable def smulSectionEquiv (m : Γ(L, W)) [IsIso (unitSmulRestrictHom m)]
    {V : X.Opens} (hV : V ≤ W) : Γ(X, V) ≃ₗ[Γ(X, V)] Γ(L, V) :=
  LinearEquiv.ofBijective
    { toFun := smulSection m V hV
      map_add' := (smulSection m V hV).map_add
      map_smul' := smulSection_smul m V hV }
    (bijective_smulSection m hV)

@[simp]
lemma smulSectionEquiv_apply (m : Γ(L, W)) [IsIso (unitSmulRestrictHom m)]
    {V : X.Opens} (hV : V ≤ W) (r : Γ(X, V)) :
    smulSectionEquiv m hV r = smulSection m V hV r := rfl

/-- **Contracting the second factor of `F ⊗ L` against a trivialisation of `L`.** Over an open
subset on which `m` trivialises `L`, the sectionwise tensor product `Γ(F, V) ⊗ Γ(L, V)` maps to
`Γ(F, V)` by using `m` to read a section of `L` as a function. -/
noncomputable def tensorContract (F : X.Modules) (m : Γ(L, W))
    [IsIso (unitSmulRestrictHom m)] {V : X.Opens} (hV : V ≤ W) :
    Γ(F, V) ⊗[Γ(X, V)] Γ(L, V) →ₗ[Γ(X, V)] Γ(F, V) :=
  TensorProduct.lift (LinearMap.mk₂ Γ(X, V)
    (fun (a : Γ(F, V)) (l : Γ(L, V)) ↦ (smulSectionEquiv m hV).symm l • a)
    (fun _ _ _ ↦ smul_add _ _ _) (fun _ _ _ ↦ smul_comm _ _ _)
    (fun _ _ _ ↦ by rw [map_add, add_smul])
    (fun _ _ _ ↦ by rw [_root_.map_smul, smul_eq_mul, mul_smul]))

lemma tensorContract_tmul (F : X.Modules) (m : Γ(L, W)) [IsIso (unitSmulRestrictHom m)]
    {V : X.Opens} (hV : V ≤ W) (a : Γ(F, V)) (l : Γ(L, V)) :
    tensorContract F m hV (a ⊗ₜ[Γ(X, V)] l) = (smulSectionEquiv m hV).symm l • a := rfl

/-- **A vanishing tensor against a trivialised section is a vanishing product.** -/
theorem smul_eq_zero_of_tmul_eq_zero (F : X.Modules) (m : Γ(L, W))
    [IsIso (unitSmulRestrictHom m)] {V : X.Opens} (hV : V ≤ W) (a : Γ(F, V)) (r : Γ(X, V))
    (h : a ⊗ₜ[Γ(X, V)] smulSection m V hV r = 0) : r • a = 0 := by
  have h' := congrArg (tensorContract F m hV) h
  rwa [map_zero, tensorContract_tmul, ← smulSectionEquiv_apply,
    LinearEquiv.symm_apply_apply] at h'

/-- **Over a trivialising open every element of the sectionwise tensor product is a product with
the trivialising section.** -/
theorem app_mu_eq_tensorMk (F : X.Modules) (m : Γ(L, W)) [IsIso (unitSmulRestrictHom m)]
    {V : X.Opens} (hV : V ≤ W) (z : Γ(F, V) ⊗[Γ(X, V)] Γ(L, V)) :
    ((μ (SheafOfModules.forgetRestrict (R := X.sheaf)) F L).app (op V)).hom z =
      tensorMk V (tensorContract F m hV z) (L.presheaf.map (homOfLE hV).op m) := by
  induction z with
  | zero => rw [map_zero, map_zero, tensorMk_zero_left]
  | tmul a l =>
    have hl : (smulSectionEquiv m hV).symm l • L.presheaf.map (homOfLE hV).op m = l :=
      (smulSectionEquiv m hV).apply_symm_apply l
    rw [tensorContract_tmul, tensorMk_smul_left, ← tensorMk_smul_right, hl]
    rfl
  | add z z' hz hz' => rw [map_add, hz, hz', map_add, tensorMk_add_left]

/-- **Local description of the sections of `F ⊗ L` over a trivialising open**: every section is,
after restriction to a neighbourhood of any of its points, the product of a section of `F` with
the trivialising section. -/
theorem exists_tensorMk_eq (F : X.Modules) (m : Γ(L, W)) [IsIso (unitSmulRestrictHom m)]
    {U : X.Opens} (hUW : U ≤ W) (y : Γ(F ⊗ L, U)) {x : X} (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧ ∃ b : Γ(F, V),
      (F ⊗ L).presheaf.map (homOfLE hVU).op y =
        tensorMk V b (L.presheaf.map (homOfLE (hVU.trans hUW)).op m) := by
  have hls := (SheafOfModules.w_toPresheaf_map_mu (R := X.sheaf) F L).isLocallySurjective
  obtain ⟨V, hVU, ⟨z, hz⟩, hxV⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).1 hls U y x hx
  exact ⟨V, hVU, hxV, tensorContract F m (hVU.trans hUW) z,
    hz.symm.trans (app_mu_eq_tensorMk F m (hVU.trans hUW) z)⟩

end Trivialisation

/-- **The nonzerodivisor criterion for an invertible sheaf: sufficiency.** If `L` is invertible
and the global section `s` of `L` vanishes at no associated point of the quasi-coherent sheaf
`F`, then multiplication by `s` is a monomorphism `F ⟶ F ⊗ L`. -/
theorem mono_mulSection_of_forall_not_vanishesAt [IsLocallyNoetherian X] {L : X.Modules}
    (hL : L.Invertible) (F : X.Modules) [F.IsQuasicoherent] (s : Γ(L, ⊤))
    (hs : ∀ x ∈ F.associatedPoints, ¬ L.VanishesAt s x) :
    Mono (mulSection F s) := by
  have hres : ∀ (A : X.Modules) {V V' : X.Opens} (h : V ≤ V') (a : Γ(A, ⊤)),
      A.presheaf.map (homOfLE h).op (A.presheaf.map V'.leTop.op a) =
        A.presheaf.map V.leTop.op a := by
    intro A V V' h a
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    congr 2
  refine mono_of_injective_app _ fun U ↦ ?_
  have hzero : ∀ t : Γ(F, U), Hom.app (mulSection F s) U t = 0 → t = 0 := by
    intro t ht
    rw [app_mulSection] at ht
    refine TopCat.Presheaf.section_ext ⟨F.presheaf, F.isSheaf⟩ U t 0 fun x hxU ↦ ?_
    obtain ⟨V₀, hV₀U, hxV₀, hker⟩ :=
      exists_restrict_tmul_eq_zero t (L.presheaf.map U.leTop.op s) ht hxU
    obtain ⟨W, hxW, m, hm⟩ := hL.exists_isIso_unitSmulRestrictHom x
    have : IsIso (unitSmulRestrictHom m) := hm
    obtain ⟨g, hgW⟩ := exists_eq_smul m (L.presheaf.map W.leTop.op s)
    obtain ⟨-, ⟨V, hVaff, rfl⟩, hxV, hVsub⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((V₀ ⊓ W : X.Opens) : Set X) from ⟨hxV₀, hxW⟩) (V₀ ⊓ W).2
    have hVV₀ : V ≤ V₀ := fun y hy ↦ (hVsub hy).1
    have hVW : V ≤ W := fun y hy ↦ (hVsub hy).2
    have hsV : L.presheaf.map (homOfLE (hVV₀.trans hV₀U)).op (L.presheaf.map U.leTop.op s) =
        smulSection m V hVW (X.presheaf.map (homOfLE hVW).op g) := by
      rw [hres L, ← map_smulSection m le_rfl hVW (homOfLE hVW) g, smulSection_self, ← hgW,
        hres L]
    have hkey : X.presheaf.map (homOfLE hVW).op g •
        F.presheaf.map (homOfLE (hVV₀.trans hV₀U)).op t = 0 :=
      smul_eq_zero_of_tmul_eq_zero F m hVW _ _ (hsV ▸ hker V hVV₀)
    have hnoeth : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hVaff⟩
    have hreg : IsSMulRegular Γ(F, V) (X.presheaf.map (homOfLE hVW).op g) := by
      rw [isSMulRegular_iff_associatedPoints_subset_basicOpen F hVaff]
      rintro y ⟨hy, hyV⟩
      rw [Scheme.basicOpen_res]
      refine ⟨hyV, ?_⟩
      by_contra hyb
      exact hs y hy ((vanishesAt_iff_notMem_basicOpen m s g hgW (hVW hyV)).2 hyb)
    have ht0 : F.presheaf.map (homOfLE (hVV₀.trans hV₀U)).op t = 0 :=
      hreg (hkey.trans (smul_zero _).symm)
    rw [map_zero, ← TopCat.Presheaf.germ_res_apply F.presheaf
      (homOfLE (hVV₀.trans hV₀U)) x hxV t, ht0, map_zero]
  intro a b hab
  have hsub : Hom.app (mulSection F s) U (a - b) = 0 := by rw [map_sub, hab, sub_self]
  simpa [sub_eq_zero] using hzero _ hsub

section Support

variable {L : X.Modules}

/-- **A tensor product with an invertible sheaf has trivial stalk wherever the first factor
does.** -/
theorem eq_zero_of_subsingleton_stalk (hL : L.Invertible) (F : X.Modules) {x : X}
    (hx : Subsingleton (F.presheaf.stalk x)) (y : (F ⊗ L).presheaf.stalk x) : y = 0 := by
  obtain ⟨W, hxW, m, hm⟩ := hL.exists_isIso_unitSmulRestrictHom x
  have : IsIso (unitSmulRestrictHom m) := hm
  obtain ⟨U, hxU, y₀, rfl⟩ := (F ⊗ L).presheaf.exists_germ_eq y
  have hxUW : x ∈ U ⊓ W := ⟨hxU, hxW⟩
  rw [← (F ⊗ L).presheaf.germ_res_apply (homOfLE (inf_le_left : U ⊓ W ≤ U)) x hxUW y₀]
  obtain ⟨V, hVU, hxV, b, hb⟩ := exists_tensorMk_eq F m (inf_le_right : U ⊓ W ≤ W)
    ((F ⊗ L).presheaf.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op y₀) hxUW
  rw [← (F ⊗ L).presheaf.germ_res_apply (homOfLE hVU) x hxV _, hb]
  obtain ⟨V', hxV', i, i', hbb⟩ :=
    F.presheaf.germ_eq x hxV hxV b 0 (Subsingleton.elim _ _)
  rw [map_zero] at hbb
  rw [← (F ⊗ L).presheaf.germ_res_apply i x hxV' _, map_tensorMk, hbb, tensorMk_zero_left,
    map_zero]

/-- **The support of `F ⊗ L` is contained in the support of `F`** when `L` is invertible. -/
theorem support_tensor_subset (hL : L.Invertible) (F : X.Modules) :
    (F ⊗ L).support ⊆ F.support := by
  intro x hx
  by_contra hxF
  have hsubF : Subsingleton (F.presheaf.stalk x) :=
    not_nontrivial_iff_subsingleton.1 (fun h ↦ hxF h)
  obtain ⟨a, b, hab⟩ := (mem_support_iff (F ⊗ L) x).1 hx
  exact hab ((eq_zero_of_subsingleton_stalk hL F hsubF a).trans
    (eq_zero_of_subsingleton_stalk hL F hsubF b).symm)

/-- **At a point where the section does not vanish, multiplication by it is surjective on
stalks.** -/
theorem surjective_stalkFunctor_map_mulSection (hL : L.Invertible) (F : X.Modules) (s : Γ(L, ⊤))
    {x : X} (hx : ¬ L.VanishesAt s x) :
    Function.Surjective
      ((SheafOfModules.stalkFunctor X.ringCatSheaf x).map (mulSection F s)) := by
  obtain ⟨W, hxW, m, hm⟩ := hL.exists_isIso_unitSmulRestrictHom x
  have : IsIso (unitSmulRestrictHom m) := hm
  obtain ⟨g, hgW⟩ := exists_eq_smul m (L.presheaf.map W.leTop.op s)
  have hxg : x ∈ X.basicOpen g := by
    by_contra h
    exact hx ((vanishesAt_iff_notMem_basicOpen m s g hgW hxW).2 h)
  intro y
  obtain ⟨U, hxU, y₀, rfl⟩ := (F ⊗ L).presheaf.exists_germ_eq y
  have hxB : x ∈ U ⊓ X.basicOpen g := ⟨hxU, hxg⟩
  have hBW : U ⊓ X.basicOpen g ≤ W := inf_le_right.trans (X.basicOpen_le g)
  rw [← (F ⊗ L).presheaf.germ_res_apply
    (homOfLE (inf_le_left : U ⊓ X.basicOpen g ≤ U)) x hxB y₀]
  obtain ⟨V, hVB, hxV, b, hb⟩ := exists_tensorMk_eq F m hBW
    ((F ⊗ L).presheaf.map (homOfLE (inf_le_left : U ⊓ X.basicOpen g ≤ U)).op y₀) hxB
  rw [← (F ⊗ L).presheaf.germ_res_apply (homOfLE hVB) x hxV _, hb]
  have hVW : V ≤ W := hVB.trans hBW
  have hVg : V ≤ X.basicOpen g := hVB.trans inf_le_right
  obtain ⟨u, hu⟩ : IsUnit (X.presheaf.map (homOfLE hVW).op g) := by
    have h₀ : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le g)).op g) :=
      X.toRingedSpace.isUnit_res_basicOpen g
    have h₂ : X.presheaf.map (homOfLE hVW).op g =
        X.presheaf.map (homOfLE hVg).op
          (X.presheaf.map (homOfLE (X.basicOpen_le g)).op g) := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      congr 2
    rw [h₂]
    exact h₀.map _
  have hmV : L.presheaf.map (homOfLE hVW).op m = ((u⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) •
      L.presheaf.map V.leTop.op s := by
    have h₁ : L.presheaf.map V.leTop.op s =
        X.presheaf.map (homOfLE hVW).op g • L.presheaf.map (homOfLE hVW).op m := by
      rw [show L.presheaf.map V.leTop.op s =
        L.presheaf.map (homOfLE hVW).op (L.presheaf.map W.leTop.op s) from by
          rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]; congr 2,
        hgW, Scheme.Modules.map_smul]
    rw [h₁, ← hu, smul_smul, Units.inv_mul, one_smul]
  refine ⟨F.presheaf.germ V x hxV (((u⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) • b), ?_⟩
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV
    (mulSection F s).mapPresheaf (((u⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) • b)).trans ?_
  congr 1
  change Hom.app (mulSection F s) V _ = _
  rw [app_mulSection, tensorMk_smul_left, ← tensorMk_smul_right, ← hmV]

/-- The map induced on stalks by the projection onto the cokernel of multiplication by a global
section is surjective. -/
theorem surjective_stalkFunctor_map_cokernelπ (F : X.Modules) (s : Γ(L, ⊤)) (x : X) :
    Function.Surjective ((SheafOfModules.stalkFunctor X.ringCatSheaf x).map
      (cokernel.π (mulSection F s))) := by
  have hepi : Epi ((SheafOfModules.stalkFunctor X.ringCatSheaf x).map
      (cokernel.π (mulSection F s))) :=
    (SheafOfModules.stalkFunctor X.ringCatSheaf x).map_epi _
  exact (AddCommGrpCat.epi_iff_surjective _).1 hepi

/-- **The cokernel of multiplication by a global section of an invertible sheaf is supported in
the support of `F`.** -/
theorem support_cokernel_mulSection_subset (hL : L.Invertible) (F : X.Modules) (s : Γ(L, ⊤)) :
    (cokernel (mulSection F s)).support ⊆ F.support := by
  intro x hx
  by_contra hxF
  have hsubF : Subsingleton (F.presheaf.stalk x) :=
    not_nontrivial_iff_subsingleton.1 fun h ↦ hxF h
  obtain ⟨a, b, hab⟩ := (mem_support_iff _ x).1 hx
  obtain ⟨a', rfl⟩ := surjective_stalkFunctor_map_cokernelπ F s x a
  obtain ⟨b', rfl⟩ := surjective_stalkFunctor_map_cokernelπ F s x b
  rw [eq_zero_of_subsingleton_stalk hL F hsubF a', eq_zero_of_subsingleton_stalk hL F hsubF b']
    at hab
  exact hab rfl

/-- **The cokernel of multiplication by a global section is supported where the section
vanishes.** -/
theorem notMem_support_cokernel_mulSection (hL : L.Invertible) (F : X.Modules) (s : Γ(L, ⊤))
    {x : X} (hx : ¬ L.VanishesAt s x) : x ∉ (cokernel (mulSection F s)).support := by
  intro hmem
  obtain ⟨a, b, hab⟩ := (mem_support_iff _ x).1 hmem
  have key : ∀ w : (cokernel (mulSection F s)).presheaf.stalk x, w = 0 := by
    intro w
    obtain ⟨y, rfl⟩ := surjective_stalkFunctor_map_cokernelπ F s x w
    obtain ⟨z, rfl⟩ := surjective_stalkFunctor_map_mulSection hL F s hx y
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, cokernel.condition,
      Functor.map_zero]
    rfl
  exact hab ((key a).trans (key b).symm)

/-- **The support of `F` is contained in the support of `F ⊗ L`** when `L` is invertible:
tensoring by a tensor inverse of `L` turns `F ⊗ L` back into `F`, and tensoring cannot enlarge
the support by `AlgebraicGeometry.Scheme.Modules.support_tensor_subset`. -/
theorem support_subset_support_tensor (hL : L.Invertible) (F : X.Modules) :
    F.support ⊆ (F ⊗ L).support := by
  have e : F ≅ (F ⊗ L) ⊗ hL.tensorInv :=
    (ρ_ F).symm ≪≫ whiskerLeftIso F hL.tensorInvIso.symm ≪≫ (α_ F L hL.tensorInv).symm
  rw [support_congr e]
  exact support_tensor_subset (SheafOfModules.invertible_tensorInv hL) (F ⊗ L)

/-- **Tensoring by an invertible sheaf does not change the support.** -/
theorem support_tensor (hL : L.Invertible) (F : X.Modules) : (F ⊗ L).support = F.support :=
  subset_antisymm (support_tensor_subset hL F) (support_subset_support_tensor hL F)

/-- **At a point where the section vanishes, multiplication by it lands in `𝔪ₓ (F ⊗ L)ₓ` on
stalks.** In a trivialisation `L|_W ≅ 𝒪_W` by a section `m`, the section `s` restricts to
`g • m`, and `s` vanishes at `x` exactly when `g` is not invertible at `x`
(`AlgebraicGeometry.Scheme.Modules.vanishesAt_iff_notMem_basicOpen`); the germ of `g` is then a
scalar in the maximal ideal which factors out of every product `t ⊗ s`. -/
theorem stalkMap_mulSection_mem_smul_maximalIdeal (hL : L.Invertible) (F : X.Modules)
    (s : Γ(L, ⊤)) {x : X} (hx : L.VanishesAt s x) (z : F.presheaf.stalk x) :
    (mulSection F s).stalkMap x z ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
        (⊤ : Submodule (X.presheaf.stalk x) ((F ⊗ L).presheaf.stalk x)) := by
  obtain ⟨W, hxW, m, hm⟩ := hL.exists_isIso_unitSmulRestrictHom x
  have : IsIso (unitSmulRestrictHom m) := hm
  obtain ⟨g, hgW⟩ := exists_eq_smul m (L.presheaf.map W.leTop.op s)
  have hgmax : X.presheaf.germ W x hxW g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    have hxg : x ∉ X.basicOpen g := (vanishesAt_iff_notMem_basicOpen m s g hgW hxW).1 hx
    rw [Scheme.mem_basicOpen X g x hxW] at hxg
    exact (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hxg)
  obtain ⟨U, hxU, b, rfl⟩ := F.presheaf.exists_germ_eq z
  have hxV : x ∈ U ⊓ W := ⟨hxU, hxW⟩
  rw [← F.presheaf.germ_res_apply (homOfLE (inf_le_left : U ⊓ W ≤ U)) x hxV b,
    Hom.germ_stalkMap_apply, app_mulSection]
  have hsV : L.presheaf.map (U ⊓ W).leTop.op s =
      X.presheaf.map (homOfLE (inf_le_right : U ⊓ W ≤ W)).op g •
        L.presheaf.map (homOfLE (inf_le_right : U ⊓ W ≤ W)).op m := by
    rw [show L.presheaf.map (U ⊓ W).leTop.op s =
      L.presheaf.map (homOfLE (inf_le_right : U ⊓ W ≤ W)).op
        (L.presheaf.map W.leTop.op s) from by
          rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]; congr 2,
      hgW, Scheme.Modules.map_smul]
  rw [hsV, tensorMk_smul_right, germ_smul,
    X.presheaf.germ_res_apply (homOfLE (inf_le_right : U ⊓ W ≤ W)) x hxV g]
  exact Submodule.smul_mem_smul hgmax Submodule.mem_top

/-- **The cokernel of multiplication by a global section is supported at every point of the
support of `F` where the section vanishes.**

This is Nakayama's lemma. Taking stalks at `x` is exact, so the stalk of the cokernel is the
quotient of `(F ⊗ L)ₓ` by the image of multiplication by `s`, and that image is contained in
`𝔪ₓ (F ⊗ L)ₓ` because `s` vanishes at `x`
(`AlgebraicGeometry.Scheme.Modules.stalkMap_mulSection_mem_smul_maximalIdeal`). A vanishing
cokernel would therefore give `(F ⊗ L)ₓ = 𝔪ₓ (F ⊗ L)ₓ`, forcing the finite module `(F ⊗ L)ₓ`
over the local ring `𝒪_{X, x}` to vanish — but it does not, since `x` lies in the support of
`F`. -/
theorem mem_support_cokernel_mulSection (hL : L.Invertible) (F : X.Modules) [F.IsCoherent]
    (s : Γ(L, ⊤)) (hmono : Mono (mulSection F s)) {x : X} (hxF : x ∈ F.support)
    (hxs : L.VanishesAt s x) : x ∈ (cokernel (mulSection F s)).support := by
  by_contra hmem
  have hsub : Subsingleton ((cokernel (mulSection F s)).presheaf.stalk x) :=
    not_nontrivial_iff_subsingleton.1 fun h ↦ hmem h
  have hFL : (F ⊗ L).IsCoherent := isCoherent_tensorObj_of_invertible F hL
  have hfin : Module.Finite (X.presheaf.stalk x) ((F ⊗ L).presheaf.stalk x) :=
    finite_stalk (F ⊗ L) x
  have hSE : (ShortComplex.mk (mulSection F s) (cokernel.π (mulSection F s))
      (cokernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_cokernel _
      mono_f := hmono
      epi_g := inferInstance }
  have hex := (hSE.map_stalkFunctor (R := X.ringCatSheaf) x).exact
  rw [ShortComplex.ab_exact_iff] at hex
  have hle : (⊤ : Submodule (X.presheaf.stalk x) ((F ⊗ L).presheaf.stalk x)) ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) • ⊤ := by
    intro y _
    obtain ⟨z, hz⟩ := hex y (hsub.elim _ _)
    rw [← hz]
    exact stalkMap_mulSection_mem_smul_maximalIdeal hL F s hxs z
  have htop : (⊤ : Submodule (X.presheaf.stalk x) ((F ⊗ L).presheaf.stalk x)) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ ⊤ (Module.finite_def.1 hfin) hle
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  have hnt : Nontrivial ((F ⊗ L).presheaf.stalk x) := support_subset_support_tensor hL F hxF
  obtain ⟨a, ha⟩ := exists_ne (0 : (F ⊗ L).presheaf.stalk x)
  have hmem : a ∈ (⊤ : Submodule (X.presheaf.stalk x) ((F ⊗ L).presheaf.stalk x)) :=
    Submodule.mem_top
  rw [htop, Submodule.mem_bot] at hmem
  exact ha hmem

/-- **The support of the cokernel of the hyperplane map is `Supp F ∩ Z(s)`**: the cokernel of
multiplication by a global section `s` of an invertible sheaf `L` is supported exactly at the
points of the support of `F` at which `s` vanishes.

The two inclusions are `AlgebraicGeometry.Scheme.Modules.support_cokernel_mulSection_subset`
together with `AlgebraicGeometry.Scheme.Modules.notMem_support_cokernel_mulSection`, and
`AlgebraicGeometry.Scheme.Modules.mem_support_cokernel_mulSection`. -/
theorem support_cokernel_mulSection (hL : L.Invertible) (F : X.Modules) [F.IsCoherent]
    (s : Γ(L, ⊤)) (hmono : Mono (mulSection F s)) :
    (cokernel (mulSection F s)).support = F.support ∩ {x | L.VanishesAt s x} := by
  ext x
  refine ⟨fun hx ↦ ⟨support_cokernel_mulSection_subset hL F s hx, ?_⟩, ?_⟩
  · by_contra h
    exact notMem_support_cokernel_mulSection hL F s h hx
  · rintro ⟨hxF, hxs⟩
    exact mem_support_cokernel_mulSection hL F s hmono hxF hxs

end Support

/-- **The nonzerodivisor criterion for an invertible sheaf: necessity.** If multiplication by
the global section `s` of an invertible sheaf `L` is a monomorphism `F ⟶ F ⊗ L`, then `s`
vanishes at no associated point of `F`. -/
theorem forall_not_vanishesAt_of_mono_mulSection [IsLocallyNoetherian X] {L : X.Modules}
    (hL : L.Invertible) (F : X.Modules) [F.IsQuasicoherent] (s : Γ(L, ⊤))
    (hmono : Mono (mulSection F s)) : ∀ x ∈ F.associatedPoints, ¬ L.VanishesAt s x := by
  intro x hx hvan
  obtain ⟨W, hxW, m, hm⟩ := hL.exists_isIso_unitSmulRestrictHom x
  have : IsIso (unitSmulRestrictHom m) := hm
  obtain ⟨g, hgW⟩ := exists_eq_smul m (L.presheaf.map W.leTop.op s)
  have hxg : x ∉ X.basicOpen g := (vanishesAt_iff_notMem_basicOpen m s g hgW hxW).1 hvan
  obtain ⟨-, ⟨V, hVaff, rfl⟩, hxV, hVsub⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (W : Set X) from hxW) W.2
  have hVW : V ≤ W := fun y hy ↦ hVsub hy
  have hnoeth : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hVaff⟩
  have hnreg : ¬ IsSMulRegular Γ(F, V) (X.presheaf.map (homOfLE hVW).op g) := by
    rw [isSMulRegular_iff_associatedPoints_subset_basicOpen F hVaff]
    intro hsub
    have hmem := hsub ⟨hx, hxV⟩
    rw [Scheme.basicOpen_res] at hmem
    exact hxg hmem.2
  obtain ⟨b, c, hbc, hne⟩ := Function.not_injective_iff.1 hnreg
  refine hne (sub_eq_zero.1 ?_)
  have ha : X.presheaf.map (homOfLE hVW).op g • (b - c) = 0 := by
    rw [smul_sub, show X.presheaf.map (homOfLE hVW).op g • b =
      X.presheaf.map (homOfLE hVW).op g • c from hbc, sub_self]
  have hres : L.presheaf.map V.leTop.op s =
      smulSection m V hVW (X.presheaf.map (homOfLE hVW).op g) := by
    rw [← map_smulSection m le_rfl hVW (homOfLE hVW) g, smulSection_self, ← hgW,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    congr 2
  have hinj : Function.Injective (Hom.app (mulSection F s) V) :=
    injective_app_of_mono (M := F) (N := F ⊗ L) (mulSection F s) hmono V
  refine hinj ?_
  rw [app_mulSection, hres, map_zero, smulSection_apply, tensorMk_smul_right,
    ← tensorMk_smul_left, ha, tensorMk_zero_left]

/-- **The nonzerodivisor criterion for an invertible sheaf.** For `L` invertible and `F`
quasi-coherent on a locally Noetherian scheme, multiplication by a global section `s` of `L` is a
monomorphism `F ⟶ F ⊗ L` if and only if `s` vanishes at no associated point of `F`. -/
theorem mono_mulSection_iff [IsLocallyNoetherian X] {L : X.Modules} (hL : L.Invertible)
    (F : X.Modules) [F.IsQuasicoherent] (s : Γ(L, ⊤)) :
    Mono (mulSection F s) ↔ ∀ x ∈ F.associatedPoints, ¬ L.VanishesAt s x :=
  ⟨forall_not_vanishesAt_of_mono_mulSection hL F s,
    mono_mulSection_of_forall_not_vanishesAt hL F s⟩

/-- **The hyperplane exact sequence.** Let `F` be a coherent sheaf on a locally Noetherian
scheme `X` and let `L` be an invertible sheaf with a global section `s` vanishing at no
associated point of `F`. Then there is a short exact sequence

```
0 ⟶ F ⟶ F ⊗ L ⟶ G ⟶ 0
```

in which `G` is coherent, the first map is multiplication by `s`, the support of `G` is the
intersection of the support of `F` with the zero locus of `s`, and `G` is not supported at any
generic point of an irreducible component of the support of `F` — that is, at any point of the
support of `F` to which no other point of the support specialises.

This is the form consumed by `exists_shortExact_supportDim_add_one_le` below: the sequence is
the one along which the Euler characteristic is additive, and the last condition is what makes
the dimension of the support of `G` drop. -/
theorem exists_shortExact_tensor_of_forall_not_vanishesAt [IsLocallyNoetherian X]
    {L : X.Modules} (hL : L.Invertible) (F : X.Modules) [F.IsCoherent] (s : Γ(L, ⊤))
    (hs : ∀ x ∈ F.associatedPoints, ¬ L.VanishesAt s x) :
    ∃ (G : X.Modules) (_ : G.IsCoherent) (u : F ⟶ F ⊗ L) (v : F ⊗ L ⟶ G) (hw : u ≫ v = 0),
      (ShortComplex.mk u v hw).ShortExact ∧ G.support = F.support ∩ {x | L.VanishesAt s x} ∧
        ∀ x ∈ F.support, (∀ y : X, y ∈ F.support → y ⤳ x → y = x) → x ∉ G.support := by
  have hFL : (F ⊗ L).IsCoherent := isCoherent_tensorObj_of_invertible F hL
  refine ⟨cokernel (mulSection F s),
    isCoherent_cokernel (mulSection F s) inferInstance hFL,
    mulSection F s, cokernel.π _, cokernel.condition _,
    { exact := ShortComplex.exact_cokernel _
      mono_f := mono_mulSection_of_forall_not_vanishesAt hL F s hs
      epi_g := inferInstance },
    support_cokernel_mulSection hL F s (mono_mulSection_of_forall_not_vanishesAt hL F s hs),
    fun x hx hmin ↦ ?_⟩
  obtain ⟨U, hU, hxU⟩ : ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨U, hU, hxU⟩
  have hnoeth : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hfin : Module.Finite Γ(X, U) Γ(F, U) := finite_sections F ⟨U, hU⟩
  exact notMem_support_cokernel_mulSection hL F s
    (hs x (isAssociatedPoint_of_minimal_mem_support F hU ⟨x, hxU⟩ hx hmin))

/-- **`lem:deg-general-hyperplane`: a hyperplane section avoiding the associated points.** Let
`X` be a quasi-compact locally Noetherian scheme over an infinite field `k`, let `F` be a
coherent sheaf of `𝒪ₓ`-modules and let `L` be a globally generated line bundle on `X` — a very
ample one, in the application. Then there is a short exact sequence

```
0 ⟶ F ⟶ F ⊗ L ⟶ G ⟶ 0
```

whose first map is multiplication by a global section of `L`, with `G` coherent and
`dim G + 1 ≤ dim F`. -/
theorem exists_shortExact_supportDim_add_one_le (k : Type u) [Field k] [Infinite k]
    [X.Over (Spec (.of k))] [CompactSpace X] [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsCoherent] {L : X.Modules} (hL : L.Invertible) [L.IsGloballyGenerated] :
    ∃ (G : X.Modules) (_ : G.IsCoherent) (u : F ⟶ F ⊗ L) (v : F ⊗ L ⟶ G) (hw : u ≫ v = 0),
      (ShortComplex.mk u v hw).ShortExact ∧ G.supportDim + 1 ≤ F.supportDim := by
  obtain ⟨s, hs⟩ := exists_forall_associatedPoints_not_vanishesAt_of_invertible k F hL
  obtain ⟨G, hG, u, v, hw, hSE, hGF, hmin⟩ :=
    exists_shortExact_tensor_of_forall_not_vanishesAt hL F s hs
  have : G.IsCoherent := hG
  exact ⟨G, hG, u, v, hw, hSE,
    supportDim_add_one_le_supportDim_of_forall_minimal
      (hGF.subset.trans Set.inter_subset_left) fun x hx hmin' ↦
      hmin x hx fun y hy hyx ↦ hmin' y hy hyx⟩

end AlgebraicGeometry.Scheme.Modules
