/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Sheaf.Paper.RingedSiteIdeal
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Paper.FlatRingedCechBaseChange
import Sheaf.Paper.RingedCechHomCoefficientAction
import Sheaf.Paper.ExtendedCechCompletionModel
import Sheaf.Paper.RestrictionLocalCompleteness

/-!
# Flat ringed-site equivalence on locally derived complete objects

Source: Stacks Project, Algebraization, Tags 099I and 0999
(blueprint: lem-weil-pbc-flat-ringed-ideal-complete-equivalence).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Restriction of scalars is exact on module sheaves.
Source: Stacks Project, Algebraization, Tag 099C
(blueprint: lem-weil-pbc-flat-ringed-ideal-complete-equivalence).
Proof: the underlying additive sheaf is unchanged. Kernels are sectionwise kernels with
restricted action; cokernels are sheafifications of the same additive presheaf cokernels.
The same description applies to finite products and coproducts. -/
theorem siteRestrictScalars_exact {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    PreservesFiniteLimits
      (SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)) ∧
    PreservesFiniteColimits
      (SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)) := by
  let r := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  have : PreservesFiniteLimits (r ⋙ SheafOfModules.toSheaf (siteModuleRings R)) := by
    change PreservesFiniteLimits (SheafOfModules.toSheaf (siteModuleRings B))
    infer_instance
  have : PreservesFiniteColimits (r ⋙ SheafOfModules.toSheaf (siteModuleRings R)) := by
    change PreservesFiniteColimits (SheafOfModules.toSheaf (siteModuleRings B))
    infer_instance
  have : PreservesFiniteColimits (SheafOfModules.toSheaf (siteModuleRings R)) :=
    inferInstance
  have : HasFiniteColimits (SheafOfModules.{u} (siteModuleRings R)) := inferInstance
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves r
      (SheafOfModules.toSheaf (siteModuleRings R)),
    preservesFiniteColimits_of_reflects_of_preserves r
      (SheafOfModules.toSheaf (siteModuleRings R))⟩

/-- Derived restriction of scalars, using Mathlib's restriction of scalars and its exact
functor localization, rather than an unspecified functor between derived categories.
Source: Stacks Project, Algebraization, Tags 099C and 099I
(blueprint: lem-weil-pbc-flat-ringed-ideal-complete-equivalence). -/
noncomputable def siteDerivedRestrictScalars {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (siteModuleRings B))] :
    DerivedCategory (SheafOfModules.{u} (siteModuleRings B)) ⥤
      DerivedCategory (SheafOfModules.{u} (siteModuleRings R)) :=
  letI := (siteRestrictScalars_exact φ).1
  letI := (siteRestrictScalars_exact φ).2
  (SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapDerivedCategory


private theorem siteDerivedRestrictScalars_reflectsIsomorphisms
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (siteModuleRings B))] :
    (siteDerivedRestrictScalars φ).ReflectsIsomorphisms := by
  let r := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  let := (siteRestrictScalars_exact φ).1
  let := (siteRestrictScalars_exact φ).2
  have : (r ⋙ SheafOfModules.toSheaf (siteModuleRings R)).ReflectsIsomorphisms := by
    change (SheafOfModules.toSheaf (siteModuleRings B)).ReflectsIsomorphisms
    infer_instance
  have : r.ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_comp r (SheafOfModules.toSheaf (siteModuleRings R))
  refine ⟨fun {X Y} f hf ↦ ?_⟩
  apply (DerivedCategory.isIso_iff _ f).mpr
  intro n
  let := hf
  have : IsIso (r.map ((DerivedCategory.homologyFunctor _ n).map f)) :=
    (NatIso.isIso_map_iff (r.mapDerivedCategoryHomologyFunctorIso n) f).mpr
      (inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor _ n).map
        ((siteDerivedRestrictScalars φ).map f))))
  exact isIso_of_reflects_iso ((DerivedCategory.homologyFunctor _ n).map f) r

private theorem locallyDerivedComplete_of_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (siteModuleRings R))]
    [∀ U : C, HasDerivedCategory.{w}
      (ringedSiteModules.{u} (siteModuleRings (R.over U)))]
    {E E' : ringedSiteDerived R} (e : E ≅ E')
    (h : IsLocallyDerivedRingedIdealComplete R I.module I.inclusion E) :
    IsLocallyDerivedRingedIdealComplete R I.module I.inclusion E' := by
  intro U f hf
  exact (h U f hf).of_iso ((derivedInternalHom (J.over U) (R.over U)).mapIso
    ((Iso.refl _).prod ((ringedDerivedRestriction R U).mapIso e.symm)))

private theorem siteDerivedRestrictScalars_complete_iff
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (siteModuleRings B))]
    [∀ U : C, HasDerivedCategory.{w}
      (ringedSiteModules.{u} (siteModuleRings (R.over U)))]
    [∀ U : C, HasDerivedCategory.{w}
      (ringedSiteModules.{u} (siteModuleRings (B.over U)))]
    (M : ringedSiteDerived B) :
    IsLocallyDerivedRingedIdealComplete R I.module I.inclusion
      ((siteDerivedRestrictScalars φ).obj M) ↔
    IsLocallyDerivedRingedIdealComplete B (I.extension φ).module
      (I.extension φ).inclusion M := by
  let r := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  let := (siteRestrictScalars_exact φ).1
  let := (siteRestrictScalars_exact φ).2
  have hIB : ∀ (U : C) (b : B.obj.obj (Opposite.op U)),
      b ∈ (I.extension φ).sections U ↔ ∃ S : Sieve U, S ∈ J U ∧
        ∀ (V : C) (g : V ⟶ U), S g →
          B.obj.map g.op b ∈ Ideal.map (φ.hom.app (Opposite.op V)).hom (I.sections V) := by
    intro U b
    rw [show I.extension φ = Classical.choose (I.existsUnique_extension φ).exists from rfl]
    rw [(Classical.choose_spec (I.existsUnique_extension φ).exists) U b]
    simp only [Ideal.map, Set.image_eq_range]
    rfl
  have h := restrictScalars_locallyDerivedComplete_iff J R B φ I (I.extension φ) hIB M
  let e : (siteDerivedRestrictScalars φ).obj M ≅
      DerivedCategory.Q.obj ((r.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (DerivedCategory.Q.objPreimage M)) :=
    (r.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso M)).symm ≪≫
      r.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage M)
  exact ⟨fun hM ↦ h.mp (locallyDerivedComplete_of_iso R I e hM),
    fun hM ↦ locallyDerivedComplete_of_iso R I e.symm (h.mpr hM)⟩


/-- Restriction of scalars along a flat ring-sheaf map which is an isomorphism modulo a
locally finitely generated ideal induces an equivalence of the locally derived complete
full subcategories. The natural isomorphism in the conclusion identifies the equivalence
with the specified derived restriction functor on the ambient categories.

Source: Stacks Project, Algebraization, Tags 099I and 0999
(blueprint: lem-weil-pbc-flat-ringed-ideal-complete-equivalence).

Proof:
1. Restriction of scalars is exact and conservative, since its underlying additive sheaf
is unchanged. It therefore induces the stated derived functor. By
`lem-weil-pbc-restriction-local-completeness`, it preserves and reflects local completeness.
2. Choose the augmented extended Cech model `K → R[0]` from
`lem-weil-pbc-extended-cech-completion-model`. Flatness makes termwise tensoring with `B`
exact, giving `K_B → B[0]` and `u : K → r K_B`. On every generating slice, localization
commutes with tensor: `(a/f^n) ⊗ b ↦ φ(a)b/φ(f)^n` with inverse
`b/φ(f)^n ↦ (1/f^n) ⊗ b`. Finite products in this model are finite direct sums.
Slice restriction is exact (`lem-weil-pbc-site-restriction-exact`) and preserves quotients;
flatness restricts (`lem-weil-pbc-slice-restriction-flat`). Apply
`lem-weil-pbc-flat-extended-cech-comparison` locally to deduce that `u` is a quasi-isomorphism.
3. Define `F(E)` by the Hom complex from `r K_B` into the functorial K-injective replacement
of a representative of `E`, with action `(b h)(k) = h(bk)`. This action commutes with the
Hom differential and with restrictions. Naturality and two-out-of-three show replacement
maps preserve quasi-isomorphisms; `lem-pur-rhom-well-defined` then makes the Hom maps
quasi-isomorphisms. Thus the construction descends to a functor `D(R) → D(B)`.
4. Precomposition with `u` identifies `r F(E)` with `RHom_R(K,E)`. For complete `E`, the
completion unit identifies this with `E`, naturally. Completeness is reflected by `r`,
so `F` also restricts to the complete subcategories.
5. For complete `M` over `B`, send a homogeneous `m` to the cochain
`k ↦ q(ε_B(k)m)`, zero off degree zero of `k`. This is a chain map because `ε_B d_K = 0`
and `q` is a chain map. It is `B`-linear under the action in step 3, and natural. After
precomposition with `u`, it is exactly the completion unit of `r M`. Hence its restriction
is an isomorphism by step 4; conservativity of restriction makes it an isomorphism over
`B`. These two natural isomorphisms exhibit the equivalence asserted here. -/
theorem flat_ringed_ideal_complete_equivalence
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (I : RingedSiteIdeal R)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (siteModuleRings R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (siteModuleRings B))]
    [∀ U : C, HasDerivedCategory.{w}
      (ringedSiteModules.{u} (siteModuleRings (R.over U)))]
    [∀ U : C, HasDerivedCategory.{w}
      (ringedSiteModules.{u} (siteModuleRings (B.over U)))]
    (hI : SheafOfModules.IsFiniteType.{u, u, u} I.module)
    (hflat : SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (SheafOfModules.unit (siteModuleRings B))))
    (hquot : I.IsQuotientIso φ) :
    ∃ e : ObjectProperty.FullSubcategory
        (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion) ≌
        ObjectProperty.FullSubcategory
          (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion),
      Nonempty (e.functor ⋙
        ObjectProperty.ι (IsLocallyDerivedRingedIdealComplete R I.module I.inclusion) ≅
        ObjectProperty.ι
          (IsLocallyDerivedRingedIdealComplete B (I.extension φ).module (I.extension φ).inclusion) ⋙
          siteDerivedRestrictScalars φ) := by
  classical
  let := (siteRestrictScalars_exact φ).1
  let := (siteRestrictScalars_exact φ).2
  let r : ringedSiteDerived B ⥤ ringedSiteDerived R :=
    (SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).mapDerivedCategory
  let : r.ReflectsIsomorphisms := siteDerivedRestrictScalars_reflectsIsomorphisms φ
  let := hI
  have : Mono I.inclusion := ⟨fun {Z} f g h ↦ by
    ext U x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      (congrArg (fun k : Z ⟶ SheafOfModules.unit (siteModuleRings R) ↦ k.val.app U) h) x⟩
  obtain ⟨hex, hmodel⟩ := exists_ringedExtendedCech_completion_model J R I.module I.inclusion
  obtain ⟨K, ε, hK⟩ := hex
  obtain ⟨_, hnat, _, hunit⟩ := hmodel K ε hK
  obtain ⟨KB, εB, u, hu, hε⟩ := flat_ringed_cech_base_change φ I hI hflat hquot K ε hK
  obtain ⟨T, θ, β, hβ⟩ := ringed_cech_hom_coefficient_action φ K ε KB εB u hu hε
  let P : ObjectProperty (ringedSiteDerived R) :=
    IsLocallyDerivedRingedIdealComplete R I.module I.inclusion
  let PB : ObjectProperty (ringedSiteDerived B) :=
    IsLocallyDerivedRingedIdealComplete B (I.extension φ).module
      (I.extension φ).inclusion
  let F : PB.FullSubcategory ⥤ P.FullSubcategory :=
    P.lift (PB.ι ⋙ r) (fun M ↦
      (siteDerivedRestrictScalars_complete_iff φ I M.obj).mpr M.property)
  have hη (E : P.FullSubcategory) : IsIso (ringedCechCompletionUnit R K ε E.obj) :=
    hunit E.obj E.property
  let G : P.FullSubcategory ⥤ PB.FullSubcategory :=
    PB.lift (P.ι ⋙ T) (fun E ↦ by
      let := hη E
      exact (siteDerivedRestrictScalars_complete_iff φ I (T.obj E.obj)).mp
        (locallyDerivedComplete_of_iso R I
          ((asIso (ringedCechCompletionUnit R K ε E.obj)) ≪≫ (θ.app E.obj).symm)
          E.property))
  have hβiso (M : PB.FullSubcategory) : IsIso (β.app M.obj) := by
    have hc := (siteDerivedRestrictScalars_complete_iff φ I M.obj).mpr M.property
    have : IsIso (ringedCechCompletionUnit R K ε (r.obj M.obj)) := hunit _ hc
    have hfac : r.map (β.app M.obj) ≫ θ.hom.app (r.obj M.obj) =
        ringedCechCompletionUnit R K ε (r.obj M.obj) := hβ M.obj
    have : IsIso (r.map (β.app M.obj) ≫ θ.hom.app (r.obj M.obj)) := by
      rw [hfac]
      infer_instance
    have : IsIso (r.map (β.app M.obj)) := by
      exact IsIso.of_isIso_comp_right _ (θ.hom.app (r.obj M.obj))
    exact isIso_of_reflects_iso (β.app M.obj) r
  let η : 𝟭 PB.FullSubcategory ≅ F ⋙ G :=
    NatIso.ofComponents (fun M ↦ by
      letI := hβiso M
      exact PB.isoMk (asIso (β.app M.obj))) (fun {M N} f ↦ by
        apply ObjectProperty.hom_ext PB
        exact β.naturality f.hom)
  let α : 𝟭 P.FullSubcategory ≅ G ⋙ F :=
    NatIso.ofComponents (fun E ↦ by
      let := hη E
      exact P.isoMk ((asIso (ringedCechCompletionUnit R K ε E.obj)) ≪≫
        (θ.app E.obj).symm)) (fun {E E'} f ↦ by
      apply ObjectProperty.hom_ext P
      change f.hom ≫ (ringedCechCompletionUnit R K ε E'.obj ≫ θ.inv.app E'.obj) =
        (ringedCechCompletionUnit R K ε E.obj ≫ θ.inv.app E.obj) ≫
          r.map (T.map f.hom)
      rw [← Category.assoc, ← hnat E.obj E'.obj f.hom, Category.assoc,
        θ.inv.naturality f.hom]
      simp only [Functor.comp_map, Category.assoc]
      rfl)
  exact ⟨Equivalence.mk F G η α.symm, ⟨Iso.refl _⟩⟩

end CategoryTheory
