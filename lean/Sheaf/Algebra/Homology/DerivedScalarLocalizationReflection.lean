/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups N9 and H3
-/
module

public import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.CategoryTheory.ScalarLocalizationSheafExact
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Reflection by derived scalar localization

Source: Stacks Project, Modules on Sites, Tags 03ET, 03CY and 03CZ;
Derived Categories, Tags 015F, 0FND and 09T5; Cohomology on Sites, Tags 06YS and 07A6.
The derived-reflection argument is the agent argument extracted from the returned parent
proof, steps 2–3; it is not a verbatim assertion of Tag 03ET.
(blueprint: lem-sfb-derived-scalar-localization-reflection)
-/

@[expose] public section

set_option autoImplicit false

universe uC vC r wR wS

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false in
-- Fractions first give B-linearity. Local representatives then give S-linearity;
-- module sheafification detects the required local surjectivity of B → S.
private theorem localizationRestriction_full
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [HasSheafify J CommRingCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    (R : Sheaf J CommRingCat.{r})
    (s : (R.obj ⋙ CategoryTheory.forget CommRingCat.{r}).sections) :
    (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map
      (ringedLocalizationRingUnitOfUniverses R s))).Full := by
  classical
  let B := ringedLocalizationRingPresheafOfUniverses R s
  let S := ringedLocalizationRingOfUniverses R s
  let α : B ⟶ S.obj := toSheafify J B
  let φ : R ⟶ S := ringedLocalizationRingUnitOfUniverses R s
  let P := ringedSectionLocalizationPresheafOfUniverses R s
  let U := restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  obtain ⟨e, he⟩ := ringedLocalizationRing_moduleComparisonOfUniverses R s
  let ι : P ⟶ (U.obj (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val :=
    PresheafOfModules.homMk
      (Functor.whiskerRight α (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat))
      (by
        intro V r x
        change R.obj.obj V at r
        change ringedSectionLocalizationCarrierOfUniverses R s V at x
        change (α.app V).hom (r • x) = _
        rw [Algebra.smul_def, (α.app V).hom.map_mul]
        rfl)
  have hι : ι ≫ e.hom.val =
      (PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app P := by
    ext V x
    exact he V x
  have hi : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf _).map ι) := by
    have hη : Presheaf.IsLocallySurjective J
        ((PresheafOfModules.toPresheaf _).map (ι ≫ e.hom.val)) := by
      rw [hι, PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
      exact (J.W_toSheafify P.presheaf).isLocallySurjective
    have : IsIso e.hom.val := inferInstanceAs (IsIso ((SheafOfModules.forget _).map e.hom))
    rw [Functor.map_comp] at hη
    exact (Presheaf.isLocallySurjective_comp_iff J _ _).1 hη
  let : Presheaf.IsLocallySurjective J
      (Functor.whiskerRight α (forget₂ CommRingCat RingCat)) := by
    rw [Presheaf.isLocallySurjective_iff_whisker_forget]
    rw [Presheaf.isLocallySurjective_iff_whisker_forget] at hi
    exact hi
  constructor
  intro M N g
  let fB : (PresheafOfModules.restrictScalars
        (Functor.whiskerRight α (forget₂ CommRingCat RingCat))).obj M.val ⟶
      (PresheafOfModules.restrictScalars
        (Functor.whiskerRight α (forget₂ CommRingCat RingCat))).obj N.val :=
    PresheafOfModules.homMk
      (show ((PresheafOfModules.restrictScalars
          (Functor.whiskerRight α (forget₂ CommRingCat RingCat))).obj M.val).presheaf ⟶
        ((PresheafOfModules.restrictScalars
          (Functor.whiskerRight α (forget₂ CommRingCat RingCat))).obj N.val).presheaf from
        (PresheafOfModules.toPresheaf
          (derivedChangeRingIndependentCoefficients J R).obj).map g.val) (by
      intro V b x
      change ringedSectionLocalizationCarrierOfUniverses R s V at b
      obtain ⟨⟨a, d⟩, hd⟩ := IsLocalization.surj (R := R.obj.obj V)
        (Submonoid.powers (s.val V : R.obj.obj V)) b
      change M.val.obj V at x
      let gV : M.val.obj V →+ N.val.obj V := (g.val.app V).hom.toAddMonoidHom
      change gV ((α.app V).hom b • x) = (α.app V).hom b • gV x
      have hd' : (α.app V).hom b * (φ.hom.app V).hom d =
          (φ.hom.app V).hom a := by
        change (α.app V).hom b *
          (α.app V).hom (algebraMap (R.obj.obj V)
            (ringedSectionLocalizationCarrierOfUniverses R s V) d) = _
        rw [← map_mul, hd]
        rfl
      have hv : IsUnit ((φ.hom.app V).hom d) :=
        (IsLocalization.map_units (ringedSectionLocalizationCarrierOfUniverses R s V) d).map
          (α.app V).hom
      apply hv.smul_left_cancel.mp
      change (φ.hom.app V).hom d • gV ((α.app V).hom b • x) =
        (φ.hom.app V).hom d • ((α.app V).hom b • gV x)
      have hg (r : R.obj.obj V) (y : M.val.obj V) :
          gV ((φ.hom.app V).hom r • y) =
            (φ.hom.app V).hom r • gV y := (g.val.app V).hom.map_smul r y
      rw [← hg, smul_smul, mul_comm _ ((α.app V).hom b), hd', hg,
        smul_smul, mul_comm _ ((α.app V).hom b), hd'])
  let f : M ⟶ N := ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
    (Functor.whiskerRight α (forget₂ CommRingCat RingCat)) N.isSheaf).symm fB⟩
  refine ⟨f, ?_⟩
  have hf := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
    (Functor.whiskerRight α (forget₂ CommRingCat RingCat)) N.isSheaf).apply_symm_apply fB
  apply SheafOfModules.hom_ext
  ext V x
  exact congrArg (fun k ↦ k.app V x) hf

set_option backward.isDefEq.respectTransparency false in
/-- Derived localization is reflective, with the scalar-unit and multiplication normalization
on every complex. The model `m` is the existing universal derived-change-of-rings pair;
its ordinary functor has the prescribed sheafified tensor objects and maps. Thus quantifying
over `m` chooses no new tensor or derived extension. The two module categories may have
independent derived morphism universes.

The ordinary unit and counit formulas use the actual abelian sheafification map on pure
tensors. The natural comparison `c` is the universal counit `m.ε`, now invertible everywhere.
The comparison for restriction is Mathlib's `mapDerivedCategoryFactors`. The two equations
following `c.hom = m.ε` express the derived unit and counit in exactly these identifications.
The equivalence `e` records both the precomposition map and its specified inverse.

Source: Stacks Project, Modules on Sites, Tags 03ET, 03CY, 03CZ; Derived Categories,
Tags 015F, 0FND, 09T5; Cohomology on Sites, Tags 06YS, 07A6.
(blueprint: lem-sfb-derived-scalar-localization-reflection)

Proof:
1. `lem-weil-pbc-scalar-localization-sheaf-exact` gives exactness of actual sheafified
scalar extension, and `lem-pur-sheaf-ring-coefficient-ordinary-adjunction` gives exact
restriction and the ordinary adjunction. Its Hom formula gives the unit `1 ⊗ x` and
multiplication counit `b ⊗ x ↦ b • x` by the balancing relation.
2. `lem-weil-pbc-exact-functor-derived-factorization` and
`lem-weil-pbc-exact-functor-derived-functor` factor both exact termwise functors through
localization, on the full unbounded derived categories. Uniqueness of universal derived
pairs identifies this extension with `m.T`, and its comparison with `m.ε`.
3. Descend the degreewise ordinary unit and counit using
`lem-weil-pbc-localization-universal-property`. The ordinary triangle identities descend
as well, because transformations are determined after precomposition with localization.
4. Compare this adjunction with `lem-pur-sheaf-ring-derived-coefficient-adjunction` on
flat-term K-flat representatives, using the tensor switch if the tensor order is reversed.
The universal comparisons agree. `lem-pc-kflat-resolution` and naturality extend the
unit formula to every complex; essential surjectivity from
`lem-sfb-derived-localization-additive` extends it to every derived object. The unit
fixes the Hom correspondence and hence the counit, proving the two normalization formulas.
5. For an S-module T, the R-linear map j(x) = 1 ⊗ x commutes with the inverse of s,
because multiplication by s is invertible on both sides. It is therefore linear over
the section-localization presheaf, and `lem-pc-sites-module-sheafification-interface`
makes it S-linear. Multiplication composed with j is the identity, and j composed with
multiplication is the identity on pure tensors, hence on their sheafification.
6. These inverse maps commute with differentials. Multiplication is thus invertible on
every complex. The derived counit formula and essential surjectivity show it is an
isomorphism on every object of D(S).
7. The triangle identities and invertibility of the counit give
F(η_A) = ε_(FA)⁻¹, hence UF(η_A) = η_(UFA).
8. Define Ψ(h) = Uε_N ∘ UF(h). Naturality and the right triangle identity give
Ψ(h) ∘ η_A = h. For q : UFA ⟶ UN, step 7 and naturality give
Ψ(q ∘ η_A) = Uε_N ∘ UF(q) ∘ η_(UFA) = q. These are the two inverse equations.
All constructions allow unbounded complexes, the zero ring, and zero or nilpotent s. -/
theorem derivedScalarLocalizationReflection
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [HasSheafify J CommRingCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
    (R : Sheaf J CommRingCat.{r})
    (s : (R.obj ⋙ CategoryTheory.forget CommRingCat.{r}).sections)
    [HasDerivedCategory.{wR}
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J (ringedLocalizationRingOfUniverses R s)))] :
    ∃ (_ : PreservesFiniteLimits (restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
            (ringedLocalizationRingUnitOfUniverses R s))))
      (_ : PreservesFiniteColimits (restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
            (ringedLocalizationRingUnitOfUniverses R s)))),
    ∀ m : DerivedChangeOfRingsCochainModel.{uC, vC, r, wR, wS}
        (ringedLocalizationRingUnitOfUniverses R s),
      PreservesFiniteLimits m.E ∧ PreservesFiniteColimits m.E ∧
      ∃ a : m.E ⊣ restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
            (ringedLocalizationRingUnitOfUniverses R s)),
        (∀ (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))
          (V : Cᵒᵖ) (x : M.val.obj V),
          ((a.unit.app M ≫ (restrictScalars
              ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                (ringedLocalizationRingUnitOfUniverses R s))).map
                  (eqToHom (m.obj_eq M))).val.app V) x =
            (CategoryTheory.toSheafify J
              (changeOfRingsPresheaf
                (ringedLocalizationRingUnitOfUniverses R s) M).presheaf).app V
              ((1 : (ringedLocalizationRingOfUniverses R s).obj.obj V) ⊗ₜ[R.obj.obj V,
                ((ringedLocalizationRingUnitOfUniverses R s).hom.app V).hom] x)) ∧
        (∀ (N : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J
              (ringedLocalizationRingOfUniverses R s)))
          (V : Cᵒᵖ) (b : (ringedLocalizationRingOfUniverses R s).obj.obj V)
          (x : N.val.obj V),
          ((eqToHom (m.obj_eq ((restrictScalars
                ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                  (ringedLocalizationRingUnitOfUniverses R s))).obj N)).symm ≫
              a.counit.app N).val.app V)
            ((CategoryTheory.toSheafify J
                (changeOfRingsPresheaf (ringedLocalizationRingUnitOfUniverses R s)
                  ((restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      (ringedLocalizationRingUnitOfUniverses R s))).obj N)).presheaf).app V
              (b ⊗ₜ[R.obj.obj V,
                ((ringedLocalizationRingUnitOfUniverses R s).hom.app V).hom] x)) = b • x) ∧
        ∃ (d : m.T ⊣ (restrictScalars
              ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                (ringedLocalizationRingUnitOfUniverses R s))).mapDerivedCategory)
          (c : DerivedCategory.Q ⋙ m.T ≅
            m.E.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q),
          c.hom = m.ε ∧
          (∀ M : CochainComplex
              (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) ℤ,
            d.unit.app (DerivedCategory.Q.obj M) ≫
                (restrictScalars
                  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                    (ringedLocalizationRingUnitOfUniverses R s))).mapDerivedCategory.map
                      (c.hom.app M) ≫
                (restrictScalars
                  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                    (ringedLocalizationRingUnitOfUniverses R s))).mapDerivedCategoryFactors.hom.app
                      ((m.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) =
              DerivedCategory.Q.map ((a.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app M)) ∧
          (∀ N : CochainComplex (ringedSiteModules.{r}
              (derivedChangeRingIndependentCoefficients J
                (ringedLocalizationRingOfUniverses R s))) ℤ,
            d.counit.app (DerivedCategory.Q.obj N) =
              m.T.map ((restrictScalars
                  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                    (ringedLocalizationRingUnitOfUniverses R s))).mapDerivedCategoryFactors.hom.app
                      N) ≫
                c.hom.app (((restrictScalars
                  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                    (ringedLocalizationRingUnitOfUniverses R s))).mapHomologicalComplex
                      (ComplexShape.up ℤ)).obj N) ≫
                DerivedCategory.Q.map
                  ((a.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app N)) ∧
          (∀ N : DerivedCategory (ringedSiteModules.{r}
              (derivedChangeRingIndependentCoefficients J
                (ringedLocalizationRingOfUniverses R s))), IsIso (d.counit.app N)) ∧
          (∀ (A : DerivedCategory
              (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)))
            (N : DerivedCategory (ringedSiteModules.{r}
              (derivedChangeRingIndependentCoefficients J
                (ringedLocalizationRingOfUniverses R s)))),
            ∃ e : ((restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      (ringedLocalizationRingUnitOfUniverses R s))).mapDerivedCategory.obj
                        (m.T.obj A) ⟶
                    (restrictScalars
                      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                        (ringedLocalizationRingUnitOfUniverses R s))).mapDerivedCategory.obj N) ≃
                  (A ⟶ (restrictScalars
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                      (ringedLocalizationRingUnitOfUniverses R s))).mapDerivedCategory.obj N),
              (∀ q, e q = d.unit.app A ≫ q) ∧
              (∀ h, e.symm h =
                (restrictScalars
                  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                    (ringedLocalizationRingUnitOfUniverses R s))).mapDerivedCategory.map
                      (m.T.map h) ≫
                (restrictScalars
                  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                    (ringedLocalizationRingUnitOfUniverses R s))).mapDerivedCategory.map
                      (d.counit.app N))) ∧
          (∀ A : DerivedCategory
              (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)),
            (restrictScalars
                ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                  (ringedLocalizationRingUnitOfUniverses R s))).mapDerivedCategory.map
                    (m.T.map (d.unit.app A)) =
              d.unit.app ((restrictScalars
                ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map
                  (ringedLocalizationRingUnitOfUniverses R s))).mapDerivedCategory.obj
                    (m.T.obj A))) := by
  classical
  let φ := ringedLocalizationRingUnitOfUniverses R s
  let U := restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  obtain ⟨hUl, hUc, ha⟩ := sheafRingCoefficientOrdinaryAdjunction φ
  have := hUl
  have := hUc
  refine ⟨hUl, hUc, ?_⟩
  intro m
  obtain ⟨E, hE, hmE, _, _, _, htransfer⟩ := scalarLocalization_sheaf_exact J R s
  let i : m.E ≅ E := NatIso.ofComponents
    (fun M ↦ eqToIso (m.obj_eq M) ≪≫ (eqToIso (hE M)).symm) (by
      intro M N f
      dsimp
      rw [m.map_eq, hmE]
      simp
      rfl)
  obtain ⟨_, hEl, hEc⟩ := htransfer m.E ⟨i⟩
  have := hEl
  have := hEc
  obtain ⟨a, ha⟩ := ha m.E m.obj_eq m.map_eq
  have hunit (M) (V) (x) := ha M (changeOfRings φ M) (𝟙 _) V x
  have hu : ∀ (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R))
      (V : Cᵒᵖ) (x : M.val.obj V),
      ((a.unit.app M ≫ U.map (eqToHom (m.obj_eq M))).val.app V) x =
        (CategoryTheory.toSheafify J (changeOfRingsPresheaf φ M).presheaf).app V
          ((1 : (ringedLocalizationRingOfUniverses R s).obj.obj V) ⊗ₜ[R.obj.obj V,
            (φ.hom.app V).hom] x) := by
    intro M V x
    simpa [Adjunction.homEquiv_unit, U] using hunit M V x
  refine ⟨hEl, hEc, a, hu, ?_, ?_⟩
  · intro N V b x
    let η := (CategoryTheory.toSheafify J
      (changeOfRingsPresheaf φ (U.obj N)).presheaf).app V
    let f := eqToHom (m.obj_eq (U.obj N)).symm ≫ a.counit.app N
    have hc := ha (U.obj N) N f V x
    have hf : eqToHom (m.obj_eq (U.obj N)) ≫ f = a.counit.app N := by
      dsimp [f]
      simp
    have hcid : a.homEquiv (U.obj N) N (a.counit.app N) = 𝟙 _ := by
      rw [← a.homEquiv_symm_id, Equiv.apply_symm_apply]
    rw [hf, hcid] at hc
    change x = f.val.app V (η ((1 : (ringedLocalizationRingOfUniverses R s).obj.obj V)
      ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x)) at hc
    have ht := ModuleCat.ExtendScalars.smul_tmul
      (M := (U.obj N).val.obj V) (φ.hom.app V).hom b 1 x
    simp only [mul_one] at ht
    change f.val.app V (η _) = _
    rw [← ht]
    let η' := (PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
      (changeOfRingsPresheaf φ (U.obj N))
    change f.val.app V (η'.app V (b • _)) = _
    rw [map_smul, map_smul]
    exact congrArg (fun y : N.val.obj V ↦ b • y) hc.symm
  -- Descending the exact ordinary adjunction directly gives the required normalization.
  · have hcomp := m.E.exactFunctor_derivedFunctor m.E.mapDerivedCategory
      m.E.mapDerivedCategoryFactors
    have hε : ∀ M, IsIso (m.ε.app M) :=
      hcomp.2.2.2.1 m.T m.ε m.universal
    have : ∀ M, IsIso (m.ε.app M) := hε
    have : IsIso m.ε := NatIso.isIso_of_isIso_app _
    let Ud := U.mapDerivedCategory.{wS, wR}
    let u := U.mapDerivedCategoryFactors.{wS, wR}
    let c := asIso m.ε
    let : CatCommSq (m.E.mapHomologicalComplex (.up ℤ))
        DerivedCategory.Q DerivedCategory.Q m.T := ⟨c.symm⟩
    let : CatCommSq (U.mapHomologicalComplex (.up ℤ))
        DerivedCategory.Q DerivedCategory.Q Ud :=
      ⟨u.symm⟩
    let ac := a.mapHomologicalComplex (.up ℤ)
    let d := ac.localization DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
      DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ)) m.T Ud
    have hdu (M) : d.unit.app (DerivedCategory.Q.obj M) ≫
        Ud.map (c.hom.app M) ≫
        u.hom.app ((m.E.mapHomologicalComplex (.up ℤ)).obj M) =
        DerivedCategory.Q.map (ac.unit.app M) := by
      dsimp [d]
      rw [Adjunction.localization_unit_app]
      simp only [Category.assoc]
      change DerivedCategory.Q.map (ac.unit.app M) ≫
        u.inv.app ((m.E.mapHomologicalComplex (.up ℤ)).obj M) ≫
        Ud.map (c.inv.app M) ≫ Ud.map (c.hom.app M) ≫
        u.hom.app ((m.E.mapHomologicalComplex (.up ℤ)).obj M) = _
      rw [← Ud.map_comp_assoc, Iso.inv_hom_id_app]
      erw [Ud.map_id]
      rw [Category.id_comp, Iso.inv_hom_id_app]
      exact Category.comp_id _
    have hdc (N) : d.counit.app (DerivedCategory.Q.obj N) =
        m.T.map (u.hom.app N) ≫
        c.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj N) ≫
        DerivedCategory.Q.map (ac.counit.app N) := by
      exact ac.localization_counit_app _ _ _ _ _ _ N
    have hfull : U.Full := localizationRestriction_full R s
    have := hfull
    have hfaithful : U.Faithful := by
      constructor
      intro M N f g h
      apply SheafOfModules.hom_ext
      ext V x
      exact congrArg (fun k ↦ k.val.app V x) h
    have := hfaithful
    have hdi : ∀ N, IsIso (d.counit.app N) := by
      intro N
      let e := DerivedCategory.Q.objObjPreimageIso N
      have hi : IsIso (d.counit.app (DerivedCategory.Q.obj
          (DerivedCategory.Q.objPreimage N))) := by
        rw [hdc]
        have : IsIso (ac.counit.app (DerivedCategory.Q.objPreimage N)) := by
          have : ∀ n, IsIso ((ac.counit.app (DerivedCategory.Q.objPreimage N)).f n) :=
            fun n ↦ show IsIso (a.counit.app ((DerivedCategory.Q.objPreimage N).X n)) by
              infer_instance
          exact HomologicalComplex.Hom.isIso_of_components _
        infer_instance
      have hn : (Ud ⋙ m.T).map e.hom ≫ d.counit.app N =
          d.counit.app (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage N)) ≫
            e.hom := d.counit.naturality e.hom
      have heq : d.counit.app N =
          (Ud ⋙ m.T).map e.inv ≫
            d.counit.app (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage N)) ≫
              e.hom := by
        rw [← hn, ← Functor.map_comp_assoc, e.inv_hom_id,
          (Ud ⋙ m.T).map_id, Category.id_comp]
      have := hi
      rw [heq]
      infer_instance
    have heta (A) : Ud.map (m.T.map (d.unit.app A)) =
        d.unit.app (Ud.obj (m.T.obj A)) := by
      have := hdi (m.T.obj A)
      apply (cancel_mono (Ud.map (d.counit.app (m.T.obj A)))).1
      calc
        _ = Ud.map
            (m.T.map (d.unit.app A) ≫ d.counit.app (m.T.obj A)) :=
          (Ud.map_comp _ _).symm
        _ = Ud.map (𝟙 (m.T.obj A)) :=
          congrArg (fun f ↦ Ud.map f) (d.left_triangle_components A)
        _ = 𝟙 _ := Ud.map_id _
        _ = _ := (d.right_triangle_components (m.T.obj A)).symm
    refine ⟨d, c, rfl, hdu, hdc, hdi, ?_, heta⟩
    intro A N
    refine ⟨{ toFun := fun q ↦ d.unit.app A ≫ q
              invFun := fun h ↦ Ud.map (m.T.map h) ≫
                Ud.map (d.counit.app N)
              left_inv := ?_
              right_inv := ?_ }, fun _ ↦ rfl, fun _ ↦ rfl⟩
    · intro q
      dsimp
      rw [Functor.map_comp, Functor.map_comp, heta]
      change (d.unit.app _ ≫ (m.T ⋙ Ud).map q) ≫ _ = q
      rw [← d.unit.naturality, Category.assoc, d.right_triangle_components]
      exact Category.comp_id q
    · intro h
      dsimp
      change d.unit.app A ≫ (m.T ⋙ Ud).map h ≫ _ = h
      rw [← Category.assoc, ← d.unit.naturality, Category.assoc, d.right_triangle_components]
      exact Category.comp_id h

end SheafOfModules
