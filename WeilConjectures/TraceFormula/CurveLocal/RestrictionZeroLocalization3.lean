/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.ModelVanishing
public import WeilConjectures.TraceFormula.CurveLocal.FrobeniusModel
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsRestrictionBasic
public import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.TraceFormula.CurveLocal.ModelVanishing
import WeilConjectures.TraceFormula.CurveLocal.FrobeniusModel
import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.TraceFormula.CurveLocal.SectionsRestriction
import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsRestrictionBasic

/-! # Localization of the supported restriction on a curve

Source: literature/blueprint/latest/blueprint/sec-trace-formula/
sk-lem-tf-curve-restriction-zero/det-tf-restriction-zero-localization.md,
clauses (i)--(iii) (blueprint: det-tf-restriction-zero-localization).

All objects and arrows below use classical étale sheaves of modules. The two copies
of the strictly local curve are identical copies of `strictLocalization M.y`.
The external product on the complement of both axes is written as the restriction
of the external product on the original curve. This is precisely the restriction of
`N ⊠ Q`, by functoriality and monoidality of inverse image; it avoids choosing a new
external-product comparison or new projections on strict henselizations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.CurveLocalModel

open Scheme

local instance {S T : Scheme.{u}} (f : S ⟶ T)
    [SmoothOfRelativeDimension 1 f] : Smooth f :=
  SmoothOfRelativeDimension.smooth 1 f

variable {k : Type u} [Field k] [IsAlgClosed k] (M : CurveLocalModel k)

local instance : IsClosedImmersion M.y :=
  isClosedImmersion_of_comp_eq_id M.f M.y M.y_comp

/-- Reduction to the ordinary restriction on the punctured diagonal.

Source: clauses (i)--(iii) and their proof in
literature/blueprint/latest/blueprint/sec-trace-formula/sk-lem-tf-curve-restriction-zero/
det-tf-restriction-zero-localization.md
(blueprint: det-tf-restriction-zero-localization).

Proof plan, following the four reviewed DAG steps: (1) the open--closed triangle
and `K_y = 0` identify `K` with extension by zero. Open-immersion internal-Hom
adjunction identifies its Verdier dual with the direct image of its restriction.
Ordinary external Künneth, the open projection formula and extension-by-zero base
change give `P ≅ Rf_*g_!(N ⊠ Q)`; continuity of étale cohomology identifies these
expressions after strict localization. (2) On `T` and on its diagonal `B`, derived
sections are the closed stalk, whose second tensor factor is zero. (3) The supported
restriction is the first component of the canonical morphism of localization
triangles, so its shift commutes with the two connecting maps, which are now
isomorphisms. (4) Restrict the direct-image expression to `T - G`, apply Leray,
and restrict to `B - y`, which avoids both axes. This identifies the third component
with ordinary restriction from `T - (V ∪ G)`. Conjugation by these isomorphisms
and the shift equivalence gives exactly the final equivalence of zero morphisms.
-/
theorem restrictionZeroLocalization
    {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k]
    (X : Over (Spec (.of k))) [QuasiCompact X.hom] [IsSeparated X.hom]
    [SmoothOfRelativeDimension 1 X.hom]
    {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀}
    {Φ : X ⟶ X}
    (hΦ : ProEtale.CondensedRing.IsModelFrobenius Φ f₀ p)
    (m : ℕ) (hm : 1 ≤ m)
    (y : ProEtale.CondensedRing.RationalPoint X)
    (hy : y ≫ ProEtale.CondensedRing.frobeniusIterate Φ m = y)
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (ell : ℕ) [Fact ell.Prime] (hell : (ell : k) ≠ 0)
    (hΛ : ∃ n : ℕ, (ell : Λ) ^ n = 0)
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hctf : DerivedCategory.boundedConstructibleFiniteTor Λ X.left K)
    (hK : IsZero (D((y.left)^*[ModuleCat.{u + 1} Λ]).obj K)) :
    let M := ofModelFrobenius hΦ hm y hy
    let L := (verdierDual Λ M.f).obj (op K)
    let c := strictLocalizationToBase M.y
    let j := M.localizationPuncture.ι
    let Kloc := D((c)^*[ModuleCat.{u + 1} Λ]).obj K
    let Lloc := D((c)^*[ModuleCat.{u + 1} Λ]).obj L
    let N := D((j)^*[ModuleCat.{u + 1} Λ]).obj Lloc
    let Q := D((j)^*[ModuleCat.{u + 1} Λ]).obj Kloc
    let F := M.puncturedExtension L K
    Nonempty (Lloc ≅ (R((j)_*[ModuleCat.{u + 1} Λ])).obj N) ∧
    Nonempty (Kloc ≅ D((j)_!open[ModuleCat.{u + 1} Λ]).obj Q) ∧
    ∀ (P : DerivedCategory.Plus
        (Sheaf M.T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (eP : P.obj ≅ D((M.τ)^*[ModuleCat.{u + 1} Λ]).obj
        (externalProduct (ModuleCat.{u + 1} Λ) M.f M.f L K)),
      Nonempty (P.obj ≅ (R((M.v.openComplement.ι)_*[ModuleCat.{u + 1} Λ])).obj F) ∧
      IsZero ((sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.a).obj P).obj₂ ∧
      IsZero ((sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.yB).obj
        (D+((M.b)^*[ModuleCat.{u + 1} Λ]).obj P)).obj₂ ∧
      let S := (sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.a).obj P
      let B := (sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ) M.yB).obj
        (D+((M.b)^*[ModuleCat.{u + 1} Λ]).obj P)
      let rho := sectionsWithSupportRestriction
        (ModuleCat.{u + 1} Λ) M.b M.a M.yB M.openComplement_yB_le P
      let r := puncturedRestrictionMap
        (ModuleCat.{u + 1} Λ) M.b M.a M.yB M.openComplement_yB_le P
      let iO : M.O.toScheme ⟶ M.v.openComplement.toScheme :=
        M.T.homOfLE inf_le_right
      let FO := D((iO)^*[ModuleCat.{u + 1} Λ]).obj F
      Nonempty (D((M.ψ)^*[ModuleCat.{u + 1} Λ]).obj FO ≅
        M.puncturedDiagonalProduct L K) ∧
      IsIso S.mor₃ ∧ IsIso B.mor₃ ∧
      S.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map rho = r ≫ B.mor₃ ∧
      ∃ (s : S.obj₃ ≅
          (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) M.O.toScheme).obj FO)
        (t : B.obj₃ ≅
          (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ)
            M.yB.openComplement.toScheme).obj
            (D((M.ψ)^*[ModuleCat.{u + 1} Λ]).obj FO)),
        r ≫ t.hom = s.hom ≫ globalSectionsRestriction M.ψ FO ∧
        (rho = 0 ↔ globalSectionsRestriction M.ψ FO = 0)  := by
  dsimp
  let M := ofModelFrobenius hΦ hm y hy
  let L := (verdierDual Λ M.f).obj (op K)
  have hdual := restrictionZeroLocalization_dualComparison M L K
  refine ⟨?_, ?_, ?_⟩
  · simpa [M, L, localizationPuncture] using hdual
  · let c := strictLocalizationToBase M.y
    let j := M.localizationPuncture.ι
    let i := pullback.snd M.y c
    let Kloc := D((c)^*[ModuleCat.{u + 1} Λ]).obj K
    let Q := D((j)^*[ModuleCat.{u + 1} Λ]).obj Kloc
    letI : IsClosedImmersion i := MorphismProperty.pullback_snd _ _ inferInstance
    have hij : Set.range i.base = (Set.range j.base)ᶜ := by
      rw [Scheme.Pullback.range_snd, Scheme.Opens.range_ι]
      change (strictLocalizationToBase M.y).base ⁻¹' Set.range M.y.base =
        ((strictLocalizationToBase M.y).base ⁻¹' (Set.range M.y.base)ᶜ)ᶜ
      rw [Set.preimage_compl, compl_compl]
    have hKyL : IsZero (L((M.y)^*[ModuleCat.{u + 1} Λ]).obj K) := by
      have hKy : IsZero (D((M.y)^*[ModuleCat.{u + 1} Λ]).obj K) := by
        simpa only [ofModelFrobenius_y, M] using hK
      exact hKy.of_iso ((leftDerivedUpperStarIsoMapDerivedCategory _ M.y).app K)
    have hKloc : IsZero (D((i)^*[ModuleCat.{u + 1} Λ]).obj Kloc) := by
      let p := pullback.fst M.y c
      have hpL : IsZero (L((p)^*[ModuleCat.{u + 1} Λ]).obj
          (L((M.y)^*[ModuleCat.{u + 1} Λ]).obj K)) := Functor.map_isZero _ hKyL
      have hpcL : IsZero (L((p ≫ M.y)^*[ModuleCat.{u + 1} Λ]).obj K) :=
        hpL.of_iso ((leftDerivedUpperStarComp _ p M.y).app K)
      have hpcD : IsZero (D((p ≫ M.y)^*[ModuleCat.{u + 1} Λ]).obj K) :=
        hpcL.of_iso ((leftDerivedUpperStarIsoMapDerivedCategory _ (p ≫ M.y)).app K).symm
      have hicD : IsZero (D((i ≫ c)^*[ModuleCat.{u + 1} Λ]).obj K) := by
        simpa only [i, p, c, pullback.condition] using hpcD
      have hicL : IsZero (L((i ≫ c)^*[ModuleCat.{u + 1} Λ]).obj K) :=
        hicD.of_iso ((leftDerivedUpperStarIsoMapDerivedCategory _ (i ≫ c)).app K)
      have hiL : IsZero (L((i)^*[ModuleCat.{u + 1} Λ]).obj
          (L((c)^*[ModuleCat.{u + 1} Λ]).obj K)) :=
        hicL.of_iso ((leftDerivedUpperStarComp _ i c).app K).symm
      exact hiL.of_iso (((leftDerivedUpperStarIsoMapDerivedCategory _ i).app
          (D((c)^*[ModuleCat.{u + 1} Λ]).obj K)).symm ≪≫
        (L((i)^*[ModuleCat.{u + 1} Λ])).mapIso
          ((leftDerivedUpperStarIsoMapDerivedCategory _ c).app K).symm)
    have hRi : IsZero (R((i)_*[ModuleCat.{u + 1} Λ]).obj
        (D((i)^*[ModuleCat.{u + 1} Λ]).obj Kloc)) := Functor.map_isZero _ hKloc
    obtain ⟨w, hw⟩ := exists_distTriang_openClosed (ModuleCat.{u + 1} Λ) j i hij Kloc
    have hi : IsIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} Λ) j).counit.app Kloc) :=
      (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hw).1 hRi
    let e := asIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} Λ) j).counit.app Kloc)
    exact ⟨by simpa [M, c, j, Kloc, Q] using e.symm⟩
  intro P eP
  have hKy : IsZero (D(((ofModelFrobenius hΦ hm y hy).y)^*[ModuleCat.{u + 1} Λ]).obj K) := by
    simpa only [ofModelFrobenius_y] using hK
  have hKyL : IsZero (L(((ofModelFrobenius hΦ hm y hy).y)^*[ModuleCat.{u + 1} Λ]).obj K) :=
    hKy.of_iso ((leftDerivedUpperStarIsoMapDerivedCategory _
      (ofModelFrobenius hΦ hm y hy).y).app K)
  have eP' : P.obj ≅ L(((ofModelFrobenius hΦ hm y hy).τ)^*[ModuleCat.{u + 1} Λ]).obj
      (externalProduct (ModuleCat.{u + 1} Λ) (ofModelFrobenius hΦ hm y hy).f
        (ofModelFrobenius hΦ hm y hy).f
        ((verdierDual Λ (ofModelFrobenius hΦ hm y hy).f).obj (op K)) K) :=
    eP ≪≫ ((leftDerivedUpperStarIsoMapDerivedCategory _
      (ofModelFrobenius hΦ hm y hy).τ).app _).symm
  have hA := isZero_obj₂_a (ofModelFrobenius hΦ hm y hy)
    ((verdierDual Λ (ofModelFrobenius hΦ hm y hy).f).obj (op K)) K hKyL P eP'
  have hB := isZero_obj₂_yB (ofModelFrobenius hΦ hm y hy)
    ((verdierDual Λ (ofModelFrobenius hΦ hm y hy).f).obj (op K)) K hKyL P eP'
  have eP'' : P.obj ≅ D(((ofModelFrobenius hΦ hm y hy).τ)^*[ModuleCat.{u + 1} Λ]).obj
      (externalProduct (ModuleCat.{u + 1} Λ) (ofModelFrobenius hΦ hm y hy).f
        (ofModelFrobenius hΦ hm y hy).f
        ((verdierDual Λ (ofModelFrobenius hΦ hm y hy).f).obj (op K)) K) := by
    simpa using eP
  have hext := restrictionZeroLocalization_externalComparison
    (ofModelFrobenius hΦ hm y hy)
    ((verdierDual Λ (ofModelFrobenius hΦ hm y hy).f).obj (op K)) K P eP''
  refine ⟨?_, hA, hB, ?_⟩
  · simpa [puncturedExtension, puncturedExternal] using hext
  let S := (sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ)
    (ofModelFrobenius hΦ hm y hy).a).obj P
  let B := (sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ)
    (ofModelFrobenius hΦ hm y hy).yB).obj
      (D+(((ofModelFrobenius hΦ hm y hy).b)^*[ModuleCat.{u + 1} Λ]).obj P)
  let rho := sectionsWithSupportRestriction (ModuleCat.{u + 1} Λ)
    (ofModelFrobenius hΦ hm y hy).b (ofModelFrobenius hΦ hm y hy).a
    (ofModelFrobenius hΦ hm y hy).yB
    (ofModelFrobenius hΦ hm y hy).openComplement_yB_le P
  let r := puncturedRestrictionMap (ModuleCat.{u + 1} Λ)
    (ofModelFrobenius hΦ hm y hy).b (ofModelFrobenius hΦ hm y hy).a
    (ofModelFrobenius hΦ hm y hy).yB
    (ofModelFrobenius hΦ hm y hy).openComplement_yB_le P
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hcompat := restrictionZeroLocalization_compatibility
      (ofModelFrobenius hΦ hm y hy)
      ((verdierDual Λ (ofModelFrobenius hΦ hm y hy).f).obj (op K)) K P eP'' hA hB
    exact hcompat.1
  · let S := (sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ)
        (ofModelFrobenius hΦ hm y hy).a).obj P
    exact (S.isZero₂_iff_isIso₃
      (sectionsWithSupportTriangle_obj_distinguished _ _ _)).1 hA
  · let B := (sectionsWithSupportTriangle (ModuleCat.{u + 1} Λ)
        (ofModelFrobenius hΦ hm y hy).yB).obj
        (D+(((ofModelFrobenius hΦ hm y hy).b)^*[ModuleCat.{u + 1} Λ]).obj P)
    exact (B.isZero₂_iff_isIso₃
      (sectionsWithSupportTriangle_obj_distinguished _ _ _)).1 hB
  · exact ((sectionsWithSupportTrianglePullback (ModuleCat.{u + 1} Λ)
      (ofModelFrobenius hΦ hm y hy).b (ofModelFrobenius hΦ hm y hy).a
      (ofModelFrobenius hΦ hm y hy).yB
      (ofModelFrobenius hΦ hm y hy).openComplement_yB_le).app P).comm₃
  · have hcompat := restrictionZeroLocalization_compatibility
      (ofModelFrobenius hΦ hm y hy)
      ((verdierDual Λ (ofModelFrobenius hΦ hm y hy).f).obj (op K)) K P eP'' hA hB
    rcases hcompat.2 with ⟨s, t, hst⟩
    refine ⟨s, t, ?_⟩
    constructor
    · simpa only [puncturedExtension, puncturedExternal, puncturedDiagonalProduct, twoAxesOpen,
        twoAxesInclusion, L, ofModelFrobenius_f] using hst.1
    · simpa only [puncturedExtension, puncturedExternal, puncturedDiagonalProduct, twoAxesOpen,
        twoAxesInclusion, L, ofModelFrobenius_f] using hst.2

end AlgebraicGeometry.Etale.CurveLocalModel
