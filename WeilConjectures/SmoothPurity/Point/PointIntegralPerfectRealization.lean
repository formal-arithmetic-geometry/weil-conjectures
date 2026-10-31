/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint

import WeilConjectures.SixFunctors.PointDerivedHom.PointExactExtensionSections
import all WeilConjectures.SixFunctors.Supporting.PointSectionsReconstruction

/-! # Completed perfect realization at a geometric point

Source: the integral argument, steps 2–3 and 6–7, of
`lem-weil-point-fibre-equivalence`.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Completed constant realization embeds bounded finitely generated complete complexes
as integral constructible complexes, and is left adjoint to the specified sections functor.
Source: Stacks, Modules on Sites, Tags 03EI and 093M; Bhatt–Scholze, Propositions
6.6.11 and 6.8.11(3); the point-fibre proof, steps 2–3 and 6–7.
(blueprint: lem-weil-point-integral-perfect-realization).

Proof: write A = O_E and B for its completed constant algebra sheaf. Realize an
A-module M by B tensor over the constant A sheaf with the constant M sheaf.
The balanced formula b tensor m ↦ b times t(m) extends by sheafification and gives
an adjunction with sections restricted along the actual constant-to-completion map.
The ring B is flat over constant A, so realization and sections are exact and the
adjunction descends termwise to derived categories. Its unit on finite free modules
is the constant-section map A ≅ Gamma(B). Exactness and finite presentations make
its unit invertible on every finitely generated A-module, hence on every complex
with finitely generated cohomology. Over the coefficient DVR, finite modules have
length-one finite projective resolutions; bounded cohomology assembly therefore
makes every source complex perfect. Its completed realization is derived complete
and has uniformly bounded constructible finite reductions, by the completed
constant reduction theorem and the stratified-perfect characterization. Thus the
adjunction restricts to the two stated full subcategories with the same unit.
This asserts only the fully faithful realization; it does not assert the counit
is invertible on arbitrary integral constructible complexes. -/
theorem pointIntegralPerfectRealization
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ L : (DerivedCategory.pointFgComplete
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
        (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)})).FullSubcategory ⥤
        sfIntegralConstructibleCategory l E (Spec (.of D.k)),
      ∃ a : L ⊣ pointIntegralFibre D l hl E, ∀ M, IsIso (a.unit.app M) := by
  classical
  obtain ⟨L, hobj, hmap, hLl, hLc, hRl, hRc, hscalar, adj, hex, _⟩ :=
    PointDerivedHom.point_exact_extension_sections.{u, u} D l hl E 1 (by decide) true
  let := hLl
  let := hLc
  let := hRl
  let := hRc
  let := adj.left_adjoint_additive
  have hrec := pointSectionsReconstruction D l hl E 1 (by decide) true L hobj
    (fun _ _ f ↦ hmap f) adj hex hscalar
  -- Compare the standard module-derived category with its smaller model.
  let R := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)
  let e := ShrinkHoms.equivalence.{u + 1}
    (@DerivedCategory (ModuleCat.{u + 1} R) _ _ (HasDerivedCategory.standard _))
  let P := sfIntegralConstructible l E (Spec (.of D.k))
  let Q := DerivedCategory.pointFgComplete R
    (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)})
  have hforward (M : Q.FullSubcategory) :
      IsIso (adj.mapDerivedCategoryAdjunction.unit.app (e.inverse.obj M.obj)) ∧
        P (L.mapDerivedCategory.obj (e.inverse.obj M.obj)) := by
    obtain ⟨⟨s, hs⟩, hfin, _⟩ := M.property
    have eH (i : ℤ) :
        (DerivedCategory.homologyFunctor.{u + 2} (ModuleCat.{u + 1} R) i).obj
          (e.inverse.obj M.obj) ≅
        (moduleHomologySmall R i).obj M.obj :=
      (moduleHomologyShrinkIso R i).app (e.inverse.obj M.obj) ≪≫
        (moduleHomologySmall R i).mapIso (e.counitIso.app M.obj)
    have h := hrec.1 (e.inverse.obj M.obj) ⟨s,
      fun i hi ↦ (hs i hi).of_iso (eH i), fun i ↦
        (Module.Finite.equiv_iff (eH i).toLinearEquiv).mpr (hfin i)⟩
    exact ⟨h.1, h.2.1⟩
  let S := pointIntegralSections l E D.k
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} R) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  -- Both derived sections functors factor the same functor on complexes.
  let σ : (PointDerivedHom.sections.{u, u} D.k
      (PointDerivedHom.coefficientSheaf.{u, u} D.k l E 1 true)
      (PointDerivedHom.coefficientMap.{u, u} D.k l E 1 true)).mapDerivedCategory ⋙
        e.functor ≅ S.mapDerivedCategory := by
    let G := S.mapDerivedCategory
    let H := S.mapHomologicalComplex (.up ℤ) ⋙ (moduleQSmall R)
    let W := HomologicalComplex.quasiIso (scalarReductionSource l E (Spec (.of D.k)))
      (.up ℤ)
    let F := (PointDerivedHom.sections.{u, u} D.k
      (PointDerivedHom.coefficientSheaf.{u, u} D.k l E 1 true)
      (PointDerivedHom.coefficientMap.{u, u} D.k l E 1 true)).mapDerivedCategory ⋙ e.functor
    letI : Localization.Lifting DerivedCategory.Q W H F :=
      ⟨(Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (show DerivedCategory.Q ⋙
            (PointDerivedHom.sections.{u, u} D.k
              (PointDerivedHom.coefficientSheaf.{u, u} D.k l E 1 true)
              (PointDerivedHom.coefficientMap.{u, u} D.k l E 1 true)).mapDerivedCategory ≅
            S.mapHomologicalComplex (.up ℤ) ⋙ _ from
              Functor.mapDerivedCategoryFactors _) e.functor ≪≫
          Functor.associator _ _ _⟩
    letI : Localization.Lifting DerivedCategory.Q W H G :=
      ⟨S.mapDerivedCategoryFactors⟩
    exact Localization.liftNatIso DerivedCategory.Q W H H F G (Iso.refl _)
  let τ : (PointDerivedHom.sections.{u, u} D.k
      (PointDerivedHom.coefficientSheaf.{u, u} D.k l E 1 true)
      (PointDerivedHom.coefficientMap.{u, u} D.k l E 1 true)).mapDerivedCategory ≅
        S.mapDerivedCategory ⋙ e.inverse :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ e.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight σ e.inverse
  -- Restrict the ambient adjunction, retaining its specified right adjoint.
  let F := P.lift ((Q.ι ⋙ e.inverse) ⋙ L.mapDerivedCategory)
    (fun M ↦ (hforward M).2)
  let a : F ⊣ pointIntegralFibre D l hl E :=
    adj.mapDerivedCategoryAdjunction.restrictFullyFaithful
      (Q.fullyFaithfulι.comp e.fullyFaithfulInverse) P.fullyFaithfulι
      (Iso.refl _) (Functor.isoWhiskerLeft P.ι τ ≪≫ (Functor.associator _ _ _).symm)
  refine ⟨F, a, fun M ↦ ?_⟩
  rw [← isIso_iff_of_reflects_iso _ (Q.ι ⋙ e.inverse)]
  change IsIso ((Q.ι ⋙ e.inverse).map (a.unit.app M))
  dsimp only [a]
  rw [Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [Iso.refl_hom, NatTrans.id_app, Functor.comp_obj, ObjectProperty.ι_obj]
  have := (hforward M).1
  infer_instance

end WeilConjectures
