/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Projective.ProjectiveLineRestriction
import WeilConjectures.AlgebraicGeometry.Native.NativeProjectiveLineCohomology
import WeilConjectures.AlgebraicGeometry.Native.NativeProjectiveLineOpenRestriction
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineGeometricBaseChange
import WeilConjectures.SixFunctors.Constructible.ConstructibleSplitEndomorphism
import WeilConjectures.WeilSheaf.Operations

/-! # Projective-line cohomology outside the top degree

Source: latest blueprint, thm-amb-p1-decomposition.proof.md, the geometric-fibre
calculation and the coefficient passage in lem-pur-b3-weil-projective-decomposition.
(blueprint: lem-pur-h3-projective-off-top).
-/

@[expose] public section

universe u
open CategoryTheory Limits Endofunctor
open CategoryTheory.Endofunctor

namespace AlgebraicGeometry.WeilComplex

private theorem section_restriction_unit
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (I : D ⥤ C) (e : L ⋙ I ≅ 𝟭 C) (K : C) :
    adj.unit.app K ≫ e.inv.app ((L ⋙ R).obj K) ≫
      I.map (adj.counit.app (L.obj K)) ≫ e.hom.app K = 𝟙 K := by
  have h := e.inv.naturality (adj.unit.app K)
  dsimp only [Functor.id_map, Functor.comp_map] at h
  rw [← Category.assoc, ← Category.assoc, h]
  have ht : L.map (adj.unit.app K) ≫ adj.counit.app (L.obj K) = 𝟙 _ :=
    adj.left_triangle_components K
  simp only [Category.assoc, ← I.map_comp]
  rw [ht, I.map_id]
  simp

private theorem projectiveLine_unit_restriction
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) :
    (upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l)
        (ProjectiveLine X ↘ X)).unit.app K ≫
      (projectiveLineRestriction X).app K = 𝟙 K := by
  let q := ProjectiveLine X ↘ X
  let i := ProjectiveLine.infinity X
  let : i.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change (i ≫ q) ≫ (X ↘ Spec (CommRingCat.of k₀)) = _
    rw [ProjectiveLine.infinity_over, Category.id_comp]⟩
  let L := upperStar (k₀ := k₀) (l := l) q
  let R := derivedLowerStar (k₀ := k₀) (l := l) q
  let I := upperStar (k₀ := k₀) (l := l) i
  let e : L ⋙ I ≅ 𝟭 _ :=
    (upperStarCompIso i q).symm ≪≫ upperStarCongrIso ProjectiveLine.infinity_over ≪≫
      upperStarIdIso X
  dsimp only [projectiveLineRestriction, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app]
  dsimp only [Functor.comp_obj]
  simp only [Category.id_comp]
  change _ ≫ (e.inv.app ((L ⋙ R).obj K) ≫
    I.map ((upperStarDerivedLowerStarAdjunction q).counit.app (L.obj K)) ≫
      e.hom.app K) = _
  simpa only [Category.assoc] using
    section_restriction_unit (upperStarDerivedLowerStarAdjunction q) I e K

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ}
  [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]

set_option linter.unusedSectionVars false in
set_option maxHeartbeats 300000 in
-- Explicit derived comparisons on an affine cover require additional elaboration.
/-- The unit computes degree zero, and the other non-top cohomology groups vanish.
(blueprint: lem-pur-h3-projective-off-top).

Source: latest blueprint, thm-amb-p1-decomposition.proof.md, projective-line calculation
and its extension to pulled-back constructible coefficients.

Proof: forget Frobenius and restrict to the affine open cover of the geometric base.
Exact native/condensed comparison identifies the underlying ordinary derived image.
The constant projective-line decomposition and the proper projection formula give a
sum of M[0] and its flat signed Tate tensor shifted by -2. Hence H⁰ is isomorphic to M,
and all positive cohomology except H² vanishes. Open base change identifies these
local calculations with the restricted global cohomology objects.

For the actual degree-zero unit map, restriction at infinity is a retraction by the
adjunction triangle identity. After cohomology, forgetting and open restriction this
remains a split monomorphism. Identify both its ends with the same constructible sheaf
using the local calculation and H⁰(M[0]) ≅ M. A split endomorphism of a constructible
adic sheaf on the noetherian affine base is invertible. Open restrictions detect
isomorphisms and zero objects, and exact conservative forgetting reflects them in
the Weil heart. No normalization of a geometric derived splitting is required. -/
theorem projectiveLine_cohomology_off_top (M : WeilSheaf k₀ l X) :
    IsIso ((homologySheaf 0).map
      ((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l)
        (ProjectiveLine X ↘ X)).unit.app (WeilSheaf.toComplex.obj M))) ∧
    ∀ i : ℤ, 0 < i → i ≠ 2 →
    IsZero ((homologySheaf i).obj
        ((projectiveLineCohomology (k₀ := k₀) (l := l) X).obj
          (WeilSheaf.toComplex.obj M))) := by
  classical
  let k := AlgebraicClosure k₀
  let Z := (X ↘ Spec (.of k₀)).geometricFiber
  let : Z.Over (Spec (.of k)) :=
    ⟨(X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure⟩
  have : LocallyOfFiniteType (Z ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType
      (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure)
  have : Fact (ringChar k).Prime := ⟨by
    rw [← Algebra.ringChar_eq k₀ k]
    exact CharP.char_is_prime k₀ _⟩
  have : Fact (ringChar k ≠ l) := ⟨by
    rw [← Algebra.ringChar_eq k₀ k]
    exact Fact.out⟩
  let q := ProjectiveLine X ↘ X
  let qb := Scheme.Hom.geometricFiberMap q (comp_over q (Spec (.of k₀)))
  let K := WeilSheaf.toComplex.obj M
  let G := (projectiveLineCohomology (k₀ := k₀) (l := l) X).obj K
  let F : WeilSheaf k₀ l X ⥤ ProEtale.AdicSheaf l Z :=
    (WeilSheaf.objectProperty k₀ l X).ι ⋙ IsoAlgebra.forget _
  have : F.ReflectsIsomorphisms := by
    change ((WeilSheaf.objectProperty k₀ l X).ι ⋙
      (IsoAlgebra.ι _ ⋙ Algebra.forget _)).ReflectsIsomorphisms
    infer_instance
  let C := Z.affineCover
  let η := (upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) q).unit.app K
  have hη : IsSplitMono η :=
    ⟨⟨⟨(projectiveLineRestriction X).app K, projectiveLine_unit_restriction X K⟩⟩⟩
  let eK : forget.obj K ≅ (DerivedCategory.singleFunctor _ 0).obj M.obj.carrier :=
    ((IsoAlgebra.forget _).mapDerivedCategorySingleFunctor 0).app M.obj
  let eG : forget.obj G ≅ (ProEtale.adicLowerStar l qb).rightDerivedFunctor.obj
      ((ProEtale.adicUpperStar l qb).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj M.obj.carrier)) :=
    (nonempty_derivedLowerStar_comp_forget_iso (k₀ := k₀) (l := l) q).some.app
        ((upperStar (k₀ := k₀) (l := l) q).obj K) ≪≫
      (ProEtale.adicLowerStar l qb).rightDerivedFunctor.mapIso
        ((upperStarCompForgetIso (k₀ := k₀) (l := l) q).app K ≪≫
          (ProEtale.adicUpperStar l qb).mapDerivedCategory.mapIso eK)
  let eH (n : ℤ) : F.obj ((homologySheaf n).obj G) ≅
      (DerivedCategory.homologyFunctor _ n).obj
        ((ProEtale.adicLowerStar l qb).rightDerivedFunctor.obj
          ((ProEtale.adicUpperStar l qb).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor _ 0).obj M.obj.carrier))) :=
    ((IsoAlgebra.forget _).mapDerivedCategoryHomologyFunctorIso n).app G.obj ≪≫
      (DerivedCategory.homologyFunctor _ n).mapIso eG
  have hlocal (a : C.I₀) :
      Nonempty ((ProEtale.adicUpperStar l (C.f a)).obj
          (F.obj ((homologySheaf 0).obj G)) ≅
        (ProEtale.adicUpperStar l (C.f a)).obj M.obj.carrier) ∧
      ∀ i : ℤ, 0 < i → i ≠ 2 → IsZero ((ProEtale.adicUpperStar l (C.f a)).obj
        (F.obj ((homologySheaf i).obj G))) := by
    let U := C.X a
    let j := C.f a
    let : U.Over (Spec (.of k)) := ⟨j ≫ (Z ↘ Spec (.of k))⟩
    have : LocallyOfFiniteType (U ↘ Spec (.of k)) :=
      inferInstanceAs (LocallyOfFiniteType (j ≫ (Z ↘ Spec (.of k))))
    have : IsSeparated (U ↘ Spec (.of k)) := inferInstance
    have : QuasiCompact (U ↘ Spec (.of k)) := inferInstance
    obtain ⟨b, hsq⟩ := exists_projectiveLine_geometric_baseChange k₀ X j
    have : IsOpenImmersion b :=
      MorphismProperty.of_isPullback hsq inferInstance
    let MU := (ProEtale.adicUpperStar l j).obj M.obj.carrier
    have hMU : ProEtale.IsAdicConstructibleSheaf MU :=
      ProEtale.IsAdicConstructibleSheaf.upperStar j M.isAdicConstructibleSheaf_carrier
    have hu : IsUnit (l : Γ(U, ⊤)) := by
      have hlk : IsUnit (l : k) := by
        apply isUnit_iff_ne_zero.mpr
        exact CharP.cast_ne_zero_of_ne_of_prime (R := k) (p := ringChar k₀)
          (Fact.out : l.Prime) (Fact.out : ringChar k₀ ≠ l)
      let ρ : CommRingCat.of k ⟶ CommRingCat.of Γ(U, ⊤) :=
        (Scheme.ΓSpecIso (.of k)).inv ≫ (U ↘ Spec (.of k)).appTop
      have hmap : ρ.hom (l : k) = (l : Γ(U, ⊤)) := map_natCast ρ.hom l
      rw [← hmap]
      exact hlk.map ρ.hom
    obtain ⟨⟨e0⟩, hv⟩ := ProEtale.native_projectiveLine_cohomology k₀ k l
      (Ne.symm Fact.out) U hu MU hMU
    let e (n : ℤ) := (ProEtale.adicUpperStar l j).mapIso (eH n) ≪≫
      (ProEtale.native_projectiveLine_open_cohomology_comparison l qb j b hsq
        M.obj.carrier n).some
    exact ⟨⟨e 0 ≪≫ e0⟩, fun i hi hi2 ↦ (hv i hi hi2).of_iso (e i)⟩
  constructor
  · let f := F.map ((homologySheaf 0).map η)
    have : IsIso f := by
      apply ProEtale.isIso_of_isIso_adicUpperStar l C.f
        (Scheme.zariskiPrecoverage_le_proetalePrecoverage _ C.mem₀) f
      intro a
      let j := C.f a
      let MU := (ProEtale.adicUpperStar l j).obj M.obj.carrier
      have : IsLocallyNoetherian (C.X a) :=
        LocallyOfFiniteType.isLocallyNoetherian
          (j ≫ (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure)
      obtain ⟨et⟩ := (hlocal a).1
      let es := (ProEtale.adicUpperStar l j).mapIso
        (F.mapIso (WeilSheaf.toComplexCompHomologySheafIso.app M))
      let g : MU ⟶ MU := es.inv ≫ (ProEtale.adicUpperStar l j).map f ≫ et.hom
      have : IsSplitMono g := inferInstance
      have : IsIso g := WeilConjectures.constructible_splitEndo_isIso
        (ProEtale.IsAdicConstructibleSheaf.upperStar j M.isAdicConstructibleSheaf_carrier) g
      have heq : (ProEtale.adicUpperStar l j).map f = es.hom ≫ g ≫ et.inv := by
        simp only [g, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
          Category.comp_id]
      rw [heq]
      infer_instance
    exact isIso_of_reflects_iso ((homologySheaf 0).map η) F
  · intro i hi hi2
    apply WeilSheaf.isZero_iff_isZero_carrier.mpr
    exact ProEtale.isZero_of_isZero_adicUpperStar l C.f
      (Scheme.zariskiPrecoverage_le_proetalePrecoverage _ C.mem₀)
      (fun a ↦ (hlocal a).2 i hi hi2)

end AlgebraicGeometry.WeilComplex
