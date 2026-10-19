/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.PurityRankOneSectionData
import WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
/-!
# Higher cohomology on the two geometric lines

Source: Milne, Lectures on Etale Cohomology, Section 15; blueprint sk-prop-cd-affine
and sk-prop-a1-kummer, Degrees 0 and 1.
(blueprint: lem-pur-finite-line-high-cohomology).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.RankOne
private def objectCohomEquiv (A : Type (u + 1)) [CommRing A]
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ) :
    ((sections X.smallEtaleTopology A (Scheme.Etale.mk j)).rightDerived q).obj F ≃+
      Sheaf.H ((Etale.openImmersionRestriction AddCommGrpCat.{u + 1} j).obj
        ((Etale.moduleAbelianForget A X).obj F)) q := by
  letI := (Etale.module_cohomology_conventions A X).2.1 F (Scheme.Etale.mk j) q
  let e := asIso ((Etale.moduleEvaluationForgetComparison A X (Scheme.Etale.mk j) q).app F)
  let e' := (evaluationExt X (Scheme.Etale.mk j) q).app ((Etale.moduleAbelianForget A X).obj F)
  exact e.addCommGroupIsoToAddEquiv.trans (e'.addCommGroupIsoToAddEquiv.trans
    (etaleCohomologyOverOpenEquiv j ((Etale.moduleAbelianForget A X).obj F) q))

private theorem line_isCurve (Ω : Type u) [Field Ω] :
    IsCurve (lineProjection (Spec (CommRingCat.of Ω))) := by
  let S := Spec (CommRingCat.of Ω)
  change IsCurve (((AffineSpace (ULift.{u} (Fin 1)) S) ↘ S))
  refine { krullDim_le_one := ?_ }
  rw [topologicalKrullDim_affineSpace_of_isAffine]
  change topologicalKrullDim (PrimeSpectrum Ω) + Nat.card (ULift.{u} (Fin 1)) ≤ 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  simp

private theorem punctured_isCurve (Ω : Type u) [Field Ω] :
    IsCurve (puncturedProjection (Spec (CommRingCat.of Ω))) := by
  let S := Spec (CommRingCat.of Ω)
  have : IsCurve (lineProjection S) := line_isCurve Ω
  have : IsAffine (Line S) := inferInstanceAs (IsAffine (AffineSpace (ULift.{u} (Fin 1)) S))
  have : QuasiCompact (openImmersion S) := by
    change QuasiCompact (((Line S).basicOpen (coordinate S)).ι)
    infer_instance
  change IsCurve (openImmersion S ≫ lineProjection S)
  refine { krullDim_le_one := ?_ }
  exact (openImmersion S).isOpenEmbedding.isInducing.topologicalKrullDim_le.trans
    (IsCurve.krullDim_le_one (f := lineProjection S))

private theorem moduleSheaf_torsion (A : Type (u + 1)) [CommRing A]
    (n : ℕ) (hn : 0 < n) (hA : (n : A) = 0) (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    ((Etale.moduleAbelianForget A X).obj F).IsTorsion := by
  apply Sheaf.IsTorsion.of_forall_isAddTorsion
  intro U s
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, ?_⟩
  let : Module A (((Etale.moduleAbelianForget A X).obj F).obj.obj U) :=
    (F.obj.obj U).isModule
  rw [← Nat.cast_smul_eq_nsmul A, hA, zero_smul]

private theorem objectCohom_isZero (A : Type (u + 1)) [CommRing A]
    (n : ℕ) (hn : 0 < n) (hA : (n : A) = 0)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [IsAffine U]
    (a : U ⟶ Spec (CommRingCat.of Ω)) [IsCurve a]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ) (hq : 2 ≤ q) :
    IsZero (((sections X.smallEtaleTopology A (Scheme.Etale.mk j)).rightDerived q).obj F) := by
  let G := (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).obj F
  have hG := moduleSheaf_torsion A n hn hA U G
  have : Subsingleton (Sheaf.H ((Etale.moduleAbelianForget A U).obj G) q) :=
    IsCurve.subsingleton_sheafH_of_two_le_of_isAffine a _ hG q hq
  have : Subsingleton (Sheaf.H
      ((Etale.openImmersionRestriction AddCommGrpCat.{u + 1} j).obj
        ((Etale.moduleAbelianForget A X).obj F)) q) := by
    convert (inferInstance : Subsingleton
      (Sheaf.H ((Etale.moduleAbelianForget A U).obj G) q)) using 1
    rfl
  have : Subsingleton (((sections X.smallEtaleTopology A
      (Scheme.Etale.mk j)).rightDerived q).obj F) :=
    (objectCohomEquiv A j F q).toEquiv.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/-- The two affine curves have no cohomology above degree one for any sheaf annihilated
by a positive integer.
Source: Milne, Section 15; blueprint sk-prop-cd-affine and sk-prop-a1-kummer.
(blueprint: lem-pur-finite-line-high-cohomology).

Proof: affine space over Spec Ω has dimension one, by the affine-space dimension formula.
Its coordinate basic open is affine and has dimension at most one by the open embedding.
Every section of the underlying abelian sheaf is killed by n, so that sheaf is torsion.
Apply the affine-curve cohomological-dimension theorem, also to restriction to the open.
The module-forgetful derived-evaluation comparison, the cocycle-normalized evaluation/Ext
comparison, and the open-cohomology equivalence transfer these zero groups to the specified
module-valued derived evaluations. -/
theorem finite_line_high_cohomology (A : Type (u + 1)) [CommRing A]
    (n : ℕ) (hn : 0 < n) (hA : (n : A) = 0)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (F : Sheaf (Line (Spec (CommRingCat.of Ω))).smallEtaleTopology
      (ModuleCat.{u + 1} A)) (q : ℕ) (hq : 2 ≤ q) :
    IsZero (((sections (Line (Spec (CommRingCat.of Ω))).smallEtaleTopology A
      (Scheme.Etale.mk (𝟙 (Line (Spec (CommRingCat.of Ω)))))).rightDerived q).obj F) ∧
    IsZero (((sections (Line (Spec (CommRingCat.of Ω))).smallEtaleTopology A
      (openObject (Spec (CommRingCat.of Ω)))).rightDerived q).obj F) := by
  let S := Spec (CommRingCat.of Ω)
  have : IsCurve (lineProjection S) := line_isCurve Ω
  have : IsCurve (puncturedProjection S) := punctured_isCurve Ω
  have : IsAffine (Line S) := inferInstanceAs (IsAffine (AffineSpace (ULift.{u} (Fin 1)) S))
  have : IsAffine (Punctured S) := inferInstanceAs
    (IsAffine (((Line S).basicOpen (coordinate S)).toScheme))
  exact ⟨objectCohom_isZero A n hn hA Ω (𝟙 (Line S)) (lineProjection S) F q hq,
    objectCohom_isZero A n hn hA Ω (openImmersion S) (puncturedProjection S) F q hq⟩
end WeilConjectures.PurityFiniteSetting.RankOne
