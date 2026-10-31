/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CommonStageCurveWeilMiddleExtension
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartCommonStratification
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.HomologyZero
import WeilConjectures.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible
import WeilConjectures.AlgebraicGeometry.AdicConstructibilityPredicateComparison
import all WeilConjectures.AlgebraicGeometry.CoefficientHeartClosure

/-! # Ordinary middle extension with condensed coefficients

Source: latest blueprint, def-wf-middle-extension, ordinary direct-image paragraph
(blueprint: def-wf-middle-extension).

The earlier interfaces stay imported. The additional interface uses the actual condensed
module direct image, and the canonical zeroth-derived-functor comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {U C : Scheme.{u}} (j : U ⟶ C)

/-- The degree-zero sheaf followed by cohomological shift by one.
Source: latest blueprint, def-wf-middle-extension, final sentence
(blueprint: def-wf-middle-extension). -/
def shiftedSheaf (X : Scheme.{u}) :=
  DerivedCategory.singleFunctor
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) 0 ⋙
    shiftFunctor _ (1 : ℤ)

/-- The ordinary module direct image, with the source's actual condensed coefficients.
Source: latest blueprint, def-wf-middle-extension, displayed definition
(blueprint: def-wf-middle-extension). -/
abbrev condensedMiddleExtension := lowerStar Λ j

/-- The canonical degree-zero identification H⁰(Rj_* F[0]) ≅ j_* F.
Source: latest blueprint, def-wf-middle-extension, displayed definition
(blueprint: def-wf-middle-extension). -/
def condensedMiddleExtensionDegreeZeroIso :
    DerivedCategory.singleFunctor _ 0 ⋙ (lowerStar Λ j).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor _ 0 ≅ condensedMiddleExtension Λ j :=
  (lowerStar Λ j).singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso

/-- First take ordinary direct image, then put the sheaf in degree zero and shift by one.
Source: latest blueprint, def-wf-middle-extension, final paragraph
(blueprint: def-wf-middle-extension). -/
def shiftedOrdinaryImage := condensedMiddleExtension Λ j ⋙ shiftedSheaf Λ C

/-- Constructibility of ordinary middle extension of a lisse sheaf on a smooth curve.
Source: latest blueprint, def-wf-middle-extension, constructibility sentence
(blueprint: def-wf-middle-extension).

Proof: the base changes U, C of U₀, C₀ to the algebraic closure are separated of finite
type, and the closure has characteristic p ≠ ℓ. A lisse module is locally finitely presented
(finite free on a pro-étale cover, a cokernel of a zero map), so with the identity one-stratum
stratification F is constructible in the stratified convention. The single-sheaf finiteness
theorem for direct image (lem-sfb-dc-lower-star-single-constructible), in degree zero and for
the geometric open immersion j, makes H⁰(Rj_*F[0]) constructible; the preceding canonical
comparison identifies it with the ordinary direct image j_*F. On the Noetherian quasi-compact
target C the adic predicate comparison (lem-sfb-adic-constructibility-predicate-comparison)
turns this into the finite constant local-model predicate. -/
theorem condensedMiddleExtension_constructible
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (_hEll : ell ≠ D.p) (c : Scheme.MiddleExtensionCurve D)
    (F : Mod (Sheaf (Scheme.ProEt.topology (D.geometricFiber c.U).left)
      Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell)
        (D.geometricFiber c.U).left))
    (_hF : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) F) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj ell)
      (D.geometricFiber c.C).left
      ((condensedMiddleExtension (Profinite.padicAlgClRingObj ell)
        (WeilConjectures.qbarCurveGeometricOpen D c)).obj F) := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have : Fact (ringChar D.k).Prime := ⟨by rw [ringChar.eq D.k D.p]; exact D.prime⟩
  have : Fact (ringChar D.k ≠ ell) := ⟨by rw [ringChar.eq D.k D.p]; exact _hEll.symm⟩
  let X := D.geometricFiber c.U
  let Y := D.geometricFiber c.C
  -- Use exactly the geometric open immersion occurring in the conclusion.
  let f : X ⟶ Y := Over.homMk (WeilConjectures.qbarCurveGeometricOpen D c)
    (Over.w ((Over.pullback (Spec.map
      (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map c.j))
  have : LocallyOfFiniteType X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd c.U.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : QuasiCompact X.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd c.U.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : IsSeparated X.hom :=
    inferInstanceAs (IsSeparated (pullback.snd c.U.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : LocallyOfFiniteType Y.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd c.C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : QuasiCompact Y.hom :=
    inferInstanceAs (QuasiCompact (pullback.snd c.C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have : IsSeparated Y.hom :=
    inferInstanceAs (IsSeparated (pullback.snd c.C.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left) F := by
    let S : Scheme.Stratification X.left :=
      { n := 1
        stratum := fun _ ↦ Set.univ
        isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
        isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
        iUnion_stratum_eq_univ := Set.iUnion_const _
        pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
        domain := fun _ ↦ X.left
        immersion := fun _ ↦ 𝟙 X.left
        range_immersion := fun _ ↦ Set.range_id' }
    exact ⟨S, fun _ ↦ localFinitePresentation_pullback (𝟙 X.left)
      (heart_lfp_of_lisse (Profinite.padicAlgClRingObj ell) _hF)⟩
  have hzero := finiteTypeDirectImage_single_constructible ell f F hF 0
  have hpush : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicAlgClRingObj ell) Y.left)
      ((lowerStar (Profinite.padicAlgClRingObj ell) f.left).obj F) :=
    _root_.constructible_of_iso
      ((condensedMiddleExtensionDegreeZeroIso
        (Profinite.padicAlgClRingObj ell) f.left).app F) hzero
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  exact (adicConstructibilityPredicateComparison ell Y.left
    (Profinite.padicAlgClRingObj ell) .algebraicClosure).1 _ |>.mp hpush

end AlgebraicGeometry.ProEtale.CondensedRing
