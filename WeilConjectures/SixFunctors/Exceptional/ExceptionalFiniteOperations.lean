/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Exceptional.ExceptionalFiniteRestrictionAdjunction
public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalClassHom
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SmoothPurity.Supporting.ConstructibleIntervalsUnordered
public import WeilConjectures.CategoryTheory.Ringed.RingedProEtaleTorAmplitudeOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.Sf.SfOpenExceptionalBaseChange
import WeilConjectures.SixFunctors.Exceptional.ExceptionalFiniteIntrinsicBounds
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImageSupplement
import WeilConjectures.AlgebraicGeometry.Open.OpenExtensionFiniteTor

/-!
# Exact finite-coefficient exceptional adjunctions

The categories are the published full intrinsic constant-coefficient categories.
The normalization is expressed in their canonical fixed-module coordinates, using
exactly the specified-compactification ordinary etale adjunction.

## References

* Zheng, Propositions 2.23, 2.29, 3.16, Lemma 5.22 and Proposition 5.24
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace WeilConjectures

/-- Choice of exact additive adjunctions on the actual full finite-Tor categories,
with the specified ambient functors, transported Hom normalization and uniform bounds.
The right shift is precisely the adjoint of the chosen left shift. -/
theorem exists_sfFiniteExceptionalOperations (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (d : ℕ) (hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞)) :
    ∃ cMinus cPlus : ℤ, ∀ (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l)
      (n : ℕ+),
    ∃ (F : finiteTorConstructibleCategory l E.carrier n n.pos X ⥤
          finiteTorConstructibleCategory l E.carrier n n.pos Y)
      (G : finiteTorConstructibleCategory l E.carrier n n.pos Y ⥤
          finiteTorConstructibleCategory l E.carrier n n.pos X)
      (eF : F ⋙ (finiteTorConstructible l E.carrier n n.pos Y).ι =
        (finiteTorConstructible l E.carrier n n.pos X).ι ⋙
          sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E.carrier n))
      (eG : G ⋙ (finiteTorConstructible l E.carrier n n.pos X).ι =
        (finiteTorConstructible l E.carrier n n.pos Y).ι ⋙
          sfFiniteOperationsIntrinsicRight l E n c)
      (_ : F.Additive) (_ : G.Additive) (_ : F.CommShift ℤ) (sG : G.CommShift ℤ)
      (adj : F ⊣ G),
      F.IsTriangulated ∧ G.IsTriangulated ∧
      adj.unit.CommShift ℤ ∧ adj.counit.CommShift ℤ ∧
      sG = adj.rightAdjointCommShift ℤ ∧
      ∃ (rF : F ⋙ sfFiniteOperationsRealization l E n Y ≅
          sfFiniteOperationsRealization l E n X ⋙
            ProEtale.rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} (ULift.{u + 1, u}
                (Padic.coefficientExtensionRing l E.carrier n))) c)
        (rG : G ⋙ sfFiniteOperationsRealization l E n X ≅
          sfFiniteOperationsRealization l E n Y ⋙ ProEtale.sfFiniteExceptionalAt
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.carrier n)) c)
        (hX : ∀ K : finiteTorConstructibleCategory l E.carrier n n.pos X,
          DerivedCategory.TStructure.t.plus ((sfFiniteOperationsRealization l E n X).obj K))
        (hY : ∀ L : finiteTorConstructibleCategory l E.carrier n n.pos Y,
          DerivedCategory.TStructure.t.plus ((sfFiniteOperationsRealization l E n Y).obj L)),
      rF = sfFiniteOperationsLeftRealization l E n c F eF ∧
      rG = sfFiniteOperationsRightRealization l E n c G eG ∧
      rF.hom.CommShift ℤ ∧ rG.hom.CommShift ℤ ∧
      (∀ K : finiteTorConstructibleCategory l E.carrier n n.pos X,
        Nonempty (FixedEtaleOriginWitness X
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.carrier n))
          ⟨(sfFiniteOperationsRealization l E n X).obj K, hX K⟩)) ∧
      (∀ (K : finiteTorConstructibleCategory l E.carrier n n.pos X)
        (L : finiteTorConstructibleCategory l E.carrier n n.pos Y)
        (W : FixedEtaleOriginWitness X
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.carrier n))
          ⟨(sfFiniteOperationsRealization l E n X).obj K, hX K⟩) (a : F.obj K ⟶ L),
        (sfFiniteOperationsRealization l E n X).map (adj.homEquiv K L a) ≫ rG.hom.app L =
          sfFiniteOperationsHomEquiv l E n D.k (Y ↘ Spec (.of D.k)) c
            ⟨(sfFiniteOperationsRealization l E n X).obj K, hX K⟩ W
            ⟨(sfFiniteOperationsRealization l E n Y).obj L, hY L⟩
            (rF.inv.app K ≫ (sfFiniteOperationsRealization l E n Y).map a)) ∧
      (∀ (K : finiteTorConstructibleCategory l E.carrier n n.pos X) (a b : ℤ),
        HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E.carrier n) K.obj a b →
        HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E.carrier n)
          (F.obj K).obj a (b + 2 * (d : ℤ))) ∧
      (∀ (L : finiteTorConstructibleCategory l E.carrier n n.pos Y) (a b : ℤ),
        constructibleInterval l E.carrier n n.pos Y a b L.obj →
        constructibleInterval l E.carrier n n.pos X (a + cMinus) (b + cPlus) (G.obj L).obj) ∧
      (∀ (L : finiteTorConstructibleCategory l E.carrier n n.pos Y) (a b : ℤ),
        HasProEtaleTorAmplitude Y (Padic.coefficientExtensionRing l E.carrier n) L.obj a b →
        HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E.carrier n)
          (G.obj L).obj (a + cMinus) (b + cPlus)) := by
  classical
  let : c.Z.Over (Spec (.of D.k)) := ⟨c.g ≫ (Y ↘ Spec (.of D.k))⟩
  let : LocallyOfFiniteType (c.Z ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (c.g ≫ (Y ↘ Spec (.of D.k))))
  let : QuasiCompact (c.Z ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (c.g ≫ (Y ↘ Spec (.of D.k))))
  let : c.i.IsOver (Spec (.of D.k)) := (Scheme.Hom.isOver_iff (Spec (.of D.k))).mpr (by
    change c.i ≫ c.g ≫ (Y ↘ Spec (.of D.k)) = X ↘ Spec (.of D.k)
    rw [← Category.assoc, ← c.comm]
    exact comp_over f _)
  let : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  obtain ⟨cMinus, cPlus, hright⟩ :=
    sfFiniteOperations_intrinsicExceptionalBounds D l _hl f c
  refine ⟨cMinus, cPlus, ?_⟩
  intro E n
  let A := Padic.coefficientExtensionRing l E.carrier n
  let PX := finiteTorConstructible l E.carrier n n.pos X
  let PY := finiteTorConstructible l E.carrier n n.pos Y
  let support := sfIntrinsicCompactSupport c A
  have hsupport (K : PX.FullSubcategory) (a b : ℤ)
      (h : HasProEtaleTorAmplitude X A K.obj a b) :
      PY (support.obj K.obj) ∧
        HasProEtaleTorAmplitude Y A (support.obj K.obj) a (b + 2 * (d : ℤ)) := by
    obtain ⟨hj, _, htor⟩ := finiteStageDerivedExtensionByZero_constructibleFiniteTor
      D l _hl E.carrier n n.pos c.i K.obj K.property.1 K.property.2
    let g : Over.mk (c.Z ↘ Spec (.of D.k)) ⟶ Over.mk (Y ↘ Spec (.of D.k)) :=
      Over.homMk c.g rfl
    let : LocallyOfFiniteType (Over.mk (c.Z ↘ Spec (.of D.k))).hom :=
      inferInstanceAs (LocallyOfFiniteType (c.g ≫ (Y ↘ Spec (.of D.k))))
    let : QuasiCompact (Over.mk (c.Z ↘ Spec (.of D.k))).hom :=
      inferInstanceAs (QuasiCompact (c.g ≫ (Y ↘ Spec (.of D.k))))
    let : LocallyOfFiniteType (Over.mk (Y ↘ Spec (.of D.k))).hom :=
      inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of D.k)))
    let : QuasiCompact (Over.mk (Y ↘ Spec (.of D.k))).hom :=
      inferInstanceAs (QuasiCompact (Y ↘ Spec (.of D.k)))
    let : IsSeparated g.left := inferInstanceAs (IsSeparated c.g)
    let : LocallyOfFiniteType g.left := inferInstanceAs (LocallyOfFiniteType c.g)
    let : QuasiCompact g.left := inferInstanceAs (QuasiCompact c.g)
    obtain ⟨hc, ht⟩ := ProEtale.finiteCoefficientDirectImage_boundedConstructible_torAmplitude
      D l _hl E.carrier n n.pos _ _ g d hd a b hj (htor a b h)
    exact ⟨⟨hc, a, b + 2 * (d : ℤ), ht⟩, ht⟩
  have hpres (K : PX.FullSubcategory) : PY (support.obj K.obj) := by
    obtain ⟨a, b, h⟩ := K.property.2
    exact (hsupport K a b h).1
  obtain ⟨hpresG, hinterval, htorG⟩ := hright E n
  let F := PY.lift (PX.ι ⋙ support) hpres
  let G := PX.lift (PY.ι ⋙ sfFiniteOperationsIntrinsicRight l E n c) hpresG
  have eF : F ⋙ PY.ι = PX.ι ⋙ support := rfl
  have eG : G ⋙ PX.ι = PY.ι ⋙ sfFiniteOperationsIntrinsicRight l E n c := rfl
  obtain ⟨hadd, sF, adj, htri, rF, rG, hX, hY, heF, heG, hsF, hsG, horigin, hnorm⟩ :=
    sfFiniteOperations_restrictedAdjunction D l _hl f c E n F G eF eG
  let := hadd
  let := sF
  let := adj.rightAdjointCommShift ℤ
  let := htri
  let := adj.commShift_of_leftAdjoint ℤ
  let := adj.right_adjoint_additive
  have htriG : G.IsTriangulated := adj.isTriangulated_rightAdjoint
  refine ⟨F, G, eF, eG, hadd, inferInstance, sF, adj.rightAdjointCommShift ℤ, adj,
    htri, htriG, inferInstance, inferInstance, rfl,
    rF, rG, hX, hY, heF, heG, hsF, hsG, horigin, hnorm, ?_, ?_, ?_⟩
  · intro K a b h
    exact (hsupport K a b h).2
  · exact hinterval
  · exact htorG

end WeilConjectures
