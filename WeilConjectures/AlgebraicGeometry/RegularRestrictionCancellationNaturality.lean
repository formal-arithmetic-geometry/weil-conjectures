/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularComparisonEtaleRestrictionData

/-! # RegularRestrictionCancellationNaturality

(blueprint: lem-pur-regular-restriction-cancellation-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Co-projection and cancellation carry the oriented restriction square to the
specified regular comparison. The hypothesis is the comparison before
co-projection, with both Tate pullbacks displayed explicitly.

Proof (postponed): apply the co-projection restriction square with the factors
(A_X,T_X(nX)) to the assumed equality. The result is the restriction equality
for the q maps in regular diagonal cancellation. Tensor with the inverse of
the m-th root power. Strong monoidality of pullback, its unit equation and
preservation of the root evaluation identify the resulting maps with the two
q-prime maps; ordered Tate addition uses nX=m+c. Apply co-projection restriction
a second time with (A_X,T_X(c)), now in the inverse direction. The resulting
map satisfies exactly the tensor/projection/counit equation characterizing
the restricted Phi. Uniqueness in regular diagonal twist cancellation
identifies it with the specified Phi on U. Every coefficient comparison is
the root- and pure-tensor-normalized one. No permutation of odd factors is
introduced; the same argument applies when m or c is zero and when the schemes
are empty.
Source: regular-immersion proof Steps 1--2 under Step 4(ii), the fifth proof
step of the parent node (blueprint: lem-pur-regular-restriction-cancellation-naturality). -/
theorem regularRestrictionCancellationNaturality
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X U : Scheme.{u}}
    (i : Z ⟶ X) (uMap : U ⟶ X)
    [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [IsSeparated (U ↘ Spec (.of P.field.k))]
    [i.IsOver (Spec (.of P.field.k))] [uMap.IsOver (Spec (.of P.field.k))]
    [IsSeparated i] [LocallyOfFiniteType i] [QuasiCompact i]
    [IsSeparated uMap] [LocallyOfFiniteType uMap] [QuasiCompact uMap]
    [Etale uMap] [IsClosedImmersion i]
    [HasInvertibleExponent P.Coefficient X]
    [HasInvertibleExponent P.Coefficient Z]
    [HasInvertibleExponent P.Coefficient U]
    (nX m c : ℕ) (hdim : nX = m + c)
    [SmoothOfRelativeDimension nX (X ↘ Spec (.of P.field.k))]
    [SmoothOfRelativeDimension m (i ≫ (X ↘ Spec (.of P.field.k)))]
    [SmoothOfRelativeDimension nX (uMap ≫ (X ↘ Spec (.of P.field.k)))] :
    (let V := pullback i uMap
    letI : V.Over (Spec (.of P.field.k)) :=
      ⟨pullback.snd i uMap ≫ uMap ≫ (X ↘ Spec (.of P.field.k))⟩
    letI : HasInvertibleExponent P.Coefficient V :=
      HasInvertibleExponent.of_hom (pullback.fst i uMap)
    letI : LocallyOfFiniteType (V ↘ Spec (.of P.field.k)) := by
      change LocallyOfFiniteType
        (pullback.snd i uMap ≫ uMap ≫ (X ↘ Spec (.of P.field.k)))
      infer_instance
    letI : QuasiCompact (V ↘ Spec (.of P.field.k)) := by
      change QuasiCompact
        (pullback.snd i uMap ≫ uMap ≫ (X ↘ Spec (.of P.field.k)))
      infer_instance
    letI : IsSeparated (pullback i uMap ↘ Spec (.of P.field.k)) := by
      change IsSeparated
        (pullback.snd i uMap ≫ uMap ≫ (X ↘ Spec (.of P.field.k)))
      infer_instance
    let v := pullback.fst i uMap
    let iU := pullback.snd i uMap
    letI : (pullback.fst i uMap).IsOver (Spec (.of P.field.k)) := by
      refine ⟨?_⟩
      change pullback.fst i uMap ≫ (Z ↘ Spec (.of P.field.k)) =
        pullback.snd i uMap ≫ uMap ≫ (X ↘ Spec (.of P.field.k))
      calc
        pullback.fst i uMap ≫ (Z ↘ Spec (.of P.field.k)) =
            pullback.fst i uMap ≫ i ≫ (X ↘ Spec (.of P.field.k)) := by
              simpa only [Category.assoc] using congrArg
                (fun q => pullback.fst i uMap ≫ q)
                (comp_over i (Spec (.of P.field.k))).symm
        _ = pullback.snd i uMap ≫ uMap ≫ (X ↘ Spec (.of P.field.k)) := by
              simpa only [Category.assoc] using congrArg
                (fun q => q ≫ (X ↘ Spec (.of P.field.k)))
                (pullback.condition (f := i) (g := uMap))
    letI : (pullback.snd i uMap).IsOver (Spec (.of P.field.k)) := by
      refine ⟨?_⟩
      change pullback.snd i uMap ≫ (U ↘ Spec (.of P.field.k)) =
        pullback.snd i uMap ≫ uMap ≫ (X ↘ Spec (.of P.field.k))
      simpa only [Category.assoc] using congrArg
        (fun q => pullback.snd i uMap ≫ q)
        (comp_over uMap (Spec (.of P.field.k))).symm
    letI : Etale v := by
      dsimp [v]
      infer_instance
    letI : IsClosedImmersion iU := by
      dsimp [iU]
      infer_instance
    let aX := X ↘ Spec (.of P.field.k)
    let aZ := i ≫ aX
    let aU := uMap ≫ aX
    let aV := iU ≫ aU
    letI : SmoothOfRelativeDimension m aV := by
      have : SmoothOfRelativeDimension 0 v :=
        (Etale.iff_smoothOfRelativeDimension_zero v).mp inferInstance
      have hv : SmoothOfRelativeDimension m (v ≫ aZ) := by
        simpa using (smoothOfRelativeDimension_comp (n := 0) (m := m) v aZ)
      rw [show aV = v ≫ aZ by
        change (pullback.snd i uMap ≫ uMap) ≫ aX =
          (pullback.fst i uMap ≫ i) ≫ aX
        simpa only [Category.assoc] using congrArg (fun q => q ≫ aX)
          (pullback.condition (f := i) (g := uMap)).symm]
      exact hv
    letI : HasCompactification aX := inferInstance
    letI : HasCompactification aZ := inferInstance
    letI : HasCompactification aU := inferInstance
    letI : HasCompactification aV := inferInstance
    let W_X := dualizingComplex P.Coefficient aX
    let W_Z := dualizingComplex P.Coefficient aZ
    let W_U := dualizingComplex P.Coefficient aU
    let W_V := dualizingComplex P.Coefficient aV
    let P_X : W_X ≅ P.diagonalTwistEtale X nX := by
      simpa [W_X] using (regularCanonicalDualizingIso P aX nX)
    let P_Z : W_Z ≅ P.diagonalTwistEtale Z m := by
      simpa [W_Z] using (regularCanonicalDualizingIso P aZ m)
    let P_U : W_U ≅ P.diagonalTwistEtale U nX := by
      simpa [W_U] using (regularCanonicalDualizingIso P aU nX)
    let P_V : W_V ≅ P.diagonalTwistEtale V m := by
      simpa [W_V] using (regularCanonicalDualizingIso P aV m)
    let b := (WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition
      P.Coefficient i aX).app (constantComplex P.Coefficient (Spec (.of P.field.k)))
    let bU := (WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition
      P.Coefficient iU aU).app (constantComplex P.Coefficient (Spec (.of P.field.k)))
    (∀ t : OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates,
      P_V.inv ≫ bU.hom ≫ (FiniteEtaleNormalization.exceptional P iU).map P_U.hom ≫
        (FiniteEtaleNormalization.exceptional P iU).map
        (vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t uMap (P.diagonalExponent_isUnit aX) nX).inv ≫
        regularRestrictionBaseChange P i uMap v iU
          (pullback.condition (f := i) (g := uMap)).symm (P.diagonalTwistEtale X nX) =
      (vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t v (P.diagonalExponent_isUnit aZ) m).inv ≫
      (FiniteEtaleNormalization.pull P v).map
        (P_Z.inv ≫ b.hom ≫ (FiniteEtaleNormalization.exceptional P i).map P_X.hom)) →
    ∀ t : OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates,
      regularDiagonalComparisonPhi P iU aU m nX c hdim W_U W_V bU P_U P_V ≫
        (FiniteEtaleNormalization.exceptional P iU).map
          ((vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates t uMap (P.diagonalExponent_isUnit aX) c).inv) ≫
        regularRestrictionBaseChange P i uMap v iU (pullback.condition (f := i) (g := uMap)).symm
          (P.diagonalTwistEtale X c) =
      (leftDerivedUpperStarConstantComplexIso P.Coefficient v).inv ≫
        (FiniteEtaleNormalization.pull P v).map
          (regularDiagonalComparisonPhi P i aX m nX c hdim W_X W_Z b P_X P_Z)) := by
  sorry

end AlgebraicGeometry.Etale
