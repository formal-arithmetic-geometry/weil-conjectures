/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q9
-/
module

public import Sheaf.SixFunctors.IntegralDualizingSupportSystemHom
public import Sheaf.SixFunctors.IntegralDualizingMappingTower
import Sheaf.SixFunctors.CoefPairingNativeOperations
import Sheaf.Paper.QcqsCompactSupportNativeTowerComparison
import Sheaf.Paper.QcqsCompactSupportStrictReductionGamma
import all Sheaf.Paper.CompactSupportRepresentativeIndependence
import Sheaf.Paper.SfIntegralConstructibleTriangulated

/-! # Compact support reconstructed before applying Hom

Source: prop-coef-integral-dualizing, proof paragraph 2, compact-support reduction.
(blueprint: lem-coef-integral-dualizing-support-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem dualizingLimitIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (Y : Scheme.{u}) :
    Nonempty (integralDualizingLimit l E Y ≅ coefficientConstantTowerLimit l E Y) := by
  let H := ringedStrictTowerHomotopyLimitOfUniverses.{u + 2, u + 1, u, u}
    (Scheme.ProEt.topology Y) (completedIntegralCoefficientSheafUnrestricted l E Y)
    (completedIntegralCoefficient_mul_commUnrestricted l E Y)
  let U := (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ⥤ scalarReductionSource l E Y)
  have hd := H.choose_spec.choose_spec.1
  have hc := canonicalDerivedUnit_isDerived U
  let η := H.choose_spec.choose
  let η' := canonicalDerivedUnit U
  have hc' : U.rightDerivedFunctor.IsRightDerivedFunctor η'
      (HomologicalComplex.quasiIso _ (.up ℤ)) := hc
  exact ⟨@Functor.rightDerivedUnique _ _ _ _ _ _ H.choose U.rightDerivedFunctor _ _ η η'
    (HomologicalComplex.quasiIso _ (.up ℤ)) _ hd hc'⟩

attribute [local irreducible] integralDualizingCompactTower integralDualizingLimit
  coefficientSequenceLimit coefficientConstantTowerLimit sfIntegralConstructible
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The actual integral support value is constructible and its reduction is the
quotient-system support value, naturally before any dual or Hom is taken.

Source: prop-coef-integral-dualizing, second proof paragraph, compact-support
reduction; integralCompactSupport_prescribedReductions.
(blueprint: lem-coef-integral-dualizing-support-reduction).

Proof: fix the Nagata compactification used by both support constructions.
The normalized reduction calculus compares S.reduction with the reduction used
in integralDualizingCompactTower by the unique left-adjoint comparison compatible
with their total-limit adjunctions. The scalar restriction isomorphisms of G
identify its ordinary open and proper operations with the actual ones on towers.
An R-linear map between the quotient-sheaf modules is quotient-linear: locally
every quotient scalar lifts to R, so R-linearity gives the required scalar law.
Thus the ordinary comparisons lift to quotient modules before being derived;
their derived comparisons retain the ordinary adjunction units and counits.
Compose these comparisons on strict representatives to identify the restricted
system support with the compact-support tower in the definition of F. The
right-derived-limit comparison therefore identifies F with the total limit of
that system, retaining each of its actual projections.
For each constructible K, integral_residue_tor gives a common finite Tor interval
for its reductions. A finite dimension bound exists since X is finite type over
a field. Apply integralCompactSupport_prescribedReductions to the defining Roos
triangle and these bounds. It proves that F(K) is integral constructible and
that every projection's reduction adjunct is invertible. Take the reduction
counit for the base calculus B and transport it through the strict tower
comparison just constructed. Its evaluated components are precisely those
projection adjuncts, by B.counit_projection. B.isIso_iff_evaluations makes the
counit invertible as a system map. Naturality of the counit, strict support
comparisons and limit comparison gives a natural isomorphism of functors.
This argument constructs the system map before testing its evaluations; it
does not lift a family of finite isomorphisms. Zero input and empty X give zero
support, and the first quotient is included in the same Roos triangle. -/
theorem integralDualizing_support_reduction
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
    (B : CoefficientDerivedSystemCalculus l E (Spec (.of D.k))) :
    let F := (sfIntegralConstructible l E X).ι ⋙
      integralDualizingCompactTower l E D hl X ⋙
        integralDualizingLimit l E (Spec (.of D.k))
    (∀ K : sfIntegralConstructibleCategory l E X,
      sfIntegralConstructible l E (Spec (.of D.k)) (F.obj K)) ∧
      Nonempty (F ⋙ B.reduction ≅ integralDualizingSystemSupport D l E X S G)  := by
  classical
  let Y := Spec (.of D.k)
  let : Y.Over Y := ⟨𝟙 _⟩
  let c := finiteDualizingCompactification D X
  let : (X ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  let hk := finiteFieldDatumPrimeUnit D l hl
  let N := S.reduction ⋙ ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) c.i ⋙
      ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.g
  obtain ⟨a, _⟩ := qcqsCompactSupport_nativeTowerComparison l E D.k hk c S
  let a' : integralDualizingCompactTower l E D hl X ≅
      N ⋙ coefficientSequenceDerivedRestriction l E Y := by
    unfold integralDualizingCompactTower integralDualizingCompactification
    exact a
  obtain ⟨ζ⟩ := dualizingLimitIso l E Y
  let t : (sfIntegralConstructible l E X).ι ⋙
      integralDualizingCompactTower l E D hl X ⋙ integralDualizingLimit l E Y ≅
      (sfIntegralConstructible l E X).ι ⋙ N ⋙ coefficientSequenceLimit l E Y := by
    unfold coefficientSequenceLimit
    exact Functor.isoWhiskerLeft (sfIntegralConstructible l E X).ι
      (Functor.isoWhiskerRight a' (integralDualizingLimit l E Y) ≪≫
        Functor.isoWhiskerLeft (N ⋙ coefficientSequenceDerivedRestriction l E Y) ζ)
  obtain ⟨γ, hγ⟩ := qcqsCompactSupport_strictReductionGamma l E D.k hk c S B
  let d := t ≪≫ γ.symm
  refine ⟨fun K ↦ (sfIntegralConstructible l E Y).prop_of_iso
    (d.app K).symm ((sfCompactSupportFiniteIntegralFunctor l D.k hk c E).obj K).property,
    ?_⟩
  have hε (K : sfIntegralConstructibleCategory l E X) :
      IsIso (B.adjunction.counit.app (N.obj K.obj)) := by
    apply (B.isIso_iff_evaluations _).2
    intro n
    let V := coefficientSequenceDerivedEvaluation l E Y n
    let P := coefficientFiniteDerivedExtension l E Y n
    let adj := coefficientFiniteAdjunction l E Y n
    let e := Functor.isoWhiskerLeft S.reduction (compactSupportSystemEvaluation l E c n) ≪≫
      Functor.isoWhiskerRight (S.reductionEvaluation n)
        (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)))
    let q := B.adjunction.counit.app (N.obj K.obj)
    have heq : P.map (γ.hom.app K) ≫
        (B.reductionEvaluation n).inv.app ((coefficientSequenceLimit l E Y).obj (N.obj K.obj)) ≫
        V.map q ≫ e.hom.app K.obj =
        (sfCompactSupportFiniteReductionIso l D.k hk c E K n).hom := by
      apply (adj.homEquiv _ _).injective
      rw [← Category.assoc
        ((B.reductionEvaluation n).inv.app
          ((coefficientSequenceLimit l E Y).obj (N.obj K.obj)))
        (V.map q) (e.hom.app K.obj),
        Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
      erw [B.counit_projection]
      exact (hγ K n).trans (by rw [Adjunction.homEquiv_unit]; rfl)
    have : IsIso (P.map (γ.hom.app K) ≫
        (B.reductionEvaluation n).inv.app ((coefficientSequenceLimit l E Y).obj (N.obj K.obj)) ≫
        V.map q ≫ e.hom.app K.obj) := by rw [heq]; infer_instance
    have : IsIso ((B.reductionEvaluation n).inv.app
        ((coefficientSequenceLimit l E Y).obj (N.obj K.obj)) ≫
        V.map q ≫ e.hom.app K.obj) := IsIso.of_isIso_comp_left (P.map (γ.hom.app K)) _
    have : IsIso (V.map q ≫ e.hom.app K.obj) := IsIso.of_isIso_comp_left
      ((B.reductionEvaluation n).inv.app _) _
    exact IsIso.of_isIso_comp_right (V.map q) (e.hom.app K.obj)
  let ε : ((sfIntegralConstructible l E X).ι ⋙ N ⋙ coefficientSequenceLimit l E Y) ⋙
      B.reduction ≅ (sfIntegralConstructible l E X).ι ⋙ N :=
    NatIso.ofComponents (fun K ↦ @asIso _ _ _ _
      (B.adjunction.counit.app (N.obj K.obj)) (hε K))
      (fun f ↦ B.adjunction.counit.naturality (N.map f.hom))
  obtain ⟨jo, ⟨jp⟩⟩ := coefPairing_native_operations l E c S G
  let := ProEtale.VaryingRing.extensionAdditive
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) c.i
  let := ProEtale.VaryingRing.extensionLimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) c.i
  let := ProEtale.VaryingRing.extensionColimits
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) c.i
  let := ProEtale.VaryingRing.push_additive
    (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) c.g
  let b : G.openModules.mapDerivedCategory ⋙ G.properModules.rightDerivedFunctor ≅
      ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.i ⋙
      ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.g :=
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso jo)
      G.properModules.rightDerivedFunctor ≪≫
        Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorNatIso jp)
  exact ⟨Functor.isoWhiskerRight t B.reduction ≪≫ ε ≪≫
    Functor.isoWhiskerLeft ((sfIntegralConstructible l E X).ι ⋙ S.reduction) b.symm⟩

end WeilConjectures
