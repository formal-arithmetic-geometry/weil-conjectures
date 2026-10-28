/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData
public import Sheaf.Paper.CommonStagePullbackNormalizedDescent
import all Sheaf.Paper.GeneralAlgebraicallyClosedCoefficientStages
import all Mathlib.Logic.Small.Defs
import all Mathlib.Algebra.Field.Shrink
import all Mathlib.Algebra.Algebra.Shrink
import Sheaf.Paper.QcqsCompletedRefinement
import Sheaf.Paper.RefinementOpenRestriction
import Sheaf.Paper.IsomorphismPullbackRawStage
import Sheaf.Paper.CompletedDirectImageTargetIso
import Sheaf.CategoryTheory.ScalarLocalizationComponentIso
import WeilConjectures.Compactification.CommonRefinement

/-! The stagewise rational family used by the compact-support target comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
open GeneralAlgebraicallyClosedCoefficients

open PurCompactSupport
open TensorProduct

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  proEtaleRingDerivedAdjunction openDerivedAdjunction refinementRestriction

private theorem completedRefinementIso
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [f.IsOver (Spec (.of k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d) :
    Nonempty ((sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ≅
      (sfIntegralConstructible l E X).ι ⋙ image (completed l E) d) := by
  let R := completed l E
  let hi := completedPull_comp l E c.i r.hom
  let I := (sfIntegralConstructible l E X).ι
  let ε := Functor.whiskerLeft I (refinementOpenMap R r hi)
  have hε (K : sfIntegralConstructibleCategory l E X) : IsIso (ε.app K) := by
    obtain ⟨ρ, εK, he, _⟩ := sfQcqsCompletedRefinement_exists l E k hl r K
    have hθ : IsIso (refinementRestriction R r hi K.obj) := by
      obtain ⟨θ, happ, hiso, _⟩ := exists_refinementRestriction R r hi
      have ht : IsIso (θ.app K.obj) :=
        (NatTrans.isIso_iff_isIso_app θ).mp hiso K.obj
      exact (happ K.obj) ▸ ht
    have heq : ε.app K = εK.hom := by
      apply ((openDerivedAdjunction R d.i).homEquiv _ _).injective
      apply (cancel_mono (refinementRestriction R r hi K.obj)).1
      exact (refinementOpenMap_normalization R r hi K.obj).trans he.symm
    exact heq.symm ▸ (inferInstance : IsIso εK.hom)
  have : IsIso ε := NatIso.isIso_of_isIso_app ε
  exact ⟨Functor.isoWhiskerLeft I
      (Functor.isoWhiskerLeft (openExtension R c.i).mapDerivedCategory
        (geometricPushComposition R r.hom d.g (completedPull_comp l E r.hom d.g) ≪≫
          eqToIso (congrArg (fun g ↦ push R g) r.hom_g)).symm) ≪≫
    Functor.isoWhiskerRight (asIso ε).symm (push R d.g)⟩

private theorem integralTargetIso
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (f : X ⟶ Y) (g : X ⟶ Z) (e : Y ≅ Z) (h : f ≫ e.hom = g)
    [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification f) (c' : Compactification g) :
    Nonempty (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) c E ≅
      sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) c' E ⋙
        constructibleIntegralPullback l E e.hom) := by
  let d : Compactification f :=
    { Z := c'.Z, g := c'.g ≫ e.inv, i := c'.i,
      comm := by rw [← Category.assoc, ← c'.comm, ← h]; simp,
      isProper := inferInstance, isOpenImmersion := inferInstance }
  obtain ⟨a⟩ := completedRefinementIso l E D.k (coefficientPrimeUnit l D hl)
    (Compactification.infFst c d)
  obtain ⟨b⟩ := completedRefinementIso l E D.k (coefficientPrimeUnit l D hl)
    (Compactification.infSnd c d)
  let I := (sfIntegralConstructible l E X).ι
  let V := (sfIntegralConstructible l E Y).ι
  let W := (sfIntegralConstructible l E Z).ι
  obtain ⟨t⟩ := completedDirectImageTargetIso l E c'.g e
  have hY (y : Y) : IsUnit (l : Y.presheaf.stalk y) :=
    isUnit_of_map_unit (IsLocalRing.residue (Y.presheaf.stalk y)) _
      ((map_natCast (IsLocalRing.residue (Y.presheaf.stalk y)) l).symm ▸
        isUnit_of_invertible (l : Y.residueField y))
  have hZ (z : Z) : IsUnit (l : Z.presheaf.stalk z) :=
    isUnit_of_map_unit (IsLocalRing.residue (Z.presheaf.stalk z)) _
      ((map_natCast (IsLocalRing.residue (Z.presheaf.stalk z)) l).symm ▸
        isUnit_of_invertible (l : Z.residueField z))
  obtain ⟨s, q, _⟩ := isomorphismPullbackRawStage l E e.hom hY hZ
  let γ : sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) c E ⋙ V ≅
      (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) c' E ⋙
        constructibleIntegralPullback l E e.hom) ⋙ V :=
    (sfQcqsCompactSupportRealization l E D.k (coefficientPrimeUnit l D hl) c).symm ≪≫
      a.symm ≪≫ b ≪≫
      Functor.isoWhiskerLeft I
        (Functor.isoWhiskerLeft (openExtension (completed l E) c'.i).mapDerivedCategory t) ≪≫
      Functor.isoWhiskerRight
        (sfQcqsCompactSupportRealization l E D.k (coefficientPrimeUnit l D hl) c')
        (AlgebraicGeometry.ProEtale.inverseImageIntegralDerived l E e.hom) ≪≫
      Functor.isoWhiskerLeft
        (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) c' E) q
  exact ⟨NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ (γ.app K))
    (fun v ↦ ObjectProperty.hom_ext _ (γ.hom.naturality v))⟩

private theorem rationalTargetIso
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (f : X ⟶ Y) (g : X ⟶ Z) (e : Y ≅ Z) (h : f ≫ e.hom = g)
    [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification f) (c' : Compactification g) :
    Nonempty (sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) c E ≅
      sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) c' E ⋙
        rationalDerivedPullback l E e.hom) := by
  obtain ⟨a⟩ := integralTargetIso l E D hl f g e h c c'
  let A := sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) c E
  let B := sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) c' E
  let P := constructibleIntegralPullback l E e.hom
  let Ar := sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) c E
  let Br := sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) c' E
  let Pr := rationalDerivedPullback l E e.hom
  let R := Padic.coefficientExtensionIntegers l E
  let t := Padic.coefficientExtensionUniformizer l E
  let := (sfCompactSupportFiniteIntegralFunctor_linear l D.k
    (coefficientPrimeUnit l D hl) c E).1
  let := (sfCompactSupportFiniteIntegralFunctor_linear l D.k
    (coefficientPrimeUnit l D hl) c E).2
  let := (sfCompactSupportFiniteIntegralFunctor_linear l D.k
    (coefficientPrimeUnit l D hl) c' E).1
  let := (sfCompactSupportFiniteIntegralFunctor_linear l D.k
    (coefficientPrimeUnit l D hl) c' E).2
  have hP := (rationalDerivedPullback_existsUnique l E e.hom).exists.choose_spec
  let : Ar.Additive := ⟨fun {_ _ f g} ↦ map_add _ f g⟩
  let : Br.Additive := ⟨fun {_ _ f g} ↦ map_add _ f g⟩
  have : Pr.Additive := hP.1
  obtain ⟨b, _⟩ := ScalarLocalization.existsUnique_iso_of_component_formulas
    t t id A (B ⋙ P) a Ar (Br ⋙ Pr)
    (fun _ ↦ rfl) (fun K ↦ hP.2.1 (Br.obj K))
    (fun K L f r ↦ by
      change HEq ((A.mapLinearMap R).baseChange (Localization.Away t) (r ⊗ₜ[R] f)) _
      simp only [LinearMap.baseChange_tmul, Functor.mapLinearMap_apply]
      rfl)
    (fun K L f r ↦ by
      change HEq (Pr.map ((B.mapLinearMap R).baseChange
        (Localization.Away t) (r ⊗ₜ[R] f))) _
      simp only [LinearMap.baseChange_tmul, Functor.mapLinearMap_apply]
      exact hP.2.2 (B.obj K) (B.obj L) (B.map f) r)
  exact ⟨b⟩

set_option linter.unusedVariables false in
/-- Stagewise part of the finite rational target comparison.
Source: the coefficient comparison in the exceptional-adjunction construction
(blueprint: lem-sf-compact-support-target-rational-iso-family).

Proof: compare the compactifications through a common refinement using the normalized
completed open-extension maps. Transport the proper map along the inverse target
isomorphism, identify direct image with exact inverse image, and restrict by the
qcqs realization and the isomorphism pullback comparison. Localize the resulting
integral natural isomorphism using the prescribed pure-tensor formulas. Conjugate
by the two rationalLeft identifications and choose one comparison at each finite
stage. Transition compatibility is the separate coherence statement.
-/
theorem compact_support_target_rational_iso_family
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y Z : Scheme.{max u v}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (f : X ⟶ Y) (g : X ⟶ Z) (e : Y ≅ Z) (h : f ≫ e.hom = g)
    [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (R : RingSystem.{u, v} l Ω D hl (f := f))
    (F : FieldSystem.{u, v} l Ω D hl R) (c : Compactification f)
    (R' : RingSystem.{u, v} l Ω D hl (f := g))
    (F' : FieldSystem.{u, v} l Ω D hl R') (c' : Compactification g) :
    ∃ a : ∀ i : AlgebraicallyClosedCoefficients.Index l Ω,
      (R.operation c (.rational (commonField.{u, v} l Ω i))).F ≅
        (R'.operation c' (.rational (commonField.{u, v} l Ω i))).F ⋙
          rationalDerivedPullback l (AlgebraicallyClosedCoefficients.Coefficient.{max u v}
            l Ω i) e.hom,
      True := by
  classical
  have a (i : AlgebraicallyClosedCoefficients.Index l Ω) :=
    rationalTargetIso l (commonField.{u, v} l Ω i).carrier D hl f g e h c c'
  refine ⟨fun i ↦ R.rationalLeft c (commonField.{u, v} l Ω i) ≪≫
    (a i).some ≪≫
    Functor.isoWhiskerRight (R'.rationalLeft c' (commonField.{u, v} l Ω i)).symm
      (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{max u v} l Ω i) e.hom), trivial⟩

end WeilConjectures.ConstructibleExceptionalCoefficients
