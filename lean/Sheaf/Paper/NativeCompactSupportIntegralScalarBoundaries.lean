/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.LocallyFiniteAdicCompactSupportData

import Sheaf.Paper.FiniteStageActionNormalizedComparison

/-! Natural boundary comparisons for the integral compact-support scalar morphism. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward false
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard Padic
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
set_option allowUnsafeReducibility true in
attribute [local irreducible]
  WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageSystem
attribute [local instance 2000] Shrink.instField
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (P : CoefficientConstruction l (ULift.{u} (PadicAlgCl l)) D hl (f := f))
  (c : Compactification f)

attribute [local irreducible] ScalarLocalization.category

set_option allowUnsafeReducibility true in
attribute [local reducible] ScalarLocalization.category in
private def finiteActionLocalization (E : Index l (PadicAlgCl l)) :
    sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) X ⋙
        sfCompactSupportFiniteFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c
          (Coefficient l (PadicAlgCl l) E) ≅
      sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c
          (Coefficient l (PadicAlgCl l) E) ⋙
        sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) Y :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    dsimp only [sfRationalConstructibleLocalization, ScalarLocalization.localization,
      sfCompactSupportFiniteFunctor, Functor.comp_map, Functor.comp_obj, Iso.refl_hom]
    rw [Category.comp_id, Category.id_comp]
    unfold sfCompactSupportFiniteHomMap
    rfl)


private theorem finiteActionLocalization_map_hom_app [G : NativeGeometry.{u} l]
    (target : Realization l Y) (E : Index l (PadicAlgCl l))
    (K : sfIntegralConstructibleCategory l (Coefficient l (PadicAlgCl l) E) X) :
    (GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := Y) E ⋙ target.J ⋙
      (sections l Y).mapDerivedCategory).map
        ((finiteActionLocalization l D hl c E).hom.app K) = 𝟙 _ := by
  change (GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := Y) E ⋙ target.J ⋙
    (sections l Y).mapDerivedCategory).map (𝟙 _) = 𝟙 _
  exact CategoryTheory.Functor.map_id _ _

private def sourceRational [G : NativeGeometry.{u} l]
    (target : Realization l Y) (stage : StageAction l D hl P c)
    (E : Index l (PadicAlgCl l)) :=
  (finiteStageAction_normalizedComparison l (PadicAlgCl l) X Y stage.system
    (fun E ↦ P.ring.operation c (.rational (finiteField l E)))
    (fun E ↦ sfCompactSupportFiniteFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c
      (Coefficient l (PadicAlgCl l) E))
    (fun E ↦ P.ring.rationalLeft c (finiteField l E)) stage.finite E
    (target.J ⋙ (sections l Y).mapDerivedCategory)).choose

private theorem sourceRational_component [G : NativeGeometry.{u} l]
    (target : Realization l Y) (stage : StageAction l D hl P c)
    (E : Index l (PadicAlgCl l))
    (A : sfRationalConstructibleCategory l (Coefficient l (PadicAlgCl l) E) X) :
    ∃ (B B' : sfRationalConstructibleCategory l (Coefficient l (PadicAlgCl l) E) Y)
      (r : B ⟶ B'), HEq r ((P.ring.rationalLeft c (finiteField l E)).hom.app A) ∧
      HEq ((target.J ⋙ (sections l Y).mapDerivedCategory).map
        ((sourceRational l D hl P c target stage E).hom.app A))
        ((target.J ⋙ (sections l Y).mapDerivedCategory).map
          ((GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := l) (Ω := PadicAlgCl l) (Y := Y) E).map r)) :=
  (finiteStageAction_normalizedComparison l (PadicAlgCl l) X Y stage.system
    (fun E ↦ P.ring.operation c (.rational (finiteField l E)))
    (fun E ↦ sfCompactSupportFiniteFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c
      (Coefficient l (PadicAlgCl l) E))
    (fun E ↦ P.ring.rationalLeft c (finiteField l E)) stage.finite E
    (target.J ⋙ (sections l Y).mapDerivedCategory)).choose_spec A

attribute [local irreducible] sourceRational

private def sourceIntegral [G : NativeGeometry.{u} l]
    (target : Realization l Y) (stage : StageAction l D hl P c)
    (E : Index l (PadicAlgCl l)) :
    sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) X ⋙
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ stage.system.functor ⋙ target.J) ⋙
        (sections l Y).mapDerivedCategory ≅
      (sfIntegralConstructible l (Coefficient l (PadicAlgCl l) E) X).ι ⋙
        PurCompactSupport.image (PurCompactSupport.completed l
          (Coefficient l (PadicAlgCl l) E)) c ⋙
        pbcDerivedExtend ((target.coefficient E).integralMap l Y) :=
  Functor.isoWhiskerLeft
      (sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) X)
      (Functor.isoWhiskerRight (sourceRational l D hl P c target stage E)
        (target.J ⋙ (sections l Y).mapDerivedCategory)) ≪≫
    Functor.isoWhiskerRight (finiteActionLocalization l D hl c E)
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := Y) E ⋙
        target.J ⋙ (sections l Y).mapDerivedCategory) ≪≫
    Functor.isoWhiskerLeft
      (sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c
        (Coefficient l (PadicAlgCl l) E)) (target.integral E) ≪≫
    Functor.isoWhiskerRight
      (sfQcqsCompactSupportRealization l (Coefficient l (PadicAlgCl l) E)
        D.k (PurCompactSupport.coefficientPrimeUnit l D hl) c).symm
      (pbcDerivedExtend ((target.coefficient E).integralMap l Y))

private def targetIntegral [G : NativeGeometry.{u} l]
    (source : Realization l X) (E : Index l (PadicAlgCl l)) :
    (sfIntegralConstructible l (Coefficient l (PadicAlgCl l) E) X).ι ⋙
        pbcDerivedExtend ((source.coefficient E).integralMap l X) ⋙
        PurCompactSupport.image (nativeCoefficients l) c ≅
      sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) X ⋙
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ source.J ⋙ actual l c) ⋙
        (sections l Y).mapDerivedCategory :=
  Functor.isoWhiskerRight (source.integral E).symm
      (PurCompactSupport.image (nativeCoefficients l) c) ≪≫
    Functor.isoWhiskerLeft
      (sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) X ⋙
        GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ source.J)
      (operationTransport l c).symm

attribute [local irreducible] sourceIntegral targetIntegral

private theorem threeArrow_identity
    {T : Type*} [Category T] {M₀ M₁ M₂ M₃ : T}
    (a₀ : M₀ ⟶ M₁) (a₁ : M₁ ⟶ M₂) (a₂ : M₂ ⟶ M₃) :
    a₀ ≫ 𝟙 M₁ ≫ a₁ ≫ a₂ = a₀ ≫ a₁ ≫ a₂ := by
  simp only [Category.id_comp]

private theorem rationalLeft_integral_component
    (E : Index l (PadicAlgCl l))
    (K : finiteTorConstructibleIntegralCategory l (Coefficient l (PadicAlgCl l) E) X) :
    HEq ((P.ring.rationalLeft c (finiteField l E)).hom.app
      ((sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) X).obj
        ((PurCompactSupport.finiteTorIntegralInclusion l
          (Coefficient l (PadicAlgCl l) E) X).obj K)))
      ((P.ring.rationalLeft c (finiteField l E)).hom.app
        ((rationalization l (ULift.{u} (PadicAlgCl l)) (finiteField l E) X).obj K)) := by
  rfl

set_option maxHeartbeats 400000 in
-- The component formulas compare cached presentations of the coefficient categories.
/-- Construct the two natural boundary isomorphisms and their prescribed components.
Source: Bhatt--Scholze, Definition 6.7.6, Proposition 6.8.14 and Remark 6.8.15.
Proof: on the source boundary, compose the stage inclusion and rationalLeft
comparisons, localization of the integral action, the target integral realization,
and derived extension of inverse sfQcqsCompactSupportRealization. On the target
boundary, compose compact support of the inverse source integral realization with
inverse operationTransport. Evaluate on each integral finite-Tor object. The stage
comparison gives the recorded rational arrow; the localization comparison has
identity components. Functoriality of identities gives the first three arrows and
the last two arrows, respectively. This construction contains no scalar mate.
(blueprint: lem-sf-native-integral-scalar-boundaries). -/
theorem native_integral_scalar_boundaries [G : NativeGeometry.{u} l]
    (source : Realization l X) (target : Realization l Y)
    (stage : StageAction l D hl P c) (E : Index l (PadicAlgCl l)) :
    ∃ (b :
    sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) X ⋙
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ stage.system.functor ⋙ target.J) ⋙
        (sections l Y).mapDerivedCategory ≅
      (sfIntegralConstructible l (Coefficient l (PadicAlgCl l) E) X).ι ⋙
        PurCompactSupport.image (PurCompactSupport.completed l
          (Coefficient l (PadicAlgCl l) E)) c ⋙
        pbcDerivedExtend ((target.coefficient E).integralMap l Y))
      (d :
    (sfIntegralConstructible l (Coefficient l (PadicAlgCl l) E) X).ι ⋙
        pbcDerivedExtend ((source.coefficient E).integralMap l X) ⋙
        PurCompactSupport.image (nativeCoefficients l) c ≅
      sfRationalConstructibleLocalization l (Coefficient l (PadicAlgCl l) E) X ⋙
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ source.J ⋙ actual l c) ⋙
        (sections l Y).mapDerivedCategory),
      ∀ K : finiteTorConstructibleIntegralCategory l
          (Coefficient l (PadicAlgCl l) E) X,
    let rationalInput :=
      (rationalization l (ULift.{u} (PadicAlgCl l)) (finiteField l E) X).obj K
    let input := (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj rationalInput
    ∃ (A B : sfRationalConstructibleCategory l
          (Coefficient l (PadicAlgCl l) E) Y) (r : A ⟶ B),
      HEq r ((P.ring.rationalLeft c (finiteField l E)).hom.app rationalInput) ∧
    ∃ (M₁ M₂ M₅ : DerivedCategory
          (proEtaleRingModules Y (ringSheaf l Y)))
      (a₀ : (sections l Y).mapDerivedCategory.obj
        ((sfRationalConstructibleLocalization l
          (Coefficient l (PadicAlgCl l) E) X ⋙
          (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ stage.system.functor ⋙ target.J)).obj
            ((PurCompactSupport.finiteTorIntegralInclusion l
              (Coefficient l (PadicAlgCl l) E) X).obj K)) ⟶ M₁)
      (a₁ : M₁ ⟶ M₂)
      (a₂ : M₂ ⟶ (PurCompactSupport.image (PurCompactSupport.completed l
          (Coefficient l (PadicAlgCl l) E)) c ⋙
          pbcDerivedExtend ((target.coefficient E).integralMap l Y)).obj K.obj)
      (a₄ : (pbcDerivedExtend ((source.coefficient E).integralMap l X) ⋙
          PurCompactSupport.image (nativeCoefficients l) c).obj K.obj ⟶ M₅)
      (a₅ : M₅ ⟶ (sections l Y).mapDerivedCategory.obj
        ((sfRationalConstructibleLocalization l
          (Coefficient l (PadicAlgCl l) E) X ⋙
          (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E ⋙ source.J ⋙ actual l c)).obj
            ((PurCompactSupport.finiteTorIntegralInclusion l
              (Coefficient l (PadicAlgCl l) E) X).obj K))),
      HEq a₀ ((sections l Y).mapDerivedCategory.map
        (target.J.map ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := Y) E).map r))) ∧
      HEq a₁ ((target.integral E).hom.app
          ((sfCompactSupportFiniteIntegralFunctor l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) c
            (Coefficient l (PadicAlgCl l) E)).obj
              ((PurCompactSupport.finiteTorIntegralInclusion l
                (Coefficient l (PadicAlgCl l) E) X).obj K))) ∧
      HEq a₂ ((pbcDerivedExtend ((target.coefficient E).integralMap l Y)).map
          ((sfQcqsCompactSupportRealization l (Coefficient l (PadicAlgCl l) E)
            D.k (PurCompactSupport.coefficientPrimeUnit l D hl) c).inv.app
              ((PurCompactSupport.finiteTorIntegralInclusion l
                (Coefficient l (PadicAlgCl l) E) X).obj K))) ∧
      HEq a₄ ((PurCompactSupport.image (nativeCoefficients l) c).map
          ((source.integral E).inv.app
            ((PurCompactSupport.finiteTorIntegralInclusion l
              (Coefficient l (PadicAlgCl l) E) X).obj K))) ∧
      HEq a₅ ((operationTransport l c).inv.app (source.J.obj input)) ∧
      b.hom.app ((PurCompactSupport.finiteTorIntegralInclusion l
          (Coefficient l (PadicAlgCl l) E) X).obj K) = a₀ ≫ a₁ ≫ a₂ ∧
      d.hom.app ((PurCompactSupport.finiteTorIntegralInclusion l
          (Coefficient l (PadicAlgCl l) E) X).obj K) = a₄ ≫ a₅ := by
  let b := sourceIntegral l D hl P c target stage E
  let d := targetIntegral l c source E
  refine ⟨b, d, fun K ↦ ?_⟩
  dsimp only [rationalization, Functor.comp_obj]
  let L := (PurCompactSupport.finiteTorIntegralInclusion l
    (Coefficient l (PadicAlgCl l) E) X).obj K
  let R := (sfRationalConstructibleLocalization l
    (Coefficient l (PadicAlgCl l) E) X).obj L
  let h := sourceRational_component l D hl P c target stage E R
  let A := h.choose
  let B := h.choose_spec.choose
  let r := h.choose_spec.choose_spec.choose
  have hr := h.choose_spec.choose_spec.choose_spec.1
  have h₀ := h.choose_spec.choose_spec.choose_spec.2
  let a₀ := (target.J ⋙ (sections l Y).mapDerivedCategory).map
    ((sourceRational l D hl P c target stage E).hom.app R)
  let a₁ := (target.integral E).hom.app
    ((sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c
      (Coefficient l (PadicAlgCl l) E)).obj L)
  let a₂ := (pbcDerivedExtend ((target.coefficient E).integralMap l Y)).map
    ((sfQcqsCompactSupportRealization l (Coefficient l (PadicAlgCl l) E)
      D.k (PurCompactSupport.coefficientPrimeUnit l D hl) c).inv.app L)
  let a₄ := (PurCompactSupport.image (nativeCoefficients l) c).map
    ((source.integral E).inv.app L)
  let a₅ := (operationTransport l c).inv.app
    (source.J.obj ((GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj R))
  refine ⟨A, B, r, ?_, ?_⟩
  · exact hr.trans (rationalLeft_integral_component l D hl P c E K)
  · let M₁ := (target.J ⋙ (sections l Y).mapDerivedCategory).obj
      ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := Y) E).obj
        ((sfCompactSupportFiniteFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c
          (Coefficient l (PadicAlgCl l) E)).obj R))
    let M₂ := (pbcDerivedExtend ((target.coefficient E).integralMap l Y)).obj
      ((sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c
        (Coefficient l (PadicAlgCl l) E)).obj L).obj
    let M₅ := (PurCompactSupport.image (nativeCoefficients l) c).obj
      ((sections l X).mapDerivedCategory.obj
        (source.J.obj ((GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := X) E).obj R)))
    refine ⟨M₁, M₂, M₅, ?_⟩
    refine ⟨a₀, ?_⟩
    refine ⟨a₁, a₂, a₄, a₅, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact h₀
    · exact HEq.rfl
    · exact HEq.rfl
    · exact HEq.rfl
    · exact HEq.rfl
    · dsimp only [b]
      unfold sourceIntegral
      change a₀ ≫ (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := Y) E ⋙ target.J ⋙
        (sections l Y).mapDerivedCategory).map
          ((finiteActionLocalization l D hl c E).hom.app L) ≫ a₁ ≫ a₂ = _
      erw [finiteActionLocalization_map_hom_app]
      exact threeArrow_identity a₀ a₁ a₂
    · dsimp only [d]
      unfold targetIntegral
      rfl

end WeilConjectures.LocallyFiniteAdicCompactSupport
