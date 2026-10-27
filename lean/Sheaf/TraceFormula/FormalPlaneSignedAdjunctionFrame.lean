/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Sheaf.TraceFormula.CompletedConormalDeterminantComparison
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # The signed adjunction frame of a completed plane equation

Source: Stacks Project, Duality, Tags 0E9Y and 0E9Z, relation-first determinant formula;
the completed specialization and inverse-frame refinement in the DAG
(blueprint: lem-trf-formal-plane-signed-adjunction-frame).

The affine dictionary represents the formal determinant module by the global sections
of its associated sheaf. Its dual factor is the dual of the first exterior power of the
conormal module, canonically the dual of the conormal module itself. Tensor factors put
the coefficient ring first. The degree-one exterior equivalence is explicit at the generic
point. Regularity of the single equation is a conclusion, not an input.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

open CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A plane equation presenting the complete local algebra. Surjectivity and the kernel
identity encode the specified quotient isomorphism. No regularity proof is included.
Source: Stacks, 0E9Y and 0E9Z, completed plane specialization
(blueprint: lem-trf-formal-plane-signed-adjunction-frame). -/
structure FormalPlaneEquation (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (a : Ideal R) where
  equation : MvPowerSeries (Fin 2) k
  nonzero : equation ≠ 0
  in_variables : equation ∈ Ideal.span
    (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) k))
  quotient : MvPowerSeries (Fin 2) k →ₐ[k] R
  surjective : Function.Surjective quotient
  kernel : RingHom.ker quotient = Ideal.span (Set.range (fun _ : Fin 1 ↦ equation))
  local_hom : IsLocalHom quotient.toRingHom
  continuous : @Continuous _ _
    (@MvPowerSeries.WithPiTopology.instTopologicalSpace (Fin 2) k ⊤)
    a.adicTopology quotient

/-- Insert the proved regularity of the equation into the existing formal-presentation
interface; the quotient and equation are unchanged.
Source: Stacks, 0E9Y and 08SL
(blueprint: lem-trf-formal-plane-signed-adjunction-frame). -/
def FormalPlaneEquation.presentation {k R : Type u}
    [Field k] [CommRing R] [Algebra k R] {a : Ideal R}
    (P : FormalPlaneEquation k R a)
    (h : RingTheory.Sequence.IsRegular (MvPowerSeries (Fin 2) k)
      (List.ofFn (fun _ : Fin 1 ↦ P.equation))) :
    CompletedConormalFormalPresentation k R a 1 where
  n := 2
  c := 1
  rank_eq := rfl
  quotient := P.quotient
  surjective := P.surjective
  local_hom := P.local_hom
  continuous := P.continuous
  equations := fun _ ↦ P.equation
  in_variables := fun _ ↦ P.in_variables
  regular := h
  kernel := P.kernel

section Frame

variable {k S A : Type u} [Field k] [CommRing S] [CommRing A] [IsLocalRing A]
variable [Algebra k S] [Algebra S A] [Algebra k A] [IsScalarTower k S A]
variable [∀ X : Scheme.{u}, HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
variable {J : FlatLCIAdjunctionSystem (Spec.map (CommRingCat.ofHom (algebraMap k S))) 1}
variable (C : CompletedConormalDeterminantComparison (A := A) J)
variable (P : FormalPlaneEquation k (Algebra.LocalCompletion A)
  ((IsLocalRing.maximalIdeal A).map (algebraMap A (Algebra.LocalCompletion A))))
variable (h : RingTheory.Sequence.IsRegular (MvPowerSeries (Fin 2) k)
  (List.ofFn (fun _ : Fin 1 ↦ P.equation)))

/-- The formal determinant module in the affine module/sheaf dictionary, with its actual
conormal quotient and coordinate module. Source: Stacks, 0E9Y and 0E9Z
(blueprint: lem-trf-formal-plane-signed-adjunction-frame). -/
abbrev formalPlaneDeterminantModule :=
  (moduleSpecΓFunctor (R := CommRingCat.of (Algebra.LocalCompletion A))).obj
    ((P.presentation h).model (C.formal (P.presentation h)).differential).line

/-- The canonical completed comparison, transported through the affine equivalence.
Source: Stacks, 0E9Y and 0E9Z, and the completed conormal comparison
(blueprint: lem-trf-formal-plane-signed-adjunction-frame). -/
def formalPlaneComparison :
    completedConormalSource (A := A) J ≃ₗ[Algebra.LocalCompletion A]
      formalPlaneDeterminantModule C P h :=
  (((tilde.toTildeΓNatIso (R := CommRingCat.of (Algebra.LocalCompletion A))).app
    (completedConormalSource (A := A) J)) ≪≫
    (moduleSpecΓFunctor (R := CommRingCat.of (Algebra.LocalCompletion A))).mapIso
      (C.comparison (P.presentation h))).toLinearEquiv

/-- The dual relation factor, represented by a section of the actual sheaf dual.
Source: Stacks, 0E9Y, dual relation preceding the coordinate wedge
(blueprint: lem-trf-formal-plane-signed-adjunction-frame). -/
abbrev formalPlaneDualSection :=
  Γ(SheafOfModules.homObj
    (R := (Spec (CommRingCat.of (Algebra.LocalCompletion A))).sheaf)
    (Scheme.Modules.exteriorSheaf
      ((tilde.functor (CommRingCat.of (Algebra.LocalCompletion A))).obj
        (ModuleCat.of (Algebra.LocalCompletion A) (P.presentation h).extension.Cotangent)) 1)
    (SheafOfModules.unit (Spec (CommRingCat.of (Algebra.LocalCompletion A))).ringCatSheaf), ⊤)

/-- Evaluation of the dual relation section on the wedge consisting of the single relation.
Source: Stacks, 0E9Y (blueprint: lem-trf-formal-plane-signed-adjunction-frame). -/
def IsFormalPlaneDualGenerator (α : formalPlaneDualSection P h) : Prop :=
  α.app (op (Over.mk (𝟙 (⊤ : (Spec (CommRingCat.of (Algebra.LocalCompletion A))).Opens))))
    (Scheme.Modules.exteriorSheafSection _ 1 ⊤ (fun j ↦
      completedConormalSection (ModuleCat.of (Algebra.LocalCompletion A)
        (P.presentation h).extension.Cotangent) ((C.formal (P.presentation h)).basis j))) =
      (1 : Γ(Spec (CommRingCat.of (Algebra.LocalCompletion A)), ⊤))

/-- The positively oriented tensor `f-bar-dual tensor (dx wedge dy)`.
Source: Stacks, 0E9Y (blueprint: lem-trf-formal-plane-signed-adjunction-frame). -/
def formalPlaneOrientation (α : formalPlaneDualSection P h) :
    formalPlaneDeterminantModule C P h :=
  @id (formalPlaneDeterminantModule C P h)
    (Scheme.Modules.tmulSection (X := Spec (CommRingCat.of (Algebra.LocalCompletion A)))
      (N := Scheme.Modules.exteriorSheaf
        ((tilde.functor (CommRingCat.of (Algebra.LocalCompletion A))).obj
          (ModuleCat.of (Algebra.LocalCompletion A) (Fin 2 → Algebra.LocalCompletion A))) 2)
      α (Scheme.Modules.exteriorSheafSection _ 2 ⊤ (fun i ↦
        completedConormalSection
          (ModuleCat.of (Algebra.LocalCompletion A) (Fin 2 → Algebra.LocalCompletion A))
          (Pi.single i 1))))

end Frame

/-- The image of a completed differential in its field-valued fibre.
Source: Stacks, 0C4D and 0E9Y
(blueprint: lem-trf-formal-plane-signed-adjunction-frame). -/
def formalPlaneCoordinate {k A L : Type u}
    [Field k] [CommRing A] [Algebra k A] [IsLocalRing A]
    [Field L] [Algebra A L] [Algebra (Algebra.LocalCompletion A) L]
    [IsScalarTower A (Algebra.LocalCompletion A) L]
    (D : Derivation k (Algebra.LocalCompletion A) (Algebra.CompletedDifferentials k A))
    (P : FormalPlaneEquation k (Algebra.LocalCompletion A)
      ((IsLocalRing.maximalIdeal A).map (algebraMap A (Algebra.LocalCompletion A))))
    (i : Fin 2) : L ⊗[A] KaehlerDifferential k A :=
  TensorProduct.map
    (IsScalarTower.toAlgHom A (Algebra.LocalCompletion A) L).toLinearMap
    (LinearMap.id : KaehlerDifferential k A →ₗ[A] KaehlerDifferential k A)
    (D (P.quotient (MvPowerSeries.X i)))

/-- The actual coefficient of the formal partial derivative in the chosen field.
Source: Stacks, 0E9Y (blueprint: lem-trf-formal-plane-signed-adjunction-frame). -/
def formalPlanePartial {k R L : Type u} [Field k] [CommRing R] [Algebra k R]
    [Field L] [Algebra R L] {a : Ideal R} (P : FormalPlaneEquation k R a) (i : Fin 2) : L :=
  algebraMap R L (P.quotient (MvPowerSeries.pderiv k i P.equation))

/-- Extension of a completed adjunction element to the generic field, using tensor
associativity in the coefficient-first convention. Source: Stacks, 0E9Z
(blueprint: lem-trf-formal-plane-signed-adjunction-frame). -/
def formalPlaneGenericSource {k S A L : Type u}
    [Field k] [CommRing S] [CommRing A] [IsLocalRing A] [Field L]
    [Algebra k S] [Algebra S A] [Algebra S L]
    [Algebra (Algebra.LocalCompletion A) L]
    [IsScalarTower S (Algebra.LocalCompletion A) L]
    (J : FlatLCIAdjunctionSystem (Spec.map (CommRingCat.ofHom (algebraMap k S))) 1)
    (t : completedConormalSource (A := A) J) : L ⊗[S] completedConormalAdjunctionSections J :=
  TensorProduct.map
    (IsScalarTower.toAlgHom S (Algebra.LocalCompletion A) L).toLinearMap
    (LinearMap.id : completedConormalAdjunctionSections J →ₗ[S]
      completedConormalAdjunctionSections J) t

/-- Signed plane adjunction and its field-valued inverse fractions. All presentations use
one normalized comparison system; its algebraic and formal change maps are those of the
completed-conormal theorem, including its three-presentation composition law.

Source: Stacks, Duality, 0E9Y and 0E9Z, completed plane specialization
(blueprint: lem-trf-formal-plane-signed-adjunction-frame).

Proof:
1. Lowest nonzero homogeneous parts show that the power series ring is a domain. Thus
   the nonzero equation is regular; being in the variable ideal makes its quotient nonzero.
   Cancellation of f in hf = uf squared proves that its conormal class is a basis.
2. Apply lem-trf-completed-conormal-determinant-comparison with d=1, n=2, c=1. Its hypotheses
   hold by reducedness, finite type, pure dimension, lci, rational residue field and the
   algebraically closed (hence perfect) coefficient field. Its comparison uses the adjunction
   line of lem-trf-flat-lci-canonical-adjunction. The negative of the positive tensor orientation
   has a unique inverse image eta, and eta is a basis.
3. The derivation is the unique continuous extension from
   lem-trf-completion-kahler-differential-comparison. The general comparison's generic
   normalization supplies the exact conormal sequence, without assuming a flat field map.
4. Its relation-first wedge sends ex to minus b times the positive orientation and ey to
   a times that orientation. Since Phi(eta) is the negative orientation, these are respectively
   b Phi(eta) and minus a Phi(eta). Adding a relation to a lift contributes its self-wedge, zero.
5. Apply the inverse determinant comparison to get ex/b and minus ey/a. The image of the
   base-changed basis eta under the smooth isomorphism is nonzero, proving both nonvanishing
   claims. When both coefficients are nonzero the fractions agree by a ex + b ey = 0.
6. The comparison system's algebraic and continuous formal change clauses give compatibility.
   Its formalComparison maps compose through their common algebraic source. Its generic
   normalization identifies every presentation's inverse with the same algebraic smooth map.
-/
theorem exists_formalPlaneSignedAdjunctionFrame
    {k S : Type u} [Field k] [IsAlgClosed k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [_root_.IsReduced S]
    [∀ X : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (hpure : (Spec (CommRingCat.of S)).IsPureDimension 1)
    (hlci : Algebra.IsLocalCompleteIntersection k S)
    (p : Ideal S) [p.IsMaximal] (hresidue : Nonempty ((S ⧸ p) ≃ₐ[k] k))
    [_root_.IsReduced (Algebra.LocalCompletion (Localization.AtPrime p))]
    (J : FlatLCIAdjunctionSystem (Spec.map (CommRingCat.ofHom (algebraMap k S))) 1)
    (hJ : J.IsNormalized) :
    ∃ C : CompletedConormalDeterminantComparison (A := Localization.AtPrime p) J,
      (∀ D : Derivation k (Algebra.LocalCompletion (Localization.AtPrime p))
          (Algebra.CompletedDifferentials k (Localization.AtPrime p)),
        Algebra.IsCompletedDifferentialExtension k (Localization.AtPrime p) D → D = C.derivation) ∧
      ∀ P : FormalPlaneEquation k (Algebra.LocalCompletion (Localization.AtPrime p))
          ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
            (algebraMap (Localization.AtPrime p)
              (Algebra.LocalCompletion (Localization.AtPrime p)))),
        ∃ h : RingTheory.Sequence.IsRegular (MvPowerSeries (Fin 2) k)
            (List.ofFn (fun _ : Fin 1 ↦ P.equation)),
          (∃ q : (P.presentation h).extension.ker,
            q.val = P.equation ∧
              (C.formal (P.presentation h)).basis (0 : Fin 1) = Algebra.Extension.Cotangent.mk q) ∧
          ∃ α : formalPlaneDualSection P h,
            IsFormalPlaneDualGenerator C P h α ∧
            ∃ B : Module.Basis (Fin 1) (Algebra.LocalCompletion (Localization.AtPrime p))
                (completedConormalSource (A := Localization.AtPrime p) J),
              formalPlaneComparison C P h (B 0) = -formalPlaneOrientation C P h α ∧
              (∀ η : completedConormalSource (A := Localization.AtPrime p) J,
                formalPlaneComparison C P h η = -formalPlaneOrientation C P h α → η = B 0) ∧
              ∀ (L : Type u) [Field L] [Algebra (Localization.AtPrime p) L] [Algebra S L]
                [Algebra (Algebra.LocalCompletion (Localization.AtPrime p)) L]
                [IsScalarTower S (Localization.AtPrime p) L]
                [IsScalarTower (Localization.AtPrime p)
                  (Algebra.LocalCompletion (Localization.AtPrime p)) L]
                [IsScalarTower S (Algebra.LocalCompletion (Localization.AtPrime p)) L],
                IsCompletedConormalGeneric (k := k) (S := S)
                  (A := Localization.AtPrime p) (L := L) →
                ∃ γ : (L ⊗[S] completedConormalAdjunctionSections J) ≃ₗ[L]
                    L ⊗[Localization.AtPrime p] KaehlerDifferential k (Localization.AtPrime p),
                  IsCompletedConormalSmoothComparison J
                    (fun s ↦ (exteriorPower.oneEquiv L _).symm (γ ((1 : L) ⊗ₜ[S] s))) ∧
                  ∀ (_hab : formalPlanePartial (L := L) P 0 ≠ 0 ∨
                    formalPlanePartial (L := L) P 1 ≠ 0),
                  Function.Injective ((P.presentation h).genericJacobian (L := L)) ∧
                  Function.Exact ((P.presentation h).genericJacobian (L := L))
                    ((C.formal (P.presentation h)).genericAugmentation (L := L)) ∧
                  Function.Surjective
                    ((C.formal (P.presentation h)).genericAugmentation (L := L)) ∧
                  ∃ δ : (L ⊗[Localization.AtPrime p]
                      KaehlerDifferential k (Localization.AtPrime p)) ≃ₗ[L]
                      L ⊗[Algebra.LocalCompletion (Localization.AtPrime p)]
                        formalPlaneDeterminantModule C P h,
                    IsCompletedConormalGenericDeterminant (C.formal (P.presentation h))
                      ((exteriorPower.oneEquiv L _).trans δ) ∧
                    (∀ t : completedConormalSource (A := Localization.AtPrime p) J,
                      δ (γ (formalPlaneGenericSource J t)) =
                        (1 : L) ⊗ₜ[Algebra.LocalCompletion (Localization.AtPrime p)]
                          formalPlaneComparison C P h t) ∧
                    δ (formalPlaneCoordinate (L := L) C.derivation P 0) =
                      formalPlanePartial (L := L) P 1 •
                        ((1 : L) ⊗ₜ[Algebra.LocalCompletion (Localization.AtPrime p)]
                          formalPlaneComparison C P h (B 0)) ∧
                    δ (formalPlaneCoordinate (L := L) C.derivation P 1) =
                      -formalPlanePartial (L := L) P 0 •
                        ((1 : L) ⊗ₜ[Algebra.LocalCompletion (Localization.AtPrime p)]
                          formalPlaneComparison C P h (B 0)) ∧
                    (formalPlanePartial (L := L) P 1 ≠ 0 →
                      γ (formalPlaneGenericSource J (B 0)) =
                        (formalPlanePartial (L := L) P 1)⁻¹ •
                          formalPlaneCoordinate (L := L) C.derivation P 0 ∧
                        (formalPlanePartial (L := L) P 1)⁻¹ •
                          formalPlaneCoordinate (L := L) C.derivation P 0 ≠ 0) ∧
                    (formalPlanePartial (L := L) P 0 ≠ 0 →
                      γ (formalPlaneGenericSource J (B 0)) =
                        -(formalPlanePartial (L := L) P 0)⁻¹ •
                          formalPlaneCoordinate (L := L) C.derivation P 1 ∧
                        -(formalPlanePartial (L := L) P 0)⁻¹ •
                          formalPlaneCoordinate (L := L) C.derivation P 1 ≠ 0) := by
  sorry

end AlgebraicGeometry
