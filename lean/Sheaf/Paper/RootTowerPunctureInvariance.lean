/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.Paper.StrictLocalKummerTameModule
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses

/-! # Puncturing a full parameter-root tower

Source: blueprint main-20261015, direct-image proof paragraph (3), agent-extracted
full-root-tower calculation (blueprint: lem-sfb-root-tower-puncture-invariance).
The coefficient is the all-continuous-map condensed ring, including for an incomplete
algebraic closure. No finite-subextension coefficient convention is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The open obtained by inverting exactly the selected coordinate product.
Source: direct-image proof paragraph (3), full-root puncture calculation
(blueprint: lem-sfb-root-tower-puncture-invariance). -/
def rootCoordinateOpen (p : ℕ) {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (s : Finset (Fin r)) :
    (Spec (.of (tameRootAlgebra p t))).Opens :=
  PrimeSpectrum.basicOpen (algebraMap R (tameRootAlgebra p t) (∏ i ∈ s, t i))

/-- Pullback of an indicated open to the actual profinite test object.
Source: direct-image proof paragraph (3), the definition of j_{A,P}
(blueprint: lem-sfb-root-tower-puncture-invariance). -/
def rootTestOpen {T : Scheme.{u}} (V : T.Opens) (P : Profinite.{u}) :
    ((profiniteToProEtOf T).obj P).left.Opens :=
  (TopologicalSpace.Opens.map ((profiniteToProEtOf T).obj P).hom.base).obj V

namespace CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The actual derived unit, with the canonical exact pullback as left adjoint.
Source: sk-def-sfb-module-derived-pushpull and direct-image proof paragraph (3)
(blueprint: lem-sfb-root-tower-puncture-invariance). -/
def punctureDerivedAdjunction {V T : Scheme.{u}} (j : V ⟶ T) :=
  (derivedUpperStarLowerStarAdjunction Λ j).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory Λ j)

/-- The canonical termwise pullback comparison of a commutative square.
Source: direct-image proof paragraph (3), unit base-change calculation
(blueprint: lem-sfb-root-tower-puncture-invariance). -/
def punctureSquareComparison {V T V' T' : Scheme.{u}}
    (j : V ⟶ T) (j' : V' ⟶ T') (g : T' ⟶ T) (gV : V' ⟶ V)
    (w : gV ≫ j = j' ≫ g) :
    (upperStar Λ g).mapDerivedCategory ⋙ (upperStar Λ j').mapDerivedCategory ≅
      (upperStar Λ j).mapDerivedCategory ⋙ (upperStar Λ gV).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((upperStarComp Λ j' g).symm ≪≫
        eqToIso (congrArg (upperStar Λ) w.symm) ≪≫ upperStarComp Λ gV j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The exchange is the adjunct of pulled-back counit, including square transport.
Source: direct-image proof paragraph (3), step 6 of the node proof
(blueprint: lem-sfb-root-tower-puncture-invariance). -/
def punctureDerivedExchange {V T V' T' : Scheme.{u}}
    (j : V ⟶ T) (j' : V' ⟶ T') (g : T' ⟶ T) (gV : V' ⟶ V)
    (w : gV ≫ j = j' ≫ g)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
      (condensedRingObj Λ V))) :=
  (punctureDerivedAdjunction Λ j').homEquiv _ _
    ((punctureSquareComparison Λ j j' g gV w).hom.app
        ((moduleObjectDerivedPushforward Λ j).obj K) ≫
      (upperStar Λ gV).mapDerivedCategory.map
        ((punctureDerivedAdjunction Λ j).counit.app K))

/-- Normalized exchange on the target of the unit: its codomain is Rj'_*j'^*g^*K.
Source: direct-image proof paragraph (3), unit and inverse-unit compatibility
(blueprint: lem-sfb-root-tower-puncture-invariance). -/
def punctureUnitExchange {V T V' T' : Scheme.{u}}
    (j : V ⟶ T) (j' : V' ⟶ T') (g : T' ⟶ T) (gV : V' ⟶ V)
    (w : gV ≫ j = j' ≫ g)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))) :=
  punctureDerivedExchange Λ j j' g gV w ((upperStar Λ j).mapDerivedCategory.obj K) ≫
    (moduleObjectDerivedPushforward Λ j').map
      ((punctureSquareComparison Λ j j' g gV w).inv.app K)

/-- Canonical identification of pullback along the identity with the identity functor.
Source: direct-image proof paragraph (3), empty-coordinate normalization
(blueprint: lem-sfb-root-tower-puncture-invariance). -/
def punctureIdentityLeftComparison (T : Scheme.{u}) :
    (upperStar Λ (𝟙 T)).mapDerivedCategory ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso (upperStarId Λ T) ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The identity pushforward comparison is the right mate of the identity pullback comparison.
Source: direct-image proof paragraph (3), empty-coordinate normalization
(blueprint: lem-sfb-root-tower-puncture-invariance). -/
def punctureIdentityRightComparison (T : Scheme.{u}) :
    moduleObjectDerivedPushforward Λ (𝟙 T) ≅ 𝟭 _ :=
  conjugateIsoEquiv (punctureDerivedAdjunction Λ (𝟙 T)) Adjunction.id
    (punctureIdentityLeftComparison Λ T).symm

/-- The identity-open unit is literally the identity after the canonical identity comparisons.
Source: direct-image proof paragraph (3), A empty, including r zero
(blueprint: lem-sfb-root-tower-puncture-invariance). -/
def PunctureIdentityAssertions : Prop :=
  ∀ (T : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))),
    (punctureDerivedAdjunction Λ (𝟙 T)).unit.app K ≫
      (punctureIdentityRightComparison Λ T).hom.app
        ((upperStar Λ (𝟙 T)).mapDerivedCategory.obj K) ≫
      (punctureIdentityLeftComparison Λ T).hom.app K = 𝟙 K

/-- The invertible actual unit and its functoriality, expressed using its uniquely determined
inverse. The square equations live on T' itself, so include profinite family actions.
Source: direct-image proof paragraph (3), steps 5--7
(blueprint: lem-sfb-root-tower-puncture-invariance). -/
def PunctureUnitAssertions {V T : Scheme.{u}} (j : V ⟶ T)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))) : Prop :=
  ∃ e : K ≅ (moduleObjectDerivedPushforward Λ j).obj
      ((upperStar Λ j).mapDerivedCategory.obj K),
    e.hom = (punctureDerivedAdjunction Λ j).unit.app K ∧
    (∀ (K' : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T))) (f : K ⟶ K')
      (e' : K' ≅ (moduleObjectDerivedPushforward Λ j).obj
        ((upperStar Λ j).mapDerivedCategory.obj K')),
      e'.hom = (punctureDerivedAdjunction Λ j).unit.app K' →
        f ≫ e'.hom = e.hom ≫ (moduleObjectDerivedPushforward Λ j).map
          ((upperStar Λ j).mapDerivedCategory.map f) ∧
        e.inv ≫ f = (moduleObjectDerivedPushforward Λ j).map
          ((upperStar Λ j).mapDerivedCategory.map f) ≫ e'.inv) ∧
    ∀ (V' T' : Scheme.{u}) (j' : V' ⟶ T') (g : T' ⟶ T) (gV : V' ⟶ V)
      (w : gV ≫ j = j' ≫ g),
      (upperStar Λ g).mapDerivedCategory.map e.hom ≫
          punctureUnitExchange Λ j j' g gV w K =
        (punctureDerivedAdjunction Λ j').unit.app
          ((upperStar Λ g).mapDerivedCategory.obj K) ∧
      ∀ e' : (upperStar Λ g).mapDerivedCategory.obj K ≅
          (moduleObjectDerivedPushforward Λ j').obj
            ((upperStar Λ j').mapDerivedCategory.obj
              ((upperStar Λ g).mapDerivedCategory.obj K)),
        e'.hom = (punctureDerivedAdjunction Λ j').unit.app
            ((upperStar Λ g).mapDerivedCategory.obj K) →
          IsIso (punctureUnitExchange Λ j j' g gV w K) ∧
          (upperStar Λ g).mapDerivedCategory.map e.inv =
            punctureUnitExchange Λ j j' g gV w K ≫ e'.inv

end CondensedRing

/-- Puncturing selected coordinates preserves the supplied lisse module on the full tower,
including after affine-chart base change and arbitrary profinite parametrization.
Source: direct-image proof paragraph (3), agent-extracted full-root calculation
(blueprint: lem-sfb-root-tower-puncture-invariance).

Proof: (1) alpha is invertible by lem-sfb-alpha-iso; the transport equivalence of
lem-sfb-internal-module-operations-transport identifies exact internal pullback and
its specified adjunction with the section-ring model. (2) Absorb P in U[P]; tensoring
the root presentation with LC(P,Z) identifies T[P] and all its coordinate opens.
Lisse trivializations pull back. (3) For one new coordinate use
lem-sfb-root-coordinate-supported-vanishing on the original supplied module restricted
to the preceding puncture. The principal complement is quasi-compact, so clause 4 of
det-lem-formal-closed-support-adjunction makes the actual open unit invertible.
(4) Induct on the finite set of inverted coordinates. The normalized composition of
lem-sfb-derived-composition-adjunction-normalization identifies each successive unit
with the composite of the previous unit and the pushed-forward next unit.
The Grothendieck hypotheses follow from lem-weil-pbc-ring-sheaves-grothendieck via
step (1). Every enumeration gives the same specified unit. (5) Unit naturality gives
the module-map equation; composing with inverses gives its inverse equation.
(6) The exchange is the adjunct of the pulled-back counit. Transposing exchange after
the pulled-back unit gives the identity by the triangle identity, hence the new unit.
Invertible units then imply invertible exchange and the inverse equation.
(7) Apply that calculation to the actual Q-parametrized action morphism and the supplied
module-action isomorphism; no evaluation at points of Q occurs. The same holds on
T[P times Q]. (8) Empty coordinates give the identity open, with the identity normalized
unit. Empty charts or parameters and rank-zero modules give zero objects and identities.
No completeness of the algebraic closure or positive-rank assumption is used. -/
theorem rootTower_puncture_invariance
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (E Ω : Type u) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] [NormedField Ω] [NormedAlgebra E Ω]
    [IsAlgClosure E Ω]
    (Y : Scheme.{u}) (y : Y ⟶ Spec (.of k)) [LocallyOfFiniteType y] [QuasiCompact y]
    [IsSeparated y] (hY : IsRegularScheme Y)
    (A : Type u) [CommRing A] (b : Spec (.of A) ⟶ Y) [Etale b]
    (r : ℕ) (t : Fin r → A) (H : (Spec (.of A)).IdealSheafData)
    (hH : IsStrictNormalCrossingsBoundary H)
    (hproduct : H = Scheme.IdealSheafData.ofIdealTop
      (Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of A)).inv (∏ i, t i)}))
    (hbranches : Set.range (fun i : Fin r ↦ PrimeSpectrum.zeroLocus ({t i} : Set A)) =
      Set.image (Set.image Subtype.val) (irreducibleComponents (H.support : Set (Spec (.of A)))))
    (R : Type u) [CommRing R] (a : A →+* R)
    [WeaklyEtale (Spec.map (CommRingCat.ofHom a))] :
    (∀ (N : Mod
      (Sheaf (Scheme.ProEt.topology (Spec (.of (tameRootAlgebra p (fun i ↦ a (t i))))))
        Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E)
        (Spec (.of (tameRootAlgebra p (fun i ↦ a (t i))))))),
      IsLisseCoefficientModule (Profinite.continuousCoefficientRingObj E) N →
      ∀ (s : Finset (Fin r)) (U' : Scheme.{u}) (v : U' ⟶ Spec (.of R)) [WeaklyEtale v]
        (P : Profinite.{u}),
        CondensedRing.PunctureUnitAssertions (Profinite.continuousCoefficientRingObj E)
          (rootTestOpen
            ((TopologicalSpace.Opens.map
              (pullback.fst (Spec.map (CommRingCat.ofHom
                (algebraMap R (tameRootAlgebra p (fun i ↦ a (t i)))))) v).base).obj
                (rootCoordinateOpen p (fun i ↦ a (t i)) s)) P).ι
          ((DerivedCategory.singleFunctor _ 0).obj
            ((CondensedRing.upperStar (Profinite.continuousCoefficientRingObj E)
              (((profiniteToProEtOf _).obj P).hom ≫
                pullback.fst (Spec.map (CommRingCat.ofHom
                  (algebraMap R (tameRootAlgebra p (fun i ↦ a (t i)))))) v)).obj N))) ∧
    (∀ (N : Mod
      (Sheaf (Scheme.ProEt.topology (Spec (.of (tameRootAlgebra p (fun i ↦ a (t i))))))
        Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj Ω)
        (Spec (.of (tameRootAlgebra p (fun i ↦ a (t i))))))),
      IsLisseCoefficientModule (Profinite.continuousCoefficientRingObj Ω) N →
      ∀ (s : Finset (Fin r)) (U' : Scheme.{u}) (v : U' ⟶ Spec (.of R)) [WeaklyEtale v]
        (P : Profinite.{u}),
        CondensedRing.PunctureUnitAssertions (Profinite.continuousCoefficientRingObj Ω)
          (rootTestOpen
            ((TopologicalSpace.Opens.map
              (pullback.fst (Spec.map (CommRingCat.ofHom
                (algebraMap R (tameRootAlgebra p (fun i ↦ a (t i)))))) v).base).obj
                (rootCoordinateOpen p (fun i ↦ a (t i)) s)) P).ι
          ((DerivedCategory.singleFunctor _ 0).obj
            ((CondensedRing.upperStar (Profinite.continuousCoefficientRingObj Ω)
              (((profiniteToProEtOf _).obj P).hom ≫
                pullback.fst (Spec.map (CommRingCat.ofHom
                  (algebraMap R (tameRootAlgebra p (fun i ↦ a (t i)))))) v)).obj N))) ∧
    CondensedRing.PunctureIdentityAssertions (Profinite.continuousCoefficientRingObj E) ∧
    CondensedRing.PunctureIdentityAssertions (Profinite.continuousCoefficientRingObj Ω) := by
  sorry

end AlgebraicGeometry.ProEtale
