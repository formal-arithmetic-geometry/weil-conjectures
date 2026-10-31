/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalSheafExt
public import WeilConjectures.AlgebraicGeometry.Kummer.KummerStrictAdjunctCompatibility
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalFiniteArrowLift

/-! # Strict Kummer target and functorial finite reduction
Source: diagonal tower system proof, target paragraph of step (3) and step (4).
(blueprint: lem-sfb-kummer-strict-target-transport). -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] CategoryTheory.Abelian.Ext
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance 11000] kummerModuleHasExt kummerAbHasExt

attribute [local irreducible] DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ diagonalDerivedSingleCounit
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison cartierRootsIso
  cartierEtaleKummerUnit cartierProKummerUnit cartierProIntegralGenerator cartierProRootMap
  cartierReducedEtale cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierResidueReducedPro diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary

/-- The negative Yoneda product of two degree-one classes, with its group
structure shared by name.
Source: the negative target comparison in the diagonal tower proof, step (4)
(blueprint: lem-sfb-kummer-strict-target-transport).
This is the actual negative product; its definition chooses no auxiliary data. -/
@[irreducible] def negativeExtProduct
    {A : Type*} [Category A] [Abelian A] [HasExt.{w} A]
    {S M P : A} (f : Ext S M 1) (κ : Ext M P 1) : Ext S P 2 :=
  -(f.comp κ rfl)

/-- The full scalar adjunct of a residue-linear degree-two class.
Source: derived scalar-adjunction naturality in the diagonal tower proof, step (4)
(blueprint: lem-sfb-kummer-strict-target-transport).
This is the actual forgetful image followed by precomposition with the generator;
its real body is shared until the Cartier sign calculation unfolds it. -/
@[irreducible] def kummerScalarAdjunct
    {A : Type*} [Category A] [Abelian A] [HasExt.{w} A]
    {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]
    (V : C ⥤ A) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    {S : A} {Q P : C} (g : S ⟶ V.obj Q) (e : Ext Q P 2) : Ext S (V.obj P) 2 :=
  (Ext.mk₀ g).comp (e.mapExactFunctor V) (zero_add 2)

/-- The scalar-adjunct and evaluation equations for a reduced degree-one arrow.
This formula uses abstract categories so that its coefficient constructions are
shared parameters rather than repeatedly unfolded terms.
Source: diagonal tower system proof, step (4), derived-adjunction naturality
(blueprint: lem-sfb-kummer-strict-target-transport). -/
@[irreducible] def KummerArrowTransport
    (ℓ : ℕ) {A : Type*} [Category A] [abA : Abelian A] [hA : HasExt.{w} A]
    {B : Type*} [Category B] [abB : Abelian B] [hB : HasExt.{w} B]
    {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    (L : A ⥤ B) (U : B ⥤ A) (ad : L ⊣ U) (D : DiagonalDerivedReduction ℓ L)
    (F : C ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (V : C ⥤ A) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (n : ℕ) (P : C) (M : A) (κ : Ext M (V.obj P) 1)
    (H : ℕᵒᵖ ⥤ B)
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj M)⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (t : H.obj (op n) ≅ F.obj P) : Prop :=
  ∀ (S : A)
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj S) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj S)),
    a.hom = diagonalDerivedSingleCounit ℓ L D S →
    ∀ (Q : C) (s : (D.ordinary.E.obj S).obj (op n) ≅ F.obj Q) (g : S ⟶ V.obj Q),
      HEq (ad.unit.app S ≫ U.map ((D.ordinary.π n).app S ≫ s.hom)) g →
      ∀ f : Ext S M 1, ∃ e : Ext Q P 2,
        kummerScalarAdjunct V g e = negativeExtProduct f κ ∧
        (Ext.mk₀ s.inv).comp
            (((Ext.homEquiv.symm (a.inv ≫ D.T.map f.hom ≫ b.hom)).mapExactFunctor
              ((evaluation ℕᵒᵖ B).obj (op n))).comp
              (Ext.mk₀ t.hom) (add_zero 2)) (zero_add 2) = exactFunctorExtImage F e

/-- Strict target data for Kummer transport, shared by the scheme calculation
and its formal assembly. All object and isomorphism fields are actual data.
Source: diagonal tower system proof, step (3), target paragraph
(blueprint: lem-sfb-kummer-strict-target-transport). -/
structure KummerTargetData
    (ℓ : ℕ) {A : Type*} [Category A] [abA : Abelian A] [hA : HasExt.{w} A]
    {B : Type*} [Category B] [abB : Abelian B] [hB : HasExt.{w} B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    (L : A ⥤ B) (U : B ⥤ A) (ad : L ⊣ U) (D : DiagonalDerivedReduction ℓ L)
    (C : ℕ → Type*) [catC : ∀ n, Category (C n)] [abC : ∀ n, Abelian (C n)]
    [hC : ∀ n, HasExt.{w} (C n)]
    (F : ∀ n, C n ⥤ B) [Fadd : ∀ n, (F n).Additive]
    [Flim : ∀ n, PreservesFiniteLimits (F n)]
    [Fcolim : ∀ n, PreservesFiniteColimits (F n)]
    (V : ∀ n, C n ⥤ A) [Vadd : ∀ n, (V n).Additive]
    [Vlim : ∀ n, PreservesFiniteLimits (V n)]
    [Vcolim : ∀ n, PreservesFiniteColimits (V n)]
    (M : A) (rootsTower : ℕᵒᵖ ⥤ A) (P : ∀ n, C n)
    (κ : ∀ n, Ext M ((V n).obj (P n)) 1)
    (rootNorm : ∀ H : ℕᵒᵖ ⥤ B, (H ⋙ U ≅ rootsTower) →
      ∀ n, (H.obj (op n) ≅ (F n).obj (P n)) → Prop) where
  /-- One actual system. -/
  H : ℕᵒᵖ ⥤ B
  /-- Identification as an underlying abelian tower. -/
  roots : H ⋙ U ≅ rootsTower
  /-- One derived comparison in the strict-system category. -/
  b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj M)⟦(1 : ℤ)⟧) ≅
    ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧
  /-- The finite coefficient comparisons. -/
  t : ∀ n, H.obj (op n) ≅ (F n).obj (P n)
  /-- The prescribed root normalization. -/
  normalized : ∀ n, rootNorm H roots n (t n)
  /-- Full residue-linear transport before restriction. -/
  transport : ∀ n, KummerArrowTransport ℓ L U ad D (F n) (V n) n (P n) M (κ n) H b (t n)

/-- The strict Kummer data type for the actual pro-etale coefficient categories.
It specializes the abstract structure and chooses no data from an existence proof.
Source: diagonal tower system proof, target paragraph of (3) and formula (4)
(blueprint: lem-sfb-kummer-strict-target-transport). -/
def KummerStrictTarget (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasExt.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W)) : Type _ :=
  KummerTargetData
    (A := DiagonalAb W) (B := DiagonalMod ℓ W)
    (abA := diagonalAbSheafAbelian W) (abB := diagonalModuleSheafAbelian _ W)
    (hA := kummerAbHasExt W) (hB := kummerModuleHasExt _ W)
    (abC := fun n => diagonalModuleSheafAbelian (diagonalResidue.{u} ℓ n) W)
    (hC := fun n => kummerModuleHasExt (diagonalResidue.{u} ℓ n) W)
    (Fadd := fun n => diagonalFiniteToPadicAdditive ℓ n W)
    (Flim := fun n => diagonalFiniteToPadicLimits ℓ n W)
    (Fcolim := fun n => diagonalFiniteToPadicColimits ℓ n W)
    (Vadd := fun n => cartierForgetAdditive (diagonalResidue.{u} ℓ n) W)
    (Vlim := fun n => cartierForgetLimits (diagonalResidue.{u} ℓ n) W)
    (Vcolim := fun n => cartierForgetColimits (diagonalResidue.{u} ℓ n) W)
    ℓ (diagonalScalarExtension ℓ W) (diagonalForget ℓ W)
    (diagonalScalarAdjunction ℓ W) D
    (fun n => Sheaf (Scheme.ProEt.topology W)
      (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n)))
    (fun n => diagonalFiniteToPadic ℓ n W)
    (fun n => cartierForget (diagonalResidue.{u} ℓ n) W)
    ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj W.gmSheaf)
    (Scheme.proEtaleRootsOfUnityTower W ℓ (Fact.out : ℓ.Prime))
    (fun n => geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
      (cartierResidue_cast ℓ (n + 1)) W)
    (fun n => kummerComparedUnit ℓ W hW n)
    (kummerRootNormalization ℓ W hW)

/-- Combine residue-linear existence with conditional Kummer compatibility before
specializing the coefficient categories. -/
private theorem kummer_target_from_finite_lifts
    (ℓ : ℕ) {A : Type*} [Category A] [abA : Abelian A] [hA : HasExt.{w} A]
    {B : Type*} [Category B] [abB : Abelian B] [hB : HasExt.{w} B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
    [HasExt.{w} (ℕᵒᵖ ⥤ B)]
    (L : A ⥤ B) (U : B ⥤ A) (ad : L ⊣ U) (D : DiagonalDerivedReduction ℓ L)
    (C : ℕ → Type*) [catC : ∀ n, Category (C n)] [abC : ∀ n, Abelian (C n)]
    [hC : ∀ n, HasExt.{w} (C n)]
    (F : ∀ n, C n ⥤ B) [Fadd : ∀ n, (F n).Additive]
    [Flim : ∀ n, PreservesFiniteLimits (F n)]
    [Fcolim : ∀ n, PreservesFiniteColimits (F n)]
    (V : ∀ n, C n ⥤ A) [Vadd : ∀ n, (V n).Additive]
    [Vlim : ∀ n, PreservesFiniteLimits (V n)]
    [Vcolim : ∀ n, PreservesFiniteColimits (V n)]
    (M : A) (rootsTower : ℕᵒᵖ ⥤ A) (P : ∀ n, C n)
    (κ : ∀ n, Ext M ((V n).obj (P n)) 1)
    (rootNorm : ∀ H : ℕᵒᵖ ⥤ B, (H ⋙ U ≅ rootsTower) →
      ∀ n, (H.obj (op n) ≅ (F n).obj (P n)) → Prop)
    (ht : KummerTargetAdjunctCompatibility ℓ L U ad D C F V M rootsTower P κ rootNorm)
    (hlift : ∀ n, DiagonalFiniteArrowLifting ℓ L D (F n) n) :
    Nonempty (KummerTargetData ℓ L U ad D C F V M rootsTower P κ rootNorm) := by
  unfold KummerTargetAdjunctCompatibility at ht
  obtain ⟨H, roots, b, t, hn, hc⟩ := ht
  refine ⟨{ H := H, roots := roots, b := b, t := t, normalized := hn, transport := ?_ }⟩
  intro n
  unfold KummerArrowTransport
  intro S a ha Q s g hg f
  have hl := hlift n
  unfold DiagonalFiniteArrowLifting at hl
  obtain ⟨e, he⟩ := hl M H b (P n) (t n) S a ha Q s f
  refine ⟨e, ?_, he.symm⟩
  simpa only [kummerScalarAdjunct, negativeExtProduct] using hc n S a ha Q s g hg f e he

/-- Simultaneous reduction of shifted comparison units has the roots tower as
its strict target. Its action on any degree-one arrow is the residue-linear
arrow characterized by the negative Kummer adjunct.

Source: diagonal tower system proof, step (3), target paragraph, and step (4);
Cartier unit proof, derived reduction paragraphs
(blueprint: lem-sfb-kummer-strict-target-transport).

Proof: compute simultaneous reduction on one flat-term K-flat resolution.
At exponent n+1, compare with the constant prime-power two-term coefficient
resolution of the residue ring. Applied to comparison units this has kernel
the comparison pullback of etale roots and zero cokernel, by Kummer exactness
and exact comparison.
Identify this kernel with the actual pro-etale roots using the canonical roots
comparison. The map of resolutions is multiplication by the prime in degree
minus one and identity in degree zero. Its kernel map is thus the power-prime
transition, including its residue-induced constant p-adic action. Cohomology
in the strict system category and good truncation give H and b; take b to be
the negative of the normalized Kummer identification, uniformly at every level.
The root comparison then gives each t and its stated underlying-map equation.

Evaluation of the common resolution factors through derived extension to the
residue ring, before restriction to p-adic scalars. Its source counit and the
ordinary quotient adjunction identify the normalized source a,s,g with the
residue scalar unit. Its target unit is the negative of the positive Kummer
connecting map, preceded by the units comparison. For any degree-one map f,
naturality of this derived adjunction unit identifies the adjunct of its
residue-linear reduction e with minus f followed by the Kummer map. The same
resolution identifies restriction of e with evaluation of the strict arrow.
This proves both equations before forgetting coefficients. No Cartier divisor
or pole extension is used, and no equality of derived arrows is inferred from
levelwise equality. The statement applies to arbitrary sources, residue
objects, and degree-one maps; it does not assert the diagonal class formula. -/
theorem kummer_strict_target_transport (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    (hW : IsUnit (ℓ : Γ(W, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasExt.{u + 1} (DiagonalSystems ℓ W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W)) :
    Nonempty (KummerStrictTarget ℓ W hW D) := by
  unfold KummerStrictTarget
  apply kummer_target_from_finite_lifts
  · have h := kummer_strict_adjunct_compatibility ℓ W hW D
    unfold kummerStrictAdjunctCompatibilityStatement at h
    exact h
  · intro n
    have h := diagonal_finite_arrow_lift ℓ W D n
    unfold diagonalFiniteArrowLiftingStatement at h
    exact h

end AlgebraicGeometry.ProEtale
