/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs

/-! # Canonical scalar-extension comparisons of the native Tate lines

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-setup/sec-the-purity-statement/sk-thm-purity-transport/
sk-lem-sp-field-extension/sk-lem-sp-field-extension-towers.md, clauses (2)--(3),
the comparisons O_E(d) ⊗^L O_F ≅ O_F(d), O_E(d) ⊗^L E ≅ E(d) and E(d) ⊗^L F ≅ F(d)
(blueprint: det-sp-field-extension-towers).

All comparisons below are definitions; no choice is made.
* (a) integral: the root-projection map O_E(1) ⊗ O_F → O_F(1), the limit of the
  level maps `a ⊗ u ↦ ā ⊗ u` on A_{E,n} ⊗ μ_{ℓ^{n+1}} → A_{F,n} ⊗ μ_{ℓ^{n+1}};
  nonnegative powers through the monoidal structure of scalar extension; degree zero
  objects through the derived counit on the K-flat single complex.
* (b) localization: E_X(1) is by definition the scalar extension of O_E(1).
* (c) rational: the composite of (a) and (b) through the coefficient square
  O_E → O_F → F = O_E → E → F and the derived tensor associators.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.MonObj

-- The imported universe-polymorphic smallness instance of the pro-étale site leaves
-- an unsolvable universe constraint in the sheafification instances of `Mod.extendScalars`.
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

namespace AlgebraicGeometry.ProEtale.NativeFieldTower

/-! ## Derived single objects -/

section Single

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [MonObj Λ'] [IsCommMonObj Λ] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  (X : Scheme.{u})

/-- The derived scalar-extension counit is invertible at a K-flat single complex.
Source: clauses (2)--(3), flat Tate lines (blueprint: det-sp-field-extension-towers).
Proof: the derived functor is computed on K-flat complexes
(`isIso_leftDerivedFunctorCounit_app_of_kFlat`). -/
theorem single_counit_isIso
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      ((CochainComplex.singleFunctor _ 0).obj M)) :
    IsIso ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((CochainComplex.singleFunctor _ 0).obj M))) :=
  (Mod.extendScalars (coefficientMap a X)).isIso_leftDerivedFunctorCounit_app_of_kFlat _ hM

/-- The canonical comparison S ⊗^L_R M[0] ≅ (S ⊗_R M)[0] for K-flat M[0]: the derived
counit followed by the canonical commutation of `single` with an additive functor.
Source: clauses (2)--(3), Tate lines in degree zero
(blueprint: det-sp-field-extension-towers). -/
def derivedSingleChange
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      ((CochainComplex.singleFunctor _ 0).obj M)) :
    (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((Mod.extendScalars (coefficientMap a X)).obj M) :=
  haveI := single_counit_isIso a X M hM
  (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app M ≪≫
        ((DerivedCategory.quotientCompQhIso _).app
          ((CochainComplex.singleFunctor _ 0).obj M)).symm) ≪≫
    asIso ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((CochainComplex.singleFunctor _ 0).obj M))) ≪≫
    DerivedCategory.Qh.mapIso
      (((Mod.extendScalars (coefficientMap a X)).mapHomotopyCategoryFactors (.up ℤ)).app
        ((CochainComplex.singleFunctor _ 0).obj M)) ≪≫
    (DerivedCategory.quotientCompQhIso _).app
      (((Mod.extendScalars (coefficientMap a X)).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor _ 0).obj M)) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (Mod.extendScalars (coefficientMap a X)) (.up ℤ) 0).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app
      ((Mod.extendScalars (coefficientMap a X)).obj M)).symm

/-! ## Nonnegative powers -/

/-- Scalar extension of nonnegative powers of a line, from a comparison of the lines:
the unit comparison in degree zero and the monoidal tensorator in positive degree.
Source: signed twists, nonnegative degrees (blueprint: det-sp-field-extension-towers). -/
def twistNatChange
    {L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    {L' : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X)}
    (e : (Mod.extendScalars (coefficientMap a X)).obj L ≅ L') :
    ∀ n : ℕ, (Mod.extendScalars (coefficientMap a X)).obj
        (coefficientTwistNat X (condensedRingObj Λ X) L n) ≅
      coefficientTwistNat X (condensedRingObj Λ' X) L' n
  | 0 =>
    letI := Mod.extendScalarsMonoidal (coefficientMap a X)
    (Functor.Monoidal.εIso (Mod.extendScalars (coefficientMap a X))).symm
  | n + 1 =>
    letI := Mod.extendScalarsMonoidal (coefficientMap a X)
    (Functor.Monoidal.μIso (Mod.extendScalars (coefficientMap a X)) _ _).symm ≪≫
      (twistNatChange e n ⊗ᵢ e)

end Single

variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-! ## Coefficient maps (moved here from the Statement module, unchanged) -/

/-- Continuous integral inclusion with the spectral topology, on actual integers.
Source: clause (1), R into S (blueprint: det-sp-field-extension-towers). -/
def integralPoint {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    (⟨spIntegralCondensed l E.val⟩ : CondensedRing.ScalarSixRing.{u}) ⟶
      ⟨spIntegralCondensed l F.val⟩ :=
  letI := spectralNorm.normedField (Padic l) E.val
  letI := spectralNorm.normedField (Padic l) F.val
  CommMon.homMk (Mon.Hom.mk
    (twistContinuousMap
      (WeilConjectures.integralScalarIntegerInclusion l E.val F.val (IntermediateField.inclusion h))
      ((AddMonoidHomClass.isometry_of_norm
        (WeilConjectures.integralScalarIntegerInclusion l E.val F.val
          (IntermediateField.inclusion h))
        (fun x ↦ WeilConjectures.integralScalar_absoluteValue l E.val F.val
          (IntermediateField.inclusion h) x.val)).continuous)))

/-- Continuous rational inclusion in the same fixed closure.
Source: clause (3), E into F (blueprint: det-sp-field-extension-towers). -/
def rationalPoint {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    (⟨twistRationalRing l E.val⟩ : CondensedRing.ScalarSixRing.{u}) ⟶
      ⟨twistRationalRing l F.val⟩ :=
  letI := spectralNorm.normedField (Padic l) E.val
  letI := spectralNorm.normedField (Padic l) F.val
  CommMon.homMk (Mon.Hom.mk
    (twistContinuousMap (IntermediateField.inclusion h).toRingHom
      ((AddMonoidHomClass.isometry_of_norm (IntermediateField.inclusion h)
        (fun x ↦ WeilConjectures.integralScalar_absoluteValue l E.val F.val
          (IntermediateField.inclusion h) x)).continuous)))

/-- Inverting ell is actual derived tensor along O_E into E.
Source: clause (3) (blueprint: det-sp-field-extension-towers). -/
def localizationPoint (E : Padic.FiniteCoefficientFields l Ω) :
    (⟨spIntegralCondensed l E.val⟩ : CondensedRing.ScalarSixRing.{u}) ⟶
      ⟨twistRationalRing l E.val⟩ :=
  CommMon.homMk (Mon.Hom.mk (twistIntegralToRational l E.val))

/-- The coefficient square O_E → O_F → F equals O_E → E → F.
Source: clause (3) (blueprint: det-sp-field-extension-towers).
Proof: both composites postcompose a continuous section s with the inclusion
O_E ⊂ F of subrings of Ω; they agree pointwise, hence as condensed maps (ext). -/
theorem localization_square {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    integralPoint l Ω h ≫ localizationPoint l Ω F =
      localizationPoint l Ω E ≫ rationalPoint l Ω h := by
  sorry

/-! ## The signed lines in degree zero -/

/-- The signed integral Tate line O_E(d) in degree zero; K(d) is tensor with it.
Source: clause (2), f^*(d)[2d] (blueprint: det-sp-field-extension-towers). -/
abbrev integralLine (E : Padic.FiniteCoefficientFields l Ω) (T : Scheme.{u}) (d : ℕ) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (coefficientSignedTwist T _ (coefficientIntegralTwistOne l E.val T) (d : ℤ))

/-- The signed rational Tate line E(d) in degree zero; K(d) is tensor with it.
Source: clause (3), f_E^*(d)[2d] (blueprint: det-sp-field-extension-towers). -/
abbrev rationalLine (E : Padic.FiniteCoefficientFields l Ω) (T : Scheme.{u}) (d : ℕ) :=
  (DerivedCategory.singleFunctor _ 0).obj
    (coefficientSignedTwist T _ (coefficientRationalTwistOne l E.val T) (d : ℤ))

/-- The nonnegative integral Tate powers are K-flat in degree zero.
Source: clause (2) (blueprint: det-sp-field-extension-towers).
Proof: O_E(1) is locally free of rank one (`coefficientIntegralTwistOne_locally_trivial`),
so its tensor powers are flat; a flat module in one degree is K-flat. -/
theorem integralLine_kFlat (E : Padic.FiniteCoefficientFields l Ω) (T : Scheme.{u}) (d : ℕ) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      ((CochainComplex.singleFunctor _ 0).obj
        (coefficientTwistNat T _ (coefficientIntegralTwistOne l E.val T) d)) := by
  sorry

/-! ## (a) Integral comparison -/

section Integral

variable {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) (T : Scheme.{u})

/-- The integral coefficient map on T. -/
abbrev integralMap :=
  coefficientMap (Λ := spIntegralCondensed l E.val) (Λ' := spIntegralCondensed l F.val)
    (integralPoint l Ω h).hom.hom T

/-- The inclusion O_E/π_E^(n+1) → O_F/π_F^(n+1) on the finite coefficient rings.
Source: clause (2), root projections (blueprint: det-sp-field-extension-towers). -/
def integralFiniteMap (n : ℕ) : twistFiniteRing l E.val n ⟶ twistFiniteRing l F.val n :=
  letI : TopologicalSpace (Padic.coefficientExtensionRing l E.val (n + 1)) := ⊥
  letI : TopologicalSpace (Padic.coefficientExtensionRing l F.val (n + 1)) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing l E.val (n + 1)) := ⟨rfl⟩
  letI : DiscreteTopology (Padic.coefficientExtensionRing l F.val (n + 1)) := ⟨rfl⟩
  twistContinuousMap
    (WeilConjectures.integralScalarQuotientMap l E.val F.val (IntermediateField.inclusion h) n)
    continuous_of_discreteTopology

/-- The level map A_{E,n} ⊗ μ → A_{F,n} ⊗ μ, a ⊗ u ↦ ā ⊗ u, as an O_E-linear map
into the restricted O_F-level.
Source: clause (2), root projections (blueprint: det-sp-field-extension-towers). -/
def integralLevelRestricted (n : ℕ) :
    coefficientIntegralTwistLevel l E.val T n ⟶
      (Mod.comap (integralMap l Ω h T)).obj (coefficientIntegralTwistLevel l F.val T n) :=
  Mod.homMk
    (_root_.AlgebraicGeometry.ProEtale.coefficientMap (integralFiniteMap l Ω h n) T ⊗ₘ
      𝟙 (rootsOfUnitySheaf T (l ^ (n + 1))))
    (by
      -- Linearity: the coefficient square O_E → A_{E,n} → A_{F,n} = O_E → O_F → A_{F,n}
      -- commutes, so the argument of `coefficientFreeTensor_linear` applies.
      sorry)

/-- The adjoint level map O_F ⊗ (A_{E,n} ⊗ μ) → A_{F,n} ⊗ μ.
Source: clause (2), root projections (blueprint: det-sp-field-extension-towers). -/
def integralLevel (n : ℕ) :
    (Mod.extendScalars (integralMap l Ω h T)).obj (coefficientIntegralTwistLevel l E.val T n) ⟶
      coefficientIntegralTwistLevel l F.val T n :=
  ((Mod.extendRestrictAdjunction (integralMap l Ω h T)).homEquiv _ _).symm
    (integralLevelRestricted l Ω h T n)

/-- The level maps commute with the reduction/l-th power transitions.
Source: clause (2) (blueprint: det-sp-field-extension-towers).
Proof: on generators a ⊗ u both composites give (reduced ā) ⊗ u^l, since the
coefficient inclusion commutes with reduction and the root map is not changed. -/
theorem integralLevel_transition (n : ℕ) :
    (Mod.extendScalars (integralMap l Ω h T)).map
        (coefficientIntegralTwistTransition l E.val T n) ≫ integralLevel l Ω h T n =
      integralLevel l Ω h T (n + 1) ≫ coefficientIntegralTwistTransition l F.val T n := by
  sorry

/-- The cone of root projections over the F-tower.
Source: clause (2) (blueprint: det-sp-field-extension-towers). -/
def integralTateCone : Cone (coefficientIntegralTwistSystem l F.val T) where
  pt := (Mod.extendScalars (integralMap l Ω h T)).obj (coefficientIntegralTwistOne l E.val T)
  π :=
    { app := fun n ↦ (Mod.extendScalars (integralMap l Ω h T)).map
          (limit.π (coefficientIntegralTwistSystem l E.val T) n) ≫ integralLevel l Ω h T n.unop
      naturality := by
        -- `integralLevel_transition` and the limit cone of the E-tower.
        sorry }

/-- The canonical root-projection comparison O_E(1) ⊗ O_F → O_F(1): the unique map
whose n-th projection is the scalar extension of the n-th projection followed by the
level map (this is the `NativeLines.projections` equation).
Source: clause (2) (blueprint: det-sp-field-extension-towers). -/
def integralTateOneHom :
    (Mod.extendScalars (integralMap l Ω h T)).obj (coefficientIntegralTwistOne l E.val T) ⟶
      coefficientIntegralTwistOne l F.val T :=
  limit.lift (coefficientIntegralTwistSystem l F.val T) (integralTateCone l Ω h T)

/-- The root-projection comparison is invertible.
Source: clause (2) (blueprint: det-sp-field-extension-towers).
Proof: O_F is finite free over O_E, so O_F ⊗_{O_E} - commutes with the countable
inverse limit; levelwise A_{E,n} ⊗_{O_E} O_F → A_{F,n} is an isomorphism up to the
cofinal reindexing of uniformizer powers, and the root factor is unchanged. -/
instance integralTateOneHom_isIso : IsIso (integralTateOneHom l Ω h T) := by
  sorry

/-- (a) The canonical comparison O_E(d) ⊗^L O_F ≅ O_F(d) in degree zero.
Source: clause (2), f^*(d)[2d] (blueprint: det-sp-field-extension-towers). -/
def integralLineChange (d : ℕ) :
    (CondensedRing.scalarSixChange (integralPoint l Ω h) T).obj (integralLine l Ω E T d) ≅
      integralLine l Ω F T d :=
  haveI := integralTateOneHom_isIso l Ω h T
  derivedSingleChange (Λ := spIntegralCondensed l E.val) (Λ' := spIntegralCondensed l F.val)
      (integralPoint l Ω h).hom.hom T _ (integralLine_kFlat l Ω E T d) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (twistNatChange (Λ := spIntegralCondensed l E.val) (Λ' := spIntegralCondensed l F.val)
        (integralPoint l Ω h).hom.hom T (asIso (integralTateOneHom l Ω h T)) d)

end Integral

/-! ## (b) Localization comparison -/

/-- (b) The canonical comparison O_E(d) ⊗^L E ≅ E(d): E_X(1) is by definition the
scalar extension of O_E(1), so the line comparison is the identity.
Source: clause (3) (blueprint: det-sp-field-extension-towers). -/
def localizationLineChange (E : Padic.FiniteCoefficientFields l Ω) (T : Scheme.{u}) (d : ℕ) :
    (CondensedRing.scalarSixChange (localizationPoint l Ω E) T).obj (integralLine l Ω E T d) ≅
      rationalLine l Ω E T d :=
  derivedSingleChange (Λ := spIntegralCondensed l E.val) (Λ' := twistRationalRing l E.val)
      (localizationPoint l Ω E).hom.hom T _ (integralLine_kFlat l Ω E T d) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (twistNatChange (Λ := spIntegralCondensed l E.val) (Λ' := twistRationalRing l E.val)
        (localizationPoint l Ω E).hom.hom T
        (Iso.refl (coefficientRationalTwistOne l E.val T)) d)

/-! ## (c) Rational comparison -/

/-- Equal coefficient maps give the identity comparison of derived scalar extensions. -/
def scalarSixChangeCongr {Λ Λ' : CondensedRing.ScalarSixRing.{u}} {a b : Λ ⟶ Λ'} (e : a = b)
    (T : Scheme.{u}) :
    CondensedRing.scalarSixChange a T ≅ CondensedRing.scalarSixChange b T :=
  eqToIso (congrArg (fun c ↦ CondensedRing.scalarSixChange c T) e)

/-- (c) The canonical comparison E(d) ⊗^L F ≅ F(d), the composite of (a) and (b)
through the coefficient square and the derived tensor associators.
Source: clause (3) (blueprint: det-sp-field-extension-towers). -/
def rationalLineChange {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
    (T : Scheme.{u}) (d : ℕ) :
    (CondensedRing.scalarSixChange (rationalPoint l Ω h) T).obj (rationalLine l Ω E T d) ≅
      rationalLine l Ω F T d :=
  (CondensedRing.scalarSixChange (rationalPoint l Ω h) T).mapIso
      (localizationLineChange l Ω E T d).symm ≪≫
    (CondensedRing.scalarSixTower (localizationPoint l Ω E) (rationalPoint l Ω h) T).app
      (integralLine l Ω E T d) ≪≫
    (scalarSixChangeCongr (localization_square l Ω h).symm T).app (integralLine l Ω E T d) ≪≫
    ((CondensedRing.scalarSixTower (integralPoint l Ω h) (localizationPoint l Ω F) T).app
      (integralLine l Ω E T d)).symm ≪≫
    (CondensedRing.scalarSixChange (localizationPoint l Ω F) T).mapIso
      (integralLineChange l Ω h T d) ≪≫
    localizationLineChange l Ω F T d

end AlgebraicGeometry.ProEtale.NativeFieldTower
