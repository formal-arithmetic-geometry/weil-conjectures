/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# The finite coefficient setting for purity

Source: blueprint sec-smooth-purity/sk-def-purity-conv/def-pur-conventions.md
(blueprint: def-pur-conventions).

The fixed field datum, coefficient closure, finite subextension and positive level are
bundled together. The coefficient ring is the existing quotient construction, not new data.
The small pro-etale site retains its object universe u+1 and morphism universe u.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures

/-- The finite-level purity setting. The field and coefficient data are the published
constructions of def-weil-finite-field-fiber; E is literally a finite subextension of
its fixed coefficient closure. Source: blueprint sk-def-purity-conv,
def-pur-conventions (blueprint: def-pur-conventions). -/
structure PurityFiniteSetting where
  field : FiniteFieldDatum.{u}
  coefficients : field.CoefficientDatum
  extension : IntermediateField (Padic coefficients.l) coefficients.Qbar
  [finiteExtension : FiniteDimensional (Padic coefficients.l) extension]
  level : ℕ
  level_pos : 1 ≤ level

attribute [instance] PurityFiniteSetting.finiteExtension

namespace PurityFiniteSetting

/-- The coefficient ring in the conventions is the existing quotient O_E/(varpi_E^n).
Source: blueprint sk-def-purity-conv, finite coefficient notation
(blueprint: def-pur-conventions). -/
noncomputable def Ring (P : PurityFiniteSetting.{u}) : Type u :=
  Padic.coefficientExtensionRing P.coefficients.l P.extension P.level

/-- The ordinary commutative ring structure on the existing finite coefficient quotient.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-conventions). -/
noncomputable instance ringCommRing (P : PurityFiniteSetting.{u}) : CommRing P.Ring :=
  inferInstanceAs (CommRing
    (Padic.coefficientExtensionRing P.coefficients.l P.extension P.level))

/-- The ramification index is the order of ell in the DVR with uniformizer varpi_E.
Source: blueprint sk-def-purity-conv and lem-pur-finite-kummer-level
(blueprint: def-pur-conventions). -/
noncomputable def ramificationIndex (P : PurityFiniteSetting.{u}) : ℕ :=
  (emultiplicity (Padic.coefficientExtensionUniformizer P.coefficients.l P.extension)
    (P.coefficients.l : Padic.coefficientExtensionIntegers
      P.coefficients.l P.extension)).toNat

/-- When e divides n, N=n/e is the finite Kummer level of the affine-line datum.
Source: blueprint sk-prop-a1-kummer, def-pur-affine-line-datum
(blueprint: def-pur-conventions). -/
noncomputable def kummerLevel (P : PurityFiniteSetting.{u}) : ℕ :=
  P.level / P.ramificationIndex

/-- The standard size lift of A for sheaves on the small site. Source: blueprint
sk-def-purity-conv, coefficient-size convention (blueprint: def-pur-conventions). -/
noncomputable def Coefficient (P : PurityFiniteSetting.{u}) : Type (u + 1) :=
  ULift.{u + 1} P.Ring

/-- The coefficient ring structure, cached once for all coefficient sheaf constructions.
This is the ordinary ULift structure on the existing quotient, with no new ring data.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-conventions). -/
noncomputable instance coefficientCommRing (P : PurityFiniteSetting.{u}) :
    CommRing P.Coefficient := inferInstanceAs (CommRing (ULift.{u + 1} P.Ring))

/-- The required finite Kummer exponent. Source: blueprint def-pur-affine-line-datum,
finite-level paragraph (blueprint: def-pur-conventions). -/
noncomputable def exponent (P : PurityFiniteSetting.{u}) : ℕ :=
  P.coefficients.l ^ P.kummerLevel

/-- The divisibility hypothesis makes the exponent kill the coefficient quotient.
Source: blueprint def-pur-affine-line-datum, finite-level paragraph
(blueprint: def-pur-conventions).
Proof: In the DVR O_E the order of ell is e, so ell is a unit times varpi^e.
If e divides n, raising to n/e identifies (ell^(n/e)) with (varpi^n).
The image of ell^(n/e) in the quotient O_E/(varpi^n), and hence in its ULift, is zero. -/
theorem exponent_coefficient_eq_zero (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) : (P.exponent : P.Coefficient) = 0 := by
  sorry

/-- Constant finite module coefficients on the etale site. Source: blueprint
sk-def-purity-conv (blueprint: def-pur-conventions). -/
noncomputable def constantEtale (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient) :=
  (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)).obj
    (ModuleCat.of P.Coefficient P.Coefficient)

/-- The actual finite root line with extended coefficients. Source: blueprint
sk-def-purity-conv (blueprint: def-pur-conventions). -/
noncomputable def twistEtale (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient) :=
  Scheme.finiteEtaleTateSheaf P.Coefficient P.exponent T
    (P.exponent_coefficient_eq_zero h) 1

/-- The scalar-forgetting functor used only to specify the actual Kummer class.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-conventions). -/
noncomputable def forgetEtale (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient) ⥤
      Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  sheafCompose T.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1})

/-- Additivity of scalar forgetting. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-conventions).
Proof: addition of sheaf morphisms and forgetting scalars are computed sectionwise. -/
theorem forgetEtale_additive (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (P.forgetEtale T).Additive := by
  sorry

attribute [instance] forgetEtale_additive

/-- Exactness of scalar forgetting. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-conventions).
Proof: the forgetful functor is both adjoints via extension, restriction and coextension
along Z to A. Sheafification transports these adjunctions. It therefore preserves finite
limits and finite colimits, as in moduleSheafForgetIsLeftAdjoint. -/
theorem forgetEtale_preservesFiniteColimits (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    PreservesFiniteColimits (P.forgetEtale T) := by
  sorry

attribute [instance] forgetEtale_preservesFiniteColimits

/-- Left exactness of scalar forgetting. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-conventions).
Proof: forgetting is a right adjoint, and the sheaf functor inherits its adjunction. -/
theorem forgetEtale_preservesFiniteLimits (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    PreservesFiniteLimits (P.forgetEtale T) := by
  sorry

attribute [instance] forgetEtale_preservesFiniteLimits

/-- Scalar forgetting commutes with sheafification. Source: blueprint sk-def-purity-conv
(blueprint: def-pur-conventions).
Proof: the coefficient forgetful functor preserves finite limits and all colimits,
using both scalar adjunctions. The sheafification comparison is consequently invertible. -/
theorem forget_preservesSheafification (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    T.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}) := by
  sorry

attribute [instance] forget_preservesSheafification

/-- The comparison's degree-zero free-generator map, Z to the underlying constant A.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-conventions). -/
noncomputable def integerToConstant (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶ (P.forgetEtale T).obj (P.constantEtale T) :=
  (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((AddCommGrpCat.uliftZMultiplesAddEquiv (AddCommGrpCat.of P.Coefficient)).symm 1) ≫
    (constantCommuteCompose T.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1})).inv.app
        (ModuleCat.of P.Coefficient P.Coefficient)

/-- The canonical map from module cohomology to the underlying abelian Ext group.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-conventions). -/
noncomputable def moduleClassToAbelian (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
    (x : Abelian.Ext (P.constantEtale T) F 1) :
    Sheaf.H ((P.forgetEtale T).obj F) 1 :=
  (Abelian.Ext.mk₀ (P.integerToConstant T)).comp
    (x.mapExactFunctor (P.forgetEtale T)) (zero_add 1)

/-- This comparison is bijective, so it selects no arbitrary cohomology class.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-conventions).
Proof: Hom_A(A,-) is global sections. Forgetting an injective module sheaf is acyclic
for abelian global sections. Apply the natural acyclic-resolution comparison, whose
map in degree zero is precisely precomposition by Z to A. It is bijective in degree one. -/
theorem moduleClassToAbelian_bijective (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :
    Function.Bijective (P.moduleClassToAbelian T F) := by
  sorry

/-- Constant pro-etale coefficients, via the canonical comparison inverse image.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-conventions). -/
noncomputable def constant (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).obj (P.constantEtale T)

/-- The finite pro-etale twist, via the canonical comparison inverse image.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-conventions). -/
noncomputable def twist (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).obj (P.twistEtale h T)

/-- Either of the two actual coefficient sheaves used in the proposition.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-conventions). -/
noncomputable def coefficientSheaf (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u}) (twisted : Bool) :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient) :=
  if twisted then P.twist h T else P.constant T

/-- The actual degree-zero object of the unbounded derived category.
Source: blueprint sk-def-purity-conv (blueprint: def-pur-conventions). -/
noncomputable def derivedSheaf (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u}) (twisted : Bool) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) :=
  (DerivedCategory.singleFunctor
    (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) 0).obj
      (P.coefficientSheaf h T twisted)

/-- Invertibility of the Kummer exponent on any k-scheme, without a finite-type
restriction. Source: blueprint sk-def-purity-conv (blueprint: def-pur-conventions).
Proof: the fixed field has characteristic p and ell differs from p, so ell, hence every
power of ell, is a unit in k. Its image along the structure morphism is a unit. -/
theorem exponent_isUnit (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (a : T ⟶ Spec (CommRingCat.of P.field.k)) : IsUnit (P.exponent : Γ(T, ⊤)) := by
  sorry

/-- The coefficient prime is invertible in every local ring of a scheme over the fixed
algebraically closed finite-field base.
Source: blueprint def-pur-conventions, ell distinct from the characteristic
(blueprint: def-pur-conventions).
Proof: k_0 has cardinality p^a with p prime and a positive, hence characteristic p.
Its algebraic closure k has the same characteristic. The prime ell differs from p,
so its image is a nonzero element of the field k and therefore a unit. The structure
map induces k to the local ring at x, preserving units and the scalar ell. -/
theorem coefficientPrime_isUnit_stalk (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (a : T ⟶ Spec (CommRingCat.of P.field.k)) (x : T) :
    IsUnit (P.coefficients.l : T.presheaf.stalk x) := by
  sorry

end PurityFiniteSetting
end WeilConjectures
