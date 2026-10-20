/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Duality
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.Sites.PullbackFlat
public import WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.KFlat
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Compactification.NagataCompactification

/-! # Finite-level constructible exceptional inverse image

Source: blueprint sec-smooth-purity/sk-def-sf-operations,
def-weil-exceptional-inverse-image (blueprint: def-weil-exceptional-inverse-image).

The functor is the published comparison transport of the etale right adjoint.
The Noetherian finite-type interface supplies its bounded-below instance without
postulating an ambient pro-etale right adjoint.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

/-- Finiteness of the actual positive coefficient quotient, including its standard size lift.
Source: blueprint finite coefficient setting (blueprint: def-weil-exceptional-inverse-image).
Proof: use finiteness of O_E/(varpi^n) and transport along ULift. -/
theorem finiteCoefficient (P : PurityFiniteSetting.{u}) : Finite P.Coefficient := by
  have : Finite P.Ring :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  exact inferInstanceAs (Finite (ULift P.Ring))

attribute [instance] finiteCoefficient

/-- Bounded-below preservation for the etale right adjoint over a Noetherian target.
Source: blueprint def-weil-exceptional-inverse-image, defining properties paragraph
(blueprint: def-weil-exceptional-inverse-image).
Proof: the proper part of a compactification is finite type over a Noetherian scheme.
Its fibre dimensions have a finite global bound by quasi-compactness. Proper torsion
cohomology has amplitude at most twice this bound; open extension is exact.
The adjunction and t-structure orthogonality then bound the right adjoint below. -/
theorem exceptionalBoundedBelow (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    [IsNoetherian Y] : Etale.HasBoundedBelowUpperShriek (ModuleCat.{u + 1} Λ) f := by
  infer_instance

/-- A finite-type scheme over a field is Noetherian.
Source: blueprint def-weil-exceptional-inverse-image, initial setting
(blueprint: def-weil-exceptional-inverse-image).
Proof: fields are Noetherian, finite-type affine algebras are Noetherian, and a finite
cover of the scheme by these affine spectra gives a Noetherian scheme. -/
theorem noetherian (P : PurityFiniteSetting.{u}) {T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType a] [QuasiCompact a] :
    IsNoetherian T := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian a
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace a
  exact ⟨⟩

/-- The coefficient tensor unit is concentrated in degree zero and hence bounded below.
Source: blueprint def-weil-exceptional-inverse-image, constant coefficient object
(blueprint: def-weil-exceptional-inverse-image).
Proof: the derived tensor unit is the constant coefficient sheaf in degree zero;
its negative cohomology vanishes. -/
theorem unitPlus (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    _root_.DerivedCategory.TStructure.t.plus
      (𝟙_ (_root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)))) := by
  refine ⟨0, ?_⟩
  change _root_.DerivedCategory.TStructure.t.IsGE
    (_root_.DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) 0).obj (𝟙_ _))) 0
  infer_instance

/-- The actual finite-level constructible exceptional functor, with its required
bounded-below interface supplied from the finite-type field setting.
Source: blueprint def-weil-exceptional-inverse-image, finite-level displayed definition
(blueprint: def-weil-exceptional-inverse-image). -/
noncomputable def exceptional (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] :=
  letI := P.noetherian aY
  letI := exceptionalBoundedBelow P.Coefficient f
  ProEtale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f

/-- The relative dualizing object is the exceptional inverse image of the coefficient unit.
Source: blueprint def-weil-exceptional-inverse-image and def-pur-co-smoothness
(blueprint: def-weil-exceptional-inverse-image). -/
noncomputable def dualizing (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] :=
  letI := P.noetherian aY
  letI := exceptionalBoundedBelow P.Coefficient f
  ProEtale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) f

/-- The published counit, with the same finite-type field interface.
Source: blueprint def-weil-exceptional-inverse-image, adjunction characterization
(blueprint: def-weil-exceptional-inverse-image). -/
noncomputable def counit (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    (hK : _root_.DerivedCategory.TStructure.t.plus K) :
    (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) f).obj
      ((P.exceptional f aY).obj K) ⟶ K :=
  letI := P.noetherian aY
  letI := exceptionalBoundedBelow P.Coefficient f
  ProEtale.rightDerivedUpperShriekCounit f K hK

end WeilConjectures.PurityFiniteSetting

namespace AlgebraicGeometry.ProEtale

/-- The bounded-below preservation required by the finite-level exceptional operation.
Source: blueprint def-weil-exceptional-inverse-image, its displayed D+ functor and the
paragraph asserting that its properties are theorems
(blueprint: def-weil-exceptional-inverse-image).

Proof: compactify the separated finite-type map by Nagata. The ambient scheme is of
finite type over the field, hence has finite dimension, as do all its geometric fibres,
with a common bound. Proper base change and the torsion cohomological-dimension theorem
bound the higher proper direct images of every module sheaf by twice that bound.
Extension by zero is exact, so the same bound applies to the compact-support functor.
The finite-width hypercohomology filtration extends this upper bound to every complex
concentrated in degrees at most m, with output at most m plus the common bound.
Apply Etale.hasBoundedBelowUpperShriek: t-structure orthogonality and the etale
adjunction then bound its right adjoint below. This concerns the ordinary etale
adjunction, not a right adjoint on the ambient pro-etale category.
-/
theorem finiteTypeHasBoundedBelowUpperShriek
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [HasCompactification f] :
    Etale.HasBoundedBelowUpperShriek (ModuleCat.{u + 1} Λ) f := by
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  infer_instance

/-- The actual transported finite-level exceptional functor, with its bounded-below
interface supplied by the finite-type theorem rather than assumed as an ambient datum.
It is exactly nu_X^* composed with the etale right adjoint and R nu_Y,*.
Source: blueprint def-weil-exceptional-inverse-image, finite-level displayed definition
(blueprint: def-weil-exceptional-inverse-image). -/
noncomputable def finiteTypeExceptionalInverseImage
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [HasCompactification f] :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ)) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  letI := finiteTypeHasBoundedBelowUpperShriek Λ k f
  rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) f

end AlgebraicGeometry.ProEtale
