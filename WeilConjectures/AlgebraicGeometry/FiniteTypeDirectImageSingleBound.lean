/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteConstructibleEncoding
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteRestrictionEncoding
import WeilConjectures.AlgebraicGeometry.FiniteTypeAlgClHeartFiniteImage
import WeilConjectures.AlgebraicGeometry.FiniteTypeIntegralHeartBound
import WeilConjectures.AlgebraicGeometry.FiniteTypeRationalHeartIntegralImage
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.AlgebraicGeometry.UnboundedDirectImageBoundedBelow
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage

/-! # Finiteness of direct images of constructible sheaves in degree zero -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

include ℓ k

private theorem rational_single_bound
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E]
    (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left) F) :
    ∃ b : ℤ, ((R((f.left)_*⟦Profinite.continuousMapRingObj E⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE b := by
  obtain ⟨N, hN, ⟨e⟩⟩ := finiteTypeRationalHeart_integralImage ℓ f E F hF
  obtain ⟨b, hb⟩ := finiteTypeIntegralHeart_boundedAbove ℓ f E N hN
  let S := Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) Y.left)
  have : PreservesFiniteLimits S := integralScalarExtension_exact ℓ E Y.left
  have : (((R((f.left)_*⟦integralCoeff ℓ E⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj N))).IsLE b := hb
  have hs := S.isLE_mapDerivedCategory_obj
    ((R((f.left)_*⟦integralCoeff ℓ E⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj N)) b
  have hloc := DerivedCategory.TStructure.t.isLE_of_iso
    (S.leftDerivedFunctorIsoMapDerivedCategory.app
      ((R((f.left)_*⟦integralCoeff ℓ E⟧)).obj
        ((DerivedCategory.singleFunctor _ 0).obj N))).symm b
  exact ⟨b, DerivedCategory.TStructure.t.isLE_of_iso e b⟩

private theorem integral_subring_single_bound
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (O : Subring E) (hO : O = continuousIntegers ℓ E)
    (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj O) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj O) X.left) F) :
    ∃ b : ℤ, ((R((f.left)_*⟦Profinite.continuousMapRingObj O⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE b := by
  subst O
  exact finiteTypeIntegralHeart_boundedAbove ℓ f E F hF

/-- The direct image of a constructible `ℚ̲̄_ℓ`-sheaf placed in degree zero is bounded above.
The other coefficient rings of Deligne's finiteness theorem are the declarations of the same
name in the namespaces `ContinuousMapRingObj`, `PadicIntegersRingObj`, `UnitBallRingObj` and
`FiniteDiscreteRingObj`.

Source: Deligne, SGA 4½, Th. finitude 1.1; Bhatt--Scholze, Sections 6.7--6.8;
blueprint `lem-sfb-dc-lower-star-preserves`, coefficient-reduction argument.
(auxiliary; not a blueprint node)

Proof: finite type over a field makes both schemes noetherian of finite dimension and
makes the morphism qcqs. For finite discrete coefficients killed by a power of ell,
use the classical etale model and the finite cohomological bound in Deligne's theorem.
For integral coefficients, a constructible sheaf is derived complete and its derived
residue-field reduction is bounded constructible on the etale site. Direct image
commutes with derived inverse limits and with this reduction, since the residue field
is a perfect coefficient complex. The uniform finite-coefficient direct-image bound
and the integral completeness criterion imply boundedness above of the integral image.
For rational coefficients choose a constructible integral sheaf model and use the
qcqs comparison of direct image with inversion of the uniformizer. Localization is
exact and preserves the bound. For the algebraic closure descend the constructible
sheaf to a finite extension, apply its bound, and use the direct-image scalar-change
comparison and exact extension to the algebraic closure. For embedded integer rings,
the induced norm identifies their subrings with the closed unit ball by equality.
The general closed-unit-ball case uses its defining norm inequality. The finite
torsion argument also covers the zero coefficient ring and n=0, since its
annihilating exponent is then one. These arguments concern only a single sheaf, not a general
bounded complex; finite truncation induction is performed by the consumer. -/
theorem finiteTypeDirectImage_single_boundedAbove
    (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))
    (hF : IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) F) :
    ∃ b : ℤ, ((R((f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE b := by
  obtain ⟨E, N, hN, ⟨e⟩⟩ := finiteTypeAlgClHeart_finiteImage ℓ f F hF
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : NormedAlgebra ℚ_[ℓ] E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  obtain ⟨b, hb⟩ := rational_single_bound ℓ f E.1 N hN
  let S := Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl Y.left ℓ E)
  have : ((R((f.left)_*⟦Profinite.continuousMapRingObj E.1⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj N)).IsLE b := hb
  have hs := S.isLE_mapDerivedCategory_obj
    ((R((f.left)_*⟦Profinite.continuousMapRingObj E.1⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj N)) b
  have hloc := DerivedCategory.TStructure.t.isLE_of_iso
    (S.leftDerivedFunctorIsoMapDerivedCategory.app
      ((R((f.left)_*⟦Profinite.continuousMapRingObj E.1⟧)).obj
        ((DerivedCategory.singleFunctor _ 0).obj N))).symm b
  exact ⟨b, DerivedCategory.TStructure.t.isLE_of_iso e b⟩

namespace ContinuousMapRingObj

/-- The direct image of a constructible `E̲`-sheaf placed in degree zero is bounded above, for a
finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` (the case `E̲` of
`ProEtale.CondensedRing.finiteTypeDirectImage_single_boundedAbove`). -/
theorem finiteTypeDirectImage_single_boundedAbove (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E) X.left) F) :
    ∃ b : ℤ, ((R((f.left)_*⟦Profinite.continuousMapRingObj E⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE b := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let : NormedAlgebra ℚ_[ℓ] E.1 :=
    { norm_smul_le c x := by
        change ‖algebraMap E.1 (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.1 (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  exact rational_single_bound ℓ f E.1 F hF

end ContinuousMapRingObj

namespace PadicIntegersRingObj

/-- The direct image of a constructible `𝒪̲_E`-sheaf placed in degree zero is bounded above, for a
finite subextension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` (the case `𝒪̲_E` of
`ProEtale.CondensedRing.finiteTypeDirectImage_single_boundedAbove`). -/
theorem finiteTypeDirectImage_single_boundedAbove
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    (F : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left))
    (hF : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) F) :
    ∃ b : ℤ, ((R((f.left)_*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsLE b := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let : NormedAlgebra ℚ_[ℓ] E :=
    { norm_smul_le c x := by
        change ‖algebraMap E (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  have hO : (PadicAlgCl.integers ℓ E).toSubring = continuousIntegers ℓ E := by
    ext x
    rfl
  exact integral_subring_single_bound ℓ f E _ hO F hF

end PadicIntegersRingObj

namespace UnitBallRingObj

end UnitBallRingObj

namespace FiniteDiscreteRingObj

end FiniteDiscreteRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
