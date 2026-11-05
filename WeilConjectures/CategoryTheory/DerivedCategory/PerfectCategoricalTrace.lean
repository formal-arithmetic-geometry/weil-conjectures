/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFiniteCohomologyComplexes
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectPackageOnSiteSupplement
public import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The scalar-valued categorical trace of a perfect ring complex

Source: Weil conjectures blueprint, smooth purity,
`sk-prop-sf-trace-perfectness/def-trf-categorical-trace.md`, order 1826
(blueprint: def-trf-categorical-trace).

Perfect objects use the recorded bounded finite-projective predicate. Their dual is the
actual derived internal Hom into the tensor unit. Evaluation is its counit, with the
canonical Koszul symmetry putting the dual first. Coevaluation is the inverse image of
the identity under the canonical tensor--Hom comparison; thus it is determined by
that comparison, with no choice of an unspecified duality datum. On a bounded projective
model this inverse is the finite dual-frame sum in the node. The symmetry is constructed
by descent of the signed symmetry of complexes, rather than chosen from mere existence.

The upstream internal Hom uses the tensor-left adjunction convention. Its comparison
with the recorded total module Hom multiplies the component from model degree `p`
in Hom degree `j` by `(-1)^(p*j)`. For dual evaluation `p + j = 0`, this cancels
the Koszul sign from putting the dual first; evaluation is therefore `φ ⊗ x ↦ φ(x)`.
The corresponding coevaluation is the unsigned finite dual-frame sum.

The auxiliary model dual and frame maps use the recorded total Hom complex and splitting
package. The scalar identification uses the inverse Hom bijection of the degree-zero
embedding and evaluation at one. No cohomological supertrace formula is used to define it.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace DerivedCategory

/-- The actual Koszul braiding descended from the homotopy category.
Source: blueprint order 1826, signed tensor symmetry
(blueprint: def-trf-categorical-trace). -/
@[instance_reducible]
noncomputable def perfectTraceCanonicalBraiding
    (C : Type v) [Category.{u} C] [Abelian C] [IsGrothendieckAbelian.{u} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory.{u} C] :
    BraidedCategory (DerivedCategory C) :=
  DerivedMonoidal.braidedCategory' (Qh (C := C))
    (HomotopyCategory.quasiIso C (.up ℤ))

variable {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]

/-- The derived dual `RHom_R(P,R)`.
Source: blueprint order 1826 (blueprint: def-trf-categorical-trace). -/
noncomputable def perfectTraceDual (P : DerivedCategory (ModuleCat.{u} R)) :
    DerivedCategory (ModuleCat.{u} R) :=
  (ihom P).obj (𝟙_ _)

/-- The canonical right-dual datum, constructed from the internal Hom and the inverse
of its tensor--Hom comparison. No dual object or pairing is chosen from `Nonempty`.
Source: blueprint order 1826 (blueprint: def-trf-categorical-trace). -/
@[instance_reducible]
noncomputable def perfectTraceHasRightDual (P : DerivedCategory (ModuleCat.{u} R))
    (hP : IsPerfectRingComplex P) : HasRightDual P :=
  letI := perfectTraceCanonicalBraiding (ModuleCat.{u} R)
  letI := IsPerfect.isIso_ihomUnitTensorToIhom hP P
  letI : ExactPairing (perfectTraceDual P) P := MonoidalClosed.exactPairingOfIsIso P
  { rightDual := perfectTraceDual P
    exact := BraidedCategory.exactPairing_swap (perfectTraceDual P) P }

/-- The scalar attached to an endomorphism of `R[0]`: transport from the tensor unit,
apply the inverse Hom bijection for the fully faithful single functor, then evaluate at one.
Source: blueprint order 1826 (blueprint: def-trf-categorical-trace). -/
noncomputable def perfectTraceScalar
    (f : 𝟙_ (DerivedCategory (ModuleCat.{u} R)) ⟶ 𝟙_ _) : R :=
  ((singleFunctor (ModuleCat.{u} R) 0).preimage
    ((singleFunctorObjUnitIso (ModuleCat.{u} R)).hom ≫ f ≫
      (singleFunctorObjUnitIso (ModuleCat.{u} R)).inv)).hom 1

/-- The categorical trace is coevaluation, `v ⊗ 1`, the signed symmetry, and evaluation,
read as a scalar by the degree-zero Hom bijection.
Source: blueprint order 1826 (blueprint: def-trf-categorical-trace). -/
noncomputable def perfectCategoricalTrace (P : DerivedCategory (ModuleCat.{u} R))
    (hP : IsPerfectRingComplex P) (v : P ⟶ P) : R :=
  letI := perfectTraceCanonicalBraiding (ModuleCat.{u} R)
  letI := perfectTraceHasRightDual P hP
  perfectTraceScalar (MonoidalCategory.trace v)

end DerivedCategory

namespace WeilConjectures

end WeilConjectures
