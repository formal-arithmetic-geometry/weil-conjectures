/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Paper.PointFiniteCohomologyComplexes
public import Sheaf.Algebra.Homology.ModuleHomComplex
public import Sheaf.Paper.StrictPerfectPackageOnSite
public import Sheaf.Algebra.Homology.BoundedFlatKFlat
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

/-- The full category of perfect objects, not the category of all bounded finite-cohomology
objects or of unquotiented chain maps. Source: blueprint order 1826
(blueprint: def-trf-categorical-trace). -/
def perfectTraceCategory (R : Type u) [CommRing R]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)] :=
  ObjectProperty.FullSubcategory
    (IsPerfectRingComplex (R := R) : ObjectProperty (DerivedCategory (ModuleCat.{u} R)))

/-- The strict model for the dual, using the recorded module-valued total Hom, including
its signed differential. Source: blueprint order 1826
(blueprint: def-trf-categorical-trace). -/
noncomputable def perfectTraceModelDual (B : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  CochainComplex.moduleHomComplex B
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))

/-- The frame vector `π_i(u_a)` from the recorded splitting package.
Source: blueprint order 1826 (blueprint: def-trf-categorical-trace). -/
noncomputable def perfectTraceFrameVector {B : CochainComplex (ModuleCat.{u} R) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage B) (i : ℤ) (a : Fin (s.N i)) : B.X i :=
  (s.p i).hom (Pi.single a 1)

/-- The frame functional `pr_a ∘ ι_i` from the same package.
Source: blueprint order 1826 (blueprint: def-trf-categorical-trace). -/
noncomputable def perfectTraceFrameFunctional {B : CochainComplex (ModuleCat.{u} R) ℤ}
    (s : ModuleCat.StrictPerfectCoefficientPackage B) (i : ℤ) (a : Fin (s.N i)) :
    Module.Dual R (B.X i) :=
  (LinearMap.proj a).comp (s.i i).hom

/-- The derived dual `RHom_R(P,R)`.
Source: blueprint order 1826 (blueprint: def-trf-categorical-trace). -/
noncomputable def perfectTraceDual (P : DerivedCategory (ModuleCat.{u} R)) :
    DerivedCategory (ModuleCat.{u} R) :=
  (ihom P).obj (𝟙_ _)

/-- Contravariance of the derived dual, used in the representative transport
`α^∨ : P^∨ ⟶ Q(B)^∨`. Source: blueprint order 1826
(blueprint: def-trf-categorical-trace). -/
noncomputable def perfectTraceDualMap {P Q : DerivedCategory (ModuleCat.{u} R)}
    (f : P ⟶ Q) : perfectTraceDual Q ⟶ perfectTraceDual P :=
  (MonoidalClosed.pre f).app (𝟙_ _)

/-- Evaluation, with the dual as the first tensor factor. Under the signed comparison
from upstream internal Hom to `perfectTraceModelDual`, it evaluates a homogeneous
functional on a vector, and is zero in nonzero total degree.
Source: blueprint order 1826 (blueprint: def-trf-categorical-trace). -/
noncomputable def perfectTraceEvaluation (P : DerivedCategory (ModuleCat.{u} R)) :
    perfectTraceDual P ⊗ P ⟶ 𝟙_ (DerivedCategory (ModuleCat.{u} R)) :=
  letI := perfectTraceCanonicalBraiding (ModuleCat.{u} R)
  (β_ _ _).hom ≫ (ihom.ev P).app _

/-- Coevaluation is the preimage of the identity under the canonical tensor--Hom
comparison. On a bounded projective model it sends one to the finite sum of the frame
vectors tensored with their functionals. Source: blueprint order 1826
(blueprint: def-trf-categorical-trace). -/
noncomputable def perfectTraceCoevaluation (P : DerivedCategory (ModuleCat.{u} R))
    (hP : IsPerfectRingComplex P) :
    𝟙_ (DerivedCategory (ModuleCat.{u} R)) ⟶ P ⊗ perfectTraceDual P :=
  letI := perfectTraceCanonicalBraiding (ModuleCat.{u} R)
  letI := IsPerfect.isIso_ihomUnitTensorToIhom hP P
  MonoidalClosed.coevaluationOfIsIso P ≫ (β_ P (perfectTraceDual P)).inv

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

/-- The inverse scalar construction sends `a` to the derived image of multiplication by `a`.
Source: blueprint order 1826 (blueprint: def-trf-categorical-trace). -/
noncomputable def perfectTraceScalarInverse (a : R) :
    𝟙_ (DerivedCategory (ModuleCat.{u} R)) ⟶ 𝟙_ _ :=
  (singleFunctorObjUnitIso (ModuleCat.{u} R)).inv ≫
    (singleFunctor (ModuleCat.{u} R) 0).map (ModuleCat.ofHom (a • LinearMap.id)) ≫
    (singleFunctorObjUnitIso (ModuleCat.{u} R)).hom

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

/-- The trace over exactly `A_{E,n}` from the fixed global datum and coefficient closure:
`E` is a finite intermediate field in that closure, and `n ≥ 1`.
Source: blueprint order 1826 (blueprint: def-trf-categorical-trace). -/
noncomputable def finiteCoefficientCategoricalTrace (D : FiniteFieldDatum.{u})
    (c : D.CoefficientDatum) (E : IntermediateField (Padic c.l) c.Qbar)
    [FiniteDimensional (Padic c.l) E] (n : ℕ) (_hn : 1 ≤ n)
    (P : DerivedCategory (ModuleCat.{u} (Padic.coefficientExtensionRing c.l E n)))
    (hP : DerivedCategory.IsPerfectRingComplex P) (v : P ⟶ P) :
    Padic.coefficientExtensionRing c.l E n :=
  DerivedCategory.perfectCategoricalTrace P hP v

end WeilConjectures
