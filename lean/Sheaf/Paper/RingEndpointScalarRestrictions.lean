/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M7
-/
module

public import Sheaf.Paper.ConstructibleExceptionalCoefficientAssemblyData

/-! # Endpoint ring scalar restrictions -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] HasDerivedCategory.standard Padic
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] AlgebraicGeometry.Scheme.reductionDerivedChange
  AlgebraicGeometry.Scheme.completedAdicDerivedChange
  AlgebraicGeometry.Scheme.completedAdicChange AlgebraicGeometry.Scheme.reductionChange
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.presheafToSheaf
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

attribute [local instance] constructionInclusionShift

/-- Endpoint restrictions of allowed derived coefficient extensions, independently of
compactifications and exceptional adjunctions.
Source: Zheng, Lemma 5.22 and Propositions 5.24 and 5.26; scalar-mates plan steps 1 and 5
(blueprint: lem-sf-ring-endpoint-scalar-restrictions).

Proof: for a finite target use a flat representative of each finite-Tor object.
Derived base change retains its Tor interval, and finite scalar constructibility
identifies its cohomology with finite constructible target modules. Integral
reduction has the same property by its defining uniform bounds. Restrict the actual
ambient derived extension by ObjectProperty.lift, so both the inclusion equality and
its eqToIso realization are literal. For an integral generator restrict the published
strict-tower extension. Finite free completed scalar comparison identifies its
ordinary derived realization with the inverse completedScalarComparison; ramified
cofinality retains the uniform interval at all target levels. For identities and
composites with integral target use the tensor unit and associator to transport
these preservation statements and the same finite-free comparison. Induction on
Allowed gives preservation for every actual map; it is not necessary to choose
different restrictions for different witnesses. Give each restricted functor its
shift structure induced through the full target inclusion from the universal
scalar-counit shift. This makes its realization shift-compatible, and restriction
of distinguished triangles and additivity supplies exactness. The finite target
case always uses the literal lift; the completed generator case always uses the
strict-tower functor, so the two required normalizations are retained. Zero
objects and residue level n=1 use the same constructions. For every actual identity
coefficient map lift the ambient multiplication tensor unitor, preceded by the given
coefficient-map equality, through the fully faithful inclusion. Its map/preimage
equation gives precisely the ScalarIdentity normalization, independently of the
Allowed witness. No geometric operation
or compactification is used. -/
theorem exists_ring_endpoint_scalar_restrictions
    (D : FiniteFieldDatum.{max u v}) (_hl : l ≠ D.p) (W : Scheme.{max u v})
    [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))] :
    ∃ scalar : ∀ {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)),
      Allowed l a → Scalar.{u, v} l Ω a W,
    ∃ finiteScalar_eq : ∀ {s : RingStage.{max u v} l} (E : FieldStage.{max u v} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a),
      (scalar a ha).functor ⋙ RingStage.inclusion.{u, v} l Ω W (.finite E n) =
        RingStage.inclusion.{u, v} l Ω W s ⋙ pbcDerivedExtend (a.map W),
    (∀ {s : RingStage.{max u v} l} (E : FieldStage.{max u v} l) (n : ℕ+)
      (a : PurCompactSupport.Change (s.coefficients l)
        ((RingStage.finite E n).coefficients l))
      (ha : Allowed l (s := s) (t := .finite E n) a),
      (scalar a ha).realization = eqToIso (finiteScalar_eq E n a ha)) ∧
    (∀ (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier),
      (scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i)).functor ⋙
          RingStage.inclusion.{u, v} l Ω W (.integral L) =
        RingStage.inclusion.{u, v} l Ω W (.integral E) ⋙
          integralScalarExtensionOfUniverses l E.carrier L.carrier i W) ∧
    (∀ (E L : FieldStage.{max u v} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (K : C.{u, v} l Ω W (.integral E)),
      HEq ((scalar (s := .integral E) (t := .integral L)
        (PurCompactSupport.completedChange l E.carrier L.carrier i)
        (Allowed.integral E L i)).realization.inv.app K)
        ((completedScalarComparison l E.carrier L.carrier i W).app K.obj)) ∧
    (∀ {s t : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l))
      (ha : Allowed l a), (scalar a ha).realization.hom.CommShift ℤ) ∧
    (∀ {s : RingStage.{max u v} l}
      (a : PurCompactSupport.Change (s.coefficients l) (s.coefficients l))
      (h : ∀ T : Scheme.{max u v}, a.map T = 𝟙 _) (ha : Allowed l a),
      Nonempty (ScalarIdentity.{u, v} l Ω h W (scalar a ha))) := by sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
