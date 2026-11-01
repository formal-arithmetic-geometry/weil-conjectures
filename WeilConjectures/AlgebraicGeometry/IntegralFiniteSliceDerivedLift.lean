/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralFiniteSliceUnderivedSquare

/-! # Derived lift of the normalized finite slice square

Source: Stacks Tags 03DJ and 08JB; integral local structure, proof step 2.
(blueprint: lem-pe-integral-finite-slice-derived-lift).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Exact-derived composition lifts the underived normalized finite slice square.

Source: Stacks Tags 05RU and 06XY (exact functors descend to derived categories, compatibly
with composition and natural isomorphisms); integral local structure, proof step 2
(blueprint: lem-pe-integral-finite-slice-derived-lift).

Proof: let `F` be the given exact additive equivalence and `φ` the given natural isomorphism
`W.hom^* ⋙ F ≅ finiteEncodingFunctor e ⋙ sliceRestriction`. Take `G = D(F)`, the functor
induced by `F` on unbounded derived categories; it is an equivalence because `F` is. The
composition isomorphism gives `D(W.hom^*) ⋙ D(F) ≅ D(W.hom^* ⋙ F)`, the termwise extension
of `φ` gives `D(W.hom^* ⋙ F) ≅ D(finiteEncodingFunctor e ⋙ sliceRestriction)`, and the
composition isomorphism again gives `D(finiteEncodingFunctor e) ⋙ D(sliceRestriction)`,
which is `finiteEncodingDerived e ⋙ adicResidueRestriction` by definition. Slice
restriction is additive and exact (`ringedOverFunctor_*`), and an equivalence is additive. -/
theorem integralFinite_slice_derived_lift
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    ∀ (n : ℕ) (X : Scheme.{u}) (W : X.ProEt)
      (e : FiniteDiscreteOrdinary.Encoding
        (Padic.coefficientExtensionRing l E (n + 1)) X),
      ∀ (F : Mod (Sheaf (Scheme.ProEt.topology W.left) Ab.{u + 1})
            (AdicCompletion.finiteRing l E W.left n) ≌
          ConstantCompletion.Mod
            ((ConstantCompletion.constant
              (Scheme.coefficientProEtaleModelTopology.{u, u} X)
              (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))).over
                (AsSmall.up.obj W))),
        Nonempty
          ((CondensedRing.upperStar
              (DerivedNakayama.quotientRing l E (n + 1)) W.hom) ⋙ F.functor ≅
            IntegralFiniteEncoding.finiteEncodingFunctor
                (Padic.coefficientExtensionRing l E (n + 1)) X e ⋙
              integralFinite_sliceRestriction X
                (Padic.coefficientExtensionRing l E (n + 1))
                (AsSmall.up.obj W)) →
        ∃ G : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology W.left) Ab.{u + 1})
            (AdicCompletion.finiteRing l E W.left n)) ⥤
          ConstantCompletion.D
            ((ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X)
              (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))).over
                (AsSmall.up.obj W)),
        G.IsEquivalence ∧ Nonempty
          ((CondensedRing.upperStar (DerivedNakayama.quotientRing l E (n + 1))
              W.hom).mapDerivedCategory ⋙ G ≅
            IntegralFiniteEncoding.finiteEncodingDerived
                (Padic.coefficientExtensionRing l E (n + 1)) X e ⋙
              Scheme.adicResidueRestriction
                (ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X)
                  (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
                (AsSmall.up.obj W)) := by
  intro n X W e F hF
  obtain ⟨φ⟩ := hF
  have : F.functor.Additive := F.functor.additive_of_preserves_binary_products
  have : (integralFinite_sliceRestriction X (Padic.coefficientExtensionRing l E (n + 1))
      (AsSmall.up.obj W)).Additive :=
    ringedOverFunctor_additive _ _
  have : PreservesFiniteLimits (integralFinite_sliceRestriction X
      (Padic.coefficientExtensionRing l E (n + 1)) (AsSmall.up.obj W)) :=
    ringedOverFunctor_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (integralFinite_sliceRestriction X
      (Padic.coefficientExtensionRing l E (n + 1)) (AsSmall.up.obj W)) :=
    ringedOverFunctor_preservesFiniteColimits _ _
  let := HasDerivedCategory.standard (ConstantCompletion.Mod
    ((ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))).over
        (AsSmall.up.obj W)))
  refine ⟨F.functor.mapDerivedCategory, inferInstance, ⟨?_⟩⟩
  exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso φ ≪≫
    Functor.mapDerivedCategoryCompIso _ _

end AlgebraicGeometry.ProEtale
