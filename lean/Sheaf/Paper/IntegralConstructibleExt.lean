/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import Mathlib.Algebra.CharP.CharAndCard
import Sheaf.SixFunctors.IntegralExtHomContinuity
import Sheaf.Paper.IntegralStratumExtBound
import Sheaf.Paper.IntegralCoefficientExtComparison

/-!
# Continuity and boundedness of integral constructible Ext

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-ext/_section.md
and sk-lem-int-ext.proof.md (blueprint: sk-lem-int-ext).
The derived category is the ordinary unbounded category of module objects over the
pulled-back condensed valuation ring. No completeness or finite Tor condition is added
to its arbitrary second arguments in the continuity assertion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Continuity for each integer shift and a bound uniform in the second constructible sheaf.
Source: blueprint main-20261015, sk-lem-int-ext, assertions 1--2
(blueprint: sk-lem-int-ext).

Proof: Fix a bounded constructible C and an integer q. The statement of
`det-lem-int-ext-continuity` gives that the canonical map from the colimit of
Hom(C,K_i[q]) to Hom(C,(colim K_i)[q]) is an isomorphism for every filtered diagram
of complexes with a common termwise lower bound. This is the first conjunct.
For the second conjunct fix a constructible sheaf C. The final consequence of
`det-lem-int-ext-bound` gives an integer d_C, independent of N, above which all
Ext(C,N) vanish for constructible N. Its proof reduces C by a finite filtration
to extensions by zero of finite constant local models on strata. The closed-support
fibre sequence, finite Tor amplitude of the dual, and finite cohomological dimensions
bound the Ext groups of each reduction of N. Derived completeness and the Milnor
sequence add at most one to that bound. Taking a maximum over the finitely many pieces
gives d_C. Ext in integer degree q is the ambient Hom from C[0] to N[0][q]; its vanishing
is expressed by Subsingleton on that abelian Hom group. The existing bound uses spectral
integral coefficients in the scheme universe. Transport to that presentation using
`integralCoefficientExtComparison`; its additive equivalence induces a fully faithful
functor on unbounded derived categories. The singleFunctor and shift comparison
isomorphisms identify the two shifted Hom groups, so cancellation transports vanishing
back to the original embedded coefficients. -/
theorem integralConstructibleExt
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ D.p)
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))] :
    (∀ C : DerivedCategory
        (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X C →
      ∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
        (K : I ⥤ CochainComplex
          (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)) ℤ),
        (∃ b : ℤ, ∀ (i : I) (r : ℤ), r < b → IsZero ((K.obj i).X r)) →
        ∀ q : ℤ, IsIso (colimit.desc _
          ((DerivedCategory.Q ⋙ shiftFunctor _ q ⋙ preadditiveCoyoneda.obj (op C)).mapCocone
            (colimit.cocone K)))) ∧
    (∀ C : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X),
      IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X C →
      ∃ d : ℤ, ∀ N : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X),
        IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X N →
        ∀ q : ℤ, d < q →
          Subsingleton (((DerivedCategory.singleFunctor _ 0).obj C) ⟶
            ((DerivedCategory.singleFunctor _ 0).obj N)⟦q⟧)) := by
  classical
  have hchar0 : ringChar D.k₀ = D.p := by
    let : Fact D.p.Prime := ⟨D.prime⟩
    let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    have hc : Fintype.card D.k₀ = D.q := by
      simpa only [Nat.card_eq_fintype_card] using D.card_base
    have hcp : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      (hc.trans D.cardinality_eq)
    exact ringChar.eq D.k₀ D.p
  have hchar : ringChar D.k = D.p := by
    exact (Algebra.ringChar_eq D.k₀ D.k).symm.trans hchar0
  let : Fact (ringChar D.k).Prime := ⟨hchar ▸ D.prime⟩
  let : Fact (ringChar D.k ≠ ℓ) := ⟨by
    rw [hchar]
    exact Ne.symm _hℓ⟩
  let Xo : Over (Spec (.of D.k)) := Over.mk (X ↘ Spec (.of D.k))
  let : LocallyOfFiniteType Xo.hom := by
    change LocallyOfFiniteType (X ↘ Spec (.of D.k))
    infer_instance
  let : QuasiCompact Xo.hom := by
    change QuasiCompact (X ↘ Spec (.of D.k))
    infer_instance
  let : IsSeparated Xo.hom := by
    change IsSeparated (X ↘ Spec (.of D.k))
    infer_instance
  constructor
  · intro C hC I _ _ K hK q
    obtain ⟨b, hb⟩ := hK
    exact CondensedRing.integralExtHomContinuous (k := D.k) (E := E.val)
      (X := Xo) C hC K b hb q
  · have : FiniteDimensional ℚ_[ℓ] (ULift.{u} E.val) :=
      Module.Finite.equiv (ULift.moduleEquiv.symm : E.val ≃ₗ[ℚ_[ℓ]] ULift.{u} E.val)
    obtain ⟨F, hAdd, hF⟩ := integralCoefficientExtComparison ℓ E X
    let : F.functor.Additive := hAdd
    intro C hC
    obtain ⟨d, hd⟩ :=
      (CondensedRing.integral_stratum_ext_bound D ℓ _hℓ (ULift.{u} E.val) X).2
        (F.functor.obj C) (hF C hC)
    refine ⟨(d : ℤ), ?_⟩
    intro N hN q hq
    have hvan := hd (F.functor.obj N) (hF N hN) q hq
    let eC := (F.functor.mapDerivedCategorySingleFunctor 0).app C
    let eN := (F.functor.mapDerivedCategory.commShiftIso q).app
      ((DerivedCategory.singleFunctor _ 0).obj N) ≪≫
      (shiftFunctor _ q).mapIso ((F.functor.mapDerivedCategorySingleFunctor 0).app N)
    refine ⟨fun f g ↦ ?_⟩
    apply F.functor.mapDerivedCategory.map_injective
    apply (cancel_mono eN.hom).mp
    apply (cancel_epi eC.inv).mp
    exact hvan.elim _ _

end AlgebraicGeometry.ProEtale
