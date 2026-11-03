/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierModels
import WeilConjectures.AlgebraicGeometry.Finite.FiniteStageVerdierBiduality
import WeilConjectures.SixFunctors.IntegralVerdier.FiniteIntrinsicBidualComparison

/-! # Finite intrinsic geometric biduality

Source: Stacks Project, Tags 06YL and 08J9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
namespace WeilConjectures.IntegralVerdier

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] ProEtale.sheafBraidedCategory

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

include hl in
/-- The finite geometric biduality theorem in the intrinsic coefficient presentation,
with the evaluation transpose belonging to any normalized tensor presentation.

Source: thm-fix-general-biduality and lem-weil-finite-duality-site-comparison;
Stacks Project, Tags 08J9 and 08JA
(blueprint: lem-sf-finite-intrinsic-verdier-biduality).

Proof: the canonical constant-scalar realization is an exact equivalence from
fixed-scalar pro-etale module sheaves to modules over the constant ring sheaf.
Its scalar sheafification unit identifies the regular units; its derived
closed-tensor comparison identifies internal Hom and evaluation. The
exceptional-object comparison identifies the fixed-scalar dualizing complex
with integralDualizingFiniteTerm. Intrinsic constructibility and the supplied
Tor interval correspond to the fixed-scalar finite-Tor constructible predicate
by transport along the realization counit: that predicate is defined using
intrinsic realization, and Tor amplitude quantifies over all representatives.
Apply finite-stage Verdier biduality to this fixed-scalar object. Both the
fixed-scalar pairing and the given tensor presentation are normalized on
K-flat representatives by the signed Hom-complex evaluation. Thus the
realization comparison takes its biduality arrow, including both
contravariant comparison factors, to precisely delta below. Its three
comparison factors are isomorphisms. The finite-stage biduality map is an
isomorphism, so cancellation proves that delta is an isomorphism.
No perfectness of M on the pro-etale site is asserted or used. -/
theorem finiteIntrinsicVerdier_biduality (n : ℕ)
    (a : IntegralHom.TensorPresentation.{u, u} X (integralCoefficientCommRingSheaf l E X n))
    (s : SignedSymmetry X (integralCoefficientCommRingSheaf l E X n) a)
    (hs : ∀ (K L K' L' : DerivedCategory (scalarReductionTarget l E X n))
      (f : K ⟶ K') (g : L ⟶ L'),
      a.tensor.map (Prod.mkHom f g) ≫ (s.swap K' L').hom =
        (s.swap K L).hom ≫ a.tensor.map (Prod.mkHom g f))
    (he : ∀ (K K' W : DerivedCategory (scalarReductionTarget l E X n))
      (f : K' ⟶ K),
      a.tensor.map (Prod.mkHom (𝟙 K')
        ((IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).map
          (Prod.mkHom f.op (𝟙 W)))) ≫ (a.adjunction K').counit.app W =
      a.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (a.adjunction K).counit.app W)
    (M : DerivedCategory (scalarReductionTarget l E X n))
    (hM : intrinsicFiniteTorsionConstructible l E (n + 1) (by omega) X M)
    (p q : ℤ) (hTor : HasProEtaleTorAmplitude X
      (Padic.coefficientExtensionRing l E (n + 1)) M p q) :
    IsIso (delta X a s (integralDualizingFiniteTerm l E D X n) M) := by
  let B := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite B := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let e := sfIntrinsicDerivedEquivalence X B
  let K := e.inverse.obj M
  let i : e.functor.obj K ≅ M := e.counitIso.app M
  have hK : finiteTorConstructibleProEtaleModule l E (n + 1) (by omega) X K := by
    change finiteTorConstructible l E (n + 1) (by omega) X (e.functor.obj K)
    refine ⟨?_, p, q, hTor.1, ?_⟩
    · exact (Scheme.finiteTorsionConstructible D l hl E (n + 1) (by omega) X).prop_of_iso
        i.symm hM
    · intro N P he' f hf hP Q j hj
      exact hTor.2 N P (he'.map (fun z ↦ z ≪≫ i)) f hf hP Q j hj
  have hb := (finite_stage_verdier_biduality D l hl E (n + 1) (by omega)
    X (X ↘ Spec (.of D.k))).2
  obtain ⟨_, h, hh⟩ := hb
  let W := (ProEtale.sfFiniteExceptionalFixed B
    (NagataCompactification (X ↘ Spec (.of D.k)))).obj (𝟙_ _)
  let w : e.functor.obj W ≅ integralDualizingFiniteTerm l E D X n :=
    e.functor.mapIso ((ProEtale.sfFiniteExceptionalFixed B
      (finiteDualizingCompactification D X)).mapIso
        ((sfIntrinsicDerivedEquivalence (Spec (.of D.k)) B).unitIso.app (𝟙_ _) ≪≫
          (sfIntrinsicDerivedEquivalence (Spec (.of D.k)) B).inverse.mapIso
            (finiteDualizingIntrinsicUnit l E (Spec (.of D.k)) n)))
  obtain ⟨c, hc⟩ := finiteIntrinsicBidualComparison X B a s hs he W K h
    (integralDualizingFiniteTerm l E D X n) M w i
  have := hh K hK
  have hiso : IsIso (i.hom ≫ delta X a s (integralDualizingFiniteTerm l E D X n) M) := by
    rw [hc]
    infer_instance
  exact (isIso_comp_left_iff i.hom _).mp hiso

end WeilConjectures.IntegralVerdier
