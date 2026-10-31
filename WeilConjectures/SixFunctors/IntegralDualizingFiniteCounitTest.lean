/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingSystemTraceData
public import WeilConjectures.SixFunctors.CoefPairingExceptionalTests
import WeilConjectures.SixFunctors.FiniteTensorTestEtaleOrigin
import WeilConjectures.SixFunctors.FiniteDualizingUnboundedSupportComparison

/-! The finite exceptional counit tested against arbitrary scalar complexes. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem transported_counit_bijective
    {C D A B : Type*} [Category* C] [Category* D] [Category* A] [Category* B]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (P : C ⥤ A) (Q : D ⥤ B) (F : A ⥤ B) (β : P ⋙ F ≅ L ⋙ Q)
    (W : D) {Ω N : A} (o : P.obj (R.obj W) ≅ Ω)
    (J : C) (e : P.obj J ≅ N)
    (hP : Function.Bijective (fun f : J ⟶ R.obj W ↦ P.map f))
    (hQ : Function.Bijective (fun f : L.obj J ⟶ W ↦ Q.map f)) :
    Function.Bijective (fun g : N ⟶ Ω ↦
      F.map g ≫ F.map o.inv ≫ β.hom.app (R.obj W) ≫ Q.map (adj.counit.app W)) := by
  let es := (Equiv.ofBijective _ hP).trans (Iso.homCongr e o)
  let c : F.obj N ≅ Q.obj (L.obj J) := F.mapIso e.symm ≪≫ β.app J
  let et := (Equiv.ofBijective _ hQ).trans (Iso.homCongr c.symm (Iso.refl _))
  have he : (fun g : N ⟶ Ω ↦
      F.map g ≫ F.map o.inv ≫ β.hom.app (R.obj W) ≫ Q.map (adj.counit.app W)) =
      fun g ↦ et ((adj.homEquiv J W).symm (es.symm g)) := by
    funext g
    obtain ⟨f, rfl⟩ := es.surjective g
    simp only [Equiv.symm_apply_apply]
    dsimp [es, et, c, Iso.homCongr]
    rw [Adjunction.homEquiv_counit]
    simp only [Functor.map_comp, Category.assoc, Iso.map_hom_inv_id_assoc]
    have hn := β.hom.naturality f
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc (F.map (P.map f)), hn]
    simp only [Category.assoc, Category.comp_id]
  rw [he]
  exact et.bijective.comp ((adj.homEquiv J W).symm.bijective.comp es.symm.bijective)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

include hl in
/-- The transported ordinary exceptional counit represents finite duality on the
nth value of a scalar test tensored with a reduced finite-Tor constructible input.
This assertion is entirely in the finite coefficient categories: it has no quotient
system target, no supplied system trace, and no inverse-limit assembly.

Source: prop-coef-integral-dualizing, proof paragraph 2; the exceptional adjunction
and the finite duality site comparison in prop-asd-internal-adjunction.
(blueprint: lem-coef-finite-counit-test-bijective).

Proof: the finite tensor test has an unbounded etale origin J. The natural
unbounded compact-support comparison is normalized at the bounded below etale
dualizing object by the fixed finite counit. Comparison pullback induces a
bijection on maps into that bounded below object, and likewise on maps into
the base coefficient unit. Compose these two bijections with the ordinary etale
exceptional adjunction and conjugate by the origin isomorphisms. Naturality of
the compact-support comparison identifies the composite with compact-support
application followed by the specified counit. No boundedness is imposed on the
scalar test or on J. The argument also covers zero tests and empty schemes. -/
theorem integralDualizingFiniteCounit_test_bijective
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hK : finiteTorConstructibleIntegral l E X K) (n : ℕ)
    (T : DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E))) :
    Function.Bijective (fun g :
      (coefficientSequenceDerivedEvaluation l E X n).obj
        (S.systemClosed.tensor.obj
          ((G.frame.testPull S.systemClosed G.baseTensors.systemClosed).obj
            ((coefPairingEvaluationLeft l E n).obj T), S.reduction.obj K)) ⟶
          integralDualizingFiniteTerm l E D X n ↦
      (sfIntrinsicCompactSupport (finiteDualizingCompactification D X)
        (Padic.coefficientExtensionRing l E (n + 1))).map g ≫
          integralDualizingFiniteSystemCounit D l E X n) := by
  obtain ⟨J, ⟨e⟩⟩ := integralDualizingFiniteTest_etaleOrigin D l E X S G K hK n T
  obtain ⟨β, hβ⟩ := integralDualizingFiniteSupport_unboundedComparison D l hl E X n
  let P := finiteDualizingRealization l E X n
  let Q := finiteDualizingRealization l E (Spec (.of D.k)) n
  let ω := finiteDualizingEtaleTerm l E D X n
  let W := Etale.constantComplex (finiteDualizingCoeff l E n) (Spec (.of D.k))
  have hP : Function.Bijective (fun f : J ⟶ ω ↦ P.map f) :=
    ((sfIntrinsicDerivedEquivalence X
      (Padic.coefficientExtensionRing l E (n + 1))).fullyFaithfulFunctor.map_bijective _ _).comp
        (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map J ω
          (integralDualizingFiniteEtalePlus D l E X n))
  have hQ : Function.Bijective
      (fun f : (finiteDualizingEtaleSupport l E D X n).obj J ⟶ W ↦ Q.map f) :=
    (sfIntrinsicDerivedEquivalence (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (n + 1))).fullyFaithfulFunctor.map_bijective _ _
      |>.comp (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map _ W
        (Etale.boundaryCoefficientPlus (finiteDualizingCoeff l E n) (Spec (.of D.k))).property)
  have h := transported_counit_bijective (finiteDualizingEtaleAdjunction l E D X n)
    P Q _ β W (finiteDualizingOrigin l E D X n) J e hP hQ
  have hβ' :
      (sfIntrinsicCompactSupport (finiteDualizingCompactification D X)
        (Padic.coefficientExtensionRing l E (n + 1))).map
          (finiteDualizingOrigin l E D X n).inv ≫
        β.hom.app ((finiteDualizingEtaleExceptional l E D X n).obj W) ≫
        Q.map ((finiteDualizingEtaleAdjunction l E D X n).counit.app W) =
      integralDualizingFiniteSystemCounit D l E X n := hβ
  simpa only [Category.assoc, hβ'] using h

end WeilConjectures
