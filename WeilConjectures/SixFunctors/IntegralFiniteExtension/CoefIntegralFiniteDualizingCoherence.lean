/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionModels
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralScalarQuotientTransition
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefFiniteDualizingMixedQuotient

/-! # Transition coherence of finite dualizing coefficient comparisons

Source: lem-coef-integral-finite-extension, second and third paragraphs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

/-- The prescribed finite counit maps commute with every target quotient transition.
Source: current blueprint lem-coef-integral-finite-extension, paragraphs 3-4,
and finite dualizing quotient composition
(blueprint: lem-sf-integral-finite-dualizing-coherence).

Proof: expand quotient as completion followed by the normalized scalar tensor square.
Its transition formula is tensor reassociation and the actual quotient map. Substitute
wE.coherent and wL.coherent. At the cofinal ramification-multiple exponents, the
remaining equation is the finite-free dualizing counit comparison's quotient square.
At an arbitrary target exponent, factor through the larger ramification-multiple
quotient and use the finite dualizing quotient comparison. The two factorizations
of a later quotient agree by the finite comparison's composition equation. Transpose
these equations under scalar extension/restriction and the exceptional adjunction;
the units and counits used here are precisely those defining finiteEtaleU and finiteU.
The realization restriction square preserves those units and counits, so the same
identity holds on the pro-etale site. Finally cancel the target reduction isomorphism.
No integral lift or equality detection by finite evaluations is used. Identity
extensions, m=n, level zero (exponent one), and empty X obey the same formulas. -/
theorem finiteDualizing_reduction_coherent
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (wE : DualizingDatum l X D hl E) (wL : DualizingDatum l X D hl L) :
    let f := fun n : ℕ ↦
      (quotient l E L ι X n wE.omega.obj wE.omega.property.1).hom ≫
        (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).map
          (wE.reduction n).hom ≫ finiteU l E L ι X D n ≫ (wL.reduction n).inv
    ∀ {m n : ℕ} (h : n ≤ m),
      f m ≫ normalizedDVRReductionTransition l L X D hl h wL.omega.obj =
        normalizedDVRReductionTransition l L X D hl h
            ((integralScalarExtensionOfUniverses l E L ι X).obj wE.omega.obj) ≫
          (normalizedDVRRes l L X h).map (f n) := by
  dsimp only
  intro m n h
  let F (i : ℕ) := pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X i)
  let R := normalizedDVRRes l L X h
  let q (i : ℕ) := (quotient l E L ι X i wE.omega.obj wE.omega.property.1).hom
  let e (i : ℕ) := (wE.reduction i).hom
  let v (i : ℕ) := finiteU l E L ι X D i
  let tE := integralDualizingExceptionalTransition l E D X hl h
  let tL := integralDualizingExceptionalTransition l L D X hl h
  let dE := normalizedDVRReductionTransition l E X D hl h wE.omega.obj
  let dL := normalizedDVRReductionTransition l L X D hl h wL.omega.obj
  let dT := normalizedDVRReductionTransition l L X D hl h
    ((integralScalarExtensionOfUniverses l E L ι X).obj wE.omega.obj)
  let a := scalarReductionExchange l E L ι X h
  have hq : q m ≫ (F m).map dE ≫ a.app
        ((scalarReductionDerivedExtension l E X n).obj wE.omega.obj) =
      dT ≫ R.map (q n) :=
    quotient_reduction_transition l E L ι X D hl wE.omega.obj wE.omega.property.1 h
  have hv : (F m).map tE ≫ a.app (integralDualizingFiniteTerm l E D X n) ≫
      R.map (v n) = v m ≫ tL := finiteU_quotient_transition l E L ι X D hl h
  have he : e m ≫ tE = dE ≫ (normalizedDVRRes l E X h).map (e n) :=
    (wE.coherent h).symm
  have hn := a.naturality (e n)
  change (q m ≫ (F m).map (e m) ≫ v m ≫ (wL.reduction m).inv) ≫ dL =
    dT ≫ R.map (q n ≫ (F n).map (e n) ≫ v n ≫ (wL.reduction n).inv)
  apply (cancel_mono (R.map (wL.reduction n).hom)).1
  simp only [Category.assoc, ← R.map_comp, Iso.inv_hom_id, Category.comp_id]
  have hL : (wL.reduction m).inv ≫ dL ≫ R.map (wL.reduction n).hom = tL := by
    rw [wL.coherent h]
    simp only [Iso.inv_hom_id_assoc]
    rfl
  rw [hL]
  rw [← hv]
  rw [← (F m).map_comp_assoc, he, (F m).map_comp]
  simp only [Category.assoc]
  have hn' : (F m).map ((normalizedDVRRes l E X h).map (e n)) ≫
      a.app (integralDualizingFiniteTerm l E D X n) =
    a.app ((scalarReductionDerivedExtension l E X n).obj wE.omega.obj) ≫
      R.map ((F n).map (e n)) := hn
  rw [← Category.assoc ((F m).map ((normalizedDVRRes l E X h).map (e n))), hn']
  simpa only [Category.assoc, Functor.map_comp] using
    congrArg (fun z ↦ z ≫ R.map ((F n).map (e n)) ≫ R.map (v n)) hq

end WeilConjectures.IntegralFiniteExtension
