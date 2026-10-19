/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurityRankOneSectionData
import Sheaf.Paper.PurityFiniteLineCohomology
import Sheaf.AlgebraicGeometry.AffinePuncturedLineAlgebra
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Algebra
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite

/-! # Ordinary rank-one calculation before localization

Source: Milne, Lectures on Etale Cohomology, Sections 9, 14 and 16;
blueprint thm-pur-rank-one-local-calculation, Steps 1--3 and 5.
(blueprint: lem-pur-rank-one-etale-calculation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.RankOne

private def lineRingEquiv (Ω : Type u) [Field Ω] :
    Polynomial Ω ≃+* Γ(Line (Spec (CommRingCat.of Ω)), ⊤) := by
  let e := AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of Ω)
  let c := (MvPolynomial.uniqueAlgEquiv Ω (ULift.{u} (Fin 1))).toRingEquiv
  exact c.symm.trans (((Scheme.ΓSpecIso _).symm ≪≫
    Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv)

private theorem lineRingEquiv_X (Ω : Type u) [Field Ω] :
    lineRingEquiv Ω Polynomial.X = coordinate (Spec (CommRingCat.of Ω)) := by
  dsimp only [lineRingEquiv, RingEquiv.trans_apply]
  change (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of Ω)).hom.appTop
    ((Scheme.ΓSpecIso _).inv
      ((MvPolynomial.uniqueAlgEquiv Ω (ULift.{u} (Fin 1))).symm Polynomial.X)) = _
  rw [show (MvPolynomial.uniqueAlgEquiv Ω (ULift.{u} (Fin 1))).symm Polynomial.X =
    MvPolynomial.X (ULift.up 0) by
      change Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X default) Polynomial.X = _
      rw [Polynomial.eval₂_X]
      congr 1]
  change _ = AffineSpace.coord _ (ULift.up 0)
  rw [← AffineSpace.SpecIso_inv_appTop_coord]
  simp [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]

set_option backward.isDefEq.respectTransparency false in
private theorem lineRingEquiv_C (Ω : Type u) [Field Ω] (a : Ω) :
    lineRingEquiv Ω (Polynomial.C a) =
      (lineProjection (Spec (CommRingCat.of Ω))).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv a) := by
  dsimp only [lineRingEquiv, RingEquiv.trans_apply]
  change (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of Ω)).hom.appTop
    ((Scheme.ΓSpecIso _).inv
      ((MvPolynomial.uniqueAlgEquiv Ω (ULift.{u} (Fin 1))).symm (Polynomial.C a))) = _
  rw [show (MvPolynomial.uniqueAlgEquiv Ω (ULift.{u} (Fin 1))).symm (Polynomial.C a) =
    MvPolynomial.C a by
      change Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X default) (Polynomial.C a) = _
      rw [Polynomial.eval₂_C]]
  rw [AffineSpace.SpecIso_hom_appTop]
  simp [lineProjection]
  rfl

set_option backward.isDefEq.respectTransparency false in
private def puncturedRingEquiv (Ω : Type u) [Field Ω] :
    LaurentPolynomial Ω ≃+* Γ(Punctured (Spec (CommRingCat.of Ω)), ⊤) := by
  let X := Line (Spec (CommRingCat.of Ω))
  let : IsAffine X := inferInstanceAs
    (IsAffine (AffineSpace (ULift.{u} (Fin 1)) (Spec (CommRingCat.of Ω))))
  let : Algebra Γ(Line (Spec (CommRingCat.of Ω)), ⊤)
      Γ(Punctured (Spec (CommRingCat.of Ω)), ⊤) :=
    (openImmersion (Spec (CommRingCat.of Ω))).appTop.hom.toAlgebra
  let : IsLocalization.Away (coordinate (Spec (CommRingCat.of Ω)))
      Γ(Punctured (Spec (CommRingCat.of Ω)), ⊤) :=
    Γ_restrict_isLocalization X (coordinate (Spec (CommRingCat.of Ω)))
  apply IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (Polynomial.X : Polynomial Ω))
    (T := Submonoid.powers (coordinate (Spec (CommRingCat.of Ω))))
    _ _ (lineRingEquiv Ω)
  rw [Submonoid.map_powers]
  change Submonoid.powers (lineRingEquiv Ω Polynomial.X) = _
  rw [lineRingEquiv_X]

set_option backward.isDefEq.respectTransparency false in
private theorem puncturedRingEquiv_toLaurent (Ω : Type u) [Field Ω] (p : Polynomial Ω) :
    puncturedRingEquiv Ω (Polynomial.toLaurent p) =
      (openImmersion (Spec (CommRingCat.of Ω))).appTop (lineRingEquiv Ω p) := by
  let : Algebra Γ(Line (Spec (CommRingCat.of Ω)), ⊤)
      Γ(Punctured (Spec (CommRingCat.of Ω)), ⊤) :=
    (openImmersion (Spec (CommRingCat.of Ω))).appTop.hom.toAlgebra
  let : IsAffine (Line (Spec (CommRingCat.of Ω))) := inferInstanceAs
    (IsAffine (AffineSpace (ULift.{u} (Fin 1)) (Spec (CommRingCat.of Ω))))
  let : IsLocalization.Away (coordinate (Spec (CommRingCat.of Ω)))
      Γ(Punctured (Spec (CommRingCat.of Ω)), ⊤) :=
    Γ_restrict_isLocalization _ (coordinate (Spec (CommRingCat.of Ω)))
  unfold puncturedRingEquiv
  rw [← LaurentPolynomial.algebraMap_eq_toLaurent,
    IsLocalization.ringEquivOfRingEquiv_eq]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem puncturedRingEquiv_eval (Ω : Type u) [Field Ω] :
    (puncturedRingEquiv Ω).toRingHom =
      LaurentPolynomial.eval₂
        (((puncturedProjection (Spec (CommRingCat.of Ω))).appTop.hom).comp
          (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom)
        (coordinateUnit (Spec (CommRingCat.of Ω))) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial Ω))
  apply Polynomial.ringHom_ext
  · intro a
    change puncturedRingEquiv Ω (Polynomial.toLaurent (Polynomial.C a)) = _
    rw [puncturedRingEquiv_toLaurent, lineRingEquiv_C]
    simp only [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
      LaurentPolynomial.eval₂_toLaurent, Polynomial.eval₂_C]
    rfl
  · change puncturedRingEquiv Ω (Polynomial.toLaurent Polynomial.X) = _
    rw [puncturedRingEquiv_toLaurent, lineRingEquiv_X]
    simp only [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
      LaurentPolynomial.eval₂_toLaurent, Polynomial.eval₂_X]
    exact (IsUnit.unit_spec _).symm

set_option backward.isDefEq.respectTransparency false in
private theorem punctured_units_monomial (Ω : Type u) [Field Ω]
    (v : Γ(Punctured (Spec (CommRingCat.of Ω)), ⊤)ˣ) :
    ∃ (c : Ωˣ) (r : ℤ), v = constantUnit Ω c * coordinateUnit (Spec (CommRingCat.of Ω)) ^ r := by
  let w := Units.map (puncturedRingEquiv Ω).symm.toMonoidHom v
  obtain ⟨⟨c, r⟩, h⟩ := (AffinePuncturedLine.affine_punctured_line_algebra Ω).2.1.2
    (AffinePuncturedLine.specUnitSection _ w)
  have hw : AffinePuncturedLine.laurentUnit Ω c r = w := by
    have hh := congrArg (fun x ↦ x.toAdd.down.toMul) h
    exact (Units.map_injective (Scheme.ΓSpecIso
      (CommRingCat.of (LaurentPolynomial Ω))).symm.commRingCatIsoToRingEquiv.injective) hh
  refine ⟨c, r, Units.ext ?_⟩
  have hh := congrArg (fun x : (LaurentPolynomial Ω)ˣ ↦
    puncturedRingEquiv Ω (x : LaurentPolynomial Ω)) hw
  change _ = _ at hh
  rw [show ∀ a, puncturedRingEquiv Ω a =
      LaurentPolynomial.eval₂
        (((puncturedProjection (Spec (CommRingCat.of Ω))).appTop.hom).comp
          (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom)
        (coordinateUnit (Spec (CommRingCat.of Ω))) a from
      fun a ↦ congrArg (fun f : LaurentPolynomial Ω →+* _ ↦ f a)
        (puncturedRingEquiv_eval Ω)] at hh
  change LaurentPolynomial.eval₂ _ _
    (LaurentPolynomial.C (c : Ω) * LaurentPolynomial.T r) = _ at hh
  rw [LaurentPolynomial.eval₂_C_mul_T] at hh
  change _ = puncturedRingEquiv Ω ((puncturedRingEquiv Ω).symm (v :
    Γ(Punctured (Spec (CommRingCat.of Ω)), ⊤))) at hh
  rw [RingEquiv.apply_symm_apply] at hh
  exact hh.symm


private theorem coefficientPrime_unit (P : PurityFiniteSetting.{u}) :
    IsUnit (P.coefficients.l : P.field.k) := by
  let : Fintype P.field.k₀ := Fintype.ofFinite _
  have : Fact P.field.p.Prime := ⟨P.field.prime⟩
  have : CharP P.field.k₀ P.field.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, P.field.card_base, P.field.cardinality_eq])
  have : CharP P.field.k P.field.p :=
    charP_of_injective_algebraMap' P.field.k₀ P.field.p
  exact isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime _
    (Fact.out : P.coefficients.l.Prime) P.coefficients.different.symm)

set_option backward.isDefEq.respectTransparency false in
private theorem kummerClass_pow_zero (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (W : X.Etale) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (m : ℕ)
    (hm : IsUnit (m : Γ(X, ⊤)))
    (f : X.rootsOfUnitySheaf m ⟶ (Etale.moduleAbelianForget A X).obj F)
    (v : Γ(W.left, ⊤)ˣ) : kummerClass A X W F m hm f (v ^ m) = 0 := by
  let e := EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology W X.gmSheaf
  let a := e.symm (ULift.up (Additive.ofMul v))
  have ha : e.symm (ULift.up (Additive.ofMul (v ^ m))) =
      a ≫ (X.kummerSequence m).g := by
    apply e.injective
    dsimp only [e]
    rw [EtaleOpenComparison.sectionsEquiv_naturality]
    change e (e.symm _) = m • e a
    rw [AddEquiv.apply_symm_apply]
    change ULift.up (Additive.ofMul (v ^ m)) =
      m • e (e.symm (ULift.up (Additive.ofMul v)))
    rw [AddEquiv.apply_symm_apply]
    rfl
  dsimp only [e] at ha
  simp only [kummerClass, ha, ← Abelian.Ext.mk₀_comp_mk₀_assoc,
    ShortComplex.ShortExact.comp_extClass, Abelian.Ext.comp_zero,
    Abelian.Ext.zero_comp, map_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem kummerClass_mul (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (W : X.Etale) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (m : ℕ)
    (hm : IsUnit (m : Γ(X, ⊤)))
    (f : X.rootsOfUnitySheaf m ⟶ (Etale.moduleAbelianForget A X).obj F)
    (v w : Γ(W.left, ⊤)ˣ) : kummerClass A X W F m hm f (v * w) =
      kummerClass A X W F m hm f v + kummerClass A X W F m hm f w := by
  let e := EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology W X.gmSheaf
  have ha : e.symm (ULift.up (Additive.ofMul (v * w))) =
      e.symm (ULift.up (Additive.ofMul v)) + e.symm (ULift.up (Additive.ofMul w)) := by
    change e.symm (ULift.up (Additive.ofMul v) + ULift.up (Additive.ofMul w)) = _
    exact e.symm.map_add _ _
  dsimp only [e] at ha
  simp only [kummerClass, ha, Abelian.Ext.mk₀_add, Abelian.Ext.add_comp, map_add]

set_option backward.isDefEq.respectTransparency false in
private theorem kummerClass_zpow (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (W : X.Etale) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (m : ℕ)
    (hm : IsUnit (m : Γ(X, ⊤)))
    (f : X.rootsOfUnitySheaf m ⟶ (Etale.moduleAbelianForget A X).obj F)
    (v : Γ(W.left, ⊤)ˣ) (r : ℤ) : kummerClass A X W F m hm f (v ^ r) =
      r • kummerClass A X W F m hm f v := by
  let k : Additive Γ(W.left, ⊤)ˣ →+
      ((sections X.smallEtaleTopology A W).rightDerived 1).obj F := {
    toFun := fun a ↦ kummerClass A X W F m hm f a.toMul
    map_zero' := by
      change kummerClass A X W F m hm f 1 = 0
      simpa only [one_pow] using kummerClass_pow_zero A X W F m hm f 1
    map_add' := fun a b ↦ kummerClass_mul A X W F m hm f a.toMul b.toMul }
  exact map_zsmul k r (Additive.ofMul v)

set_option backward.isDefEq.respectTransparency false in
private theorem kummerClass_monomial (A : Type (u + 1)) [CommRing A]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (m : ℕ) (hm0 : 0 < m)
    (F : Sheaf (Line (Spec (CommRingCat.of Ω))).smallEtaleTopology (ModuleCat.{u + 1} A))
    (hm : IsUnit (m : Γ(Line (Spec (CommRingCat.of Ω)), ⊤)))
    (f : (Line (Spec (CommRingCat.of Ω))).rootsOfUnitySheaf m ⟶
      (Etale.moduleAbelianForget A (Line (Spec (CommRingCat.of Ω)))).obj F)
    (c : Ωˣ) (r : ℤ) :
    kummerClass A _ (openObject (Spec (CommRingCat.of Ω))) F m hm f
        (constantUnit Ω c * coordinateUnit (Spec (CommRingCat.of Ω)) ^ r) =
      r • kummerClass A _ (openObject (Spec (CommRingCat.of Ω))) F m hm f
        (coordinateUnit (Spec (CommRingCat.of Ω))) := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (c : Ω) hm0
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.ne_of_gt hm0)] at hb
    exact c.ne_zero hb.symm
  let b' : Ωˣ := Units.mk0 b hb0
  have hb' : b' ^ m = c := Units.ext hb
  have hpow : constantUnit Ω b' ^ m = constantUnit Ω c := by
    change (Units.map _ b') ^ m = Units.map _ c
    rw [← map_pow, hb']
  rw [kummerClass_mul, ← hpow, kummerClass_pow_zero, zero_add, kummerClass_zpow]

/-- The ordinary Kummer basis, vanishings and unit classes, before localization.
Source: blueprint thm-pur-rank-one-local-calculation, Steps 1--3 and 5; Milne Sections 9, 14, 16.
(blueprint: lem-pur-rank-one-etale-calculation).

Proof: choose a primitive ell^N-th root over the algebraically closed field. It identifies
roots of unity with the constant Z/ell^N line. The affine and punctured lines are connected,
so their degree-zero groups are A and restriction is the identity. Define tau_M(a) by
applying x mapping to x tensor a to the Kummer class of t. This is natural and linear in M.
For M=F_ell use the level-change map on roots and Kummer-sequence naturality, then the
prime-level affine-line computation. Induct on the cardinality of a finite Z/ell^N-module:
a nonzero element of least ell-power order gives a submodule C isomorphic to F_ell. For
Q=M/C the constant twisted sheaves form a short exact sequence, because sheafification
is exact and the root line is locally free. The coefficient long exact sequences give
positive affine-line vanishing and punctured-line vanishing above one. In degree one,
surjectivity of H0(M) to H0(Q) and H2(C)=0 give a short exact sequence. Naturality of tau
and the two outside isomorphisms prove that tau_M is bijective. For M=A it is A-linear.
Transport this calculation from abelian Ext cohomology to module derived evaluation by
the cocycle-normalized evaluation comparison. The sectionwise formula for f is the
scalar-extension insertion with label one. The coordinate basic open identifies with
the Laurent spectrum. Its units are c*t^r by the Laurent unit computation. Every scalar
c has an ell^N-th root, so its Kummer boundary is zero by exactness. Additivity of Ext
composition and of both evaluation comparisons gives kappa(c*t^r)=r*kappa(t), also for
negative r. The coefficient map and invertibility witness come from scalar extension
and invertibility of ell over the base field, respectively. Both constructions are
independent of the temporary primitive root. -/
theorem rankOne_etale_calculation (P : PurityFiniteSetting.{u})
    (N : ℕ) (hN : 1 ≤ N) (hA : ((P.coefficients.l ^ N : ℕ) : P.Coefficient) = 0)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra P.field.k Ω] :
    let S := Spec (CommRingCat.of Ω)
    let X := Line S
    let F := Scheme.finiteEtaleTateSheaf P.Coefficient (P.coefficients.l ^ N) X hA 1
    let H := ((sections X.smallEtaleTopology P.Coefficient (openObject S)).rightDerived 1).obj F
    ∃ (hm : IsUnit ((P.coefficients.l ^ N : ℕ) : Γ(X, ⊤)))
      (f : X.rootsOfUnitySheaf (P.coefficients.l ^ N) ⟶
        (Etale.moduleAbelianForget P.Coefficient X).obj F),
      (∀ (V : X.Etaleᵒᵖ) (z : (X.rootsOfUnitySheaf (P.coefficients.l ^ N)).obj.obj V),
        f.hom.app V z = Scheme.finiteEtaleTateOneGenerator P.Coefficient
          (P.coefficients.l ^ N) X hA V 1 z) ∧
      ∃ e : H ≅ ModuleCat.of P.Coefficient P.Coefficient,
        e.hom (kummerClass P.Coefficient X (openObject S) F
          (P.coefficients.l ^ N) hm f (coordinateUnit S)) = 1 ∧
        (∀ q : ℕ, 0 < q → IsZero (((sections X.smallEtaleTopology P.Coefficient
          (Scheme.Etale.mk (𝟙 X))).rightDerived q).obj F)) ∧
        (∀ q : ℕ, 2 ≤ q → IsZero (((sections X.smallEtaleTopology P.Coefficient
          (openObject S)).rightDerived q).obj F)) ∧
        IsIso ((NatTrans.rightDerived
          (F := sections X.smallEtaleTopology P.Coefficient (Scheme.Etale.mk (𝟙 X)))
          (G := sections X.smallEtaleTopology P.Coefficient (openObject S))
          ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)).map
            (restriction S).op) 0).app F) ∧
        (∀ v : Γ(Punctured S, ⊤)ˣ, ∃ (c : Ωˣ) (r : ℤ),
          v = constantUnit Ω c * coordinateUnit S ^ r) ∧
        (∀ (c : Ωˣ) (r : ℤ),
          kummerClass P.Coefficient X (openObject S) F (P.coefficients.l ^ N) hm f
            (constantUnit Ω c * coordinateUnit S ^ r) =
          r • kummerClass P.Coefficient X (openObject S) F (P.coefficients.l ^ N) hm f
            (coordinateUnit S)) := by
  let S := Spec (CommRingCat.of Ω)
  let X := Line S
  let F := Scheme.finiteEtaleTateSheaf P.Coefficient (P.coefficients.l ^ N) X hA 1
  have hℓΩ : IsUnit (P.coefficients.l : Ω) := by
    simpa only [map_natCast] using (coefficientPrime_unit P).map (algebraMap P.field.k Ω)
  let g := (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ (lineProjection S).appTop
  have hm : IsUnit ((P.coefficients.l ^ N : ℕ) : Γ(X, ⊤)) := by
    simpa only [map_pow, map_natCast, Nat.cast_pow] using (hℓΩ.pow N).map g.hom
  have : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  have : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  obtain ⟨e, he, hX, hU, hres⟩ := finite_line_cohomology P.Coefficient Ω
    P.coefficients.l N (Fact.out : P.coefficients.l.Prime) hℓΩ hN hA hm
  refine ⟨hm, Etale.ordinaryFiniteRootMap P.Coefficient (P.coefficients.l ^ N) hA X,
    ?_, e, he, hX, hU, hres, punctured_units_monomial Ω, ?_⟩
  · intro V z
    rfl
  · intro c r
    exact kummerClass_monomial P.Coefficient Ω (P.coefficients.l ^ N)
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos N) F hm _ c r

end WeilConjectures.PurityFiniteSetting.RankOne
