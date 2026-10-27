/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.LogIdealChartPresentation
public import Sheaf.AlgebraicGeometry.AssociatedLogUniversalStalks
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Locally Noetherian fs realization of an affine toric chart

Source: ILO, Exposé VI 1.1, printed p. 69; VIII 3.3.8--3.3.11, printed pp. 107--108;
Stacks, Tags 00FN, 01OV and 01OW (blueprint: lem-trf-toric-chart-fs-realization).

The existing `logIdealTensorRing` is the actual tensor algebra with its canonical
multiplication and scalar maps. We use multiplicative notation for the chart monoids;
`1` and multiplication denote the `0` and addition of the informal statement.

## Main declarations

* `toricTensorGlobalChart`: the canonical monomial map to affine global sections.
* `toricChart_fs_realization`: evaluation, Noetherianity, and the associated fs chart.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical global prelog chart `q ↦ 1 ⊗ z^q`, transported from the tensor ring
through the inverse of the affine global-sections isomorphism.
Source: ILO VI 1.1; VIII 3.3.5--3.3.11
(blueprint: lem-trf-toric-chart-fs-realization). -/
noncomputable def toricTensorGlobalChart {P Q : Type u} [CommMonoid P] [CommMonoid Q]
    (A : Type u) [CommRing A] (α : P →* A) (g : P →* Q) :
    Q →* Γ(Spec (.of (logIdealTensorRing A α g)), ⊤) :=
  (Scheme.ΓSpecIso (.of (logIdealTensorRing A α g))).inv.hom.toMonoidHom.comp
    (logIdealTensorMonomial A α g)

private theorem toricTensor_eval_surjective {P Q : Type u}
    [CommMonoid P] [CommMonoid Q] (A : Type u) [CommRing A]
    (α : P →* A) (g : P →* Q) (r : ℕ) (q : Fin r → Q)
    (hq : Submonoid.closure (Set.range q) = ⊤) :
    Function.Surjective (MvPolynomial.eval₂Hom (logIdealTensorBase A α g)
      (fun i ↦ logIdealTensorMonomial A α g (q i))) := by
  let := (MonoidAlgebra.lift ℤ A P α).toRingHom.toAlgebra
  let := (MonoidAlgebra.mapDomainRingHom ℤ g).toAlgebra
  let e := MvPolynomial.eval₂Hom (logIdealTensorBase A α g)
    (fun i ↦ logIdealTensorMonomial A α g (q i))
  have hm (x : Q) : logIdealTensorMonomial A α g x ∈ e.range := by
    have hx : x ∈ Submonoid.closure (Set.range q) := hq.symm ▸ Submonoid.mem_top x
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨MvPolynomial.X i, MvPolynomial.eval₂_X _ _ _⟩
    | one => simpa only [map_one] using e.range.one_mem
    | mul x y _ _ hx hy =>
      simpa only [map_mul] using e.range.mul_mem hx hy
  have hb (b : MonoidAlgebra ℤ Q) :
      Algebra.TensorProduct.includeRight (A := A) b ∈ e.range := by
    induction b using MonoidAlgebra.induction_on with
    | of x => exact hm x
    | add x y hx hy => simpa only [map_add] using e.range.add_mem hx hy
    | smul n x hx =>
      simpa only [map_zsmul] using e.range.zsmul_mem hx n
  intro z
  change z ∈ e.range
  induction z using TensorProduct.induction_on with
  | zero => exact e.range.zero_mem
  | add x y hx hy => exact e.range.add_mem hx hy
  | tmul a b =>
    have ha : logIdealTensorBase A α g a ∈ e.range :=
      ⟨MvPolynomial.C a, MvPolynomial.eval₂_C _ _ _⟩
    convert e.range.mul_mem ha (hb b) using 1
    simp [logIdealTensorBase, Algebra.TensorProduct.tmul_mul_tmul]

private theorem strictLocal_unit_representative {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
    (a : (strictLocalRing X t)ˣ) :
    ∃ (W : X.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W)
      (b : Γ(W.left, ⊤)ˣ), Units.map (strictLocalGerm X t W w).hom.toMonoidHom b = a := by
  let Φ := Scheme.pointSmallEtale t
  obtain ⟨W, w, b, c, hb, hc⟩ := Φ.toPresheafFiber_jointly_surjective₂
    (P := X.etaleStructurePresheaf) a.val (a⁻¹).val
  change (strictLocalGerm X t W w).hom b = a.val at hb
  change (strictLocalGerm X t W w).hom c = (a⁻¹).val at hc
  have he : Φ.toPresheafFiber W w X.etaleStructurePresheaf (b * c) =
      Φ.toPresheafFiber W w X.etaleStructurePresheaf 1 := by
    change (strictLocalGerm X t W w).hom (b * c) =
      (strictLocalGerm X t W w).hom 1
    rw [map_mul, hb, hc, a.mul_inv, map_one]
  obtain ⟨V, f, v, hv, hbc⟩ := (Φ.toPresheafFiber_eq_iff' W w (b * c) 1).mp he
  change f.left.appTop.hom (b * c) = f.left.appTop.hom 1 at hbc
  have hprod : f.left.appTop.hom b * f.left.appTop.hom c = 1 := by
    simpa only [map_mul, map_one] using hbc
  let d : Γ(V.left, ⊤)ˣ :=
    ⟨f.left.appTop.hom b, f.left.appTop.hom c, hprod, by rwa [mul_comm]⟩
  refine ⟨V, v, d, Units.ext ?_⟩
  change Φ.toPresheafFiber V v X.etaleStructurePresheaf
    (X.etaleStructurePresheaf.map f.op b) = a.val
  have h := Φ.toPresheafFiber_w_apply f v X.etaleStructurePresheaf b
  rw [hv] at h
  exact h.trans hb

private theorem log_stalkAlpha_germ {X : Scheme.{u}} (L : EtaleLogStructure X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
    (W : X.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W)
    (s : L.monoidSheaf.obj.obj (op W)) :
    L.toEtalePrelogStructure.stalkAlpha t (L.toEtalePrelogStructure.germ t W w s) =
      (strictLocalGerm X t W w).hom (L.alpha.app (op W) s) := by
  dsimp only [EtalePrelogStructure.stalkAlpha, EtalePrelogStructure.germ,
    pointedEtaleGerm]
  change ((colimit.ι (pointedEtaleStalkDiagram L.monoidSheaf t) (op ⟨W, w⟩) ≫
    colimit.desc (pointedEtaleStalkDiagram L.monoidSheaf t)
      { pt := CommMonCat.of (strictLocalRing X t), ι := _ }) :
      L.monoidSheaf.obj.obj (op W) ⟶ CommMonCat.of (strictLocalRing X t)) s = _
  rw [colimit.ι_desc]
  rfl

private theorem log_units_unique {X : Scheme.{u}} (L : EtaleLogStructure X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
    (l : (strictLocalRing X t)ˣ →* L.toEtalePrelogStructure.stalk t)
    (hl : ∀ a, L.toEtalePrelogStructure.stalkAlpha t (l a) = a.val) :
    l = L.unitsIn t := by
  ext a
  change (l.toHomUnits a).val = ↑((MulEquiv.ofBijective
    (Units.map (L.toEtalePrelogStructure.stalkAlpha t)) (L.unitsBijective Ω t)).symm a)
  apply congrArg Units.val
  apply (L.unitsBijective Ω t).1
  apply Units.ext
  change L.toEtalePrelogStructure.stalkAlpha t (l a) = _
  rw [hl]
  exact (congrArg Units.val ((MulEquiv.ofBijective
    (Units.map (L.toEtalePrelogStructure.stalkAlpha t))
      (L.unitsBijective Ω t)).apply_symm_apply a)).symm

private theorem lifted_chart_congruence {R B : Type u} [CommMonoid R] [CommRing B]
    (γ : ULift.{0, u} R →* B) (δ : R →* B)
    (h : ∀ r, γ (ULift.up r) = δ r) :
    Con.comap (MulEquiv.prodCongr MulEquiv.ulift.symm (MulEquiv.refl Bˣ))
      (map_mul _) (divisorialChartCongruence γ.mrangeRestrict) =
        divisorialChartCongruence δ.mrangeRestrict := by
  rw [divisorialChartCongruence, Con.comap_conGen_equiv]
  apply congrArg conGen
  funext x y
  apply propext
  constructor
  · rintro ⟨⟨r⟩, a, hr, hx, hy⟩
    refine ⟨r, a, ?_, ?_, ?_⟩
    · exact (h r).symm.trans hr
    · apply (MulEquiv.prodCongr MulEquiv.ulift.symm (MulEquiv.refl Bˣ)).injective
      exact hx
    · apply (MulEquiv.prodCongr MulEquiv.ulift.symm (MulEquiv.refl Bˣ)).injective
      exact hy
  · rintro ⟨r, a, hr, rfl, rfl⟩
    exact ⟨ULift.up r, a, (h r).trans hr, rfl, rfl⟩

/-- Every fs monoid chart over a locally Noetherian affine base has the prescribed
locally Noetherian fs realization, with evaluation surjective for every generating tuple.

Source: ILO VI 1.1, printed p. 69; VIII 3.3.8--3.3.11, printed pp. 107--108;
Stacks, Tags 00FN, 01OV and 01OW.
Proof:
1. For any finite tuple generating `Q`, expand a tensor into pure tensors and expand
   its monoid-algebra factor into monomials. Write each monoid element as a product
   of the tuple elements. The corresponding polynomial monomial evaluates to the
   prescribed tensor; sums give surjectivity. The empty tuple uses the empty product.
   The balanced tensor multiplication is the existing tensor-algebra multiplication
   (`def-weil-pbc-module-tensor-product`, `def-weil-pbc-mv-polynomial-ring`).
2. Local Noetherianity of `Spec A` makes `A` Noetherian
   (`pqf-lem-affine-open-locnoeth`). Finite generation of `Q` and Step 1 make the tensor
   ring a finite type `A`-algebra; it is Noetherian by
   `lem-weil-pbc-finite-type-algebra-noetherian`.
3. The single affine cover makes its spectrum locally Noetherian (`pqf-def-locnoeth`).
   Its canonical monomial homomorphism, transported by `ΓSpecIso`, is the prelog chart.
4. Apply `lem-trf-associated-log-universal-stalks` to that chart. Its pair formula
   sends `[q,1]` to `1 ⊗ z^q`, and its stalk pushout isomorphism is exactly the chart
   test of `def-trf-fs-log-blowup`. The chart monoid is fs, so the resulting log
   structure is fs. If the tensor ring is zero, its spectrum is empty and the same
   construction applies. No log structure or log regularity of the base is used.
(blueprint: lem-trf-toric-chart-fs-realization). -/
theorem toricChart_fs_realization (A : Type u) [CommRing A]
    [IsLocallyNoetherian (Spec (.of A))]
    (P Q : Type u) [CommMonoid P] [CommMonoid Q]
    (_hP : IsFineSaturatedMonoid P) (_hQ : IsFineSaturatedMonoid Q)
    (g : P →* Q) (α : P →* A) :
    (∀ (r : ℕ) (q : Fin r → Q), Submonoid.closure (Set.range q) = ⊤ →
      Function.Surjective (MvPolynomial.eval₂Hom (logIdealTensorBase A α g)
        (fun i ↦ logIdealTensorMonomial A α g (q i)))) ∧
    IsNoetherianRing (logIdealTensorRing A α g) ∧
    IsLocallyNoetherian (Spec (.of (logIdealTensorRing A α g))) ∧
    ∃ (L : EtaleLogStructure (Spec (.of (logIdealTensorRing A α g))))
      (η : associatedLogPresheaf.{0, u} (toricTensorGlobalChart A α g) ⟶ L.monoidSheaf.obj),
      IsAssociatedLogPresentation.{0, u} (toricTensorGlobalChart A α g) L η ∧
      L.IsChart (Scheme.Etale.mk (𝟙 (Spec (.of (logIdealTensorRing A α g)))))
        ((associatedLogIota.{0, u} (toricTensorGlobalChart A α g) L η).comp
          MulEquiv.ulift.symm.toMonoidHom) ∧
      (L.alpha.app (op (Scheme.Etale.mk (𝟙 (Spec (.of (logIdealTensorRing A α g))))))).hom.comp
        ((associatedLogIota.{0, u} (toricTensorGlobalChart A α g) L η).comp
          MulEquiv.ulift.symm.toMonoidHom) = toricTensorGlobalChart A α g ∧
      L.IsFineSaturated := by
  classical
  have hs := toricTensor_eval_surjective A α g
  have hA : IsNoetherianRing A := (isLocallyNoetherian_Spec (R := .of A)).mp inferInstance
  let := hA
  obtain ⟨S, hS⟩ := _hQ.1
  let q : Fin (Fintype.card S) → Q := fun i ↦ (Fintype.equivFin S).symm i
  have hq : Submonoid.closure (Set.range q) = ⊤ := by
    have hrange : Set.range q = (S : Set Q) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ((Fintype.equivFin S).symm i).property
      · intro hx
        exact ⟨(Fintype.equivFin S) ⟨x, hx⟩, by simp [q]⟩
    rwa [hrange]
  have hsur := hs _ q hq
  let := (logIdealTensorBase A α g).toAlgebra
  have : Algebra.FiniteType A (logIdealTensorRing A α g) :=
    Algebra.FiniteType.of_surjective
      (MvPolynomial.aeval (fun i ↦ logIdealTensorMonomial A α g (q i))) hsur
  have hC := Algebra.FiniteType.isNoetherianRing A (logIdealTensorRing A α g)
  let := hC
  refine ⟨hs, hC, inferInstance, ?_⟩
  let X := Spec (.of (logIdealTensorRing A α g))
  let β : Q →* Γ(X, ⊤) := toricTensorGlobalChart A α g
  let W : X.Etale := Scheme.Etale.mk (𝟙 X)
  obtain ⟨L, η, hpres, _, hstalk, _, _⟩ :=
    associatedLog_universal_stalks.{0, u} X Q β
  let c : Q →* L.monoidSheaf.obj.obj (op W) :=
    (associatedLogIota.{0, u} β L η).comp MulEquiv.ulift.symm.toMonoidHom
  have hstruct : (L.alpha.app (op W)).hom.comp c = β := by
    ext q
    change L.alpha.app (op W) (η.app (op W)
      ((divisorialChartCongruence (associatedLogBetaLift.{0, u} β W).mrangeRestrict).mk'
        (ULift.up q, 1))) = β q
    refine (hpres.2 W q 1).trans ?_
    simp [W, associatedLogBetaLift, associatedLogBeta, associatedLogDown]
    rfl
  have hchart : L.IsChart W c := by
    intro Ω _ _ t w
    obtain ⟨e, he⟩ := hstalk Ω t
    let γ := associatedLogStalkBeta.{0, u} β t
    let k : ULift.{0, u} Q × (strictLocalRing X t)ˣ →*
        divisorialChartPushout (associatedLogStalkBeta.{0, u} β t).mrangeRestrict :=
      (divisorialChartCongruence γ.mrangeRestrict).mk'
    change ∀ (V : X.Etale) (v : (Scheme.pointSmallEtale t).fiber.obj V)
      (q : Q) (a : Γ(V.left, ⊤)ˣ),
      e.hom.hom (k (ULift.up q, Units.map (strictLocalGerm X t V v).hom.toMonoidHom a)) =
        L.toEtalePrelogStructure.germ t V v (η.app (op V)
          ((divisorialChartCongruence (associatedLogBetaLift.{0, u} β V).mrangeRestrict).mk'
            (ULift.up q, a))) at he
    let l := e.hom.hom.comp (k.comp (MonoidHom.inr (ULift.{0, u} Q) _))
    have hl : l = L.unitsIn t := by
      apply log_units_unique
      intro a
      obtain ⟨V, v, b, hb⟩ := strictLocal_unit_representative t a
      rw [← hb]
      change L.toEtalePrelogStructure.stalkAlpha t
        (e.hom.hom (k (ULift.up 1, Units.map (strictLocalGerm X t V v).hom.toMonoidHom b))) = _
      rw [he V v 1 b, log_stalkAlpha_germ, hpres.2]
      simp [associatedLogBetaLift, associatedLogDown]
    have hq (q : Q) : e.hom.hom (k (ULift.up q, 1)) =
        L.toEtalePrelogStructure.germ t W w (c q) := by
      have h := he W w q 1
      rw [map_one] at h
      exact h
    let f : Q × (strictLocalRing X t)ˣ ≃*
        ULift.{0, u} Q × (strictLocalRing X t)ˣ :=
      MulEquiv.prodCongr MulEquiv.ulift.symm (MulEquiv.refl _)
    let ψ := e.hom.hom.comp (k.comp f.toMonoidHom)
    let d := (L.toEtalePrelogStructure.germ t W w).hom.comp c
    have hpair (z : Q × (strictLocalRing X t)ˣ) :
        ψ z = (d.coprod (L.unitsIn t)) z := by
      obtain ⟨q, a⟩ := z
      change e.hom.hom (k (ULift.up q, a)) = d q * L.unitsIn t a
      calc
        _ = e.hom.hom (k (ULift.up q, 1)) * e.hom.hom (k (1, a)) := by
          rw [← e.hom.hom.map_mul, ← k.map_mul]
          simp
        _ = d q * l a := by rw [hq]; rfl
        _ = _ := by rw [hl]
    let δ := (L.toEtalePrelogStructure.stalkAlpha t).comp d
    have hβ (q : Q) : δ q = γ (ULift.up q) := by
      change L.toEtalePrelogStructure.stalkAlpha t
        (L.toEtalePrelogStructure.germ t W w (c q)) = _
      rw [← hq]
      have hq₀ := he W (Over.homMk t) q 1
      simp only [map_one] at hq₀
      rw [hq₀, log_stalkAlpha_germ, hpres.2]
      simp [γ, associatedLogStalkBeta, associatedLogBetaLift,
        associatedLogBeta, associatedLogDown, W]
      rfl
    have hcon := lifted_chart_congruence γ δ (fun q ↦ (hβ q).symm)
    refine ⟨?_, ?_⟩
    · have hsur : Function.Surjective ψ :=
        e.commMonCatIsoToMulEquiv.surjective.comp
          (Con.mk'_surjective.comp f.surjective)
      intro m
      obtain ⟨z, hz⟩ := hsur m
      exact ⟨z, (hpair z).symm.trans hz⟩
    · apply Con.ext
      intro x y
      change (d.coprod (L.unitsIn t)) x = (d.coprod (L.unitsIn t)) y ↔
        (divisorialChartCongruence δ.mrangeRestrict) x y
      rw [← hpair x, ← hpair y]
      change e.hom.hom (k (f x)) = e.hom.hom (k (f y)) ↔ _
      have hinj : Function.Injective e.hom.hom :=
        e.commMonCatIsoToMulEquiv.injective
      rw [hinj.eq_iff]
      change ((f x : (divisorialChartCongruence γ.mrangeRestrict).Quotient) =
        (f y : (divisorialChartCongruence γ.mrangeRestrict).Quotient)) ↔ _
      rw [Con.eq]
      exact Iff.of_eq (congrArg (fun C : Con (Q × (strictLocalRing X t)ˣ) ↦ C x y) hcon)
  refine ⟨L, η, hpres, hchart, hstruct, ?_⟩
  intro Ω _ _ t
  exact ⟨W, Over.homMk t, Q, inferInstance, c, _hQ, hchart⟩

end AlgebraicGeometry
