module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.LogRegularMonoidalIdealContraction
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselization
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Group.Submonoid.Operations
import Sheaf.AlgebraicGeometry.FiniteChartTrivialityLocus
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Dense triviality locus and injectivity from monoidal ideal contraction

Source: the chart criterion extracted from ILO, Exposé VI 1.4, printed p. 69,
and Exposé VIII 3.4.1--3.4.3, printed p. 110
(blueprint: lem-trf-monoidal-chart-dense-injective).

The hypotheses below do not assume log regularity. Additive chart monoids are
written as `Multiplicative P` when mapping into the multiplicative log sheaf.
The helper predicate merely groups the specified chart hypotheses. The helper
unit map transports the existing log-unit identification along the canonical
comparison with the recorded affine-neighbourhood strict henselization. These
existing comparison and chart-map definitions are owned by the definition node
`def-trf-chart-strict-henselization-map`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The hypotheses on one affine pointed sharp chart, including contraction for
all monoid ideals (also the empty ideal). Cancellation is encoded by the chart's
`AddCancelCommMonoid` structure; finite generation and sharpness are explicit.
Source: extracted chart criterion, ILO VI 1.4 and VIII 3.4.1--3.4.3
(blueprint: lem-trf-monoidal-chart-dense-injective). -/
def EtaleLogStructure.IsContractingSharpChart {X : Scheme.{u}} (M : EtaleLogStructure X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
    {P : Type u} [AddCancelCommMonoid P] (W : X.Etale)
    (w : (Scheme.pointSmallEtale t).fiber.obj W)
    (c : Multiplicative P →* M.monoidSheaf.obj.obj (op W)) : Prop :=
  IsAffine W.left ∧ M.IsChart W c ∧ Monoid.FG (Multiplicative P) ∧
    (∀ p : P, IsUnit (Multiplicative.ofAdd p) → p = 0) ∧
    Function.Bijective (fun p : P ↦
      (Associates.mk (M.toEtalePrelogStructure.germ t W w
        (c (Multiplicative.ofAdd p))) : M.characteristic t)) ∧
    ∀ (J : Set P), (∀ j ∈ J, ∀ p : P, j + p ∈ J) →
      (fun p : P ↦ M.chartStrictHenselizationMap t W w c (Multiplicative.ofAdd p)) ⁻¹'
        (Ideal.span ((fun p : P ↦
          M.chartStrictHenselizationMap t W w c (Multiplicative.ofAdd p)) '' J) :
            Set (Scheme.strictHenselizationRing t)) = J

/-- The canonical inclusion of strict-henselization units into the log stalk:
transport units along the inverse comparison and apply the log-unit identification.
Source: ILO VI 1.1--1.2, as used in the extracted criterion VI 1.4
(blueprint: lem-trf-monoidal-chart-dense-injective). -/
noncomputable def EtaleLogStructure.strictHenselizationUnitsIn {X : Scheme.{u}}
    (M : EtaleLogStructure X) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X) :
    (Scheme.strictHenselizationRing t)ˣ →* M.toEtalePrelogStructure.stalk t :=
  (M.unitsIn t).comp
    (Units.map (strictLocalRingIsoStrictHenselization t).inv.hom.toMonoidHom)

private theorem contracting_nonzero {R P : Type u} [CommRing R]
    [AddCancelCommMonoid P] (a : Multiplicative P →* R)
    (hc : ∀ (J : Set P), (∀ j ∈ J, ∀ p : P, j + p ∈ J) →
      (fun p : P ↦ a (Multiplicative.ofAdd p)) ⁻¹'
        (Ideal.span ((fun p : P ↦ a (Multiplicative.ofAdd p)) '' J) : Set R) = J) :
    ∀ p : P, a (Multiplicative.ofAdd p) ≠ 0 := by
  intro p hp
  have he := hc ∅ (by simp)
  have hm : p ∈ (fun p : P ↦ a (Multiplicative.ofAdd p)) ⁻¹'
      (Ideal.span ((fun p : P ↦ a (Multiplicative.ofAdd p)) '' ∅) : Set R) := by
    simp [hp]
  rw [he] at hm
  exact hm

private theorem contracting_injective {R P : Type u} [CommRing R] [IsDomain R]
    [AddCancelCommMonoid P] (a : Multiplicative P →* R)
    (hs : ∀ p : P, IsUnit (Multiplicative.ofAdd p) → p = 0)
    (hc : ∀ (J : Set P), (∀ j ∈ J, ∀ p : P, j + p ∈ J) →
      (fun p : P ↦ a (Multiplicative.ofAdd p)) ⁻¹'
        (Ideal.span ((fun p : P ↦ a (Multiplicative.ofAdd p)) '' J) : Set R) = J) :
    Function.Injective (fun z : Multiplicative P × Rˣ ↦ (z.2 : R) * a z.1) := by
  have hdiv (p q : P) (h : a (Multiplicative.ofAdd q) ∣ a (Multiplicative.ofAdd p)) :
      ∃ r, p = q + r := by
    let J : Set P := {j | ∃ r, j = q + r}
    have hJ : ∀ j ∈ J, ∀ r : P, j + r ∈ J := by
      rintro j ⟨r, rfl⟩ s
      exact ⟨r + s, add_assoc _ _ _⟩
    have hq : a (Multiplicative.ofAdd q) ∈
        Ideal.span ((fun p : P ↦ a (Multiplicative.ofAdd p)) '' J) := by
      apply Ideal.subset_span
      exact ⟨q, ⟨0, by simp⟩, rfl⟩
    obtain ⟨b, hb⟩ := h
    have hp : p ∈ (fun p : P ↦ a (Multiplicative.ofAdd p)) ⁻¹'
        (Ideal.span ((fun p : P ↦ a (Multiplicative.ofAdd p)) '' J) : Set R) := by
      rw [Set.mem_preimage]
      rw [hb]
      exact Ideal.mul_mem_right _ _ hq
    rw [hc J hJ] at hp
    exact hp
  have hunit (p q : Multiplicative P) (v w : Rˣ)
      (h : (v : R) * a p = (w : R) * a q) : a q ∣ a p := by
    refine ⟨(↑v⁻¹ : R) * ↑w, ?_⟩
    symm
    calc
      a q * ((↑v⁻¹ : R) * ↑w) = (↑v⁻¹ : R) * ((w : R) * a q) := by ac_rfl
      _ = (↑v⁻¹ : R) * ((v : R) * a p) := congrArg _ h.symm
      _ = a p := by simp [← mul_assoc]
  rintro ⟨p, v⟩ ⟨q, w⟩ h
  obtain ⟨r, hr⟩ := hdiv p.toAdd q.toAdd (hunit p q v w h)
  obtain ⟨s, ht⟩ := hdiv q.toAdd p.toAdd (hunit q p w v h.symm)
  have hz : r + s = 0 := by
    apply add_left_cancel (a := q.toAdd)
    calc
      q.toAdd + (r + s) = (q.toAdd + r) + s := (add_assoc _ _ _).symm
      _ = p.toAdd + s := by rw [← hr]
      _ = q.toAdd + 0 := by rw [← ht, add_zero]
  have hr0 : r = 0 := hs r (isUnit_iff_exists.mpr
    ⟨Multiplicative.ofAdd s, congrArg Multiplicative.ofAdd hz,
      congrArg Multiplicative.ofAdd ((add_comm s r).trans hz)⟩)
  have hpq : p = q := by
    apply Multiplicative.toAdd.injective
    simpa [hr0] using hr
  subst q
  have hvw : v = w := Units.ext (mul_right_cancel₀
    (contracting_nonzero a hc p.toAdd) h)
  exact Prod.ext rfl hvw

private theorem unitsIn_alpha {Y : Scheme.{u}} (M : EtaleLogStructure Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Y)
    (v : (strictLocalRing Y t)ˣ) :
    M.toEtalePrelogStructure.stalkAlpha t (M.unitsIn t v) = (v : strictLocalRing Y t) := by
  let e := MulEquiv.ofBijective (Units.map (M.toEtalePrelogStructure.stalkAlpha t))
    (M.unitsBijective Ω t)
  exact congrArg Units.val (e.apply_symm_apply v)

private theorem strictUnitsIn_alpha {Y : Scheme.{u}} (M : EtaleLogStructure Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Y)
    (v : (Scheme.strictHenselizationRing t)ˣ) :
    (strictLocalRingIsoStrictHenselization t).hom.hom
      (M.toEtalePrelogStructure.stalkAlpha t (M.strictHenselizationUnitsIn t v)) =
        (v : Scheme.strictHenselizationRing t) := by
  simp only [EtaleLogStructure.strictHenselizationUnitsIn, MonoidHom.comp_apply,
    unitsIn_alpha, Units.coe_map]
  exact congrArg (fun f : Scheme.strictHenselizationRing t ⟶
    Scheme.strictHenselizationRing t ↦ f v) (strictLocalRingIsoStrictHenselization t).inv_hom_id

private theorem strictUnitsIn_surjective {Y : Scheme.{u}} (M : EtaleLogStructure Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Y)
    (v : (strictLocalRing Y t)ˣ) :
    ∃ w : (Scheme.strictHenselizationRing t)ˣ,
      M.strictHenselizationUnitsIn t w = M.unitsIn t v := by
  refine ⟨Units.map (strictLocalRingIsoStrictHenselization t).hom.hom.toMonoidHom v, ?_⟩
  apply congrArg (M.unitsIn t)
  apply Units.ext
  exact congrArg (fun f : strictLocalRing Y t ⟶ strictLocalRing Y t ↦ f v)
    (strictLocalRingIsoStrictHenselization t).hom_inv_id

private theorem pointedStrictLift {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ Y) :
    ∃ l : Spec (.of Ω) ⟶ Scheme.strictHenselizationScheme t,
      l ≫ Scheme.strictHenselizationStructuralMap t = t := by
  classical
  let N := (equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods t)).inverse
  let c : Cocone (Scheme.strictHenselizationAffineDiagram t) :=
    { pt := Γ(Spec (.of Ω), ⊤)
      ι := { app := fun j ↦ (N.obj j.unop).2.left.appTop
             naturality := by
               intro j k a
               change (Spec.map (N.map a.unop).1.left.unop).appTop ≫
                 (N.obj k.unop).2.left.appTop = (N.obj j.unop).2.left.appTop ≫ 𝟙 _
               rw [Category.comp_id, ← Scheme.Hom.comp_appTop]
               congr 1
               exact congrArg Over.Hom.left (N.map a.unop).2 } }
  let r := colimit.desc (Scheme.strictHenselizationAffineDiagram t) c
  let l := (Spec (.of Ω)).toSpecΓ ≫ Spec.map r
  have hleg (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods t)) :
      l ≫ (Scheme.strictHenselizationCone t).π.app (op (op j)) ≫
        Spec.map (Scheme.ΓSpecIso (N.obj j).1.left.unop).inv = (N.obj j).2.left := by
    change ((Spec (.of Ω)).toSpecΓ ≫ Spec.map r) ≫
      Spec.map (colimit.ι (Scheme.strictHenselizationAffineDiagram t) (op j)) ≫ _ = _
    simp only [Category.assoc]
    rw [← Spec.map_comp_assoc]
    dsimp only [r]
    rw [colimit.ι_desc]
    change (Spec (.of Ω)).toSpecΓ ≫ Spec.map (N.obj j).2.left.appTop ≫ _ = _
    rw [← Scheme.toSpecΓ_naturality_assoc]
    change (N.obj j).2.left ≫ (Spec _).toSpecΓ ≫ _ = _
    rw [toSpecΓ_SpecMap_ΓSpecIso_inv]
    exact Category.comp_id _
  let :=  (Scheme.strictHenselization_properties t).2.1
  let j := Classical.choice (IsCofiltered.nonempty
    (C := SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods t)))
  refine ⟨l, ?_⟩
  have hρ := Classical.choose_spec (Scheme.exists_strictHenselizationStructuralMap t) j
  change _ = Scheme.strictHenselizationStructuralMap t at hρ
  rw [← hρ]
  have h := congrArg (fun f ↦ f ≫ ((Scheme.AffineEtale.Spec Y).obj (N.obj j).1).hom)
    (hleg j)
  apply Eq.trans ?_ (N.obj j).2.w
  simpa only [Category.assoc, Scheme.Etale.forget_obj_hom] using h

private theorem dense_of_strictPrincipalOpens (Y : Scheme.{u}) (U : Y.Opens)
    (hdom : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Y),
      IsDomain (Scheme.strictHenselizationRing t))
    (hU : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Y),
      ∃ s : Scheme.strictHenselizationRing t, s ≠ 0 ∧
        Scheme.strictHenselizationStructuralMap t ⁻¹' (U : Set Y) =
          (PrimeSpectrum.basicOpen s).carrier) : Dense (U : Set Y) := by
  classical
  apply dense_iff_inter_open.mpr
  rintro O hO ⟨x, hx⟩
  let Ω := AlgebraicClosure (Y.residueField x)
  let t : Spec (.of Ω) ⟶ Y := (Scheme.SpecToEquivOfField Ω Y).symm
    ⟨x, CommRingCat.ofHom (algebraMap (Y.residueField x) Ω)⟩
  have ht : t default = x := by simp [t]
  let :=  hdom Ω t
  obtain ⟨s, hs, hpre⟩ := hU Ω t
  obtain ⟨l, hl⟩ := pointedStrictLift t
  let q : PrimeSpectrum (Scheme.strictHenselizationRing t) := l default
  have hq : Scheme.strictHenselizationStructuralMap t q = x := by
    change (l ≫ Scheme.strictHenselizationStructuralMap t) default = x
    rw [hl, ht]
  let η : PrimeSpectrum (Scheme.strictHenselizationRing t) := ⊥
  have hη : Scheme.strictHenselizationStructuralMap t η ∈ U := by
    change η ∈ Scheme.strictHenselizationStructuralMap t ⁻¹' (U : Set Y)
    rw [hpre]
    simpa [η] using hs
  have hgen := ((PrimeSpectrum.le_iff_specializes η q).mp bot_le).map
    (Scheme.strictHenselizationStructuralMap t).continuous
  refine ⟨Scheme.strictHenselizationStructuralMap t η, ?_, hη⟩
  exact hgen.mem_open hO (hq.symm ▸ hx)

/-- Domain strict local rings and contracting sharp charts give an open dense triviality
locus, the stated principal opens for every finite generating list, and an injective
structural map on every chart stalk. Sections restrict to units on that open.
Source: the chart criterion extracted from ILO VI 1.4, printed p. 69, and
VIII 3.4.1--3.4.3, printed p. 110
(blueprint: lem-trf-monoidal-chart-dense-injective).

Proof:
1. Apply ideal contraction to the empty ideal. Its generated ring ideal is zero,
so every chart monomial is nonzero. Products of finitely many of them are nonzero
in the domain, including the empty product 1. Sharpness and the characteristic
identification say that only 0 maps to a unit. The stalk-chart pushout is therefore
the direct product of the chart with the ring units (`def-trf-fs-log-blowup`).
2. If u*a(p) = v*a(q), contraction of the principal monoid ideals gives p=q+r
and q=p+t. Cancellation gives r+t=0; sharpness forces r=t=0. Thus p=q, and
cancellation of the nonzero a(p) in the domain gives u=v.
3. At every geometric point of W the chart pushout has trivial characteristic
exactly when all chart elements are units. A generating list reduces this to its
finitely many entries. In the affine scheme W this is precisely D(product a_W(p_i)).
The canonical strict-local germ takes that product to product a(p_i), proving the
pullback formula (`def-weil-pbc-strict-henselization-limit`).
4. The pointed charts cover X. Étale maps are flat and locally finitely presented,
so are open (`lem-weil-pbc-flat-lfp-open`); their principal-open images cover the
triviality locus and show it is open.
5. For any geometric point above x, evaluation in its algebraically closed field
gives a prime of A above x. The zero prime of the domain generalizes it, hence its
image belongs to every neighbourhood of x. Nonvanishing of the generator product
puts that image in the triviality locus. Thus every nonempty open meets the locus
(`def-weil-pbc-strict-henselization-structural-map`).
6. On the triviality locus the log axiom identifies every log germ with a ring
unit. Local inverses of the structural image of any section agree and glue, so
its restriction is a unit (`def-trf-fs-log-blowup`). -/
theorem FineSaturatedLogScheme.monoidalChart_dense_injective
    (X : FineSaturatedLogScheme.{u})
    (hdom : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ X.scheme), IsDomain (Scheme.strictHenselizationRing t))
    (hcharts : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ X.scheme),
      ∃ (P : Type u) (_ : AddCancelCommMonoid P) (W : X.scheme.Etale)
        (w : (Scheme.pointSmallEtale t).fiber.obj W)
        (c : Multiplicative P →* X.logStructure.monoidSheaf.obj.obj (op W)),
        X.logStructure.IsContractingSharpChart t W w c) :
    ∃ U : X.scheme.Opens,
      (U : Set X.scheme) = X.logStructure.trivialityLocus ∧ Dense (U : Set X.scheme) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme)
        (P : Type u) [AddCancelCommMonoid P] (W : X.scheme.Etale)
        (w : (Scheme.pointSmallEtale t).fiber.obj W)
        (c : Multiplicative P →* X.logStructure.monoidSheaf.obj.obj (op W)),
        X.logStructure.IsContractingSharpChart t W w c →
          (∀ p : P,
            X.logStructure.chartStrictHenselizationMap t W w c (Multiplicative.ofAdd p) ≠ 0) ∧
          (∀ (r : ℕ) (p : Fin r → P), AddSubmonoid.closure (Set.range p) = ⊤ →
            (∏ i : Fin r, X.logStructure.chartStrictHenselizationMap t W w c
              (Multiplicative.ofAdd (p i))) ≠ 0 ∧
            W.hom ⁻¹' (U : Set X.scheme) =
              (W.left.basicOpen (∏ i : Fin r,
                X.logStructure.alpha.app (op W) (c (Multiplicative.ofAdd (p i)))) :
                  Set W.left) ∧
            Scheme.strictHenselizationStructuralMap t ⁻¹' (U : Set X.scheme) =
              ((PrimeSpectrum.basicOpen (∏ i : Fin r,
                X.logStructure.chartStrictHenselizationMap t W w c
                  (Multiplicative.ofAdd (p i)))).carrier :
                  Set (Spec (Scheme.strictHenselizationRing t)))) ∧
          Function.Bijective
            (((X.logStructure.toEtalePrelogStructure.germ t W w).hom.comp c).coprod
              (X.logStructure.strictHenselizationUnitsIn t)) ∧
          Function.Injective (fun z : Multiplicative P × (Scheme.strictHenselizationRing t)ˣ ↦
            (z.2 : Scheme.strictHenselizationRing t) *
              X.logStructure.chartStrictHenselizationMap t W w c z.1)) ∧
      ∀ (W : X.scheme.Etale) (m : X.logStructure.monoidSheaf.obj.obj (op W)),
        IsUnit ((pullback.fst W.hom U.ι).appTop (X.logStructure.alpha.app (op W) m)) := by
  classical
  obtain ⟨U, hU, hformula, hsections⟩ := X.finiteChart_trivialityLocus
  have hdense : Dense (U : Set X.scheme) := by
    apply dense_of_strictPrincipalOpens X.scheme U hdom
    intro Ω _ _ t
    obtain ⟨P, hP, W, w, c, hc⟩ := hcharts Ω t
    let :=  hP
    let :=  hdom Ω t
    have hn := contracting_nonzero _ hc.2.2.2.2.2
    let : AddMonoid.FG P := AddMonoid.fg_iff_mul_fg.mpr hc.2.2.1
    obtain ⟨S, hS⟩ := (inferInstance : AddMonoid.FG P).fg_top
    let e := S.equivFin
    let p : Fin S.card → P := fun i ↦ (e.symm i).val
    have hrange : Set.range p = (S : Set P) := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        exact (e.symm i).property
      · intro hz
        refine ⟨e ⟨z, hz⟩, ?_⟩
        simp [p]
    have hp : AddSubmonoid.closure (Set.range p) = ⊤ := by rw [hrange]; exact hS
    refine ⟨∏ i, X.logStructure.chartStrictHenselizationMap t W w c
      (Multiplicative.ofAdd (p i)), ?_, ?_⟩
    · exact Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hn (p i))
    · exact (hformula Ω t P W w c hc.1 hc.2.1 S.card p hp).2
  refine ⟨U, hU, hdense, ?_, hsections⟩
  intro Ω _ _ t P _ W w c hc
  let :=  hdom Ω t
  let a := X.logStructure.chartStrictHenselizationMap t W w c
  have hn := contracting_nonzero a hc.2.2.2.2.2
  have hi := contracting_injective a hc.2.2.2.1 hc.2.2.2.2.2
  refine ⟨hn, ?_, ?_, hi⟩
  · intro r p hp
    exact ⟨Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hn (p i)),
      hformula Ω t P W w c hc.1 hc.2.1 r p hp⟩
  · constructor
    · intro z z' hz
      apply hi
      have he := congrArg (fun m ↦ (strictLocalRingIsoStrictHenselization t).hom.hom
        (X.logStructure.toEtalePrelogStructure.stalkAlpha t m)) hz
      simp only [MonoidHom.coprod_apply, map_mul, strictUnitsIn_alpha] at he
      change a z.1 * (z.2 : Scheme.strictHenselizationRing t) =
        a z'.1 * (z'.2 : Scheme.strictHenselizationRing t) at he
      simpa only [mul_comm] using he
    · intro m
      obtain ⟨⟨p, v⟩, hv⟩ := (hc.2.1 Ω t w).1 m
      obtain ⟨v', hv'⟩ := strictUnitsIn_surjective X.logStructure t v
      refine ⟨(p, v'), ?_⟩
      change _ * X.logStructure.strictHenselizationUnitsIn t v' = m
      rw [hv']
      exact hv

end AlgebraicGeometry
