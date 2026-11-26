/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.RingTheory.HenselianEtaleRetraction
import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# Maps from ind-étale algebras into henselian local rings

Let `A` be a filtered colimit of étale `R`-algebras and `S` a henselian local `R`-algebra. Every
embedding of residue fields `κ(q) → κ(m_S)` over `R` lifts uniquely to an `R`-algebra map
`A → S` with `q` the inverse image of `m_S`.

## Implementation details

For a single étale algebra, `B = A ⊗_R S` is étale over `S`, and the residue maps define a
surjection `φ : B → κ(m_S)` whose kernel `q'` lies over `m_S` with residue field `κ(m_S)`. The
henselian étale retraction theorem (Stacks 04GG) gives a unique retraction `B → S` with inverse
image `q'`, whose restriction to `A` is the lift; uniqueness follows from uniqueness of the
retraction. In the filtered case, uniqueness makes the lifts at each stage compatible, and the
colimit universal property gives the lift. Universe lifts are used to put `S` and `B` in the same
universe.

## References

* [Stacks, Tags 08HQ, 08HR]
* [Stacks, Tag 04GG]
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Algebra

open scoped _root_.TensorProduct in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem etale_lift_field
    {R : Type u} [CommRing R] {S A : Type v} [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] [HenselianLocalRing S] [Etale R A]
    {K : Type w} [Field K] [Algebra S K] [Algebra R K] [IsScalarTower R S K]
    (hker : RingHom.ker (algebraMap S K) = IsLocalRing.maximalIdeal S)
    (hsurj : Function.Surjective (algebraMap S K)) (χ : A →ₐ[R] K) :
    ∃! f : A →ₐ[R] S, (IsScalarTower.toAlgHom R S K).comp f = χ := by
  classical
  let B := S ⊗[R] A
  let φ : B →ₐ[S] K := AlgHom.liftEquiv R S A K χ
  let q := RingHom.ker φ.toRingHom
  let m := IsLocalRing.maximalIdeal S
  have : q.IsPrime := RingHom.ker_isPrime φ.toRingHom
  have hq : q.comap (algebraMap S B) = m := by
    ext s
    change φ (algebraMap S B s) = 0 ↔ s ∈ m
    rw [φ.commutes]
    exact congrArg (fun j : Ideal S ↦ s ∈ j) hker |>.to_iff
  have units {T : Type v} [CommRing T] (f : T →+* K) (j : Ideal T) [j.IsPrime]
      (hj : j = RingHom.ker f) : j.primeCompl ≤ (IsUnit.submonoid K).comap f := by
    intro x hx
    change IsUnit (f x)
    rw [isUnit_iff_ne_zero]
    intro he
    exact hx (by simpa [hj, RingHom.mem_ker] using he)
  let η : m.ResidueField →+* K :=
    Ideal.ResidueField.lift m (algebraMap S K) hker.ge (units _ m hker.symm)
  let ψ : q.ResidueField →+* K :=
    Ideal.ResidueField.lift q φ.toRingHom le_rfl (units _ q rfl)
  have hηsurj : Function.Surjective η := by
    intro y
    obtain ⟨s, rfl⟩ := hsurj y
    exact ⟨algebraMap S m.ResidueField s, Ideal.ResidueField.lift_algebraMap ..⟩
  let θ := Ideal.ResidueField.map m q (algebraMap S B) hq.symm
  have hθ : ψ.comp θ = η := by
    apply Ideal.ResidueField.ringHom_ext
    ext s
    simp only [RingHom.comp_apply, θ, Ideal.ResidueField.map_algebraMap,
      ψ, η, Ideal.ResidueField.lift_algebraMap]
    exact φ.commutes s
  have hres : Function.Bijective θ := by
    refine ⟨RingHom.injective θ, ?_⟩
    intro y
    obtain ⟨x, hx⟩ := hηsurj (ψ y)
    refine ⟨x, RingHom.injective ψ ?_⟩
    exact (DFunLike.congr_fun hθ x).trans hx
  have : AlgebraicGeometry.Etale
      (AlgebraicGeometry.Scheme.Spec.map (CommRingCat.ofHom (algebraMap S B)).op) := by
    apply (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Etale) (φ := CommRingCat.ofHom (algebraMap S B))).mpr
    exact (RingHom.etale_algebraMap).mpr inferInstance
  have hσ : ∃! σ : B →ₐ[S] S, m.comap σ.toRingHom = q := by
    have hAlg : TensorProduct.leftAlgebra = (algebraMap S B).toAlgebra :=
      toAlgebra_algebraMap.symm
    have h := existsUnique_algHom_of_henselianLocalRing_etale
      (algebraMap S B) q hq hres
    rw [← hAlg] at h
    exact h
  obtain ⟨σ, hσ, hσuniq⟩ := hσ
  let π : S →ₐ[S] K := Algebra.ofId S K
  have red (σ' : B →ₐ[S] S) (hσ' : m.comap σ'.toRingHom = q) : π.comp σ' = φ := by
    apply AlgHom.ext
    intro b
    obtain ⟨s, hs⟩ := hsurj (φ b)
    have hdiff : b - algebraMap S B s ∈ q := by
      change φ (b - algebraMap S B s) = 0
      simp only [map_sub, AlgHom.commutes, hs, sub_self]
    rw [← hσ'] at hdiff
    change σ' (b - algebraMap S B s) ∈ m at hdiff
    have hz : algebraMap S K (σ' (b - algebraMap S B s)) = 0 := by
      rw [← RingHom.mem_ker, hker]
      exact hdiff
    change algebraMap S K (σ' b) = φ b
    simpa only [map_sub, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_eq_zero, hs] using hz
  let f := (AlgHom.liftEquiv R S A S).symm σ
  have hf : (IsScalarTower.toAlgHom R S K).comp f = χ := by
    apply AlgHom.ext
    intro a
    have ha := DFunLike.congr_fun (red σ hσ) (1 ⊗ₜ[R] a)
    change algebraMap S K (σ (1 ⊗ₜ[R] a)) = φ (1 ⊗ₜ[R] a) at ha
    change algebraMap S K (σ (1 ⊗ₜ[R] a)) = χ a
    exact ha.trans ((AlgHom.liftEquiv_tmul χ 1 a).trans (one_smul S (χ a)))
  refine ⟨f, hf, ?_⟩
  intro f' hf'
  let σ' := AlgHom.liftEquiv R S A S f'
  have hred : π.comp σ' = φ := by
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro a
    simpa [σ', φ, π, AlgHom.liftEquiv_tmul] using DFunLike.congr_fun hf' a
  have hσ' : m.comap σ'.toRingHom = q := by
    ext b
    change σ' b ∈ IsLocalRing.maximalIdeal S ↔ φ b = 0
    rw [← hker]
    change algebraMap S K (σ' b) = 0 ↔ φ b = 0
    have hb := DFunLike.congr_fun hred b
    change algebraMap S K (σ' b) = φ b at hb
    rw [hb]
  simpa only [σ', Equiv.symm_apply_apply, f] using
    congrArg (AlgHom.liftEquiv R S A S).symm (hσuniq σ' hσ')

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every residue-valued map from a single étale algebra has a unique henselian lift.
-/
private theorem existsUnique_etale_residue_lift
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S] [HenselianLocalRing S]
    (A : Type w) [CommRing A] [Algebra R A] [Etale R A]
    (χ : A →ₐ[R] (IsLocalRing.maximalIdeal S).ResidueField) :
    ∃! f : A →ₐ[R] S,
      (IsScalarTower.toAlgHom R S (IsLocalRing.maximalIdeal S).ResidueField).comp f = χ := by
  classical
  let T := ULift.{w} S
  let D := ULift.{v} A
  let K := (IsLocalRing.maximalIdeal S).ResidueField
  let eS : T ≃ₐ[R] S := ULift.algEquiv
  let eA : D ≃ₐ[R] A := ULift.algEquiv
  let : HenselianLocalRing T := HenselianLocalRing.of_ringEquiv eS.symm.toRingEquiv
  let : Etale R D := Etale.of_equiv eA.symm
  let : Algebra T K := ((algebraMap S K).comp eS.toRingHom).toAlgebra
  let : SMul R T := (inferInstance : Algebra R T).toSMul
  let : SMul T K := (inferInstance : Algebra T K).toSMul
  let : IsScalarTower R T K := IsScalarTower.of_algebraMap_eq' (R := R) (S := T) (A := K) (by
    ext r
    exact (IsScalarTower.algebraMap_apply R S K r).trans
      (congrArg (algebraMap S K) (eS.commutes r)).symm)
  have hker : RingHom.ker (algebraMap T K) = IsLocalRing.maximalIdeal T := by
    ext x
    change algebraMap S K (eS x) = 0 ↔ x ∈ IsLocalRing.maximalIdeal T
    rw [Ideal.algebraMap_residueField_eq_zero, IsLocalRing.mem_maximalIdeal,
      IsLocalRing.mem_maximalIdeal]
    change ¬ IsUnit (eS x) ↔ ¬ IsUnit x
    exact not_congr ⟨fun h ↦ by simpa using h.map eS.symm.toRingHom,
      fun h ↦ h.map eS.toRingHom⟩
  have hsurj : Function.Surjective (algebraMap T K) :=
    (IsLocalRing.maximalIdeal S).algebraMap_residueField_surjective.comp eS.surjective
  obtain ⟨f, hf, huniq⟩ := etale_lift_field hker hsurj (χ.comp eA.toAlgHom)
  let g : A →ₐ[R] S := eS.toAlgHom.comp (f.comp eA.symm.toAlgHom)
  have hg : (IsScalarTower.toAlgHom R S K).comp g = χ := by
    apply AlgHom.ext
    intro a
    exact DFunLike.congr_fun hf (eA.symm a)
  refine ⟨g, hg, ?_⟩
  intro g' hg'
  let f' : D →ₐ[R] T := eS.symm.toAlgHom.comp (g'.comp eA.toAlgHom)
  have hf' : (IsScalarTower.toAlgHom R T K).comp f' = χ.comp eA.toAlgHom := by
    apply AlgHom.ext
    intro a
    exact DFunLike.congr_fun hg' (eA a)
  have heq := huniq f' hf'
  apply AlgHom.ext
  intro a
  exact congrArg eS (DFunLike.congr_fun heq (eA.symm a))

private theorem filteredColimit_forget
    {R : Type u} [CommRing R] {I : Type w} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{w} R) (c : Cocone F) (hc : IsColimit c) :
    Nonempty (IsColimit ((forget (CommAlgCat.{w} R)).mapCocone c)) := by
  classical
  let G := F ⋙ forget₂ (CommAlgCat.{w} R) CommRingCat.{w}
  let d := CommRingCat.FilteredColimits.colimitCocone G
  let hd := CommRingCat.FilteredColimits.colimitCoconeIsColimit G
  let i₀ : I := IsFiltered.nonempty.some
  let ρ : R →+* d.pt := (d.ι.app i₀).hom.comp (algebraMap R (F.obj i₀))
  have hρ (i : I) (r : R) : ρ r = d.ι.app i (algebraMap R (F.obj i) r) := by
    let k := IsFiltered.max i₀ i
    have h₀ := ConcreteCategory.congr_hom (d.w (IsFiltered.leftToMax i₀ i))
      (algebraMap R (F.obj i₀) r)
    have h₁ := ConcreteCategory.congr_hom (d.w (IsFiltered.rightToMax i₀ i))
      (algebraMap R (F.obj i) r)
    change d.ι.app i₀ (algebraMap R (F.obj i₀) r) = _
    exact h₀.symm.trans (by simpa [G, AlgHom.commutes] using h₁)
  let : Algebra R d.pt := ρ.toAlgebra
  let t : Cocone F :=
    { pt := CommAlgCat.of R d.pt
      ι :=
        { app := fun i ↦ CommAlgCat.ofHom
            { __ := (d.ι.app i).hom
              commutes' := fun r ↦ (hρ i r).symm }
          naturality := by
            intro i j f
            apply CommAlgCat.hom_ext
            apply AlgHom.ext
            intro x
            exact ConcreteCategory.congr_hom (d.w f) x } }
  have ht : IsColimit t := by
    refine
      { desc := fun s ↦ CommAlgCat.ofHom
          { __ := (hd.desc ((forget₂ (CommAlgCat.{w} R) CommRingCat.{w}).mapCocone s)).hom
            commutes' := ?_ }
        fac := ?_
        uniq := ?_ }
    · intro r
      change hd.desc _ (d.ι.app i₀ (algebraMap R (F.obj i₀) r)) = _
      exact (ConcreteCategory.congr_hom
        (hd.fac ((forget₂ (CommAlgCat.{w} R) CommRingCat.{w}).mapCocone s) i₀)
        (algebraMap R (F.obj i₀) r)).trans ((s.ι.app i₀).hom.commutes r)
    · intro s i
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro x
      exact ConcreteCategory.congr_hom (hd.fac _ i) x
    · intro s m hm
      apply CommAlgCat.hom_ext
      apply AlgHom.toRingHom_injective
      change m.hom.toRingHom =
        (hd.desc ((forget₂ (CommAlgCat.{w} R) CommRingCat.{w}).mapCocone s)).hom
      have h : CommRingCat.ofHom m.hom.toRingHom =
          hd.desc ((forget₂ (CommAlgCat.{w} R) CommRingCat.{w}).mapCocone s) := by
        apply hd.hom_ext
        intro i
        exact (congrArg (fun f ↦ (forget₂ (CommAlgCat.{w} R) CommRingCat.{w}).map f)
          (hm i)).trans
            (hd.fac ((forget₂ (CommAlgCat.{w} R) CommRingCat.{w}).mapCocone s) i).symm
      exact congrArg CommRingCat.Hom.hom h
  have ht' : IsColimit ((forget (CommAlgCat.{w} R)).mapCocone t) :=
    isColimitOfPreserves (forget CommRingCat.{w}) hd
  exact ⟨IsColimit.ofIsoColimit ht'
    (Functor.mapIso (Cocone.functoriality F (forget (CommAlgCat.{w} R)))
      (ht.uniqueUpToIso hc))⟩

set_option backward.isDefEq.respectTransparency false in
private theorem filteredColimit_algHom
    {R : Type u} [CommRing R] {I : Type w} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{w} R) (c : Cocone F) (hc : IsColimit c)
    {S : Type v} [CommRing S] [Algebra R S]
    (f : ∀ i, F.obj i →ₐ[R] S)
    (hf : ∀ (i j : I) (t : i ⟶ j), (f j).comp (F.map t).hom = f i) :
    ∃ g : c.pt →ₐ[R] S, ∀ i, g.comp (c.ι.app i).hom = f i := by
  classical
  let U := F ⋙ forget (CommAlgCat.{w} R)
  let d := (forget (CommAlgCat.{w} R)).mapCocone c
  let hd : IsColimit d := (filteredColimit_forget F c hc).some
  let dt : U.CoconeTypes := U.coconeTypesEquiv.symm d
  have hdt : dt.IsColimit := (Types.isColimit_iff_coconeTypesIsColimit d).mp ⟨hd⟩
  let s : U.CoconeTypes :=
    { pt := S
      ι := fun i ↦ f i
      ι_naturality := by
        intro i j t
        exact congrArg DFunLike.coe (hf i j t) }
  let g : c.pt → S := hdt.desc s
  have hg (i : I) (x : F.obj i) : g ((c.ι.app i).hom x) = f i x :=
    hdt.fac_apply s i x
  let i₀ : I := IsFiltered.nonempty.some
  refine ⟨{ toFun := g
            map_one' := ?_
            map_mul' := ?_
            map_zero' := ?_
            map_add' := ?_
            commutes' := ?_ }, ?_⟩
  · simpa only [map_one] using (hg i₀ 1).trans (map_one (f i₀))
  · intro x y
    obtain ⟨i, x, y, rfl, rfl⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂ hd x y
    change g ((c.ι.app i).hom x * (c.ι.app i).hom y) =
      g ((c.ι.app i).hom x) * g ((c.ι.app i).hom y)
    rw [← map_mul, hg, hg, hg, map_mul]
  · simpa only [map_zero] using (hg i₀ 0).trans (map_zero (f i₀))
  · intro x y
    obtain ⟨i, x, y, rfl, rfl⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂ hd x y
    change g ((c.ι.app i).hom x + (c.ι.app i).hom y) =
      g ((c.ι.app i).hom x) + g ((c.ι.app i).hom y)
    rw [← map_add, hg, hg, hg, map_add]
  · intro r
    have hι := (c.ι.app i₀).hom.commutes r
    dsimp at hι
    exact (congrArg g hι).symm.trans
      ((hg i₀ (algebraMap R (F.obj i₀) r)).trans ((f i₀).commutes r))
  · intro i
    apply AlgHom.ext
    exact hg i

/-- Let `A` be a filtered colimit of étale `R`-algebras and `S` a henselian local `R`-algebra.
Every map of residue fields `τ : κ(q) → κ(m_S)` compatible with `R` lifts to a unique
`R`-algebra map `f : A → S` such that `q` is the inverse image of `m_S` and `f` induces `τ`.
-/
theorem map_into_henselian_colimit
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S] [HenselianLocalRing S]
    (A : Type w) [CommRing A] [Algebra R A]
    (I : Type w) [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{w} R) [HasColimit F]
    (hA : Nonempty (colimit F ≅ CommAlgCat.of R A))
    (hEtale : ∀ i : I, Algebra.Etale R (F.obj i))
    (q : Ideal A) [q.IsPrime]
    (p : Ideal R) [p.IsPrime]
    (hp : p = q.comap (algebraMap R A))
    (hm : p = (IsLocalRing.maximalIdeal S).comap (algebraMap R S))
    (τ : q.ResidueField →+* (IsLocalRing.maximalIdeal S).ResidueField)
    (hτ : τ.comp (Ideal.ResidueField.map p q (algebraMap R A) hp) =
      Ideal.ResidueField.map p (IsLocalRing.maximalIdeal S) (algebraMap R S) hm) :
    ∃! f : A →ₐ[R] S,
      ∃ hf : q = (IsLocalRing.maximalIdeal S).comap f.toRingHom,
        Ideal.ResidueField.map q (IsLocalRing.maximalIdeal S) f.toRingHom hf = τ := by
  classical
  let m := IsLocalRing.maximalIdeal S
  let π : S →ₐ[R] m.ResidueField := IsScalarTower.toAlgHom R S m.ResidueField
  let χ : A →ₐ[R] m.ResidueField :=
    { __ := τ.comp (algebraMap A q.ResidueField)
      commutes' := by
        intro r
        change τ (algebraMap A q.ResidueField (algebraMap R A r)) =
          algebraMap R m.ResidueField r
        have h := DFunLike.congr_fun hτ (algebraMap R p.ResidueField r)
        simpa only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap,
          IsScalarTower.algebraMap_apply R A q.ResidueField,
          IsScalarTower.algebraMap_apply R S m.ResidueField] using h }
  have spec (f : A →ₐ[R] S) :
      (∃ hf : q = m.comap f.toRingHom,
        Ideal.ResidueField.map q m f.toRingHom hf = τ) ↔ π.comp f = χ := by
    constructor
    · rintro ⟨hf, hres⟩
      apply AlgHom.ext
      intro x
      exact (Ideal.ResidueField.map_algebraMap q m f.toRingHom hf x).symm.trans
        (DFunLike.congr_fun hres (algebraMap A q.ResidueField x))
    · intro hred
      have hf : q = m.comap f.toRingHom := by
        ext x
        change x ∈ q ↔ f x ∈ m
        have hx := DFunLike.congr_fun hred x
        change algebraMap S m.ResidueField (f x) = τ (algebraMap A q.ResidueField x) at hx
        rw [← Ideal.algebraMap_residueField_eq_zero (I := m), hx, map_eq_zero]
        exact (Ideal.algebraMap_residueField_eq_zero (I := q)).symm
      refine ⟨hf, Ideal.ResidueField.ringHom_ext ?_⟩
      apply RingHom.ext
      intro x
      exact (Ideal.ResidueField.map_algebraMap q m f.toRingHom hf x).trans
        (DFunLike.congr_fun hred x)
  obtain ⟨e⟩ := hA
  let c := (colimit.cocone F).extend e.hom
  have hc : IsColimit c := (colimit.isColimit F).extendIso e.hom
  have lifts (i : I) : ∃! f : F.obj i →ₐ[R] S,
      π.comp f = χ.comp (c.ι.app i).hom := by
    let : Etale R (F.obj i) := hEtale i
    exact existsUnique_etale_residue_lift R S (F.obj i) (χ.comp (c.ι.app i).hom)
  choose f hf huniq using lifts
  have hcompat (i j : I) (t : i ⟶ j) : (f j).comp (F.map t).hom = f i := by
    apply huniq i
    rw [← AlgHom.comp_assoc, hf j, AlgHom.comp_assoc]
    have hw := congrArg CommAlgCat.Hom.hom (c.w t)
    dsimp only [CommAlgCat.hom_comp] at hw
    rw [hw]
  obtain ⟨g, hg⟩ := filteredColimit_algHom F c hc f hcompat
  change A →ₐ[R] S at g
  have rep (x : A) : ∃ (i : I) (y : F.obj i), (c.ι.app i).hom y = x :=
    Types.jointly_surjective_of_isColimit (filteredColimit_forget F c hc).some x
  have hred : π.comp g = χ := by
    apply AlgHom.ext
    intro x
    obtain ⟨i, y, rfl⟩ := rep x
    change π (g ((c.ι.app i).hom y)) = χ ((c.ι.app i).hom y)
    exact (congrArg π (DFunLike.congr_fun (hg i) y)).trans (DFunLike.congr_fun (hf i) y)
  refine ⟨g, (spec g).mpr hred, ?_⟩
  intro g' hg'
  have hg'red := (spec g').mp hg'
  have hstage (i : I) : g'.comp (c.ι.app i).hom = f i := by
    apply huniq i
    rw [← AlgHom.comp_assoc, hg'red]
  apply AlgHom.ext
  intro x
  obtain ⟨i, y, rfl⟩ := rep x
  exact (DFunLike.congr_fun (hstage i) y).trans (DFunLike.congr_fun (hg i) y).symm

end Algebra
