/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.BertiniUniversalFamily
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.Topology.KrullDimension
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Sheaf.FieldTheory.BertiniFieldExtension
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! Intermediate steps in the incidence proof of Stacks Project, Tag 0G4F. -/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The polynomial projection after solving the first incidence variable.
Source: Stacks Project, Tag 0G4F, final paragraph.
(blueprint: lem-zl-bertini-polynomial-residue-arrow). -/
noncomputable def bertiniEliminatedProjection
    (k : Type u) [Field k] (A : CommRingCat.{u}) [Algebra k A]
    (n : ℕ) (g : Fin n → A) :
    Spec (.of (MvPolynomial (Fin n) A)) ⟶ Spec (.of (MvPolynomial (Fin (n + 1)) k)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom
    ((MvPolynomial.C : A →+* MvPolynomial (Fin n) A).comp (algebraMap k A))
    (Fin.cases (motive := fun _ : Fin (n + 1) ↦ MvPolynomial (Fin n) A)
      (-∑ i : Fin n, (MvPolynomial.C (g i) : MvPolynomial (Fin n) A) * MvPolynomial.X i)
      MvPolynomial.X)))

private noncomputable def affineResidueMap (R : CommRingCat.{u}) (x : Spec R) :
    R →+* (Spec R).residueField x :=
  ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial ≫
    (Spec R).residue x).hom

private theorem affineResidueMap_eq (R : CommRingCat.{u}) (x : Spec R) :
    CommRingCat.ofHom (affineResidueMap R x) =
      CommRingCat.ofHom (algebraMap R x.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso R x).inv := by
  exact (Scheme.Spec.algebraMap_residueFieldIso_inv R x).symm

private theorem affineResidueMap_naturality {R B : CommRingCat.{u}}
    (φ : R ⟶ B) (x : Spec B) :
    CommRingCat.ofHom (affineResidueMap R (Spec.map φ x)) ≫
        (Spec.map φ).residueFieldMap x =
      φ ≫ CommRingCat.ofHom (affineResidueMap B x) := by
  change ((Scheme.ΓSpecIso R).inv ≫
      (Spec R).presheaf.germ ⊤ ((Spec.map φ) x) trivial ≫
      (Spec R).residue ((Spec.map φ) x)) ≫ (Spec.map φ).residueFieldMap x =
    φ ≫ (Scheme.ΓSpecIso B).inv ≫ (Spec B).presheaf.germ ⊤ x trivial ≫
      (Spec B).residue x
  rw [Category.assoc, Category.assoc, Scheme.residue_residueFieldMap,
    ← Category.assoc ((Spec R).presheaf.germ _ _ _),
    Scheme.Hom.germ_stalkMap]
  simp only [Category.assoc]
  change ((Scheme.ΓSpecIso R).inv ≫ (Spec.map φ).appTop) ≫
    (Spec B).presheaf.germ ⊤ x trivial ≫ (Spec B).residue x = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  simp only [Category.assoc]

private theorem affineResidueMap_isFractionRing (R : CommRingCat.{u}) [IsDomain R]
    (x : Spec R) (hx : x.asIdeal = ⊥) :
    letI := (affineResidueMap R x).toAlgebra
    IsFractionRing R ((Spec R).residueField x) := by
  let := (affineResidueMap R x).toAlgebra
  have : IsFractionRing R x.asIdeal.ResidueField := by
    have hx' : x = (⊥ : PrimeSpectrum R) := PrimeSpectrum.ext hx
    subst x
    change IsFractionRing R (⊥ : Ideal R).ResidueField
    infer_instance
  let e : x.asIdeal.ResidueField ≃ₐ[R] (Spec R).residueField x :=
    { (Scheme.Spec.residueFieldIso R x).symm.commRingCatIsoToRingEquiv with
      commutes' r := by
        change ((Scheme.Spec.residueFieldIso R x).inv.hom.comp
          (algebraMap R x.asIdeal.ResidueField)) r = affineResidueMap R x r
        exact (congrArg (fun f ↦ f.hom r) (affineResidueMap_eq R x)).symm }
  exact IsFractionRing.of_algEquiv e

private noncomputable def polynomialFractionMap
    (A : CommRingCat.{u}) [IsDomain A] (n : ℕ) :
    MvPolynomial (Fin n) A →+* FieldTheory.bertiniOmega (FractionRing A) n :=
  (algebraMap (MvPolynomial (Fin n) (FractionRing A))
    (FieldTheory.bertiniOmega (FractionRing A) n)).comp
      (MvPolynomial.map (algebraMap A (FractionRing A)))

private theorem polynomialFractionMap_eq (A : CommRingCat.{u}) [IsDomain A] (n : ℕ) :
    algebraMap (MvPolynomial (Fin n) A)
      (FieldTheory.bertiniOmega (FractionRing A) n) = polynomialFractionMap A n := by
  rw [IsScalarTower.algebraMap_eq (MvPolynomial (Fin n) A)
    (MvPolynomial (Fin n) (FractionRing A))
    (FieldTheory.bertiniOmega (FractionRing A) n)]
  rfl

private theorem polynomialFractionMap_isFractionRing
    (A : CommRingCat.{u}) [IsDomain A] (n : ℕ) :
    IsFractionRing (MvPolynomial (Fin n) A)
      (FieldTheory.bertiniOmega (FractionRing A) n) := by
  let B := MvPolynomial (Fin n) A
  let D := MvPolynomial (Fin n) (FractionRing A)
  let Ω := FieldTheory.bertiniOmega (FractionRing A) n
  have : IsScalarTower B D Ω := inferInstance
  let M := (nonZeroDivisors A).map (MvPolynomial.C : A →+* B)
  have : IsLocalization M D := MvPolynomial.isLocalization (nonZeroDivisors A) (FractionRing A)
  have h := IsLocalization.localization_localization_isLocalization_of_has_all_units
    M (nonZeroDivisors D) Ω (fun _ hx ↦ hx.mem_nonZeroDivisors)
  have he : (nonZeroDivisors D).comap (algebraMap B D) = nonZeroDivisors B := by
    ext b
    simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    have hi : Function.Injective (algebraMap B D) :=
      MvPolynomial.map_injective (algebraMap A (FractionRing A))
        (IsFractionRing.injective A (FractionRing A))
    simpa only [map_zero] using
      (hi.ne_iff : algebraMap B D b ≠ algebraMap B D 0 ↔ b ≠ 0)
  rw [he] at h
  exact h

private theorem adjoin_finCases_neg
    (k E : Type u) [Field k] [Field E] [Algebra k E]
    (n : ℕ) (a : E) (f : Fin n → E) :
    IntermediateField.adjoin k
        (Set.range (Fin.cases (motive := fun _ : Fin (n + 1) ↦ E) (-a) f)) =
      IntermediateField.adjoin k (Set.range (Fin.lastCases a f)) := by
  apply le_antisymm
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · apply IntermediateField.neg_mem
      exact IntermediateField.subset_adjoin k _ ⟨Fin.last n, by simp⟩
    · exact IntermediateField.subset_adjoin k _ ⟨j.castSucc, by simp⟩
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · have h := IntermediateField.subset_adjoin k
        (Set.range (Fin.cases (motive := fun _ : Fin (n + 1) ↦ E) (-a) f))
        (Set.mem_range_self (0 : Fin (n + 1)))
      simp only [Fin.cases_zero] at h
      have h' := IntermediateField.neg_mem _ h
      rw [neg_neg] at h'
      simp only [Fin.lastCases_last]
      exact h'
    · exact IntermediateField.subset_adjoin k _ ⟨j.succ, by simp⟩

private theorem coe_equivOfEq_ringEquiv
    {k E : Type u} [Field k] [Field E] [Algebra k E]
    {S T : IntermediateField k E} (h : S = T) (z : S) :
    ((IntermediateField.equivOfEq h).toRingEquiv z : E) = (z : E) := rfl

private theorem algEquiv_ringEquiv_commutes
    {R D E : Type*} [CommRing R] [CommRing D] [CommRing E]
    [Algebra R D] [Algebra R E] (e : D ≃ₐ[R] E) (r : R) :
    e.toRingEquiv (algebraMap R D r) = algebraMap R E r := e.commutes r

private theorem aevalEquivField_ringEquiv_algebraMap
    {k E I : Type*} [Field k] [Field E] [Algebra k E]
    {y : I → E} (hy : AlgebraicIndependent k y) (a : MvPolynomial I k) :
    (hy.aevalEquivField.toRingEquiv
      (algebraMap (MvPolynomial I k) (FractionRing (MvPolynomial I k)) a) : E) =
        MvPolynomial.aeval y a := hy.aevalEquivField_algebraMap_apply_coe a

private noncomputable def specArrowIso
    {R S R' S' : CommRingCat.{u}} (f : R ⟶ S) (g : R' ⟶ S')
    (eR : R ≅ R') (eS : S ≅ S') (h : f ≫ eS.hom = eR.hom ≫ g) :
    Arrow.mk (Spec.map f) ≅ Arrow.mk (Spec.map g) :=
  Arrow.isoMk' _ _ (Scheme.Spec.mapIso eS.symm.op) (Scheme.Spec.mapIso eR.symm.op) (by
    change Spec.map eS.inv ≫ Spec.map g = Spec.map f ≫ Spec.map eR.inv
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply (cancel_mono eS.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, h,
      Iso.inv_hom_id_assoc])

/-- Generic residue-field computation for the eliminated affine incidence equation.

Source: Stacks Project, More on Morphisms, Tag 0G4F, final proof paragraph.
(blueprint: lem-zl-bertini-polynomial-residue-arrow).

Proof: Dominance makes the polynomial parameter substitution injective and sends the generic
point to the parameter generic point. Identify
the two generic residue fields with the respective fraction fields using the generic stalk
localizations. Localizing the injective parameter substitution identifies its fraction field
with its image, the intermediate field generated by the polynomial variables and minus the
linear combination. This intermediate field is unchanged when the last generator is negated,
so it is precisely bertiniBaseField. The target fraction field identifies with bertiniOmega
by first passing from A to Frac A. The defining substitution makes these isomorphisms commute
with the two field maps, giving the arrow isomorphism after Spec.
-/
theorem bertiniPolynomialResidueArrow
    (k : Type u) [Field k] (A : CommRingCat.{u})
    [Algebra k A] [Algebra.FiniteType k A] [IsDomain A]
    (n : ℕ) (g : Fin n → A)
    (hp : IsDominant (bertiniEliminatedProjection k A n g)) :
    let p := bertiniEliminatedProjection k A n g
    Nonempty (Arrow.mk
      (Spec.map (p.residueFieldMap (genericPoint (Spec (.of (MvPolynomial (Fin n) A)))))) ≅
      Arrow.mk (Spec.map (CommRingCat.ofHom (algebraMap
        (FieldTheory.bertiniBaseField k (FractionRing A) n
          (fun i ↦ algebraMap A (FractionRing A) (g i)))
        (FieldTheory.bertiniOmega (FractionRing A) n))))) := by
  classical
  let B := MvPolynomial (Fin n) A
  let R := MvPolynomial (Fin (n + 1)) k
  let Ω := FieldTheory.bertiniOmega (FractionRing A) n
  let F := FieldTheory.bertiniBaseField k (FractionRing A) n
    (fun i ↦ algebraMap A (FractionRing A) (g i))
  let p := bertiniEliminatedProjection k A n g
  let := hp
  let η := genericPoint (Spec (.of B))
  let ξ := p η
  have hξ : ξ = genericPoint (Spec (.of R)) := by
    apply IsGenericPoint.eq _ (genericPoint_spec _)
    have hd : closure (p '' (Set.univ : Set (Spec (.of B)))) = Set.univ := by
      rw [Set.image_univ]
      exact p.denseRange.closure_range
    exact hd ▸ (genericPoint_spec _).image p.continuous
  have hη0 : η.asIdeal = ⊥ := by
    dsimp only [η]
    rw [genericPoint_eq_bot_of_affine]
    rfl
  have hξ0 : ξ.asIdeal = ⊥ := by
    rw [hξ, genericPoint_eq_bot_of_affine]
    rfl
  let : Algebra B ((Spec (.of B)).residueField η) :=
    (affineResidueMap (.of B) η).toAlgebra
  let : Algebra R ((Spec (.of R)).residueField ξ) :=
    (affineResidueMap (.of R) ξ).toAlgebra
  have : IsFractionRing B ((Spec (.of B)).residueField η) :=
    affineResidueMap_isFractionRing (.of B) η hη0
  have : IsFractionRing R ((Spec (.of R)).residueField ξ) :=
    affineResidueMap_isFractionRing (.of R) ξ hξ0
  have : IsFractionRing B Ω := polynomialFractionMap_isFractionRing A n
  let eB : (Spec (.of B)).residueField η ≃ₐ[B] Ω :=
    (FractionRing.algEquiv B ((Spec (.of B)).residueField η)).symm.trans
      (FractionRing.algEquiv B Ω)
  let eR : (Spec (.of R)).residueField ξ ≃ₐ[R] FractionRing R :=
    (FractionRing.algEquiv R ((Spec (.of R)).residueField ξ)).symm
  let φ : R →+* B := MvPolynomial.eval₂Hom
    ((MvPolynomial.C : A →+* B).comp (algebraMap k A))
    (Fin.cases (motive := fun _ ↦ B)
      (-∑ i : Fin n, MvPolynomial.C (g i) * MvPolynomial.X i) MvPolynomial.X)
  have hφ : Function.Injective φ := by
    have hd : DenseRange (PrimeSpectrum.comap φ) := p.denseRange
    have hk := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).mp hd
    have hz : nilradical R = ⊥ := nilradical_eq_bot_iff.mpr inferInstance
    exact (RingHom.injective_iff_ker_eq_bot φ).mpr
      (le_antisymm (hz ▸ hk) bot_le)
  let y : Fin (n + 1) → Ω := Fin.cases
    (motive := fun _ ↦ Ω)
    (-FieldTheory.bertiniXi k (FractionRing A) n
      (fun i ↦ algebraMap A (FractionRing A) (g i)))
    (FieldTheory.bertiniCoordinate (FractionRing A) n)
  have hyφ : (MvPolynomial.aeval y).toRingHom = (algebraMap B Ω).comp φ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      suffices h : algebraMap k Ω a =
          algebraMap (MvPolynomial (Fin n) (FractionRing A)) Ω
            (MvPolynomial.C (algebraMap A (FractionRing A) (algebraMap k A a))) by
        simpa [φ, B, Ω, polynomialFractionMap_eq, polynomialFractionMap] using h
      change algebraMap k Ω a =
        algebraMap (MvPolynomial (Fin n) (FractionRing A)) Ω
          (algebraMap (FractionRing A) (MvPolynomial (Fin n) (FractionRing A))
            (algebraMap A (FractionRing A) (algebraMap k A a)))
      simp only [← IsScalarTower.algebraMap_apply]
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · suffices h :
            (∑ i : Fin n, algebraMap (FractionRing A) Ω
                (algebraMap A (FractionRing A) (g i)) *
              algebraMap (MvPolynomial (Fin n) (FractionRing A)) Ω (MvPolynomial.X i)) =
            ∑ i : Fin n, algebraMap (MvPolynomial (Fin n) (FractionRing A)) Ω
                (MvPolynomial.C (algebraMap A (FractionRing A) (g i))) *
              algebraMap (MvPolynomial (Fin n) (FractionRing A)) Ω (MvPolynomial.X i) by
          simpa [y, φ, FieldTheory.bertiniXi, FieldTheory.bertiniCoordinate, B, Ω,
            polynomialFractionMap_eq, polynomialFractionMap] using h
        apply Finset.sum_congr rfl
        intro i _
        congr 1
      · simp [y, φ, FieldTheory.bertiniCoordinate, B, Ω,
          polynomialFractionMap_eq, polynomialFractionMap]
  have hy : AlgebraicIndependent k y := by
    change Function.Injective (MvPolynomial.aeval y).toRingHom
    rw [hyφ]
    exact (IsFractionRing.injective B Ω).comp hφ
  have hF : IntermediateField.adjoin k (Set.range y) = F :=
    adjoin_finCases_neg k Ω n _ _
  let eF : (Spec (.of R)).residueField ξ ≃+* F :=
    eR.toRingEquiv.trans (hy.aevalEquivField.toRingEquiv.trans
      (IntermediateField.equivOfEq hF).toRingEquiv)
  have hsq : eB.toRingHom.comp (p.residueFieldMap η).hom =
      (algebraMap F Ω).comp eF.toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors R)
    apply RingHom.ext
    intro a
    have hn := congrArg (fun h ↦ h.hom a)
      (affineResidueMap_naturality (CommRingCat.ofHom φ) η)
    change eB ((p.residueFieldMap η) (algebraMap R
        ((Spec (.of R)).residueField ξ) a)) =
      (eF (algebraMap R ((Spec (.of R)).residueField ξ) a) : Ω)
    change (p.residueFieldMap η) (algebraMap R ((Spec (.of R)).residueField ξ) a) =
      algebraMap B ((Spec (.of B)).residueField η) (φ a) at hn
    rw [hn, eB.commutes]
    dsimp only [eF, RingEquiv.trans_apply]
    rw [coe_equivOfEq_ringEquiv, algEquiv_ringEquiv_commutes,
      aevalEquivField_ringEquiv_algebraMap]
    exact (congrArg (fun f : R →+* Ω ↦ f a) hyφ).symm
  exact ⟨specArrowIso (p.residueFieldMap η) (CommRingCat.ofHom (algebraMap F Ω))
    eF.toCommRingCatIso eB.toRingEquiv.toCommRingCatIso (CommRingCat.hom_ext hsq)⟩

end AlgebraicGeometry
