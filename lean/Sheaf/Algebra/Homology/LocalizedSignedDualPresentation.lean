/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Algebra.Homology.RationalTermHomComparison
public import WeilConjectures.Algebra.Homology.HomComplexToSingle
public import WeilConjectures.Algebra.Homology.HomComplexComponents
import all Sheaf.Algebra.Homology.RationalTermHomComparison
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Data.Int.Interval

/-!
# Strictification and signed dual presentation after scalar localization

Source: Stacks Project, sites-cohomology.tex, Tags 0A8X, 08JI and 08JJ;
blueprint prop-sf-dualizable, local bounded dual presentation. The strictification
argument is the agent-written finite denominator and torsion-defect calculation
using algebra.tex, Tags 00DK, 07JZ and 07K0.
(blueprint: lem-sf-localized-signed-dual-presentation).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

attribute [local instance 10000] CategoryTheory.functorCategoryPreadditive
attribute [local instance 10000] SheafOfModules.instPreadditive
attribute [local instance 10000] HomologicalComplex.instPreadditive
attribute [local instance 10000] HomologicalComplex.instLinear
attribute [local instance 10000] CategoryTheory.Functor.preservesZeroMorphisms_of_additive
attribute [local irreducible] CategoryTheory.homComplexFunctor
attribute [local irreducible] CategoryTheory.scalarLocalizationCoefficientLinear
attribute [local instance 10000] CategoryTheory.RationalTermHom.coefficientCompose
attribute [local instance 10000] CategoryTheory.RationalTermHom.coefficientSheafify
attribute [local instance 10000] CategoryTheory.RationalTermHom.coefficientLocallyBijective
attribute [local instance 10000] CategoryTheory.RationalTermHom.coefficientZero
attribute [local instance 10000] CategoryTheory.RationalTermHom.coefficientAbelian

universe u v w z

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace CategoryTheory.LocalizedSignedDual

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})

/-- The existing module-sheaf category, in the universe of the small site.
Source: Stacks, Tag 0A8X (blueprint: lem-sf-localized-signed-dual-presentation). -/
abbrev Modules := ringedSiteModules.{u}
  ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

/-- Integer cochain complexes in the existing module-sheaf category.
Source: Stacks, Tag 0A8X (blueprint: lem-sf-localized-signed-dual-presentation). -/
abbrev Complex := CochainComplex (Modules R) ℤ

/-- The finite free sheaf with its specified number of generators, including zero.
Source: Stacks, Tag 08JI (blueprint: lem-sf-localized-signed-dual-presentation). -/
abbrev free (m : ℕ) : Modules R :=
  SheafOfModules.free (ULift.{u} (Fin m))

/-- The ordinary Hom dual, using the existing Hom complex and coefficient module.
Source: Stacks, Tag 0A8X (blueprint: lem-sf-localized-signed-dual-presentation). -/
abbrev dual (P : Complex R) : Complex R :=
  homComplex (R := R) P (RationalTermHom.single R (RationalTermHom.coefficients R))

/-- Hom into the given resolution, using the existing Hom-complex bifunctor.
Source: Stacks, Tag 08JI (blueprint: lem-sf-localized-signed-dual-presentation). -/
abbrev resolvedDual (P I : Complex R) : Complex R := homComplex (R := R) P I

/-- The surviving product projection, with its target transported from R[0]^0 to R.
Source: Stacks, Tag 0A8X (blueprint: lem-sf-localized-signed-dual-presentation). -/
def dualProjection (P : Complex R) (q : ℤ) :
    (dual R P).X q ⟶
      SheafOfModules.homObj (R := R) (P.X (-q)) (RationalTermHom.coefficients R) :=
  homComplexπ (R := R) P
    (RationalTermHom.single R (RationalTermHom.coefficients R)) q (-q) 0
      (neg_add_cancel q) ≫
    SheafOfModules.homObjMap.{u, u, u, u} (R := R) (𝟙 (P.X (-q)))
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (RationalTermHom.coefficients R)).hom

/-- The actual chain map given by postcomposition with j, without localization.
Source: Stacks, Tag 08JI (blueprint: lem-sf-localized-signed-dual-presentation). -/
def postcompose (P : Complex R) {I : Complex R}
    (j : RationalTermHom.single R (RationalTermHom.coefficients R) ⟶ I) :
    dual R P ⟶ resolvedDual R P I :=
  ((homComplexFunctor (R := R)).obj (op P)).map j

/-- Precomposition by a chain map, for the ordinary dual.
Source: Stacks, Tag 0A8X (blueprint: lem-sf-localized-signed-dual-presentation). -/
def dualMap {P P' : Complex R} (f : P' ⟶ P) : dual R P ⟶ dual R P' :=
  ((homComplexFunctor (R := R)).map f.op).app
    (RationalTermHom.single R (RationalTermHom.coefficients R))

/-- Precomposition by a chain map, for Hom into I.
Source: Stacks, Tag 0A8X (blueprint: lem-sf-localized-signed-dual-presentation). -/
def resolvedDualMap (I : Complex R) {P P' : Complex R} (f : P' ⟶ P) :
    resolvedDual R P I ⟶ resolvedDual R P' I :=
  ((homComplexFunctor (R := R)).map f.op).app I

private lemma localized_numerator {A : Type v} [CommRing A]
    {D : Type u} [Category D] [Preadditive D] [Linear A D] (t : A)
    {X Y : D} (f : (ScalarLocalization.localization A D t).obj X ⟶
      (ScalarLocalization.localization A D t).obj Y) :
    ∃ n : ℕ, ∃ g : X ⟶ Y,
      (ScalarLocalization.localization A D t).map g = t ^ n • f := by
  let l := TensorProduct.mk A (Localization.Away t) (X ⟶ Y) 1
  obtain ⟨⟨g, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers t) l f
  obtain ⟨n, hn⟩ := s.property
  refine ⟨n, g, ?_⟩
  change l g = t ^ n • f
  change (s : A) • f = l g at hs
  rw [← hn] at hs
  exact hs.symm

private lemma localized_kernel {A : Type v} [CommRing A]
    {D : Type u} [Category D] [Preadditive D] [Linear A D] (t : A)
    {X Y : D} (f : X ⟶ Y)
    (hf : (ScalarLocalization.localization A D t).map f = 0) :
    ∃ n : ℕ, t ^ n • f = 0 := by
  let l := TensorProduct.mk A (Localization.Away t) (X ⟶ Y) 1
  change l f = 0 at hf
  have hl : l f = l 0 := by rw [hf, map_zero]
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_iff_exists (Submonoid.powers t) l).1 hl
  obtain ⟨n, hn⟩ := s.property
  refine ⟨n, ?_⟩
  simpa only [Submonoid.smul_def, ← hn, smul_zero] using hs

private lemma scalarIso {B : Type*} [CommRing B] {D : Type*} [Category D]
    [Preadditive D] [Linear B D] {X Y : D} (e : X ≅ Y) (b : Bˣ) :
    ∃ e' : X ≅ Y, e'.hom = (b : B) • e.hom := by
  refine ⟨⟨(b : B) • e.hom, (↑(b⁻¹) : B) • e.inv, ?_, ?_⟩, rfl⟩
  all_goals simp [Linear.smul_comp, Linear.comp_smul, smul_smul]

private lemma localized_smul {A : Type v} [CommRing A]
    {D : Type u} [Category D] [Preadditive D] [Linear A D] (t : A)
    {X Y : ScalarLocalization A D t} (r : A) (f : X ⟶ Y) :
    algebraMap A (Localization.Away t) r • f = r • f := by
  let : IsScalarTower A (Localization.Away t) (X ⟶ Y) :=
    inferInstanceAs (IsScalarTower A (Localization.Away t)
      (TensorProduct A (Localization.Away t) (X.obj ⟶ Y.obj)))
  exact IsScalarTower.algebraMap_smul (Localization.Away t) r f

private lemma integral_bounded_lift {A : Type v} [CommRing A]
    {D : Type u} [Category D] [Preadditive D] [Linear A D] [HasZeroObject D]
    (t : A) (K : CochainComplex (ScalarLocalization A D t) ℤ) (a b : ℤ)
    (hK : ∀ q : ℤ, q < a ∨ b < q → IsZero (K.X q)) :
    ∃ P : CochainComplex D ℤ,
      (∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) ∧
      (∀ q : ℤ, a ≤ q → q ≤ b → P.X q = (K.X q).obj) ∧
      Nonempty (((ScalarLocalization.localization A D t).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P ≅ K) := by
  classical
  let Q := ScalarLocalization.localization A D t
  let X (q : ℤ) : D := if a ≤ q ∧ q ≤ b then (K.X q).obj else 0
  have hX (q : ℤ) (hq : q < a ∨ b < q) : IsZero (X q) := by
    dsimp only [X]
    rw [if_neg (by omega)]
    exact isZero_zero D
  let e (q : ℤ) : Q.obj (X q) ≅ K.X q :=
    if h : a ≤ q ∧ q ≤ b then eqToIso (by simp only [X, if_pos h]; rfl)
    else (Q.map_isZero (hX q (by omega))).iso (hK q (by omega))
  let g (q : ℤ) : Q.obj (X q) ⟶ Q.obj (X (q + 1)) :=
    (e q).hom ≫ K.d q (q + 1) ≫ (e (q + 1)).inv
  have hg (q : ℤ) : g q ≫ g (q + 1) = 0 := by
    simp only [g, Category.assoc, Iso.inv_hom_id_assoc,
      HomologicalComplex.d_comp_d_assoc, zero_comp, comp_zero]
  let S := Finset.Icc a (b - 1)
  have hgzero (q : ℤ) (hq : q ∉ S) : g q = 0 := by
    by_cases hqa : q < a
    · exact (Q.map_isZero (hX q (Or.inl hqa))).eq_of_src _ _
    · exact (Q.map_isZero (hX (q + 1) (Or.inr (by
        simp only [S, Finset.mem_Icc, not_and_or] at hq
        omega)))).eq_of_tgt _ _
  choose n f hf using (fun q : ℤ ↦ localized_numerator t (g q))
  let E := S.sup n
  let f' (q : ℤ) : X q ⟶ X (q + 1) :=
    if q ∈ S then t ^ (E - n q) • f q else 0
  have hf' (q : ℤ) : Q.map (f' q) = t ^ E • g q := by
    by_cases hq : q ∈ S
    · simp only [f', if_pos hq, Functor.map_smul,
        show Q.map (f q) = t ^ n q • g q from hf q, smul_smul, ← pow_add,
        Nat.sub_add_cancel (show n q ≤ E from Finset.le_sup hq)]
    · simp only [f', if_neg hq, Functor.map_zero, hgzero q hq, smul_zero]
  have hfzero (q : ℤ) (hq : q ∉ S) : f' q = 0 := by simp only [f', if_neg hq]
  have hcomp (q : ℤ) : Q.map (f' q ≫ f' (q + 1)) = 0 := by
    simp only [Functor.map_comp, hf', Linear.smul_comp, Linear.comp_smul, hg, smul_zero]
  choose n' hn' using (fun q : ℤ ↦ localized_kernel t (f' q ≫ f' (q + 1)) (hcomp q))
  let N := S.sup n'
  have hkill (q : ℤ) : t ^ N • (f' q ≫ f' (q + 1)) = 0 := by
    by_cases hq : q ∈ S
    · have hh := congrArg (fun f ↦ t ^ (N - n' q) • f) (hn' q)
      simpa only [smul_smul, ← pow_add, Nat.sub_add_cancel (show n' q ≤ N from Finset.le_sup hq),
        smul_zero] using hh
    · rw [hfzero q hq, zero_comp, smul_zero]
  let d (q : ℤ) := t ^ N • f' q
  have hd (q : ℤ) : d q ≫ d (q + 1) = 0 := by
    dsimp only [d]
    rw [Linear.smul_comp, Linear.comp_smul, hkill, smul_zero]
  let P := CochainComplex.of X d hd
  refine ⟨P, hX, ?_, ?_⟩
  · intro q hqa hqb
    exact if_pos ⟨hqa, hqb⟩
  · have hdQ (q : ℤ) : Q.map (P.d q (q + 1)) = t ^ (N + E) • g q := by
      change Q.map (CochainComplex.of.d X d q (q + 1)) = _
      rw [CochainComplex.of_d]
      rw [Functor.map_smul, hf', smul_smul, ← pow_add]
    let u : (Localization.Away t)ˣ :=
      (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away t) t).unit
    let k (q : ℤ) := (N + E) * (b - q).toNat
    let s (q : ℤ) := (scalarIso (e q) (u ^ k q)).choose
    have hs (q : ℤ) : (s q).hom =
        (algebraMap A (Localization.Away t) t) ^ k q • (e q).hom := by
      rw [(scalarIso (e q) (u ^ k q)).choose_spec]
      simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, u]
    refine ⟨HomologicalComplex.Hom.isoOfComponents s ?_⟩
    intro q r hqr
    have hr : r = q + 1 := hqr.symm
    subst r
    change (s q).hom ≫ K.d q (q + 1) = Q.map (P.d q (q + 1)) ≫ (s (q + 1)).hom
    by_cases hq : q ∈ S
    · have hk : k q = N + E + k (q + 1) := by
        dsimp only [k]
        have hb : q ≤ b - 1 := (Finset.mem_Icc.1 hq).2
        have hnat : (b - q).toNat = (b - (q + 1)).toNat + 1 := by omega
        rw [hnat, Nat.mul_add, Nat.mul_one, Nat.add_comm]
      rw [hs, hs, hdQ]
      simp only [g, Linear.comp_smul, Linear.smul_comp, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
      rw [← localized_smul t (t ^ (N + E))]
      simp only [map_pow, smul_smul, ← pow_add]
      rw [Nat.add_comm (k (q + 1)), ← hk]
    · have hgz := hgzero q hq
      have hkz : (e q).hom ≫ K.d q (q + 1) = 0 := by
        have hh := congrArg (fun f ↦ f ≫ (e (q + 1)).hom) hgz
        simpa only [g, Category.assoc, Iso.inv_hom_id, Category.comp_id, zero_comp] using hh
      rw [hdQ, hgz, smul_zero, zero_comp, hs, Linear.smul_comp, hkz, smul_zero]

/-- A bounded localized complex has an integral chain-isomorphic lift. Underlying
objects agree on the specified interval; outside it the integral terms are zero.
The final equation transports the given localized free retraction by that very
chain isomorphism, rather than lifting either retraction map.

Source: agent-written scalar extension of blueprint prop-sf-dualizable, using
Stacks algebra.tex, Tags 00DK, 07JZ and 07K0.
(blueprint: lem-sf-localized-signed-dual-presentation).

Proof: identify tensor Hom with fractions by lem-weil-pbc-localization-tensor and
 def-weil-pbc-module-localization-away. Clear the finitely many differential
 denominators with a common t^e. Each composite of successive numerators is zero
 after localization, hence killed by some t^N_r. Choose their finite maximum N
 (zero for an empty set), and use differential t^N f_r on the original terms
 inside [a,b], and zero objects outside. Successive composites are zero since
 t^(2N) kills every defect. Put h=e+N. The degree-r isomorphism to the original
 localized complex is t^(h(b-r)) on [a,b], and the unique zero-object isomorphism
 elsewhere. Its chain identity follows from h(b-r-1)+N=h(b-r)-e; its inverse is
 multiplication by t^(-h(b-r)). This includes a>b and a=b. Transport i,p along
 these inverse components; their composite is the identity. No torsion-freeness,
 regularity of t, or integral retraction is used. -/
theorem bounded_localized_complex_lift (A : Type v) [CommRing A]
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) (t : A) :
    (fun [_linear : Linear A (Modules R)] ↦
      ∀ (Pbar : CochainComplex (ScalarLocalization A (Modules R) t) ℤ) (a₀ b₀ : ℤ),
        (∀ q : ℤ, q < a₀ ∨ b₀ < q → IsZero (Pbar.X q)) →
        ∃ P : Complex R,
          (∀ q : ℤ, q < a₀ ∨ b₀ < q → IsZero (P.X q)) ∧
          (∀ q : ℤ, a₀ ≤ q → q ≤ b₀ → P.X q = (Pbar.X q).obj) ∧
          ∃ s : ((ScalarLocalization.localization A (Modules R) t).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P ≅ Pbar,
            ∀ (q : ℤ) (m : ℕ)
              (i : Pbar.X q ⟶ (ScalarLocalization.localization A (Modules R) t).obj (free R m))
              (p : (ScalarLocalization.localization A (Modules R) t).obj (free R m) ⟶ Pbar.X q),
              i ≫ p = 𝟙 _ →
                (s.hom.f q ≫ i) ≫ (p ≫ s.inv.f q) = 𝟙 _)
      (_linear := scalarLocalizationCoefficientLinear A R a) := by
  let := scalarLocalizationCoefficientLinear A R a
  intro Pbar a₀ b₀ hPbar
  obtain ⟨P, hP, hX, ⟨s⟩⟩ := integral_bounded_lift t Pbar a₀ b₀ hPbar
  refine ⟨P, hP, hX, s, ?_⟩
  intro q m i p hip
  calc
    (s.hom.f q ≫ i) ≫ (p ≫ s.inv.f q) = s.hom.f q ≫ (i ≫ p) ≫ s.inv.f q :=
      by simp only [Category.assoc]
    _ = s.hom.f q ≫ s.inv.f q := by rw [hip, Category.id_comp]
    _ = 𝟙 _ := by
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
        HomologicalComplex.congr_hom s.hom_inv_id q


/-- Canonical transport between the two presentations of zero morphisms in the raw
localized category, followed by its actual derived-category localization.
Source: Mathlib, HasZeroMorphisms.ext; Stacks, Tag 05RU
(blueprint: lem-sf-localized-signed-dual-presentation).
Zero morphisms are unique; this cast changes neither objects nor differentials. -/
def rawDerivedObject (A : Type v) [CommRing A] [Linear A (Modules R)] (t : A)
    [hAb : Abelian (ScalarLocalization A (Modules R) t)]
    [HasDerivedCategory.{z} (ScalarLocalization A (Modules R) t)]
    (K : CochainComplex (ScalarLocalization A (Modules R) t) ℤ) :
    DerivedCategory (ScalarLocalization A (Modules R) t) :=
  DerivedCategory.Q.obj
    (cast (congrArg (fun zeros : HasZeroMorphisms (ScalarLocalization A (Modules R) t) ↦
        @HomologicalComplex ℤ (ScalarLocalization A (Modules R) t) _ zeros
          (ComplexShape.up ℤ))
      (Subsingleton.elim
        (@Preadditive.preadditiveHasZeroMorphisms (ScalarLocalization A (Modules R) t) _
          (ScalarLocalization.preadditive A (Modules R) t))
        (@Preadditive.preadditiveHasZeroMorphisms (ScalarLocalization A (Modules R) t) _
          hAb.toPreadditive))) K)

private def castComplexIso {D : Type*} [Category D]
    (z₁ z₂ : HasZeroMorphisms D) (h : z₁ = z₂)
    {K L : @HomologicalComplex ℤ D _ z₁ (ComplexShape.up ℤ)} (e : K ≅ L) :
    cast (congrArg (fun z ↦ @HomologicalComplex ℤ D _ z (ComplexShape.up ℤ)) h) K ≅
      cast (congrArg (fun z ↦ @HomologicalComplex ℤ D _ z (ComplexShape.up ℤ)) h) L := by
  subst z₂
  exact e

/-- The same lift has isomorphic images in the derived category of the raw localized
category. The category and localization structures are explicit parameters, so the
conclusion applies to every implementation in the chosen universe.

Source: blueprint prop-sf-dualizable, agent-written strictification consequence.
(blueprint: lem-sf-localized-signed-dual-presentation).
Proof: apply bounded_localized_complex_lift, keeping its integral support and object
 equalities. Apply DerivedCategory.Q.mapIso to its chain isomorphism. Every functor
 preserves inverse identities, so this requires no assertion about the cohomology
 of a localized complex or any lifting of retractions. -/
theorem bounded_localized_complex_lift_derived (A : Type v) [CommRing A]
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) (t : A) :
    (fun [_linear : Linear A (Modules R)] ↦
      ∀ [_abelian : Abelian (ScalarLocalization A (Modules R) t)]
        [_derived : HasDerivedCategory.{z} (ScalarLocalization A (Modules R) t)]
        (Pbar : CochainComplex (ScalarLocalization A (Modules R) t) ℤ) (a₀ b₀ : ℤ),
        (∀ q : ℤ, q < a₀ ∨ b₀ < q → IsZero (Pbar.X q)) →
        ∃ P : Complex R,
          (∀ q : ℤ, q < a₀ ∨ b₀ < q → IsZero (P.X q)) ∧
          (∀ q : ℤ, a₀ ≤ q → q ≤ b₀ → P.X q = (Pbar.X q).obj) ∧
          Nonempty (rawDerivedObject R A t
            (((ScalarLocalization.localization A (Modules R) t).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≅ rawDerivedObject R A t Pbar))
      (_linear := scalarLocalizationCoefficientLinear A R a) := by
  let := scalarLocalizationCoefficientLinear A R a
  intro hAb hDer Pbar a₀ b₀ hPbar
  obtain ⟨P, hP, hX, s, _⟩ := bounded_localized_complex_lift R A a t Pbar a₀ b₀ hPbar
  refine ⟨P, hP, hX, ?_⟩
  exact ⟨DerivedCategory.Q.mapIso (castComplexIso _ _ (Subsingleton.elim _ _) s)⟩

/-- Postcomposition is an actual chain map and is contravariantly natural in P.
Source: Stacks, Tag 0A8X (blueprint: lem-sf-localized-signed-dual-presentation).
Proof: def-pur-hom-complex is a bifunctor. Its naturality identity for j and the
opposite of f is the displayed square. Componentwise both composites send a local
homogeneous map phi to j phi f; this also checks the chain-map interpretation. -/
theorem postcompose_natural {I : Complex R}
    (j : RationalTermHom.single R (RationalTermHom.coefficients R) ⟶ I)
    {P P' : Complex R} (f : P' ⟶ P) :
    dualMap R f ≫ postcompose R P' j = postcompose R P j ≫ resolvedDualMap R I f := by
  exact (((homComplexFunctor (R := R)).map f.op).naturality j).symm

private lemma isIso_dependent {D : Type*} [Category D] {X : D} {Y : ℤ → D}
    {k : ℤ} (π : ∀ q, k = q → (X ⟶ Y q)) {q : ℤ} (hq : k = q)
    (hi : IsIso (π k rfl)) : IsIso (π q hq) := by
  subst q
  exact hi

private lemma dualProjection_iso (P : Complex R) (q : ℤ) :
    IsIso (dualProjection R P q) := by
  let M := RationalTermHom.single R (RationalTermHom.coefficients R)
  let π := homComplexπ (R := R) P M
  have hc : IsLimit (Fan.mk ((dual R P).X q)
      (fun p : ℤ ↦ π q p (p + q) rfl)) :=
    homComplexIsLimit P M q
  have hz (p : ℤ) (hp : p ≠ -q) :
      IsZero (SheafOfModules.homObj (R := R) (P.X p) (M.X (p + q))) := by
    have ht : IsZero (M.X (p + q)) :=
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
        (RationalTermHom.coefficients R) (p + q) (by omega)
    apply (IsZero.iff_id_eq_zero _).2
    rw [← SheafOfModules.homObjMap_id.{u, u, u, u}, ht.eq_of_tgt (𝟙 _) 0]
    apply SheafOfModules.hom_ext
    ext X φ : 3
    rfl
  have hi : IsIso (π q (-q) (-q + q) rfl) :=
    RationalTermHom.soleFactorIsIso _ hc (-q) hz
  have hi' : IsIso (π q (-q) 0 (neg_add_cancel q)) :=
    isIso_dependent (fun n hn ↦ π q (-q) n hn) (neg_add_cancel q) hi
  let e := ((SheafOfModules.homFunctor.{u, u, u, u} R).obj (op (P.X (-q)))).mapIso
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (RationalTermHom.coefficients R))
  change IsIso (π q (-q) 0 (neg_add_cancel q) ≫ e.hom)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hi' e.isIso_hom

private lemma dualProjection_d (P : Complex R) (q : ℤ) :
    (dual R P).d q (q + 1) ≫ dualProjection R P (q + 1) =
      dualProjection R P q ≫ ((q + 1).negOnePow • SheafOfModules.homObjMap
        (P.d (-(q + 1)) (-q)) (𝟙 (RationalTermHom.coefficients R))) := by
  let M := RationalTermHom.single R (RationalTermHom.coefficients R)
  let s : M.X 0 ≅ RationalTermHom.coefficients R :=
    HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (RationalTermHom.coefficients R)
  have hd := homComplex_d_π (R := R) P M q (q + 1) (-(q + 1)) 0 (-1) (-q)
    rfl (by omega) (by omega) (by omega)
  change (((homComplexFunctor.{u, u, u, u} (R := R)).obj (op P)).obj M).d q (q + 1) ≫
    (homComplexπ (R := R) P M (q + 1) (-(q + 1)) 0 (neg_add_cancel _) ≫
      SheafOfModules.homObjMap.{u, u, u, u} (𝟙 _) s.hom) =
    (homComplexπ (R := R) P M q (-q) 0 (neg_add_cancel _) ≫
      SheafOfModules.homObjMap.{u, u, u, u} (𝟙 _) s.hom) ≫
      ((q + 1).negOnePow • SheafOfModules.homObjMap
        (P.d (-(q + 1)) (-q)) (𝟙 (RationalTermHom.coefficients R)))
  erw [← Category.assoc, hd]
  have hzero : SheafOfModules.homObjMap.{u, u, u, u} (R := R) (𝟙 (P.X (-(q + 1))))
      (M.d (-1) 0) = 0 := by
    change SheafOfModules.homObjMap.{u, u, u, u} (𝟙 _) (0 : M.X (-1) ⟶ M.X 0) = 0
    apply SheafOfModules.hom_ext
    ext X φ : 3
    rfl
  erw [hzero, comp_zero, zero_sub]
  simp only [Int.negOnePow_succ, Units.neg_smul,
    Preadditive.comp_neg, Linear.comp_units_smul, Category.assoc]
  have hcomm :
      SheafOfModules.homObjMap.{u, u, u, u} (R := R)
          (P.d (-(q + 1)) (-q)) (𝟙 (M.X 0)) ≫
        SheafOfModules.homObjMap.{u, u, u, u} (R := R) (𝟙 _) s.hom =
      SheafOfModules.homObjMap.{u, u, u, u} (R := R) (𝟙 (P.X (-q))) s.hom ≫
        SheafOfModules.homObjMap.{u, u, u, u} (R := R)
          (P.d (-(q + 1)) (-q)) (𝟙 _) := by
    exact (((SheafOfModules.homFunctor.{u, u, u, u} R).map
      (P.d (-(q + 1)) (-q)).op).naturality s.hom).symm
  exact congrArg (fun f ↦ -(q.negOnePow •
    (homComplexπ (R := R) P M q (-q) 0 (neg_add_cancel q) ≫ f))) hcomm

variable [HasDerivedCategory.{w} (Modules R)]

/-- The bounded signed ordinary dual presentation and the term comparisons. The
isomorphisms are normalized by the existing product projections. The ranks are a
family on all integers, equal to zero outside the original interval.

Source: Stacks, Tags 0A8X, 08JI, 08JJ, scalar-localized extension in the blueprint
prop-sf-dualizable. (blueprint: lem-sf-localized-signed-dual-presentation).

Proof: lem-sc-hom-complex-to-single identifies the Hom dual by its surviving product
projection with def-sc-signed-sheaf-dual-complex. The Hom differential becomes
-(-1)^q precomposition by d_P^(-q-1), equal to (-1)^(q+1) precomposition. A term
outside [-b,-a] has zero source, hence is zero. For each r in [a,b], apply
lem-sf-rational-term-hom-comparison to the given localized retraction, obtaining
invertibility of the normalized postcomposition comparison and a dual retraction
from the same free sheaf. Transport along the surviving projection for r=-q.
Outside the interval use the zero sheaf and rank zero; its unique maps supply the
same conclusions. The term-comparison lemma also gives normalized identifications,
naturality under module maps, and A[1/t]-linear extensions with their naturality
on all fractions. The independent postcompose_natural square supplies chain-map
naturality. None of these steps claims that the total localized postcomposition
map is invertible. -/
theorem localized_signed_dual_presentation (A : Type v) [CommRing A]
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) (t : A)
    (I : Complex R) [I.IsKInjective]
    (j : RationalTermHom.single R (RationalTermHom.coefficients R) ⟶ I) [QuasiIso j] :
    (fun [_linear : Linear A (Modules R)] ↦
      ∃ e : ∀ F : Modules R, RationalTermHom.ordinary R F ≅
          RationalTermHom.resolved R (RationalTermHom.single R
            (RationalTermHom.coefficients R)) F,
        RationalTermHom.IsNormalized R e ∧
        (∀ (F G : Modules R) (f : F ⟶ G),
          RationalTermHom.ordinaryMap R f ≫ RationalTermHom.comparison R e j F =
            RationalTermHom.comparison R e j G ≫ RationalTermHom.resolvedMap R I f) ∧
        (∀ (P : Complex R) (a₀ b₀ : ℤ) (m : ℤ → ℕ),
          (∀ r : ℤ, r < a₀ ∨ b₀ < r → IsZero (P.X r)) →
          (∀ r : ℤ, r < a₀ ∨ b₀ < r → m r = 0) →
          (∀ r : ℤ, a₀ ≤ r → r ≤ b₀ →
            ∃ i : RationalTermHom.localizedObject R A t (RationalTermHom.single R (P.X r)) ⟶
                RationalTermHom.localizedObject R A t (RationalTermHom.single R (free R (m r))),
              ∃ p : RationalTermHom.localizedObject R A t
                  (RationalTermHom.single R (free R (m r))) ⟶
                  RationalTermHom.localizedObject R A t (RationalTermHom.single R (P.X r)),
                i ≫ p = 𝟙 _) →
          Nonempty (DerivedCategory.Q.obj (dual R P) ≅
            DerivedCategory.Q.obj
              (signedSheafDualComplex (R := R) P (RationalTermHom.coefficients R))) ∧
          (∀ q : ℤ, IsIso (dualProjection R P q)) ∧
          (∀ q : ℤ, (dual R P).d q (q + 1) ≫ dualProjection R P (q + 1) =
            dualProjection R P q ≫
              ((q + 1).negOnePow • SheafOfModules.homObjMap
                (P.d (-(q + 1)) (-q)) (𝟙 (RationalTermHom.coefficients R)))) ∧
          (∀ q : ℤ, q < -b₀ ∨ -a₀ < q → IsZero ((dual R P).X q)) ∧
          (∀ q : ℤ,
            ∃ i : RationalTermHom.localizedObject R A t
                (RationalTermHom.single R ((dual R P).X q)) ⟶
                RationalTermHom.localizedObject R A t
                  (RationalTermHom.single R (free R (m (-q)))),
              ∃ p : RationalTermHom.localizedObject R A t
                  (RationalTermHom.single R (free R (m (-q)))) ⟶
                  RationalTermHom.localizedObject R A t
                    (RationalTermHom.single R ((dual R P).X q)),
                i ≫ p = 𝟙 _) ∧
          (∀ r : ℤ, IsIso (RationalTermHom.localizedMap R A t
            (RationalTermHom.comparison R e j (P.X r))))) ∧
        ∃ b : ∀ F G : Modules R,
            (RationalTermHom.localizedObject R A t (RationalTermHom.single R F) ⟶
              RationalTermHom.localizedObject R A t (RationalTermHom.single R G)) →ₗ[
                Localization.Away t]
              (RationalTermHom.localizedObject R A t (RationalTermHom.ordinary R G) ⟶
                RationalTermHom.localizedObject R A t (RationalTermHom.ordinary R F)),
          ∃ z : ∀ F G : Modules R,
              (RationalTermHom.localizedObject R A t (RationalTermHom.single R F) ⟶
                RationalTermHom.localizedObject R A t (RationalTermHom.single R G)) →ₗ[
                  Localization.Away t]
                (RationalTermHom.localizedObject R A t (RationalTermHom.resolved R I G) ⟶
                  RationalTermHom.localizedObject R A t (RationalTermHom.resolved R I F)),
            (∀ (F G : Modules R) (f : F ⟶ G),
              b F G (RationalTermHom.localizedMap R A t
                  ((CochainComplex.singleFunctor _ 0).map f)) =
                RationalTermHom.localizedMap R A t (RationalTermHom.ordinaryMap R f) ∧
              z F G (RationalTermHom.localizedMap R A t
                  ((CochainComplex.singleFunctor _ 0).map f)) =
                RationalTermHom.localizedMap R A t (RationalTermHom.resolvedMap R I f)) ∧
            (∀ (F G : Modules R)
              (f : RationalTermHom.localizedObject R A t (RationalTermHom.single R F) ⟶
                RationalTermHom.localizedObject R A t (RationalTermHom.single R G)),
              b F G f ≫ RationalTermHom.localizedMap R A t (RationalTermHom.comparison R e j F) =
                RationalTermHom.localizedMap R A t (RationalTermHom.comparison R e j G) ≫ z F G f))
      (_linear := scalarLocalizationCoefficientLinear A R a) := by
  let := scalarLocalizationCoefficientLinear A R a
  obtain ⟨e, he, hn, hr, b, z, hbz, hnz⟩ :=
    RationalTermHom.rational_term_hom_comparison R A a t I j
  refine ⟨e, he, hn, ?_, b, z, hbz, hnz⟩
  intro P a₀ b₀ m hP _hm hret
  have hret' (r : ℤ) :
      ∃ i : RationalTermHom.localizedObject R A t (RationalTermHom.single R (P.X r)) ⟶
          RationalTermHom.localizedObject R A t (RationalTermHom.single R (free R (m r))),
        ∃ p : RationalTermHom.localizedObject R A t
            (RationalTermHom.single R (free R (m r))) ⟶
            RationalTermHom.localizedObject R A t (RationalTermHom.single R (P.X r)),
          i ≫ p = 𝟙 _ := by
    by_cases h : a₀ ≤ r ∧ r ≤ b₀
    · exact hret r h.1 h.2
    · have hz := hP r (by omega)
      have hs := (CochainComplex.singleFunctor (Modules R) 0).map_isZero hz
      have hq := DerivedCategory.Q.map_isZero hs
      have hl := (ScalarLocalization.localization A (DerivedCategory (Modules R)) t).map_isZero hq
      exact ⟨0, 0, hl.eq_of_src _ _⟩
  have ht (r : ℤ) : IsIso (RationalTermHom.localizedMap R A t
      (RationalTermHom.comparison R e j (P.X r))) ∧
      ∃ i : RationalTermHom.localizedObject R A t (RationalTermHom.ordinary R (P.X r)) ⟶
          RationalTermHom.localizedObject R A t (RationalTermHom.single R (free R (m r))),
        ∃ p : RationalTermHom.localizedObject R A t
            (RationalTermHom.single R (free R (m r))) ⟶
            RationalTermHom.localizedObject R A t (RationalTermHom.ordinary R (P.X r)),
          i ≫ p = 𝟙 _ := by
    obtain ⟨i, p, hip⟩ := hret' r
    exact hr (P.X r) (m r) i p hip
  refine ⟨?_, dualProjection_iso R P, dualProjection_d R P, ?_, ?_, fun r ↦ (ht r).1⟩
  · exact ⟨DerivedCategory.Q.mapIso (homComplex_to_single_iso P
      (RationalTermHom.coefficients R)).some⟩
  · intro q hq
    have hz := ((SheafOfModules.homFunctor.{u, u, u, u} R).flip.obj
      (RationalTermHom.coefficients R)).map_isZero (hP (-q) (by omega)).op
    exact hz.of_iso
      (@asIso _ _ _ _ (dualProjection R P q) (dualProjection_iso R P q))
  · intro q
    obtain ⟨i, p, hip⟩ := (ht (-q)).2
    let s : RationalTermHom.localizedObject R A t
        (RationalTermHom.single R ((dual R P).X q)) ≅
        RationalTermHom.localizedObject R A t (RationalTermHom.ordinary R (P.X (-q))) :=
      (ScalarLocalization.localization A (DerivedCategory (Modules R)) t).mapIso
      (DerivedCategory.Q.mapIso ((CochainComplex.singleFunctor (Modules R) 0).mapIso
        (@asIso _ _ _ _ (dualProjection R P q) (dualProjection_iso R P q))))
    refine ⟨s.hom ≫ i, p ≫ s.inv, ?_⟩
    calc
      (s.hom ≫ i) ≫ (p ≫ s.inv) = s.hom ≫ (i ≫ p) ≫ s.inv := by
        simp only [Category.assoc]
      _ = s.hom ≫ s.inv := by rw [hip, Category.id_comp]
      _ = 𝟙 _ := s.hom_inv_id


end CategoryTheory.LocalizedSignedDual
