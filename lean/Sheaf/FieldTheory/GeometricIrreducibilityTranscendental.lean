/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q85
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Nontrivial
import WeilConjectures.FieldTheory.CommonExtensionFields
import Sheaf.FieldTheory.FieldExtensionGeometricallyIrreducible
import Sheaf.FieldTheory.SepClosedAlgebrasTensorIrreducible

/-!
# Geometric irreducibility and transcendental field extensions

Source: Stacks Project, Algebra, Tag 0G31
(`lemma-geometrically-irreducible-base-change-transcendental`), with the forward
implication iterated over a finite algebraically independent family.
(blueprint: lem-zl-geometric-irreducibility-transcendental).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace AlgebraicGeometry

private theorem spec_irreducible_of_injective
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) [IrreducibleSpace (PrimeSpectrum B)] :
    IrreducibleSpace (PrimeSpectrum A) := by
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at *
  have heq : nilradical A = (nilradical B).comap f := by
    ext x
    change IsNilpotent x ↔ IsNilpotent (f x)
    constructor
    · exact fun h ↦ h.map f
    · rintro ⟨n, hn⟩
      exact ⟨n, hf (by simpa only [map_pow, map_zero] using hn)⟩
  rw [heq]
  exact Ideal.IsPrime.comap f

private theorem spec_irreducible_localization
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] [Nontrivial B]
    [IrreducibleSpace (PrimeSpectrum A)] : IrreducibleSpace (PrimeSpectrum B) := by
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at *
  have heq : nilradical B = (nilradical A).map (algebraMap A B) := by
    simpa only [nilradical, Ideal.zero_eq_bot, Ideal.map_bot] using
      (IsLocalization.map_radical M B (⊥ : Ideal A)).symm
  rw [heq]
  apply IsLocalization.isPrime_of_isPrime_disjoint M B _ inferInstance
  rw [Set.disjoint_left]
  intro x hx hxnil
  have hu := IsLocalization.map_units B (⟨x, hx⟩ : M)
  obtain ⟨n, hn⟩ := (mem_nilradical.mp hxnil).map (algebraMap A B)
  exact (hu.pow n).ne_zero hn

open scoped TensorProduct in
private theorem geometricallyIrreducible_spec_iff_tensor
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] :
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k A))) ↔
      ∀ (E : Type u) [Field E] [Algebra k E],
        IrreducibleSpace (PrimeSpectrum (A ⊗[k] E)) := by
  rw [geometricallyIrreducible_iff,
    geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  exact forall_congr' fun E ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    (pullbackSpecIso k A E).hom.homeomorph.irreducibleSpace_iff

open scoped TensorProduct in
private theorem geometricallyIrreducible_tensor_large
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (h : GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k A))))
    (E : Type v) [Field E] [Algebra k E] :
    IrreducibleSpace (PrimeSpectrum (A ⊗[k] E)) := by
  let Ω := AlgebraicClosure k
  have hΩ : IrreducibleSpace (PrimeSpectrum (A ⊗[k] Ω)) :=
    (geometricallyIrreducible_spec_iff_tensor k A).mp h Ω
  have : IrreducibleSpace (PrimeSpectrum (Ω ⊗[k] A)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.comm k Ω A).toRingEquiv).irreducibleSpace_iff.mpr hΩ
  obtain ⟨M, _, _, i, j, _, _⟩ := Field.exists_common_extension k Ω E
  let : Algebra Ω M := i.toRingHom.toAlgebra
  have : IsScalarTower k Ω M := IsScalarTower.of_algebraMap_eq (fun x ↦ (i.commutes x).symm)
  have : IrreducibleSpace (Spec (.of (Ω ⊗[k] A))) :=
    ‹IrreducibleSpace (PrimeSpectrum (Ω ⊗[k] A))›
  have : IrreducibleSpace (PrimeSpectrum (M ⊗[Ω] (Ω ⊗[k] A))) :=
    IsSepClosed.irreducibleSpace_tensorProduct Ω M (Ω ⊗[k] A)
  have : IrreducibleSpace (PrimeSpectrum (M ⊗[k] A)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.TensorProduct.cancelBaseChange k Ω M M A).toRingEquiv).irreducibleSpace_iff.mp
        inferInstance
  let f : E ⊗[k] A →ₐ[k] M ⊗[k] A :=
    Algebra.TensorProduct.map j (AlgHom.id k A)
  have : IrreducibleSpace (PrimeSpectrum (E ⊗[k] A)) :=
    spec_irreducible_of_injective f.toRingHom
      (Module.Flat.rTensor_preserves_injective_linearMap j.toLinearMap j.injective)
  exact (PrimeSpectrum.homeomorphOfRingEquiv
    (Algebra.TensorProduct.comm k A E).toRingEquiv).irreducibleSpace_iff.mpr inferInstance

open scoped TensorProduct in
private theorem fraction_baseChange_irreducible
    {k K P Q F L E : Type*}
    [Field k] [Field K] [CommRing P] [CommRing Q] [Field F] [Field L] [Field E]
    [Algebra k K] [Algebra k P] [Algebra k Q] [Algebra K Q] [Algebra P Q]
    [IsScalarTower k K Q] [IsScalarTower k P Q] [Algebra P F]
    [IsFractionRing P F] [Algebra P L] [Algebra F L] [IsScalarTower P F L]
    [Algebra Q L] [IsScalarTower P Q L] [IsFractionRing Q L]
    [Algebra k F] [IsScalarTower k P F]
    [Algebra F E] [Algebra P E] [IsScalarTower P F E]
    [Algebra k E] [IsScalarTower k F E] [IsScalarTower k P E]
    [Algebra.IsPushout k K P Q]
    [IrreducibleSpace (PrimeSpectrum (K ⊗[k] E))] :
    IrreducibleSpace (PrimeSpectrum (L ⊗[F] E)) := by
  let S := Q ⊗[P] E
  let T := L ⊗[P] E
  let f : S →ₐ[P] T :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom P Q L) (AlgHom.id P E)
  let : Algebra S T := f.toRingHom.toAlgebra
  have : IsScalarTower Q S T := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    simp [f, RingHom.algebraMap_toAlgebra]
    rfl
  have : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors Q)) T := by
    apply IsLocalization.tensorProduct_tensorProduct P E (nonZeroDivisors Q) L
    ext x
    change f (1 ⊗ₜ[P] x) = 1 ⊗ₜ[P] x
    exact (Algebra.TensorProduct.map_tmul
      (IsScalarTower.toAlgHom P Q L) (AlgHom.id P E) 1 x).trans (by rw [map_one]; rfl)
  have : IrreducibleSpace (PrimeSpectrum S) :=
    (PrimeSpectrum.homeomorphOfRingEquiv
      (Algebra.IsPushout.cancelBaseChangeAlg k K P Q E).toRingEquiv).irreducibleSpace_iff.mpr
        inferInstance
  let e := IsLocalization.algebraTensorEquiv (nonZeroDivisors P) F L E
  have : Nontrivial (L ⊗[F] E) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain F L E
      (algebraMap F L).injective (algebraMap F E).injective
  have : Nontrivial T := e.symm.toEquiv.nontrivial
  have : IrreducibleSpace (PrimeSpectrum T) :=
    spec_irreducible_localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors Q))
  exact (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).irreducibleSpace_iff.mpr inferInstance

private theorem fraction_adjoin
    {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    {ι : Type*} {t : ι → Ω} (ht : AlgebraicIndependent F t) :
    let g : MvPolynomial ι F →ₐ[F] IntermediateField.adjoin F (Set.range t) :=
      ht.aevalEquivField.toAlgHom.comp
        (IsScalarTower.toAlgHom F (MvPolynomial ι F) (FractionRing (MvPolynomial ι F)))
    let : Algebra (MvPolynomial ι F) (IntermediateField.adjoin F (Set.range t)) :=
      g.toRingHom.toAlgebra
    IsFractionRing (MvPolynomial ι F) (IntermediateField.adjoin F (Set.range t)) := by
  dsimp only
  let e := ht.aevalEquivField
  let g := e.toAlgHom.comp
    (IsScalarTower.toAlgHom F (MvPolynomial ι F) (FractionRing (MvPolynomial ι F)))
  let : Algebra (MvPolynomial ι F) (IntermediateField.adjoin F (Set.range t)) :=
    g.toRingHom.toAlgebra
  let e' : FractionRing (MvPolynomial ι F) ≃ₐ[MvPolynomial ι F]
      IntermediateField.adjoin F (Set.range t) :=
    { e.toRingEquiv with commutes' := fun _ ↦ rfl }
  exact IsFractionRing.of_algEquiv e'

/-- Geometric irreducibility ascends after adjoining the same finite algebraically
independent family to the two fields, and descends after adjoining one indeterminate.
The finite family lives in an arbitrary common extension `Ω`. Its generated intermediate
fields are `k(t₁, …, tᵣ)` and `K(t₁, …, tᵣ)`; their displayed map is the inclusion, with
scalar restriction identifying the two copies of the common ambient field. In the
converse, the rational-function map applies `algebraMap k K` to coefficients and fixes
its indeterminate. No separability, finite generation or positive cardinality is assumed.

Source: Stacks Project, Algebra, Tag 0G31
(`lemma-geometrically-irreducible-base-change-transcendental`).
(blueprint: lem-zl-geometric-irreducibility-transcendental).

Proof:
1. Use the affine pullback formula to express geometric irreducibility as irreducibility
   of all tensor spectra. Irreducibility descends along an injective ring homomorphism,
   since its inverse image of the nilradical is the nilradical. A nonzero localization
   of a ring with prime nilradical again has prime nilradical: localization commutes
   with radicals, and a denominator cannot be nilpotent in the nonzero localization.
2. The tensor criterion also holds for test fields in larger universes. First tensor
   with the algebraic closure of the base field. Embed that closure and the test field
   in a common field. The tensor-irreducibility theorem over a separably closed field
   applies; tensor reassociation and injectivity of scalar extension descend the result
   to the original test field.
3. For ascent put P = k[t₁, …, tᵣ], Q = K[t₁, …, tᵣ], F = k(t₁, …, tᵣ) and
   L = K(t₁, …, tᵣ). Algebraic independence identifies the generated fields with the
   fraction fields of P and Q, compatibly with the displayed inclusion. Polynomial
   scalar extension is a pushout, so Q ⊗[P] E is K ⊗[k] E for every field E/F.
   Localizing Q gives L ⊗[P] E, which is nonzero because it is also L ⊗[F] E.
   Step 1 preserves irreducibility under this localization. This proves the whole
   finite-family assertion at once, including r = 0.
4. For descent, every rational function over k which is not constant is transcendental
   over k. Thus k is algebraically closed in k(t), and the algebraically-closed-subfield
   criterion makes k(t)/k geometrically irreducible. Compose it with the given
   geometric irreducibility of K(t)/k(t). For every E/k, the injection K → K(t)
   stays injective after tensoring with E, and step 1 descends irreducibility to
   K ⊗[k] E. The tensor criterion proves geometric irreducibility of K/k.
-/
theorem geometricallyIrreducible_transcendental_extension
    {k K : Type u} [Field k] [Field K] [Algebra k K] :
    (GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k K))) →
      ∀ (Ω : Type (max u v)) [Field Ω] [Algebra k Ω] [Algebra K Ω] [IsScalarTower k K Ω]
        (r : ℕ) (t : Fin r → Ω), AlgebraicIndependent K t →
        GeometricallyIrreducible (Spec.map (CommRingCat.ofHom
          (IntermediateField.inclusion
            (IntermediateField.adjoin_le_iff.mpr
              (IntermediateField.subset_adjoin K (Set.range t))) :
            IntermediateField.adjoin k (Set.range t) →ₐ[k]
              (IntermediateField.adjoin K (Set.range t)).restrictScalars k).toRingHom))) ∧
    (GeometricallyIrreducible (Spec.map (CommRingCat.ofHom
        (RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap k K))
          (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
            (Polynomial.map_injective _ (algebraMap k K).injective))))) →
      GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
  by
  constructor
  · intro h Ω _ _ _ _ r t ht
    let P := MvPolynomial (Fin r) k
    let Q := MvPolynomial (Fin r) K
    let F := IntermediateField.adjoin k (Set.range t)
    let L := IntermediateField.adjoin K (Set.range t)
    have ht' : AlgebraicIndependent k t :=
      ht.restrictScalars (algebraMap k K).injective
    let g : P →ₐ[k] F := ht'.aevalEquivField.toAlgHom.comp
      (IsScalarTower.toAlgHom k P (FractionRing P))
    let q : Q →ₐ[K] L := ht.aevalEquivField.toAlgHom.comp
      (IsScalarTower.toAlgHom K Q (FractionRing Q))
    let : Algebra P F := g.toRingHom.toAlgebra
    let : Algebra Q L := q.toRingHom.toAlgebra
    have : IsFractionRing P F := fraction_adjoin ht'
    have : IsFractionRing Q L := fraction_adjoin ht
    let : Algebra P Q := MvPolynomial.algebraMvPolynomial
    have : IsScalarTower k P Q := inferInstance
    have : IsScalarTower k P F :=
      IsScalarTower.of_algebraMap_eq (fun x ↦ (g.commutes x).symm)
    have : IsScalarTower K Q L :=
      IsScalarTower.of_algebraMap_eq (fun x ↦ (q.commutes x).symm)
    have : IsScalarTower k Q L := IsScalarTower.to₁₃₄ k K Q L
    let ι : F →ₐ[k] L.restrictScalars k := IntermediateField.inclusion
      (IntermediateField.adjoin_le_iff.mpr
        (IntermediateField.subset_adjoin K (Set.range t)))
    let : Algebra F L := ι.toRingHom.toAlgebra
    have : IsScalarTower k F L :=
      IsScalarTower.of_algebraMap_eq (fun x ↦ (ι.commutes x).symm)
    let : Algebra P L := (algebraMap Q L).comp (algebraMap P Q) |>.toAlgebra
    have : IsScalarTower P Q L := IsScalarTower.of_algebraMap_eq' rfl
    have hg (p : P) : (g p : Ω) = MvPolynomial.aeval t p :=
      ht'.aevalEquivField_algebraMap_apply_coe p
    have hq (p : Q) : (q p : Ω) = MvPolynomial.aeval t p :=
      ht.aevalEquivField_algebraMap_apply_coe p
    have : IsScalarTower P F L := by
      apply IsScalarTower.of_algebraMap_eq'
      ext i
      · change (q (MvPolynomial.map (algebraMap k K) (MvPolynomial.C i)) : Ω) =
          (g (MvPolynomial.C i) : Ω)
        rw [hq, hg]
        simp [IsScalarTower.algebraMap_apply k K Ω]
      · change (q (MvPolynomial.map (algebraMap k K) (MvPolynomial.X i)) : Ω) =
          (g (MvPolynomial.X i) : Ω)
        rw [hq, hg]
        simp
    change GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap F L)))
    rw [geometricallyIrreducible_spec_iff_tensor]
    intro E _ _
    let : Algebra P E := ((algebraMap F E).comp (algebraMap P F)).toAlgebra
    let : Algebra k E := ((algebraMap F E).comp (algebraMap k F)).toAlgebra
    have : IsScalarTower P F E := IsScalarTower.of_algebraMap_eq' rfl
    have : IsScalarTower k F E := IsScalarTower.of_algebraMap_eq' rfl
    have : IsScalarTower k P E := IsScalarTower.to₁₂₄ k P F E
    have : Algebra.IsPushout k K P Q := inferInstance
    have : IrreducibleSpace (PrimeSpectrum (TensorProduct k K E)) :=
      geometricallyIrreducible_tensor_large k K h E
    exact fraction_baseChange_irreducible (k := k) (K := K) (P := P) (Q := Q)
  · intro h
    let f := RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap k K))
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (Polynomial.map_injective _ (algebraMap k K).injective))
    let : Algebra (RatFunc k) (RatFunc K) := f.toAlgebra
    have hk : GeometricallyIrreducible
        (Spec.map (CommRingCat.ofHom (algebraMap k (RatFunc k)))) := by
      apply geometricallyIrreducible_of_isAlgebraic_mem
      intro x hx
      have hc : ∃ c, x = RatFunc.C c := by
        by_contra! hc
        exact x.transcendental_of_ne_C (by simpa using hc) hx
      obtain ⟨c, hc⟩ := hc
      exact ⟨c, hc.symm⟩
    have : GeometricallyIrreducible
        (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) (RatFunc K)))) := h
    have : IsScalarTower k (RatFunc k) (RatFunc K) := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      change algebraMap k (RatFunc K) x = f (algebraMap k (RatFunc k) x)
      exact ((RatFunc.mapAlgHom (Polynomial.mapAlgHom (Algebra.ofId k K))
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
          (Polynomial.map_injective _ (algebraMap k K).injective))).commutes x).symm
    have hcomp := GeometricallyIrreducible.comp
      (Spec.map (CommRingCat.ofHom (algebraMap (RatFunc k) (RatFunc K))))
      (Spec.map (CommRingCat.ofHom (algebraMap k (RatFunc k))))
    have hL : GeometricallyIrreducible
        (Spec.map (CommRingCat.ofHom (algebraMap k (RatFunc K)))) := by
      convert hcomp using 1
      rw [← Spec.map_comp]
      congr 1
      exact congrArg CommRingCat.ofHom (IsScalarTower.algebraMap_eq k (RatFunc k) (RatFunc K))
    rw [geometricallyIrreducible_spec_iff_tensor]
    intro E _ _
    have : IrreducibleSpace (PrimeSpectrum (TensorProduct k (RatFunc K) E)) :=
      (geometricallyIrreducible_spec_iff_tensor k (RatFunc K)).mp hL E
    let j := IsScalarTower.toAlgHom k K (RatFunc K)
    exact spec_irreducible_of_injective
      (Algebra.TensorProduct.map j (AlgHom.id k E)).toRingHom
      (Module.Flat.rTensor_preserves_injective_linearMap j.toLinearMap j.injective)

end AlgebraicGeometry
