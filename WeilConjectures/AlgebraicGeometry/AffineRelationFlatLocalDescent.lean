/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.EquationalCriterion
import WeilConjectures.RingTheory.FinitePresentationAndFlatOfFiniteFreeStandardCover
import WeilConjectures.Mathlib.RingTheory.Finiteness.Descent
import WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover

/-!
# Flat-local descent for an affine relation

Source: Stacks Project, groupoids.tex, Tag 03BM, proposition-finite-flat-equivalence,
second proof paragraph; algebra.tex, Tags 03C4 and 00NX
(blueprint: lem-a1-affine-relation-flat-local-descent).
-/

@[expose] public section

universe u v

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The comparison sends `a ⊗ a'` to `σ(a) * τ(a')`.
Source: Stacks Project, Tag 03BM, comparison in proposition-finite-flat-equivalence
(blueprint: lem-a1-affine-relation-flat-local-descent). -/
def affineRelationTensorComparison
    {C A B : Type u} [CommRing C] [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B] (σ τ : A →ₐ[C] B) : A ⊗[C] A →ₐ[C] B :=
  Algebra.TensorProduct.lift σ τ (fun a a' => Commute.all (σ a) (τ a'))

/-- Bijectivity descends from faithful-flat extensions of every prime localization.
Source: Stacks Project, Tags 03C4 and 00HN, as used in Tag 03BM
(blueprint: lem-a1-affine-relation-flat-local-descent). -/
private theorem bijective_of_local_faithful_baseChange
    {R M N : Type u} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N)
    (D : PrimeSpectrum R → Type v) [∀ p, CommRing (D p)]
    [∀ p, Algebra (Localization.AtPrime p.asIdeal) (D p)]
    [∀ p, Algebra R (D p)]
    [∀ p, IsScalarTower R (Localization.AtPrime p.asIdeal) (D p)]
    (hfaithful : ∀ p, Module.FaithfullyFlat (Localization.AtPrime p.asIdeal) (D p))
    (h : ∀ p, Function.Bijective (f.baseChange (D p))) : Function.Bijective f := by
  apply bijective_of_isLocalized_maximal
    (fun P _ ↦ Localization.AtPrime P ⊗[R] M)
    (fun P _ ↦ TensorProduct.mk R (Localization.AtPrime P) M 1)
    (fun P _ ↦ Localization.AtPrime P ⊗[R] N)
    (fun P _ ↦ TensorProduct.mk R (Localization.AtPrime P) N 1) f
  intro P hP
  let p : PrimeSpectrum R := ⟨P, hP.isPrime⟩
  let : Algebra (Localization.AtPrime P) (D p) :=
    inferInstanceAs (Algebra (Localization.AtPrime p.asIdeal) (D p))
  have : IsScalarTower R (Localization.AtPrime P) (D p) :=
    inferInstanceAs (IsScalarTower R (Localization.AtPrime p.asIdeal) (D p))
  have : Module.FaithfullyFlat (Localization.AtPrime P) (D p) := hfaithful p
  have hd : Function.Bijective ((f.baseChange (Localization.AtPrime P)).baseChange (D p)) := by
    rw [LinearMap.baseChange_baseChange]
    exact (TensorProduct.AlgebraTensorModule.cancelBaseChange
      R (Localization.AtPrime P) (D p) (D p) N).symm.bijective.comp
        ((h p).comp (TensorProduct.AlgebraTensorModule.cancelBaseChange
          R (Localization.AtPrime P) (D p) (D p) M).bijective)
  have hs : Function.Bijective (f.baseChange (Localization.AtPrime P)) :=
    (Module.FaithfullyFlat.lTensor_bijective_iff_bijective
      (Localization.AtPrime P) (D p) _).mp hd
  have heq : IsLocalizedModule.map P.primeCompl
      (TensorProduct.mk R (Localization.AtPrime P) M 1)
      (TensorProduct.mk R (Localization.AtPrime P) N 1) f =
      (f.baseChange (Localization.AtPrime P)).restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext P.primeCompl
      (TensorProduct.mk R (Localization.AtPrime P) M 1)
      (TensorProduct.mk R (Localization.AtPrime P) N 1)
    rw [IsLocalizedModule.map_comp]
    rfl
  rw [heq]
  exact hs

/-- Flatness descends from faithful-flat extensions of every prime localization.
Source: Stacks Project, Tags 03C4 and 00HT, as used in Tag 03BM
(blueprint: lem-a1-affine-relation-flat-local-descent). -/
private theorem flat_of_local_faithful_baseChange
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (D : PrimeSpectrum R → Type v) [∀ p, CommRing (D p)]
    [∀ p, Algebra (Localization.AtPrime p.asIdeal) (D p)]
    [∀ p, Algebra R (D p)]
    [∀ p, IsScalarTower R (Localization.AtPrime p.asIdeal) (D p)]
    (hfaithful : ∀ p, Module.FaithfullyFlat (Localization.AtPrime p.asIdeal) (D p))
    (h : ∀ p, Module.Flat (D p) (D p ⊗[R] M)) : Module.Flat R M := by
  apply Module.flat_of_isLocalized_maximal R M
    (fun P _ ↦ Localization.AtPrime P ⊗[R] M)
    (fun P _ ↦ TensorProduct.mk R (Localization.AtPrime P) M 1)
  intro P hP
  let p : PrimeSpectrum R := ⟨P, hP.isPrime⟩
  let : Algebra (Localization.AtPrime P) (D p) :=
    inferInstanceAs (Algebra (Localization.AtPrime p.asIdeal) (D p))
  have : IsScalarTower R (Localization.AtPrime P) (D p) :=
    inferInstanceAs (IsScalarTower R (Localization.AtPrime p.asIdeal) (D p))
  have : Module.FaithfullyFlat (Localization.AtPrime P) (D p) := hfaithful p
  have := h p
  have : Module.Flat (D p) (D p ⊗[Localization.AtPrime P]
      (Localization.AtPrime P ⊗[R] M)) :=
    Module.Flat.of_linearEquiv (TensorProduct.AlgebraTensorModule.cancelBaseChange
      R (Localization.AtPrime P) (D p) (D p) M)
  have : Module.Flat (Localization.AtPrime P) (Localization.AtPrime P ⊗[R] M) :=
    Module.Flat.of_flat_tensorProduct _ _ (D p)
  exact (Module.flat_iff_of_isLocalization (Localization.AtPrime P) P.primeCompl
    (Localization.AtPrime P ⊗[R] M)).mp this

/-- Descent of the tensor comparison and finite local freeness.
Source: Stacks Project, groupoids.tex, Tag 03BM, second proof paragraph; algebra.tex,
Tags 03C4 (2), 00EO and 00NX
(blueprint: lem-a1-affine-relation-flat-local-descent).

The `A`-algebra structure on `B` is σ; the scalar tower says that σ agrees with τ on C.
The base-changed comparison is expressed on `(A ⊗[C] A) ⊗[C] D`, canonically identified
with `(A ⊗[C] D) ⊗[D] (A ⊗[C] D)`. We use `D ⊗[C] A` for its finite-free module,
via tensor symmetry. The inverse image of an affine open `Spec T` is identified with
`Spec (T ⊗[C] A)` over both `Spec A` and `Spec T`, i.e. by the affine fibre-product formula.
Localized modules express the localizations by powers in the statement.

Proof plan:
1. Tensor universal properties identify localization with tensoring by C_p, and identify
   the base change of the comparison with the displayed tensor-square comparison. On
   generators the comparison sends `(a ⊗ a') ⊗ d` to `σ(a)τ(a') ⊗ d`; the inverse scalar
   identification multiplies the two D-coefficients (def-weil-pbc-module-tensor-product,
   def-weil-pbc-module-localization).
2. Faithful flatness reflects injectivity and surjectivity of the comparison over C_p.
   Apply lem-weil-pbc-linear-map-bijective-at-maximal-localizations to get global bijectivity;
   its inverse respects the ring operations by injectivity.
3. Finite free modules are flat (lem-sc-affine-standard-cover-finite-free-local-fp-flat).
   Descend flatness along each C_p -> D_p
   (lem-weil-pbc-flatness-descends-faithfully-flat), then use
   lem-pc-affine-sections-flat-over-base with both rings equal to C. Surjectivity on spectra
   gives faithful flatness (lem-weil-pbc-flat-surjective-spectrum-faithfully-flat).
4. The given standard cover makes B finitely presented over A through σ
   (lem-sc-affine-standard-cover-finite-presentation-flat). The comparison identifies it
   with A ⊗[C] A with the first-factor action. Descend module finite presentation along
   C -> A (lem-trf-finite-presentation-module-descent-flat-local).
5. Finitely presented flat modules are projective
   (lem-weil-pbc-finitely-presented-flat-module-projective). Split a finite free surjection
   using def-weil-pbc-projective-module; the maps x -> (x - s(p(x)), p(x)) and
   (k,a) -> k + s(a) give the direct-summand decomposition. Apply
   lem-weil-pbc-finite-projective-standard-free-cover.
6. Over D(g_i), the affine fibre-product formula identifies q with the spectrum of the
   localized finite free algebra (lem-weil-pbc-fibre-product-affine-spectra,
   lem-weil-pbc-finite-free-algebra-spectrum). Finiteness is local on the target
   (lem-weil-pbc-finite-local-on-target), flatness follows from the affine ring criterion
   (lem-weil-pbc-flat-ring-map-iff-flat-affine), and the local finite-presentation charts
   are also charts for q (def-sbc-locally-finite-presentation). These give
   def-pc-finite-locally-free; surjectivity was assumed.
7. For every affine open Spec T, affine base change gives its inverse image as
   Spec (T ⊗[C] A). Tensoring the finite C-generators of A with 1 gives finite T-generators.
8. Apply Spec contravariantly to the comparison isomorphism and use the affine
   fibre-product formula. The two inclusion maps followed by the comparison are σ and τ,
   so the two projections are precisely Spec σ and Spec τ. -/
theorem affineRelation_flat_local_descent
    (C A B : Type u) [CommRing C] [CommRing A] [CommRing B]
    [Algebra C A] [Algebra A B] [Algebra C B] [IsScalarTower C A B]
    (τ : A →ₐ[C] B)
    (hinj : Function.Injective (algebraMap C A))
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap C A)))
    {n : ℕ} (f : Fin n → A) (hspan : Ideal.span (Set.range f) = ⊤)
    (hfree : ∀ i : Fin n,
      Module.Finite (Localization.Away (f i)) (LocalizedModule.Away (f i) B) ∧
      Module.Free (Localization.Away (f i)) (LocalizedModule.Away (f i) B))
    (D : PrimeSpectrum C → Type v) [∀ p, CommRing (D p)]
    [∀ p, Algebra (Localization.AtPrime p.asIdeal) (D p)]
    [∀ p, Algebra C (D p)]
    [∀ p, IsScalarTower C (Localization.AtPrime p.asIdeal) (D p)]
    (hfaithful : ∀ p, Module.FaithfullyFlat (Localization.AtPrime p.asIdeal) (D p))
    (hlocal : ∀ p, Module.Finite (D p) ((D p) ⊗[C] A) ∧
      Module.Free (D p) ((D p) ⊗[C] A) ∧
      Function.Bijective (Algebra.TensorProduct.map
        (affineRelationTensorComparison (IsScalarTower.toAlgHom C A B) τ)
        (AlgHom.id C (D p)))) :
    Function.Bijective (affineRelationTensorComparison (IsScalarTower.toAlgHom C A B) τ) ∧
    Module.Flat C A ∧ Module.FaithfullyFlat C A ∧ Module.FinitePresentation C A ∧
    (∃ (r : ℕ) (i : A →ₗ[C] (Fin r → C)) (p : (Fin r → C) →ₗ[C] A),
      p.comp i = LinearMap.id) ∧
    (∃ (l : ℕ) (g : Fin l → C), Ideal.span (Set.range g) = ⊤ ∧
      ∀ i : Fin l,
        Module.Finite (Localization.Away (g i)) (LocalizedModule.Away (g i) A) ∧
        Module.Free (Localization.Away (g i)) (LocalizedModule.Away (g i) A)) ∧
    (Spec.map (CommRingCat.ofHom (algebraMap C A))).IsFiniteLocallyFree ∧
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap C A))) ∧
    (∀ (T : Type u) [CommRing T] [Algebra C T],
      IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap C T))) →
      (∃ e : pullback (Spec.map (CommRingCat.ofHom (algebraMap C A)))
          (Spec.map (CommRingCat.ofHom (algebraMap C T))) ≅
            Spec (CommRingCat.of (T ⊗[C] A)),
        e.hom ≫ Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : A →ₐ[C] T ⊗[C] A).toRingHom) =
          pullback.fst _ _ ∧
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap T (T ⊗[C] A))) =
          pullback.snd _ _) ∧
      Module.Finite T (T ⊗[C] A)) ∧
    (∃ e : Spec (CommRingCat.of B) ≅
        pullback (Spec.map (CommRingCat.ofHom (algebraMap C A)))
          (Spec.map (CommRingCat.ofHom (algebraMap C A))),
      e.hom ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (algebraMap A B)) ∧
      e.hom ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom τ.toRingHom)) := by
  classical
  have _ := hinj
  let φ := affineRelationTensorComparison (IsScalarTower.toAlgHom C A B) τ
  have hφ : Function.Bijective φ := by
    apply bijective_of_local_faithful_baseChange φ.toLinearMap D hfaithful
    intro p
    have heq : (φ.toLinearMap.baseChange (D p)).restrictScalars C =
        (TensorProduct.comm C B (D p)).toLinearMap.comp
          ((Algebra.TensorProduct.map φ (AlgHom.id C (D p))).toLinearMap.comp
            (TensorProduct.comm C (D p) (A ⊗[C] A)).toLinearMap) := by
      ext d x
      rfl
    change Function.Bijective ((φ.toLinearMap.baseChange (D p)).restrictScalars C)
    rw [heq]
    exact (TensorProduct.comm C B (D p)).bijective.comp
      ((hlocal p).2.2.comp (TensorProduct.comm C (D p) (A ⊗[C] A)).bijective)
  have hflat : Module.Flat C A := by
    apply flat_of_local_faithful_baseChange D hfaithful
    intro p
    have := (hlocal p).2.1
    infer_instance
  have hff : Module.FaithfullyFlat C A := Module.FaithfullyFlat.of_comap_surjective hsurj
  have hfpB : Module.FinitePresentation A B :=
    (Module.finitePresentation_and_flat_of_finite_free_standard_cover f hspan hfree).1
  let ψ : (A ⊗[C] A) →ₐ[A] B :=
    { φ.toRingHom with
      commutes' := by
        intro a
        simp [φ, affineRelationTensorComparison, Algebra.TensorProduct.algebraMap_apply] }
  let eφ := AlgEquiv.ofBijective ψ hφ
  have : Module.FinitePresentation A (A ⊗[C] A) :=
    Module.FinitePresentation.of_equiv eφ.symm.toLinearEquiv
  have hfp : Module.FinitePresentation C A :=
    Module.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
      (B := A)
  have : Module.Projective C A := Module.Flat.projective_of_finitePresentation
  obtain ⟨r, p, i, _, _, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective C A
  have hcover := Module.exists_standardFreeCover_of_finite_projective C A
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap C A))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap C A))) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap C A))) := by
    rw [LocallyOfFinitePresentation.SpecMap_iff]
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance
  refine ⟨hφ, hflat, hff, hfp, ⟨r, i, p, hpi⟩, hcover, ⟨⟩, ⟨hsurj⟩, ?_, ?_⟩
  · intro T _ _ _
    refine ⟨?_, inferInstance⟩
    refine ⟨pullbackSymmetry _ _ ≪≫ pullbackSpecIso C T A, ?_, ?_⟩
    · simp
    · simp [pullbackSpecIso_hom_fst']
  · let e : Spec (CommRingCat.of B) ≅ Spec (CommRingCat.of (A ⊗[C] A)) :=
      Scheme.Spec.mapIso eφ.toRingEquiv.toCommRingCatIso.op
    refine ⟨e ≪≫ (pullbackSpecIso C A A).symm, ?_, ?_⟩
    · change e.hom ≫ (pullbackSpecIso C A A).inv ≫ pullback.fst _ _ = _
      rw [pullbackSpecIso_inv_fst]
      change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map _ = _
      rw [← Spec.map_comp]
      congr 1
      ext a
      simp [φ, affineRelationTensorComparison]
    · change e.hom ≫ (pullbackSpecIso C A A).inv ≫ pullback.snd _ _ = _
      rw [pullbackSpecIso_inv_snd]
      change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map _ = _
      rw [← Spec.map_comp]
      congr 1
      ext a
      simp [φ, affineRelationTensorComparison]

end AlgebraicGeometry
