module


public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.FinitePresentation
import Sheaf.RingTheory.UniquePrimeLocalization


/-!
# Finite local-ring map at a singleton fibre of a finite morphism

Source: literature/stacks-project/more-morphisms.tex, Tag 05B8,
lemma-finite-morphism-single-point-in-fibre, parts (2) and (3)
(blueprint: lem-trf-finite-singleton-fibre-stalk-ring).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

private theorem localization_at_unique_prime
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    (P : Ideal A) [P.IsPrime] (Q : Ideal B) [Q.IsPrime]
    (he : Ideal.comap (algebraMap A B) Q = P)
    (hu : ∀ Q' : Ideal B, Q'.IsPrime →
      Ideal.comap (algebraMap A B) Q' = P → Q' = Q) :
    IsLocalization (P.primeCompl.map (algebraMap A B)) (Localization.AtPrime Q) := by
  exact IsLocalization.isLocalization_of_algEquiv _
    (AlgEquiv.ofBijective (IsLocalization.uniquePrimeLocalizationMap P Q he)
      (IsLocalization.uniquePrimeLocalization.{u, u, u} P Q he hu).1)

/--
For a finite morphism with a singleton fibre, the induced local-ring map is finite;
if the morphism is locally of finite presentation, it is finitely presented.

Source: literature/stacks-project/more-morphisms.tex, Tag 05B8,
lemma-finite-morphism-single-point-in-fibre, parts (2) and (3)
(blueprint: lem-trf-finite-singleton-fibre-stalk-ring).

Proof steps:
1. Choose affine neighbourhoods of the image point and its preimage. The finite morphism
   becomes a finite ring map, and the singleton fibre gives a unique prime over the base prime.
   The affine stalk-localization comparison and the unique-prime localization statement identify
   the stalk map with the localized ring map. Localization preserves finite ring maps.
2. Under local finite presentation, the affine ring map is finitely presented. Localization
   preserves finite presentation, and the same stalk identifications give the displayed
   polynomial presentation.
-/
theorem finite_singleton_fibre_stalk_ring
    {T U : Scheme.{u}} (p : T ⟶ U) [IsFinite p] (t : T)
    (h : p.base ⁻¹' ({p.base t} : Set U) = ({t} : Set T)) :
    RingHom.Finite (p.stalkMap t).hom ∧
      (LocallyOfFinitePresentation p →
        ∃ (a b : ℕ) (f : Fin b → MvPolynomial (Fin a) (U.presheaf.stalk (p.base t))),
          Nonempty (@AlgEquiv (U.presheaf.stalk (p.base t))
            (T.presheaf.stalk t)
            (MvPolynomial (Fin a) (U.presheaf.stalk (p.base t)) ⧸
              Ideal.span (Set.range f))
            _ _ _ (RingHom.toAlgebra (p.stalkMap t).hom) inferInstance)) := by
  classical
  obtain ⟨V, hV, htV, _⟩ :=
    exists_isAffineOpen_mem_and_subset (x := p t) (U := ⊤) (by trivial)
  let W := p ⁻¹ᵁ V
  have hW : IsAffineOpen W := hV.preimage p
  let P := hV.primeIdealOf ⟨p t, htV⟩
  let Q := hW.primeIdealOf ⟨t, htV⟩
  let φ := (p.appLE V W le_rfl).hom
  let := φ.toAlgebra
  have hφ : φ.Finite := by
    change (p.appLE V (p ⁻¹ᵁ V) le_rfl).hom.Finite
    rw [p.appLE_eq_app]
    exact p.finite_app V hV
  have hfin : Module.Finite Γ(U, V) Γ(T, W) := hφ
  have he : Ideal.comap φ Q.asIdeal = P.asIdeal := by
    exact congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE V hV W hW le_rfl htV)
  have hu : ∀ Q' : Ideal Γ(T, W), Q'.IsPrime →
      Ideal.comap φ Q' = P.asIdeal → Q' = Q.asIdeal := by
    intro Q' hQ' hcomap
    let q' : PrimeSpectrum Γ(T, W) := ⟨Q', hQ'⟩
    have hp' : PrimeSpectrum.comap φ q' = P := PrimeSpectrum.ext hcomap
    have hpoint : p (hW.fromSpec q') = p t := by
      have hh := congrArg (fun f : Spec Γ(T, W) ⟶ U ↦ f q')
        (IsAffineOpen.SpecMap_appLE_fromSpec p hV hW le_rfl).symm
      change p (hW.fromSpec q') = hV.fromSpec (PrimeSpectrum.comap φ q') at hh
      rw [hp', hV.fromSpec_primeIdealOf] at hh
      exact hh
    have hqt : hW.fromSpec q' = t := by
      have hm : hW.fromSpec q' ∈ p.base ⁻¹' ({p.base t} : Set U) := hpoint
      rw [h] at hm
      exact hm
    have : q' = Q := hW.fromSpec.isOpenEmbedding.injective
      (hqt.trans (hW.fromSpec_primeIdealOf ⟨t, htV⟩).symm)
    exact congrArg PrimeSpectrum.asIdeal this
  have hloc := localization_at_unique_prime P.asIdeal Q.asIdeal he hu
  have heq : Localization.localRingHom P.asIdeal Q.asIdeal φ he.symm =
      (IsLocalization.map (Localization.AtPrime Q.asIdeal) φ
        (Submonoid.le_comap_map P.asIdeal.primeCompl) :
        Localization.AtPrime P.asIdeal →+* Localization.AtPrime Q.asIdeal) := by
    apply IsLocalization.ringHom_ext P.asIdeal.primeCompl
    ext x
    simp only [RingHom.comp_apply, Localization.localRingHom_to_map, IsLocalization.map_eq]
  have e := IsAffineOpen.arrowStalkMapIso p V hV W hW le_rfl htV
  have hfinite : RingHom.Finite (p.stalkMap t).hom := by
    apply (RingHom.finite_respectsIso.arrow_mk_iso_iff e).mpr
    rw [heq]
    exact RingHom.finite_localizationPreserves φ P.asIdeal.primeCompl
      (Localization.AtPrime P.asIdeal) (Localization.AtPrime Q.asIdeal) hfin
  refine ⟨hfinite, ?_⟩
  intro hfp
  have hpres : RingHom.FinitePresentation (p.stalkMap t).hom := by
    apply (RingHom.finitePresentation_respectsIso.arrow_mk_iso_iff e).mpr
    rw [heq]
    exact RingHom.finitePresentation_localizationPreserves φ P.asIdeal.primeCompl
      (Localization.AtPrime P.asIdeal) (Localization.AtPrime Q.asIdeal)
      (p.finitePresentation_appLE hV hW le_rfl)
  let := (p.stalkMap t).hom.toAlgebra
  obtain ⟨a, I, eI, hI⟩ := Algebra.FinitePresentation.iff.mp hpres
  obtain ⟨b, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  have hf' : Ideal.span (Set.range f) = I := hf
  refine ⟨a, b, f, ⟨?_⟩⟩
  exact eI.symm.trans (Ideal.quotientEquivAlgOfEq _ hf'.symm)

end AlgebraicGeometry

end
