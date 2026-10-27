module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.CompletionMapForLocalHom
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.GRingEquiv
import WeilConjectures.RingTheory.FiniteTypeGRing
import WeilConjectures.RingTheory.AdicCompletionRingEquiv
import WeilConjectures.RingTheory.RegularRingEquiv

/-! # Affine charts for local-map approximation

Source: Stacks Project, more-morphisms.tex, Tag 0CAU, lemma-map-approximation,
first paragraph and final sentence; more-algebra.tex, Tag 07PV.
(blueprint: lem-trf-local-map-affine-chart-dictionary)

The helper definitions spell out the iterated polynomial presentation and the
coordinate characterization of the completion comparisons used in the theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public noncomputable section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

namespace LocalMapAffineChart

/-- The repeated one-variable polynomial ring, including the zero-variable ring.
Source: Stacks Project, Tag 0CAU, the finite polynomial presentation.
(blueprint: lem-trf-local-map-affine-chart-dictionary) -/
def polynomialRing (R : CommRingCat.{u}) : ℕ → CommRingCat.{u}
  | 0 => R
  | n + 1 => CommRingCat.of (Polynomial (polynomialRing R n))

/-- The coefficient inclusion into the repeated polynomial ring.
Source: Stacks Project, Tag 0CAU, the finite polynomial presentation.
(blueprint: lem-trf-local-map-affine-chart-dictionary) -/
def coefficientMap (R : CommRingCat.{u}) : (n : ℕ) → R →+* polynomialRing R n
  | 0 => RingHom.id R
  | n + 1 => Polynomial.C.comp (coefficientMap R n)

/-- The canonical chart identification, with the equality of the marked points transported.
Source: Stacks Project, Tag 01HV, lemma-spec-sheaves (6).
(blueprint: lem-trf-local-map-affine-chart-dictionary) -/
def stalkEquiv {Z : Scheme.{u}} {C : CommRingCat.{u}}
    (i : Spec C ⟶ Z) [IsOpenImmersion i] (p : PrimeSpectrum C) (z : Z)
    (hp : i p = z) : Z.presheaf.stalk z ≃+* Localization.AtPrime p.asIdeal :=
  ((Z.presheaf.stalkCongr (.of_eq hp)).symm ≪≫ asIso (i.stalkMap p) ≪≫
    Spec.stalkIso C p).commRingCatIsoToRingEquiv

/-- The stalk map with its target point named explicitly.
Source: Stacks Project, Tag 01HV, functoriality of germs.
(blueprint: lem-trf-local-map-affine-chart-dictionary) -/
def stalkMapAt {Z W : Scheme.{u}} (f : Z ⟶ W) (z : Z) (w : W)
    (hf : f z = w) : W.presheaf.stalk w →+* Z.presheaf.stalk z :=
  (f.stalkMap z).hom.comp (W.presheaf.stalkCongr (.of_eq hf)).inv.hom

/-- The maximal-ideal completion, using the recorded adic completion definition.
Source: Stacks Project, Tag 07ED, with Tag 0CAU.
(blueprint: lem-trf-local-map-affine-chart-dictionary) -/
abbrev Completion (A : Type u) [CommRing A] [IsLocalRing A] :=
  AdicCompletion (IsLocalRing.maximalIdeal A) A

/-- The coordinate characterization of the completion map induced by a local ring map.
Source: Stacks Project, Tag 07ED; the characterization in
lem-weil-pbc-fs-adic-completion-map-local.
(blueprint: lem-trf-local-map-affine-chart-dictionary) -/
def HasCompletionCoordinates {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) (F : Completion A →+* Completion B) : Prop :=
  ∀ (n : ℕ) (z : Completion A) (a : A),
    AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n z =
        Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A) ^ n) a →
      AdicCompletion.evalₐ (IsLocalRing.maximalIdeal B) n (F z) =
        Ideal.Quotient.mk ((IsLocalRing.maximalIdeal B) ^ n) (f a)

/-- A completion identification with its quotient coordinates and completion-map normalization.
Source: Stacks Project, Tags 01HV and 07ED, applied in Tag 0CAU.
(blueprint: lem-trf-local-map-affine-chart-dictionary) -/
def IsCompletionIdentification {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) (E : Completion A ≃+* Completion B) : Prop :=
  HasCompletionCoordinates e.toRingHom E.toRingHom ∧
    E.toRingHom.comp (algebraMap A (Completion A)) =
      (algebraMap B (Completion B)).comp e.toRingHom

/-- Completion comparisons for two stalk maps with a common target. The comparisons identify
both completed arrows, their restrictions along the completion maps, and all positive powers
of the target maximal ideal extended to its completion.
Source: Stacks Project, Tags 01HV and 07ED, applied in the final sentence of Tag 0CAU.
(blueprint: lem-trf-local-map-affine-chart-dictionary) -/
def CompletionDictionary
    {A B C A₀ B₀ C₀ : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [CommRing A₀] [CommRing B₀] [CommRing C₀]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [IsLocalRing A₀] [IsLocalRing B₀] [IsLocalRing C₀]
    (eA : A ≃+* A₀) (eB : B ≃+* B₀) (eC : C ≃+* C₀)
    (f : A →+* C) (g : B →+* C) (f₀ : A₀ →+* C₀) (g₀ : B₀ →+* C₀) : Prop :=
  ∃ (EA : Completion A ≃+* Completion A₀)
    (EB : Completion B ≃+* Completion B₀)
    (EC : Completion C ≃+* Completion C₀)
    (F : Completion A →+* Completion C) (G : Completion B →+* Completion C)
    (F₀ : Completion A₀ →+* Completion C₀) (G₀ : Completion B₀ →+* Completion C₀),
    IsCompletionIdentification eA EA ∧ IsCompletionIdentification eB EB ∧
    IsCompletionIdentification eC EC ∧
    HasCompletionCoordinates f F ∧ HasCompletionCoordinates g G ∧
    HasCompletionCoordinates f₀ F₀ ∧ HasCompletionCoordinates g₀ G₀ ∧
    F.comp (algebraMap A (Completion A)) = (algebraMap C (Completion C)).comp f ∧
    G.comp (algebraMap B (Completion B)) = (algebraMap C (Completion C)).comp g ∧
    F₀.comp (algebraMap A₀ (Completion A₀)) = (algebraMap C₀ (Completion C₀)).comp f₀ ∧
    G₀.comp (algebraMap B₀ (Completion B₀)) = (algebraMap C₀ (Completion C₀)).comp g₀ ∧
    EC.toRingHom.comp F = F₀.comp EA.toRingHom ∧
    EC.toRingHom.comp G = G₀.comp EB.toRingHom ∧
    ∀ N : ℕ, 1 ≤ N →
      (((IsLocalRing.maximalIdeal C) ^ N).map (algebraMap C (Completion C))).map
          EC.toRingHom =
        ((IsLocalRing.maximalIdeal C₀) ^ N).map (algebraMap C₀ (Completion C₀))

end LocalMapAffineChart

open LocalMapAffineChart

namespace LocalMapAffineChart

/-- Affine charts and the full local-ring dictionary needed for local-map approximation.
Source: Stacks Project, Tag 0CAU, lemma-map-approximation, affine reduction and final sentence;
G-ring input: Tag 07PV, proposition-finite-type-over-G-ring.
(blueprint: lem-trf-local-map-affine-chart-dictionary)

Proof:
1. Choose an affine neighbourhood of s, then affine neighbourhoods of x and y in its
   inverse images. The locally finite type condition makes their section algebras finite
   type. pqf-lem-affine-open-locnoeth and lem-weil-pbc-finite-type-algebra-noetherian make
   all three rings Noetherian. lem-weil-pbc-finite-type-noetherian-finite-presentation
   gives a polynomial surjection with finitely generated kernel, also for n = 0 or m = 0.
2. lem-weil-pbc-affine-open-stalk-localization gives the canonical stalk identifications.
   Germ functoriality identifies the structure maps; locality gives the prime contractions.
   The localized maps send each fraction to the fraction of its images.
3. Transfer the G-ring hypothesis to R_r by lem-weil-pbc-g-ring-ring-equiv. Localize A
   at the image of R minus r. Its finite algebra generators remain generators over R_r,
   so lem-weil-pbc-finite-type-over-g-ring makes this intermediate algebra a G-ring.
   Localizing it at the prime over p gives A_p, by the inverse fraction maps.
4. This localization is Noetherian by lem-weil-pbc-localization-noetherian. For every
   prime of the localization, its local ring is the corresponding localization of the
   intermediate ring. lem-weil-pbc-adic-completion-ring-equiv and
   lem-weil-pbc-regular-ring-map-ring-equiv identify the completion regularity conditions.
   Thus A_p is a G-ring by its definition and lem-weil-pbc-g-ring-ring-equiv.
5. Form p_U by composing Spec h with the chart open immersion. Use
   lem-weil-pbc-etale-ring-map-iff-etale-affine and
   lem-weil-pbc-etale-composition-cancellation for etaleness. By
   lem-weil-pbc-etale-algebra-finite-presentation-localization, A' is finite type over A;
   lem-weil-pbc-finite-type-algebra-noetherian makes A' Noetherian.
6. Compose Spec phi with the Y chart. The R-algebra equation makes both composites to S
   equal. Spectrum maps are prime contraction, so the marked points map to x and y.
7. Identify the U stalk with A' localized at p'. Germ functoriality shows the stalk maps
   are h_p and phi_q on numerators, hence on fractions. Quotienting by the maximal ideals
   identifies the residue maps, proving the residue-field isomorphism implication.
8. Apply lem-weil-pbc-fs-adic-completion-map-local. The quotient maps for the stalk and
   localized arrows agree at each level, so their inverse-limit maps agree. The canonical
   completion map has coordinates given by reduction, and obeys the same compatibility.
9. The U stalk equivalence identifies maximal ideals and their powers. Its completion
   equivalence therefore sends each finite sum of N-fold products times completed elements
   to the corresponding sum. Apply the inverse for the reverse inclusion of ideal powers.
-/
theorem exists_dictionary
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (x : X) (y : Y) (s : S) (hx : f x = s) (hy : g y = s)
    (hG : IsGRing (S.presheaf.stalk s)) :
    ∃ (R A B : CommRingCat.{u}) (a : R ⟶ A) (b : R ⟶ B)
      (iR : Spec R ⟶ S) (iA : Spec A ⟶ X) (iB : Spec B ⟶ Y),
      ∃ (_ : IsOpenImmersion iR) (_ : IsOpenImmersion iA) (_ : IsOpenImmersion iB),
      ∃ (r : PrimeSpectrum R) (p : PrimeSpectrum A) (q : PrimeSpectrum B)
        (hr : iR r = s) (hp : iA p = x) (hq : iB q = y)
        (ha : r.asIdeal = p.asIdeal.comap a.hom)
        (hb : r.asIdeal = q.asIdeal.comap b.hom),
      IsNoetherianRing R ∧ IsNoetherianRing A ∧ IsNoetherianRing B ∧
      a.hom.FiniteType ∧ b.hom.FiniteType ∧
      iA ≫ f = Spec.map a ≫ iR ∧ iB ≫ g = Spec.map b ≫ iR ∧
      (∃ (n m : ℕ) (F : Fin m → polynomialRing R n)
        (π : polynomialRing R n →+* B),
        Function.Surjective π ∧ RingHom.ker π = Ideal.span (Set.range F) ∧
        π.comp (coefficientMap R n) = b.hom) ∧
      (stalkEquiv iA p x hp).toRingHom.comp (stalkMapAt f x s hx) =
        (Localization.localRingHom r.asIdeal p.asIdeal a.hom ha).comp
          (stalkEquiv iR r s hr).toRingHom ∧
      (stalkEquiv iB q y hq).toRingHom.comp (stalkMapAt g y s hy) =
        (Localization.localRingHom r.asIdeal q.asIdeal b.hom hb).comp
          (stalkEquiv iR r s hr).toRingHom ∧
      IsGRing (Localization.AtPrime p.asIdeal) ∧
      ∀ (A' : CommRingCat.{u}) (h : A ⟶ A') (_ : h.hom.Etale)
        (p' : PrimeSpectrum A') (hh : p.asIdeal = p'.asIdeal.comap h.hom),
        IsNoetherianRing A' ∧
        ∃ (hpx : (Spec.map h ≫ iA) p' = x),
        Etale (Spec.map h ≫ iA) ∧
        (Function.Bijective (Ideal.ResidueField.map p.asIdeal p'.asIdeal h.hom hh) →
          IsIso ((Spec.map h ≫ iA).residueFieldMap p')) ∧
        ∀ (φ : B ⟶ A') (_ : φ.hom.comp b.hom = h.hom.comp a.hom)
          (hφ : q.asIdeal = p'.asIdeal.comap φ.hom),
          (Spec.map h ≫ iA) ≫ f = (Spec.map φ ≫ iB) ≫ g ∧
          ∃ (hpy : (Spec.map φ ≫ iB) p' = y),
          (Spec.stalkIso A' p').commRingCatIsoToRingEquiv.toRingHom.comp
              (stalkMapAt (Spec.map h ≫ iA) p' x hpx) =
            (Localization.localRingHom p.asIdeal p'.asIdeal h.hom hh).comp
              (stalkEquiv iA p x hp).toRingHom ∧
          (Spec.stalkIso A' p').commRingCatIsoToRingEquiv.toRingHom.comp
              (stalkMapAt (Spec.map φ ≫ iB) p' y hpy) =
            (Localization.localRingHom q.asIdeal p'.asIdeal φ.hom hφ).comp
              (stalkEquiv iB q y hq).toRingHom ∧
          CompletionDictionary (stalkEquiv iA p x hp) (stalkEquiv iB q y hq)
            (Spec.stalkIso A' p').commRingCatIsoToRingEquiv
            (stalkMapAt (Spec.map h ≫ iA) p' x hpx)
            (stalkMapAt (Spec.map φ ≫ iB) p' y hpy)
            (Localization.localRingHom p.asIdeal p'.asIdeal h.hom hh)
            (Localization.localRingHom q.asIdeal p'.asIdeal φ.hom hφ) := by
  sorry

end LocalMapAffineChart
end AlgebraicGeometry
