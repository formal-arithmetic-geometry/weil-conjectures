module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.AlgebraicGeometry.TildePreservesFiniteLimits
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.RingTheory.Flat.Localization
import WeilConjectures.RingTheory.KoszulRegularFlatBaseChange
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Affine criteria for Koszul-regular closed immersions

Source: Stacks Project, divisors.tex, Tags 063D and 063G; schemes.tex, Tag 01I3;
more-algebra.tex, Tag 062H
(blueprint: lem-sfb-koszul-closed-immersion-affine-criterion).

Generation on an open neighbourhood is expressed on every affine subopen using
its ideal of sections. This is sheaf generation: both ideals are quasi-coherent,
and on an affine open surjectivity of the finite generating map is detected on
sections. No surjectivity of sections on a non-affine open is assumed.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- The defining ideal is locally generated along the closed subscheme by sections
whose germs are Koszul-regular everywhere on their neighbourhood if and only if
arbitrarily small affine neighbourhoods have finite Koszul-regular equations and
identify the inverse image with the spectrum of the quotient, over that open.
Source: Stacks Project, divisors.tex, Tags 063D and 063G
(blueprint: lem-sfb-koszul-closed-immersion-affine-criterion).

Proof: (1) At a source point intersect the given neighbourhood with the prescribed
open, and choose an affine subopen U. The affine closed-immersion criterion gives
the quotient by the section ideal a.ker.ideal U. Restrict the given sections.
(2) Associated sheafification preserves kernels by finite-limit preservation and
cokernels by its adjunction; it therefore preserves images and homology. Its unit
is an isomorphism, so it reflects zero modules, exactness, and surjectivity.
(3) The sheafified generating map is surjective. Its stalks generate the ideal,
and the stalks of the sheafified Koszul complex are the Koszul complexes of the
germs, by the exterior-power bases and differential matrices. Exactness on stalks
and reflection of exactness give Koszul regularity over the affine section ring.
(4) Conversely take an affine witness inside the whole target. Sheafification of
the generating map gives ideal-sheaf generation. The structure stalks are prime
localizations of the section ring. Localization is flat, and Tag 062H gives
Koszul regularity of the germs at every point, including points off the source.
Empty sequences are allowed, and for empty source both assertions are vacuous.
No Noetherian hypothesis is used. -/
theorem koszulClosedImmersion_affine_criterion
    {T W : Scheme.{u}} (a : T ⟶ W) [IsClosedImmersion a] :
    (∀ t : T, ∃ N : W.Opens, a t ∈ N ∧
      ∃ (r : ℕ) (s : Fin r → Γ(W, N)),
        (∀ (V : W.affineOpens) (hVN : V.1 ≤ N),
          Ideal.span (Set.range (fun i ↦ W.presheaf.map (homOfLE hVN).op (s i))) =
            a.ker.ideal V) ∧
        (∀ (w : W) (hw : w ∈ N),
          RingTheory.Sequence.IsKoszulRegular (fun i ↦ W.presheaf.germ N w hw (s i)))) ↔
    (∀ (t : T) (O : W.Opens), a t ∈ O →
      ∃ U : W.affineOpens, a t ∈ U.1 ∧ U.1 ≤ O ∧
        ∃ (r : ℕ) (f : Fin r → Γ(W, U.1)),
          RingTheory.Sequence.IsKoszulRegular f ∧
          Ideal.span (Set.range f) = a.ker.ideal U ∧
          ∃ e : (a ⁻¹ᵁ U.1).toScheme ≅
              Spec (CommRingCat.of ((Γ(W, U.1) : Type u) ⧸ a.ker.ideal U)),
            (a ∣_ U.1) ≫ U.1.toSpecΓ =
              e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (a.ker.ideal U)))) := by
  sorry

/-- For a quotient closed immersion into Spec A, the affine Koszul neighbourhoods
may be chosen to be principal opens, with ideal I extended to A_h and with the
canonical localization and quotient maps describing both spectra over Spec A.
Source: Stacks Project, divisors.tex, Tag 063G; schemes.tex, Tag 01I3;
more-algebra.tex, Tag 062H
(blueprint: lem-sfb-koszul-closed-immersion-affine-criterion).

Proof: (5) Begin with an affine Koszul neighbourhood U at the source point.
Inside its intersection with the prescribed open, choose D_A(h) containing the
image point, using the distinguished-open basis of Spec A. In Gamma(U) let b be
the restriction of h. The unit-germ description gives D_U(b) = D_A(h), and the
canonical section-ring identifications identify Gamma(U)_b with A_h.
(6) Quasi-coherent ideal localization identifies J Gamma(U)_b with I A_h under
this ring isomorphism: on fractions the section map sends j/b^n to b^(-n) times
the restriction of j. Flat base change of the generators gives Koszul-regular
generators of I A_h. The affine closed-immersion criterion gives the quotient
spectrum and its commuting structural map.
(7) Principal opens are affine, so these are the same affine witnesses refined
inside the prescribed open. Empty sequences, the zero ring and empty quotient
are included; there is no Noetherian assumption. -/
theorem koszulClosedImmersion_principal_refinement
    (A : Type u) [CommRing A] (I : Ideal A)
    (hregular : ∀ t : Spec (CommRingCat.of (A ⧸ I)),
      ∃ U : (Spec (CommRingCat.of A)).affineOpens,
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) t ∈ U.1 ∧
        ∃ (r : ℕ) (f : Fin r → Γ(Spec (CommRingCat.of A), U.1)),
          RingTheory.Sequence.IsKoszulRegular f ∧
          Ideal.span (Set.range f) =
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.ideal U) :
    ∀ (t : Spec (CommRingCat.of (A ⧸ I))) (O : (Spec (CommRingCat.of A)).Opens),
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) t ∈ O →
      ∃ h : A,
        h ∉ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) t).asIdeal ∧
        PrimeSpectrum.basicOpen h ≤ O ∧
        ∃ (r : ℕ) (f : Fin r → Localization.Away h),
          RingTheory.Sequence.IsKoszulRegular f ∧
          Ideal.span (Set.range f) = I.map (algebraMap A (Localization.Away h)) ∧
          ∃ eU : @Scheme.Opens.toScheme (Spec (CommRingCat.of A))
              (PrimeSpectrum.basicOpen h) ≅
              Spec (CommRingCat.of (Localization.Away h)),
            eU.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away h))) =
              @Scheme.Opens.ι (Spec (CommRingCat.of A)) (PrimeSpectrum.basicOpen h) ∧
            ∃ eT : ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⁻¹ᵁ
                  (PrimeSpectrum.basicOpen h)).toScheme ≅
                Spec (CommRingCat.of
                  (Localization.Away h ⧸ I.map (algebraMap A (Localization.Away h)))),
              (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ∣_
                  (PrimeSpectrum.basicOpen h)) ≫ eU.hom =
                eT.hom ≫ Spec.map (CommRingCat.ofHom
                  (Ideal.Quotient.mk (I.map (algebraMap A (Localization.Away h))))) := by
  sorry

end AlgebraicGeometry
