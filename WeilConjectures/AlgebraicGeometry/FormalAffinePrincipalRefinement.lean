/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicPrincipalChartData
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Principal refinements of Noetherian adic formal affine charts

Source: Stacks Project, Tags 0AHY and 0AHZ, and the formal counterpart of Tag 01IW;
Commutative Algebra, Tags 05GG, 0316, 05GI, 00HT, 00MB, 00HR and 00HQ.
(blueprint: lem-per-formal-affine-principal-refinement)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Principal charts, common principal refinements, and their local algebra.
Source: Stacks Tags 0AHY, 0AHZ and 01IW, with Tags 05GG, 0316, 05GI, 00MB and 00HR.
(blueprint: lem-per-formal-affine-principal-refinement)

Proof:
1. Open primes are precisely the primes containing the ideal of definition. The positive
   quotient spectra have this common space. The ringed-space colimit uses their inverse-limit
   sheaf, computed sectionwise by `lem-weil-pbc-site-sheaf-sets-limits-sectionwise`.
2. On a principal open the affine section formula
   (`lem-weil-pbc-affine-open-section-vanishing-prime`) gives the localized quotients. The
   restriction maps are the quotient-localization maps on each component.
3. Localization commutes with quotient (`lem-weil-pbc-localization-quotient-commute`). Apply
   `lem-weil-pbc-module-completion-complete` to identify the completion and its quotients.
   Localization and completion preserve Noetherianity (`lem-weil-pbc-localization-noetherian`,
   `lem-weil-pbc-adic-completion-noetherian`). The first quotient identifies the principal
   spaces, and the affine section formula identifies the sheaves on a basis.
4. For a continuous map, choose nondecreasing indices m(n) with the image of K^m(n) in L^n.
   The quotient-localization fraction maps define compatible maps on limits. Larger indices
   show independence of choices, compatibility with restrictions, identities and composition.
5. A principal open is the locus of invertible germs: use the quotient localizations in one
   direction and projection to the first quotient and its residue fields in the other.
6. Choose D_U(f) inside the given neighbourhood, then D_V(g) inside D_U(f). Restrict g to
   the completed ring C_f. Its reduction modulo K is a/f^e by Step 3 and
   `lem-weil-pbc-module-completion-complete`. Its invertibility locus is therefore D_U(fa),
   and equals D_V(g), giving the common principal refinement.
7. `lem-weil-pbc-adic-complete-jacobson-radical` puts K in every maximal ideal m. If s avoids
   m, the surjection C_s to (R/K)_s to R/m has a maximal kernel n containing KC_s and
   contracting to m.
8. Localization and Noetherian completion are flat (`lem-weil-pbc-localization-flat`,
   `lem-weil-pbc-noetherian-completion-flat`), hence their composite is flat
   (`lem-weil-pbc-flat-ring-map-comp`). Localize at n
   (`lem-weil-pbc-flat-local-ring-maps`); the resulting flat local map is faithfully flat
   (`lem-weil-pbc-flat-local-hom-faithfully-flat`), including surjectivity on spectra. -/
theorem adicFormalAffine_principal_refinement :
    (∀ (R : CommRingCat.{u}) (K : Ideal R) [IsNoetherianRing R] [IsAdicComplete K R],
      (∃ e : adicFormalSpec R K ≃ₜ {p : PrimeSpectrum R // K ≤ p.asIdeal},
        ∀ x : adicFormalSpec R K,
          (e x).val = (adicFormalSpecToSpec R K).hom.base x) ∧
      (∀ s : R,
        IsNoetherianRing (adicCompletedAway R K s) ∧
        IsAdicComplete (K.map (adicCompletedAwayMap R K s)) (adicCompletedAway R K s) ∧
        (∃! e : (adicFormalSpec R K).presheaf.obj
            (op (adicFormalPrincipalOpen R K s)) ≃+* adicCompletedAway R K s,
          IsAdicPrincipalSectionComparison R K s e) ∧
        (∃ e : adicCompletedAway R K s ≃+* (↑(limit (adicLocalizedQuotientTower R K s))),
          @IsHomeomorph _ _ (K.map (adicCompletedAwayMap R K s)).adicTopology
            (⨅ n : ℕ, TopologicalSpace.induced
              (limit.π (adicLocalizedQuotientTower R K s) (op n)).hom ⊥) e ∧
          ∀ (n : ℕ) (r : R),
            (limit.π (adicLocalizedQuotientTower R K s) (op n)).hom
                (e (adicCompletedAwayMap R K s r)) =
              algebraMap (R ⧸ K ^ (n + 1))
                (Localization.Away (Ideal.Quotient.mk (K ^ (n + 1)) s))
                (Ideal.Quotient.mk (K ^ (n + 1)) r)) ∧
        (∃ e : adicFormalSpec (CommRingCat.of (adicCompletedAway R K s))
              (K.map (adicCompletedAwayMap R K s)) ≅
            (adicFormalSpec R K).restrict (adicFormalPrincipalOpen R K s).isOpenEmbedding,
          IsAdicFormalSpectrumMap (R := R)
            (S := CommRingCat.of (adicCompletedAway R K s))
            K (K.map (adicCompletedAwayMap R K s))
            (adicCompletedAwayMap R K s)
            (e.hom ≫ (adicFormalSpec R K).ofRestrict
              (adicFormalPrincipalOpen R K s).isOpenEmbedding))) ∧
      (∀ (s t : R) (h : adicFormalPrincipalOpen R K t ≤ adicFormalPrincipalOpen R K s)
        (es : (adicFormalSpec R K).presheaf.obj
          (op (adicFormalPrincipalOpen R K s)) ≃+* adicCompletedAway R K s)
        (et : (adicFormalSpec R K).presheaf.obj
          (op (adicFormalPrincipalOpen R K t)) ≃+* adicCompletedAway R K t),
        IsAdicPrincipalSectionComparison R K s es → IsAdicPrincipalSectionComparison R K t et →
        ∃! ψ : adicCompletedAway R K s →+* adicCompletedAway R K t,
          @Continuous _ _ (K.map (adicCompletedAwayMap R K s)).adicTopology
            (K.map (adicCompletedAwayMap R K t)).adicTopology ψ ∧
          ψ.comp (adicCompletedAwayMap R K s) = adicCompletedAwayMap R K t ∧
          et.toRingHom.comp ((adicFormalSpec R K).presheaf.map (homOfLE h).op).hom =
            ψ.comp es.toRingHom) ∧
      (∀ (m : Ideal R) [m.IsMaximal], K ≤ m ∧
        ∀ s : R, s ∉ m →
          ∃ (n : Ideal (adicCompletedAway R K s)) (_ : n.IsMaximal),
            K.map (adicCompletedAwayMap R K s) ≤ n ∧
            ∃ h : m = n.comap (adicCompletedAwayMap R K s),
              (Localization.localRingHom m n (adicCompletedAwayMap R K s) h).FaithfullyFlat)) ∧
    (∀ (X : RingedSpace.{u}), (∀ x : X, ∃ U : Opens X, x ∈ U ∧ IsAdicFormalAffineOpen X U) →
      ∀ (U V : Opens X) (_ : IsAdicFormalAffineOpen X U)
        (_ : IsAdicFormalAffineOpen X V) (x : X) (N : Opens X),
        x ∈ N → N ≤ U ⊓ V →
          ∃ (s : X.presheaf.obj (op U)) (t : X.presheaf.obj (op V)),
            x ∈ X.basicOpen s ∧ X.basicOpen s ≤ N ∧
            X.basicOpen s = X.basicOpen t) ∧
    (∀ (R S : CommRingCat.{u}) (K : Ideal R) (L : Ideal S)
      [IsNoetherianRing R] [IsNoetherianRing S] [IsAdicComplete K R] [IsAdicComplete L S]
      (φ : R →+* S),
      @Continuous _ _ K.adicTopology L.adicTopology φ →
        ∃! F : adicFormalSpec S L ⟶ adicFormalSpec R K,
          IsAdicFormalSpectrumMap K L φ F ∧
          ∀ (s : R)
            (eR : (adicFormalSpec R K).presheaf.obj
              (op (adicFormalPrincipalOpen R K s)) ≃+* adicCompletedAway R K s)
            (eS : (adicFormalSpec S L).presheaf.obj
              (op (adicFormalPrincipalOpen S L (φ s))) ≃+* adicCompletedAway S L (φ s)),
            IsAdicPrincipalSectionComparison R K s eR →
            IsAdicPrincipalSectionComparison S L (φ s) eS →
            ∃ h : (Opens.map F.hom.base).obj (adicFormalPrincipalOpen R K s) =
                adicFormalPrincipalOpen S L (φ s),
              ∃! ψ : adicCompletedAway R K s →+* adicCompletedAway S L (φ s),
                @Continuous _ _ (K.map (adicCompletedAwayMap R K s)).adicTopology
                  (L.map (adicCompletedAwayMap S L (φ s))).adicTopology ψ ∧
                ψ.comp (adicCompletedAwayMap R K s) =
                  (adicCompletedAwayMap S L (φ s)).comp φ ∧
                eS.toRingHom.comp
                    (((adicFormalSpec S L).presheaf.map (eqToHom h.symm).op).hom.comp
                      (F.hom.c.app (op (adicFormalPrincipalOpen R K s))).hom) =
                  ψ.comp eR.toRingHom) := by
  sorry

end AlgebraicGeometry
