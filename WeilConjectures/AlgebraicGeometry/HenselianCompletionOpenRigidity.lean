/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.CategoryTheory.SpectralSequencePageInduction
import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension

/-!
# Henselian completion rigidity on the open complement

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé XX, §4.4,
printed pp. 373--374, CTC and the open-complement comparison (*);
Fujiwara (1995), Corollary 6.6.4
(blueprint: lem-per-henselian-completion-open-rigidity).

The auxiliary constructions name the open complement, the spectrum map of the
canonical completion homomorphism, and its base change to the open complement.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The open complement `Spec C ∖ V(I)`, with its induced open subscheme structure.
Source: ILO, Exposé XX, §4.4, p. 373, notation `U = X − V(I)`
(blueprint: lem-per-henselian-completion-open-rigidity). -/
def henselianCompletionOpen (C : Type u) [CommRing C] (I : Ideal C) :
    (Spec (CommRingCat.of C)).Opens :=
  ⟨(PrimeSpectrum.zeroLocus (I : Set C))ᶜ, (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩

/-- The spectrum map of the canonical homomorphism into the `I`-adic completion.
Source: ILO, Exposé XX, §4.4, p. 373, the completion case of `π : X' → X`
(blueprint: lem-per-henselian-completion-open-rigidity). -/
noncomputable def henselianCompletionSpecMap (C : Type u) [CommRing C] (I : Ideal C) :
    Spec (CommRingCat.of (AdicCompletion I C)) ⟶ Spec (CommRingCat.of C) :=
  Spec.map (CommRingCat.ofHom (algebraMap C (AdicCompletion I C)))

/-- The canonical map `Spec Ĉ ×[Spec C] U → U`, where `U = Spec C ∖ V(I)`.
Source: ILO, Exposé XX, §4.4, p. 373, restriction of `π` to `U'`
(blueprint: lem-per-henselian-completion-open-rigidity). -/
noncomputable def henselianCompletionOpenMap (C : Type u) [CommRing C] (I : Ideal C) :
    pullback (henselianCompletionSpecMap C I) (henselianCompletionOpen C I).ι ⟶
      (henselianCompletionOpen C I).toScheme :=
  pullback.snd _ _

/-- Completion preserves torsion étale cohomology on the open complement of a
Noetherian henselian pair, through the canonical pullback, naturally in the sheaf.
Source: ILO, Exposé XX, §4.4, printed pp. 373--374 (CTC and (*));
Fujiwara (1995), Corollary 6.6.4
(blueprint: lem-per-henselian-completion-open-rigidity).

Proof plan from the DAG:
1. Noetherianity makes `I` finitely generated. Apply
   `lem-per-admissible-modification-cohomology-presentation` to obtain the common
   closed-fibre limit topos, its two first-quadrant spectral sequences, and the
   exchange morphism whose abutment is this canonical pullback.
2. By `lem-per-admissible-modification-valuative-stalks`, the exchange morphism on
   a conservative family of points is the pullback along dense embeddings of
   henselian valued fields. Apply `lem-per-dense-henselian-field-etale-comparison`
   in each degree; conservativity makes every coefficient exchange an isomorphism.
3. Apply cohomology to these coefficient isomorphisms. The spectral sequence map
   is an isomorphism on page two, hence on later pages by `lem-sp-page-induction`.
   First-quadrant vanishing gives stabilization in each bidegree.
4. The finite abutment filtrations have isomorphic graded pieces, so
   `lem-sp-finite-filtration-induction` makes the canonical abutment map an
   isomorphism. All exchange maps and filtrations are natural in the sheaf,
   giving the naturality identity below.
-/
theorem henselian_completion_open_rigidity (C : Type u) [CommRing C] [IsNoetherianRing C]
    (I : Ideal C) [HenselianRing C I]
    (F : Sheaf (henselianCompletionOpen C I).toScheme.smallEtaleTopology
      AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ) :
    Function.Bijective (cohomologyMap (henselianCompletionOpenMap C I) F q) ∧
      ∀ (G : Sheaf (henselianCompletionOpen C I).toScheme.smallEtaleTopology
          AddCommGrpCat.{u + 1}), G.IsTorsion → ∀ (φ : F ⟶ G) (x : Sheaf.H F q),
        cohomologyMap (henselianCompletionOpenMap C I) G q (Sheaf.H.map φ q x) =
          Sheaf.H.map ((upperStar AddCommGrpCat.{u + 1}
            (henselianCompletionOpenMap C I)).map φ) q
              (cohomologyMap (henselianCompletionOpenMap C I) F q x) := by
  sorry

end AlgebraicGeometry.Etale
