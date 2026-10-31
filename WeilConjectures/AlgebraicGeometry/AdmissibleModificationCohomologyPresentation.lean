/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdmissibleModificationPresentationData

import WeilConjectures.AlgebraicGeometry.AdmissibleOpenToposPresentation
import WeilConjectures.AlgebraicGeometry.AdmissibleCompletionSpectralPresentation

/-! # Admissible-modification cohomology presentation
Source: ILO XX 4.4, printed pp.373–374.
(blueprint: lem-per-admissible-modification-cohomology-presentation).
-/

@[expose] public section

set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

/-- The whole presentation and its completion morphism, natural in the torsion
input sheaf. Both limits are presented by the same site, with the identification
normalized on the cofinal extended blowups and their closed fibres. The exchange
on coefficient colimits and on the E₂ page is specified, as is the canonical
pullback on the filtered abutment. No exchange map is required to be invertible.
Source: ILO XX 4.4, printed pages 373–374.
(blueprint: lem-per-admissible-modification-cohomology-presentation). -/
structure AdmissibleModificationPresentation {A : Type u} [CommRing A] (I : Ideal A)
    (U : (Spec (CommRingCat.of A)).Opens) where
  C : Type (u + 1)
  [smallC : SmallCategory C]
  τ : GrothendieckTopology C
  originalTopos : AdmissibleToposPresentation I C τ
  completedTopos : AdmissibleToposPresentation (admissibleCompletionIdeal I) C τ
  opens : AdmissibleOpenEmbeddings I U
  completedOpens : AdmissibleOpenEmbeddings (admissibleCompletionIdeal I)
    (admissibleCompletionOpen I U)
  comparison : AdmissibleCompletionComparison I originalTopos.site completedTopos.site
    opens completedOpens
  original : AdmissibleSpectralPresentation originalTopos.site opens
  completed : AdmissibleSpectralPresentation completedTopos.site completedOpens
  coefficientExchange (q : ℕ) : (original.coefficient q).pt ⟶
    Etale.upperStar AddCommGrpCat.{u + 1} (admissibleCompletionOpenMap I U) ⋙
      (completed.coefficient q).pt
  coefficientExchange_normalization (q : ℕ) (J : AdmissibleModification I)
      (F : Sheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((original.coefficient q).ι.app (op J)).app F ≫ (coefficientExchange q).app F =
      (original.finiteStage q J).hom.app F ≫ comparison.coefficientMap q J F ≫
        (completed.finiteStage q (comparison.extension.obj J)).inv.app _ ≫
          ((completed.coefficient q).ι.app (op (comparison.extension.obj J))).app _
  spectralSequenceMap : original.spectralSequence ⟶
    Etale.upperStar AddCommGrpCat.{u + 1} (admissibleCompletionOpenMap I U) ⋙
      completed.spectralSequence
  pageTwo_commutes (p q : ℕ)
      (F : Sheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (((spectralSequenceMap.app F).hom 2).f (p, q)) ≫
        (completed.pageTwo p q _).hom =
      (original.pageTwo p q F).hom ≫
        ((Sheaf.Γ τ AddCommGrpCat.{u + 1}).rightDerived p).map
          ((coefficientExchange q).app F)
  pullbackTorsion (F : Sheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    F.IsTorsion → ((Etale.upperStar AddCommGrpCat.{u + 1}
      (admissibleCompletionOpenMap I U)).obj F).IsTorsion
  filteredPullback (F : Sheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1})
      (hF : F.IsTorsion) :
    AdmissibleFilteredAbutmentMap (original.abutment F hF)
      (completed.abutment _ (pullbackTorsion F hF))
      (original.gradedIso F hF) (completed.gradedIso _ (pullbackTorsion F hF))
      (spectralSequenceMap.app F)
      (fun n ↦ admissibleCohomologyPullback (admissibleCompletionOpenMap I U) F n)

/-- The admissible-modification presentation for a henselian pair with finitely
generated ideal, including the coefficient-colimit formula, the first-quadrant
spectral sequence and its finite filtration, and the completion exchange morphism
with canonical filtered cohomology pullback on abutments.
Source: ILO, Travaux de Gabber, XX 4.4, printed pages 373–374, (**) and its limit,
and the final Note.
(blueprint: lem-per-admissible-modification-cohomology-presentation).

Proof: Full-support blowups are cofiltered and thin by schematic density and
separatedness. Their closed fibres are qcqs and have qcqs transition morphisms.
The finite-cover colimit site presents the limit topos and has the compatible
geometric points as a conservative family. For an injective resolution of a
torsion sheaf, proper henselian restriction identifies the derived sections of
each restricted open direct image with the same complex of sections on U.
Finite-cover continuity, exact inverse image, and exact filtered colimits identify
its limit's cohomology sheaves with the specified coefficient colimits. The
truncation hypercohomology spectral sequence gives the displayed E₂ page and the
finite first-quadrant filtration. Extension of ideals is cofinal and induces
compatible closed-fibre isomorphisms after completion. Derived exchange gives the
coefficient morphism. Naturality of restriction, continuity and truncation gives
the morphism of spectral sequences, whose filtered abutment is canonical pullback.
-/
theorem admissibleModificationCohomologyPresentation
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I] (hI : I.FG)
    (U : (Spec (CommRingCat.of A)).Opens)
    (hU : ∀ x : PrimeSpectrum A, x ∈ U ↔ x ∉ PrimeSpectrum.zeroLocus (I : Set A)) :
    Nonempty (AdmissibleModificationPresentation I U) := by
  obtain ⟨G⟩ := admissibleOpenToposPresentation I hI U hU
  obtain ⟨S⟩ := admissibleCompletionSpectralPresentation I hI U hU G.topos G.opens
  exact ⟨{
    C := G.C
    smallC := G.smallC
    τ := G.τ
    originalTopos := G.topos
    completedTopos := S.completedTopos
    opens := G.opens
    completedOpens := S.completedOpens
    comparison := S.comparison
    original := S.original
    completed := S.completed
    coefficientExchange := S.coefficientExchange
    coefficientExchange_normalization := S.coefficientExchange_normalization
    spectralSequenceMap := S.spectralSequenceMap
    pageTwo_commutes := S.pageTwo_commutes
    pullbackTorsion := S.pullbackTorsion
    filteredPullback := S.filteredPullback }⟩

end

end AlgebraicGeometry
