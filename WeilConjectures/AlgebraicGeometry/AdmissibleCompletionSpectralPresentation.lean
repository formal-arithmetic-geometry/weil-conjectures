/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdmissibleModificationPresentationData

/-! # Natural spectral presentations over the admissible limit topos
Source: ILO XX 4.4, printed pp.373–374.
(blueprint: lem-per-admissible-completion-spectral-presentation).
-/

@[expose] public section

set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

/-- The cohomological construction over a fixed original limit site and fixed
open embeddings. The completed projections and their comparison are constructed
at the same time as the natural spectral sequences, so their normalizations agree.
Source: ILO XX 4.4, (**) and (**)lim and the final Note, printed pages 373–374.
(blueprint: lem-per-admissible-completion-spectral-presentation). -/
structure AdmissibleCompletionSpectralPresentation
    {A : Type u} [CommRing A] {I : Ideal A}
    {C : Type (u + 1)} [SmallCategory C] {τ : GrothendieckTopology C}
    (P : AdmissibleToposPresentation I C τ) {U : (Spec (CommRingCat.of A)).Opens}
    (j : AdmissibleOpenEmbeddings I U) where
  completedTopos : AdmissibleToposPresentation (admissibleCompletionIdeal I) C τ
  completedOpens : AdmissibleOpenEmbeddings (admissibleCompletionIdeal I)
    (admissibleCompletionOpen I U)
  comparison : AdmissibleCompletionComparison I P.site completedTopos.site
    j completedOpens
  original : AdmissibleSpectralPresentation P.site j
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

/-- The derived coefficient construction and its natural completion morphism can
be carried out over a given presentation of the original limit topos.
Source: ILO XX 4.4, (**) and (**)lim and the final Note, printed pages 373–374.
(blueprint: lem-per-admissible-completion-spectral-presentation).

Proof: Resolve an abelian input sheaf F by a nonnegative injective resolution and
restrict j_{J*} of that resolution to each closed fibre. Direct image preserves
injectives; exact inverse image identifies its cohomology with i_J^{-1} R^q j_{J*} F.
The adjunction exchange maps of the resolutions give the canonical transition
maps, including their identity and composition laws. Pass to the termwise filtered
colimit of the projection inverse images. Exactness of these inverse images and
of filtered colimits identifies its cohomology sheaves with the coefficient
colimits in the statement. Finite-cover derived-sections continuity applies with
common lower bound zero. For torsion F the qcqs higher direct images are torsion;
proper henselian restriction and Leray identify each stage's derived sections
with RΓ(U,F). Under domination these identifications give identity maps, so the
constant-diagram colimit gives the same RΓ(U,F) on the limit site. Transport the
construction to the specified presenting site by its limit equivalence.
Apply the raw truncation-couple construction to this coefficient complex. The
truncation hypercohomology theorem gives its E₂ formula and finite first-quadrant
abutment filtration. Raw-couple naturality and derived-couple functoriality give
functoriality in F, with the associated graded maps of that very filtration.
The completed ideal is finitely generated, the completed pair is complete and
henselian, and the admissible-modification-system theorem gives the cofinal
extension functor, its blowup maps and compatible closed-fibre isomorphisms.
Transport the completed site projections to the given original site using the
cofinal inverse-limit comparison; use its canonical projection identifications
for siteComparison. Construct the completed coefficient complex in the same way.
Termwise derived exchange induces its map from the original complex. At each
finite stage its cohomology map is coefficientMap, so the colimit coprojection
identity is exactly coefficientExchange_normalization. Naturality of proper
henselian restriction and derived continuity identifies the derived-section map
with canonical completion pullback. Raw truncation naturality then gives the
spectral-sequence map, the E₂ square, and filteredPullback. Exact inverse image
preserves torsion, giving pullbackTorsion. No exchange map is inverted here.
-/
theorem admissibleCompletionSpectralPresentation
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I] (hI : I.FG)
    (U : (Spec (CommRingCat.of A)).Opens)
    (hU : ∀ x : PrimeSpectrum A, x ∈ U ↔ x ∉ PrimeSpectrum.zeroLocus (I : Set A))
    {C : Type (u + 1)} [SmallCategory C] {τ : GrothendieckTopology C}
    (P : AdmissibleToposPresentation I C τ) (j : AdmissibleOpenEmbeddings I U) :
    Nonempty (AdmissibleCompletionSpectralPresentation P j) := by sorry

end

end AlgebraicGeometry
