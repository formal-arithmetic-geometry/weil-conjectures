/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdmissibleModificationCoefficientData

/-! # Admissible-modification presentation interfaces
Source: ILO XX 4.4, printed pp.373–374.
(blueprint: def-per-admissible-modification-presentation-data).
-/

@[expose] public section

set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

/-- A presenting site for the closed-fibre limit, including its universal property
and its conservative compatible geometric points. Using all ideals rather than
its skeleton retains an equivalent small cofiltered category.
Source: ILO XX 4.4, printed page 373.
(blueprint: def-per-admissible-modification-presentation-data). -/
structure AdmissibleToposPresentation {A : Type u} [CommRing A] (I : Ideal A)
    (C : Type (u + 1)) [SmallCategory C] (τ : GrothendieckTopology C) where
  cofiltered : IsCofiltered (AdmissibleModification I)
  thin : Quiver.IsThin (AdmissibleModification I)
  site : AdmissibleLimitSite I C τ
  coherent : site.IsCoherent
  isLimit : (site.cone coherent).IsLimit
  conservative : ∀ {G H : Sheaf τ (Type (u + 1))} (f : G ⟶ H),
    (∀ (Φ : τ.Point.{u + 1}), site.IsGeometricPoint Φ →
      IsIso ((Φ.sheafFiber (A := Type (u + 1))).map f)) → IsIso f

/-- A morphism on finite abutment filtrations whose associated graded morphism
is the stable-page morphism of spectral sequences. The chosen graded
identifications are part of the spectral presentation, not arbitrary maps.
Source: ILO XX 4.4, morphism of (**)lim, page 373.
(blueprint: def-per-admissible-modification-presentation-data). -/
structure AdmissibleFilteredAbutmentMap
    {E E' : E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1}}
    {H H' : ℕ → AddCommGrpCat.{u + 1}}
    (B : E.Abutment H) (B' : E'.Abutment H')
    (e : ∀ (n p q : ℕ) (_hpq : p + q = n),
      cokernel (C := AddCommGrpCat.{u + 1})
        (Subobject.ofLE (B.filtration n (p + 1)) (B.filtration n p)
        (B.filtration_succ_le n p)) ≅ E.pageInfinity (p, q))
    (e' : ∀ (n p q : ℕ) (_hpq : p + q = n),
      cokernel (C := AddCommGrpCat.{u + 1})
        (Subobject.ofLE (B'.filtration n (p + 1)) (B'.filtration n p)
        (B'.filtration_succ_le n p)) ≅ E'.pageInfinity (p, q))
    (φ : E ⟶ E') (f : ∀ n, H n ⟶ H' n) where
  step (n p : ℕ) : (B.filtration n p : AddCommGrpCat.{u + 1}) ⟶
    (B'.filtration n p : AddCommGrpCat.{u + 1})
  commutes (n p : ℕ) : step n p ≫ (B'.filtration n p).arrow =
    (B.filtration n p).arrow ≫ f n
  stepSquare (n p : ℕ) :
    Subobject.ofLE (B.filtration n (p + 1)) (B.filtration n p)
        (B.filtration_succ_le n p) ≫ step n p =
      step n (p + 1) ≫ Subobject.ofLE (B'.filtration n (p + 1)) (B'.filtration n p)
        (B'.filtration_succ_le n p)
  gradedCommutes (n p q : ℕ) (hpq : p + q = n) :
    cokernel.map (C := AddCommGrpCat.{u + 1}) _ _ (step n (p + 1)) (step n p) (stepSquare n p) ≫
        (e' n p q hpq).hom =
      (e n p q hpq).hom ≫ (φ.hom (p + q + 2 : ℕ) (by omega)).f (p, q)

/-- The spectral presentation, natural in the input abelian sheaf. Its coefficient
functors are colimits of the actual higher-direct-image exchange diagram. Only
convergence requires torsion. The filtration has precisely the first-quadrant
bounds encoded by `SpectralSequence.Abutment`.
Source: ILO XX 4.4, (**) and (**)lim, printed page 373.
(blueprint: def-per-admissible-modification-presentation-data). -/
structure AdmissibleSpectralPresentation {A : Type u} [CommRing A] {I : Ideal A}
    {C : Type (u + 1)} [SmallCategory C] {τ : GrothendieckTopology C}
    (P : AdmissibleLimitSite I C τ) {U : (Spec (CommRingCat.of A)).Opens}
    (j : AdmissibleOpenEmbeddings I U) where
  diagram (q : ℕ) : (AdmissibleModification I)ᵒᵖ ⥤
    (Sheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf τ AddCommGrpCat.{u + 1})
  finiteStage (q : ℕ) (J : AdmissibleModification I) :
    (diagram q).obj (op J) ≅ admissibleCoefficientFunctor P j q J
  transition (q : ℕ) {J K : AdmissibleModification I} (f : J ⟶ K)
      (F : Sheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (finiteStage q K).inv.app F ≫ ((diagram q).map f.op).app F ≫
        (finiteStage q J).hom.app F = admissibleCoefficientTransition P j q f F
  coefficient (q : ℕ) : Cocone (diagram q)
  coefficientIsColimit (q : ℕ) : IsColimit (coefficient q)
  spectralSequence : Sheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
    E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1}
  pageTwo (p q : ℕ) (F : Sheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((spectralSequence.obj F).page 2).X (p, q) ≅
      ((Sheaf.Γ τ AddCommGrpCat.{u + 1}).rightDerived p).obj
        ((coefficient q).pt.obj F)
  pageTwo_naturality (p q : ℕ)
      {F G : Sheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : F ⟶ G) :
    ((spectralSequence.map f).hom 2).f (p, q) ≫ (pageTwo p q G).hom =
      (pageTwo p q F).hom ≫
        ((Sheaf.Γ τ AddCommGrpCat.{u + 1}).rightDerived p).map ((coefficient q).pt.map f)
  abutment (F : Sheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1})
      (hF : F.IsTorsion) :
    (spectralSequence.obj F).Abutment (fun n ↦
      (Etale.cohomology AddCommGrpCat.{u + 1} U.toScheme n).obj
        ((DerivedCategory.singleFunctor _ 0).obj F))
  gradedIso (F : Sheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1})
      (hF : F.IsTorsion) (n p q : ℕ) (hpq : p + q = n) :
    cokernel (C := AddCommGrpCat.{u + 1})
      (Subobject.ofLE _ _ ((abutment F hF).filtration_succ_le n p)) ≅
      (spectralSequence.obj F).pageInfinity (p, q)
  filtration_naturality
      {F G : Sheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}}
      (hF : F.IsTorsion) (hG : G.IsTorsion) (f : F ⟶ G) :
    AdmissibleFilteredAbutmentMap (abutment F hF) (abutment G hG)
      (gradedIso F hF) (gradedIso G hG) (spectralSequence.map f)
      (fun n ↦ (Etale.cohomology AddCommGrpCat.{u + 1} U.toScheme n).map
        ((DerivedCategory.singleFunctor _ 0).map f))

/-- Extension of full-support centres to the completion, the corresponding
blowup morphisms over the completion map (not asserted cartesian: the completion
need not be flat, and the final Note only identifies the Rees algebras modulo every
power of I), the closed-fibre isomorphisms, and their compatible projections
to one common limit site. Cofinality is in the filtered direction.
Source: ILO XX 4.4, printed pages 373–374 and the final Note.
(blueprint: def-per-admissible-modification-presentation-data). -/
structure AdmissibleCompletionComparison {A : Type u} [CommRing A] (I : Ideal A)
    {C : Type (u + 1)} [SmallCategory C] {τ : GrothendieckTopology C}
    (P : AdmissibleLimitSite I C τ)
    (P' : AdmissibleLimitSite (admissibleCompletionIdeal I) C τ)
    {U : (Spec (CommRingCat.of A)).Opens}
    (j : AdmissibleOpenEmbeddings I U)
    (j' : AdmissibleOpenEmbeddings (admissibleCompletionIdeal I)
      (admissibleCompletionOpen I U)) where
  extension : AdmissibleModification I ⥤
    AdmissibleModification (admissibleCompletionIdeal I)
  extensionCentre (J : AdmissibleModification I) :
    (extension.obj J).val = J.val.map (algebraMap A (AdicCompletion I A))
  cofinal : extension.op.Final
  blowupMap (J : AdmissibleModification I) :
    AffineBlowup (extension.obj J).val ⟶ AffineBlowup J.val
  blowupSquare (J : AdmissibleModification I) :
    CommSq (blowupMap J) (AffineBlowup.toSpec (extension.obj J).val)
      (AffineBlowup.toSpec J.val) (admissibleCompletionBase I)
  blowupNaturality {J K : AdmissibleModification I} (f : J ⟶ K) :
    (extension.map f).hom.left ≫ blowupMap K = blowupMap J ≫ f.hom.left
  fibreIso (J : AdmissibleModification I) :
    (admissibleClosedFibres (admissibleCompletionIdeal I)).obj (extension.obj J) ≅
      (admissibleClosedFibres I).obj J
  fibreSquare (J : AdmissibleModification I) :
    CommSq (fibreIso J).hom
      (admissibleClosedImmersion (admissibleCompletionIdeal I) (extension.obj J))
      (admissibleClosedImmersion I J) (blowupMap J)
  fibreNaturality {J K : AdmissibleModification I} (f : J ⟶ K) :
    (admissibleClosedFibres (admissibleCompletionIdeal I)).map (extension.map f) ≫
        (fibreIso K).hom =
      (fibreIso J).hom ≫ (admissibleClosedFibres I).map f
  openSquare (J : AdmissibleModification I) :
    CommSq (admissibleCompletionOpenMap I U) (j'.j (extension.obj J))
      (j.j J) (blowupMap J)
  siteComparison (J : AdmissibleModification I) :
    (fibreIso J).hom.Etale ⋙ P'.inclusion (extension.obj J) ≅ P.inclusion J

/-- The finite-stage completion exchange on the common limit topos; it is the
canonical derived exchange, restricted to the closed fibres, with inverse images
transported by the specified closed-fibre isomorphism.
Source: ILO XX 4.4, (**)lim and final Note, pages 373–374.
(blueprint: def-per-admissible-modification-presentation-data). -/
def AdmissibleCompletionComparison.coefficientMap
    {A : Type u} [CommRing A] {I : Ideal A}
    {C : Type (u + 1)} [SmallCategory C] {τ : GrothendieckTopology C}
    {P : AdmissibleLimitSite I C τ}
    {P' : AdmissibleLimitSite (admissibleCompletionIdeal I) C τ}
    {U : (Spec (CommRingCat.of A)).Opens}
    {j : AdmissibleOpenEmbeddings I U}
    {j' : AdmissibleOpenEmbeddings (admissibleCompletionIdeal I)
      (admissibleCompletionOpen I U)}
    (c : AdmissibleCompletionComparison I P P' j j') (q : ℕ)
    (J : AdmissibleModification I)
    (F : Sheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (admissibleCoefficientFunctor P j q J).obj F ⟶
      (admissibleCoefficientFunctor P' j' q (c.extension.obj J)).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} (admissibleCompletionOpenMap I U)).obj F) :=
  admissibleLocalCoefficientMap (P.inverseAb J) (P'.inverseAb (c.extension.obj J))
    (c.openSquare J) (c.fibreSquare J)
    (admissibleInverseTransport τ (P'.inclusion (c.extension.obj J)) (P.inclusion J)
      (c.fibreIso J).hom (c.siteComparison J)) q F

end

end AlgebraicGeometry
