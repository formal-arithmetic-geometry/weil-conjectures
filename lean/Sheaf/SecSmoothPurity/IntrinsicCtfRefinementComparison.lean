/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Paper.EtaleProEtaleCoefficientTransport
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import WeilConjectures.Compactification.RefinementCategory
import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

/-! # Canonical compactification change on intrinsic finite-Tor inputs

Source: Stacks Tags 0F7I, 0F7J and 099R; latest blueprint,
sk-lem-sp-reduction-exceptional.proof.md, Locality paragraph
(blueprint: def-sp-intrinsic-ctf-refinement-comparison).

This is the unique descent of the published etale common-refinement comparison through
the specified site/realization isomorphisms. The uniqueness condition determines all
components, so the data chosen below are fixed up to equality.

## Main definitions

* `refinementModel`: the specified etale comparison in intrinsic origin coordinates.
* `IsCanonicalRefinement`: the all-origin component normalization.
* `refinement`: its unique natural-isomorphism descent to intrinsic Dctf.

## Main statements

* `canonicalRefinement_existsUnique`: existence and uniqueness of this descent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.OpenInverseTranspose

private theorem descendIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (S : A ⥤ B) [S.Full] (I : C ⥤ B) (F G : B ⥤ D)
    (e : S ⋙ F ≅ S ⋙ G) (h : ∀ Q, S.essImage (I.obj Q)) :
    ∃! ρ : I ⋙ F ≅ I ⋙ G, ∀ Q E (s : S.obj E ≅ I.obj Q),
      ρ.hom.app Q = F.map s.inv ≫ e.hom.app E ≫ G.map s.hom := by
  classical
  let E := fun Q ↦ (h Q).witness
  let t := fun Q ↦ (h Q).getIso
  let a := fun Q ↦ F.mapIso (t Q).symm ≪≫ e.app (E Q) ≪≫ G.mapIso (t Q)
  have natural (Q Q' : C) (f : I.obj Q ⟶ I.obj Q') :
      F.map f ≫ (a Q').hom = (a Q).hom ≫ G.map f := by
    have hn := e.hom.naturality (S.preimage ((t Q).hom ≫ f ≫ (t Q').inv))
    dsimp at hn
    rw [S.map_preimage] at hn
    have hn' := congrArg (fun k ↦ F.map (t Q).inv ≫ k ≫ G.map (t Q').hom) hn
    simpa [a, Functor.map_comp, Category.assoc] using hn'
  let ρ : I ⋙ F ≅ I ⋙ G := NatIso.ofComponents a (fun f ↦ natural _ _ (I.map f))
  have normalized : ∀ Q E' (s : S.obj E' ≅ I.obj Q),
      ρ.hom.app Q = F.map s.inv ≫ e.hom.app E' ≫ G.map s.hom := by
    intro Q E' s
    have hn := e.hom.naturality (S.preimage (s.hom ≫ (t Q).inv))
    dsimp at hn
    rw [S.map_preimage] at hn
    have hn' := congrArg (fun k ↦ F.map s.inv ≫ k ≫ G.map (t Q).hom) hn
    simpa [ρ, a, Functor.map_comp, Category.assoc] using hn'
  refine ⟨ρ, normalized, ?_⟩
  intro σ hσ
  apply Iso.ext
  apply NatTrans.ext
  funext Q
  exact (hσ Q (E Q) (t Q)).trans (normalized Q (E Q) (t Q)).symm

/-- The specified site inverse image followed by coefficient realization, in the
intrinsic presentation used by the finite-Tor categories. Source: Stacks 099R, 00YV
(blueprint: def-sp-intrinsic-ctf-refinement-comparison). -/
abbrev site (R : Type u) [CommRing R] [Finite R] (T : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) T).mapDerivedCategory ⋙
    (sfIntrinsicDerivedEquivalence T R).functor

/-- Actual compact support at an etale origin, using the recorded support realization
and specified proper/open site comparison. Source: Stacks 099R and 0F7J
(blueprint: def-sp-intrinsic-ctf-refinement-comparison). -/
def supportSite (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (E : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} R)))) :
    (reductionCompactSupport R c.i c.g).obj ((site R X).obj E.obj) ≅
      (site R Y).obj ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) c).obj E.obj) :=
  (CoefficientCompatibility.supportPresentation R c).app
      ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) X).mapDerivedCategory.obj
        E.obj) ≪≫
    (sfIntrinsicDerivedEquivalence Y R).functor.mapIso
      ((compactSupportSiteComparison (ULift.{u + 1, u} R) c).app E)

/-- Canonical compactification change at an etale origin. The middle factor is the
published common-refinement comparison, not a freely chosen isomorphism.
Source: Stacks 0F7I, 0F7J
(blueprint: def-sp-intrinsic-ctf-refinement-comparison). -/
def refinementModel (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f)
    (E : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} R)))) :=
  supportSite R c E ≪≫
    (site R Y).mapIso
      ((Etale.rightDerivedLowerShriekOfCompactificationIso (ULift.{u + 1, u} R) c d).app
        E.obj) ≪≫ (supportSite R d E).symm

/-- The normalization of a change of compactification on the whole intrinsic Dctf
category. All etale origins and all identifications with the given input are tested.
Source: Stacks 0F7I and 099R; blueprint Locality
(blueprint: def-sp-intrinsic-ctf-refinement-comparison). -/
def IsCanonicalRefinement (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c d : Compactification f)
    (ρ : (spFiniteConstructibleTor X R).ι ⋙ reductionCompactSupport R c.i c.g ≅
      (spFiniteConstructibleTor X R).ι ⋙ reductionCompactSupport R d.i d.g) : Prop :=
  ∀ (Q : spFiniteConstructibleTorCategory X R)
    (E : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} R))))
    (s : (site R X).obj E.obj ≅ Q.obj),
    ρ.hom.app Q = (reductionCompactSupport R c.i c.g).map s.inv ≫
      (refinementModel R c d E).hom ≫ (reductionCompactSupport R d.i d.g).map s.hom

/-- The canonical comparison on arbitrary finite-Tor inputs is uniquely determined by
its etale-origin normalization. Source: Stacks 099R, 0F7I; blueprint Locality
(blueprint: def-sp-intrinsic-ctf-refinement-comparison).

Proof: the finite-ring constructible-origin theorem supplies a bounded constructible
etale antecedent for every intrinsic input, and hence a bounded-below antecedent. Define
its component by conjugating refinementModel with the antecedent isomorphism. Full
faithfulness of comparison identifies any two antecedents and all their morphisms.
Naturality of the site comparisons and the etale compactification change then proves
independence of the antecedent, naturality, and the stated normalization for every s.
The reverse compactification change gives its inverse. Any normalized comparison has
these components, so natural-transformation extensionality proves uniqueness. -/
theorem canonicalRefinement_existsUnique (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c d : Compactification f) :
    ∃! ρ : (spFiniteConstructibleTor X R).ι ⋙ reductionCompactSupport R c.i c.g ≅
      (spFiniteConstructibleTor X R).ι ⋙ reductionCompactSupport R d.i d.g,
      IsCanonicalRefinement R c d ρ := by
  classical
  let V := DerivedCategory.Plus.ι ⋙ site R X
  let F := reductionCompactSupport R c.i c.g
  let G := reductionCompactSupport R d.i d.g
  have : V.Full := by
    let C := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) X
    have : (DerivedCategory.Plus.ι ⋙ C.mapDerivedCategory).Full :=
      ⟨fun {K L} f ↦ by
        obtain ⟨g, hg⟩ :=
          (bijective_comparisonUpperStar_mapDerivedCategory_map K.obj L.obj L.property).2 f
        exact ⟨ObjectProperty.homMk g, hg⟩⟩
    exact inferInstanceAs
      ((DerivedCategory.Plus.ι ⋙ C.mapDerivedCategory) ⋙
        (sfIntrinsicDerivedEquivalence X R).functor).Full
  have origins (Q : spFiniteConstructibleTorCategory X R) : V.essImage Q.obj := by
    have h := ((finiteRing_constructibleDerived_origin X R).2.2.1 Q.obj).2
      ⟨Q.property.2.1, Q.property.1⟩
    obtain ⟨L, ⟨s⟩⟩ := h
    have hL : DerivedCategory.TStructure.t.plus L.obj := by
      obtain ⟨a, b, _, hv⟩ := L.property.2
      exact ⟨a, (DerivedCategory.isGE_iff L.obj a).2 fun i hi ↦ hv i (Or.inl hi)⟩
    let e : finiteCoefficientIntrinsicDerivedComparison X R ≅ site R X :=
      Functor.mapDerivedCategoryCompIso
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) X)
        (finiteCoefficientIntrinsicRealization X R)
    exact ⟨⟨L.obj, hL⟩, ⟨(e.app L.obj).symm ≪≫ s⟩⟩
  let support (k : Compactification f) :
      V ⋙ reductionCompactSupport R k.i k.g ≅
        (DerivedCategory.Plus.ι ⋙
          Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) k) ⋙ site R Y :=
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _ (CoefficientCompatibility.supportPresentation R k)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (compactSupportSiteComparison (ULift.{u + 1, u} R) k) _ ≪≫
      Functor.associator _ _ _
  let e : V ⋙ F ≅ V ⋙ G := support c ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft DerivedCategory.Plus.ι
        (Etale.rightDerivedLowerShriekOfCompactificationIso
          (ULift.{u + 1, u} R) c d)) (site R Y) ≪≫ (support d).symm
  have component (E : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} R)))) :
      e.hom.app E = (refinementModel R c d E).hom := by
    simp only [Functor.comp_obj, Iso.trans_assoc, Functor.isoWhiskerLeft_trans,
      Functor.isoWhiskerLeft_twice, site, Iso.self_symm_id_assoc, Iso.trans_symm,
      Iso.symm_symm_eq, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      NatTrans.comp_app, ObjectProperty.ι_obj, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerRight_app,
      Functor.comp_map, Category.comp_id, Category.id_comp, refinementModel, supportSite,
      Iso.app_hom, Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_inv, e, support]
    exact Category.id_comp _
  obtain ⟨ρ, hρ, unique⟩ := descendIso V (spFiniteConstructibleTor X R).ι F G e origins
  refine ⟨ρ, ?_, ?_⟩
  · intro Q E s
    rw [hρ Q E s, component]
  · intro σ hσ
    apply unique σ
    intro Q E s
    rw [component]
    exact hσ Q E s

/-- The uniquely normalized comparison on Dctf; only the proof of its unique
normalization is postponed, and no object is selected from bare existence.
Source: Stacks 0F7I, 099R
(blueprint: def-sp-intrinsic-ctf-refinement-comparison). -/
def refinement (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c d : Compactification f) :
    (spFiniteConstructibleTor X R).ι ⋙ reductionCompactSupport R c.i c.g ≅
      (spFiniteConstructibleTor X R).ι ⋙ reductionCompactSupport R d.i d.g :=
  (canonicalRefinement_existsUnique R c d).exists.choose

end AlgebraicGeometry.ProEtale.OpenInverseTranspose
