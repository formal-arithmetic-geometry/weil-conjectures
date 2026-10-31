/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Blowup.BaseChange
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.InducedCategory

/-! # Pointed diagrams of corresponding admissible blowups

Source: ILO, Travaux de Gabber, XX 4.4, pp.373--374, and XX 2.4.4, p.365;
Stacks, Tags 04HX and 04GU
(blueprint: def-per-admissible-completion-point-system).

The index contains every finitely generated ideal with the specified vanishing locus.
Its arrows are actual domination morphisms over Spec A. A point system includes the
corresponding completed domination maps and the canonical strict-local ring diagrams.
The equations identifying the ring maps with pointed strict-local pullbacks are part of
this presentation: the transition maps and the comparison cannot be arbitrary ring maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- All full-support admissible ideals, with arrows oriented towards a dominating blowup.
Equality of radicals is equivalent to equality of Zariski vanishing loci.
Source: ILO XX 4.4, p.373
(blueprint: def-per-admissible-completion-point-system). -/
abbrev AdmissibleBlowupIndex {A : Type u} [CommRing A] (I : Ideal A) :=
  (InducedCategory (Over (Spec (.of A)))
    (fun J : {J : Ideal A // J.FG ∧ J.radical = I.radical} ↦
      Over.mk (AffineBlowup.toSpec J.1)))ᵒᵖ

/-- The ideal at an index of the domination category.
Source: ILO XX 4.4, p.373
(blueprint: def-per-admissible-completion-point-system). -/
def AdmissibleBlowupIndex.ideal {A : Type u} [CommRing A] {I : Ideal A}
    (J : AdmissibleBlowupIndex I) : Ideal A :=
  J.unop.1

/-- The actual domination morphism underlying an index arrow.
Source: ILO XX 4.4, p.373
(blueprint: def-per-admissible-completion-point-system). -/
noncomputable def AdmissibleBlowupIndex.domination {A : Type u} [CommRing A] {I : Ideal A}
    {J K : AdmissibleBlowupIndex I} (f : J ⟶ K) :
    AffineBlowup K.ideal ⟶ AffineBlowup J.ideal :=
  f.unop.hom.left

/-- The canonical pullback on strict-local rings for compatible geometric points.
The equality transport only identifies two names for the same target geometric point.
Source: Stacks 04GU; ILO XX 2.4.4, p.365
(blueprint: def-per-admissible-completion-point-system). -/
noncomputable def pointedStrictLocalRingMap {X Y : Scheme.{u}} (f : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (x : Spec (.of Ω) ⟶ X) (h : y ≫ f = x) :
    Scheme.strictHenselizationRing x ⟶ Scheme.strictHenselizationRing y :=
  eqToHom (congrArg Scheme.strictHenselizationRing h.symm) ≫
    Spec.preimage (Scheme.strictHenselizationMap f y)

/-- The canonical A-map to the strict-local ring of a geometric point over Spec A.
Source: ILO XX 4.4, pp.373--374; Stacks 04HX
(blueprint: def-per-admissible-completion-point-system). -/
noncomputable def strictLocalBaseRingMap {A : Type u} [CommRing A]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    CommRingCat.of A ⟶ Scheme.strictHenselizationRing y :=
  Spec.preimage (Scheme.strictHenselizationStructuralMap y ≫ p)

/-- A compatible choice of geometric points and its canonical ring diagrams on all
corresponding full-support admissible blowups. The completed maps lie over Spec of the
completion and intertwine the original domination maps. The ring maps are specified by
the existing canonical pointed strict-local map, rather than just by existence.
The identity, composition, naturality and base equations present these canonical maps
as diagrams and cocones; they are coherence data, not quotient-isomorphism assumptions.
Source: ILO XX 4.4, pp.373--374, XX 2.4.4, p.365; Stacks 04HX, 04GU
(blueprint: def-per-admissible-completion-point-system). -/
structure AdmissibleCompletionPointSystem {A : Type u} [CommRing A] (I : Ideal A)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] where
  /-- Original geometric points. -/
  point : ∀ J : AdmissibleBlowupIndex I, Spec (.of Ω) ⟶ AffineBlowup J.ideal
  /-- The points lie on the closed fibre. -/
  closed : ∀ J : AdmissibleBlowupIndex I,
    ∃ z : Spec (.of Ω) ⟶ Spec (.of (A ⧸ I)),
      point J ≫ AffineBlowup.toSpec J.ideal =
        z ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  /-- Corresponding geometric points, with the same ambient residue closure. -/
  completedPoint : ∀ J : AdmissibleBlowupIndex I,
    Spec (.of Ω) ⟶ AffineBlowup (J.ideal.map (algebraMap A (AdicCompletion I A)))
  /-- The original points form a compatible system. -/
  point_naturality : ∀ {J K : AdmissibleBlowupIndex I} (f : J ⟶ K),
    point K ≫ (AdmissibleBlowupIndex.domination f) = point J
  /-- Compatibility with the canonical comparison of blowups. -/
  comparison_point : ∀ J : AdmissibleBlowupIndex I,
    completedPoint J ≫ AffineBlowup.hom (algebraMap A (AdicCompletion I A)) rfl = point J
  /-- Domination maps on completed blowups. -/
  completedDomination : ∀ {J K : AdmissibleBlowupIndex I} (_f : J ⟶ K),
    AffineBlowup (K.ideal.map (algebraMap A (AdicCompletion I A))) ⟶
      AffineBlowup (J.ideal.map (algebraMap A (AdicCompletion I A)))
  /-- Completed domination is over the completed base. -/
  completed_over : ∀ {J K : AdmissibleBlowupIndex I} (f : J ⟶ K),
    completedDomination f ≫ AffineBlowup.toSpec (J.ideal.map (algebraMap A (AdicCompletion I A))) =
      AffineBlowup.toSpec (K.ideal.map (algebraMap A (AdicCompletion I A)))
  /-- Completed domination intertwines the original domination. -/
  completed_comparison : ∀ {J K : AdmissibleBlowupIndex I} (f : J ⟶ K),
    completedDomination f ≫ AffineBlowup.hom (algebraMap A (AdicCompletion I A)) rfl =
      AffineBlowup.hom (algebraMap A (AdicCompletion I A)) rfl ≫
        AdmissibleBlowupIndex.domination f
  /-- The completed geometric points form the corresponding compatible system. -/
  completed_point_naturality : ∀ {J K : AdmissibleBlowupIndex I} (f : J ⟶ K),
    completedPoint K ≫ completedDomination f = completedPoint J
  /-- The original ring diagram, with its exact objects specified below. -/
  rings : AdmissibleBlowupIndex I ⥤ CommRingCat.{u}
  /-- The completed ring diagram, with its exact objects specified below. -/
  completedRings : AdmissibleBlowupIndex I ⥤ CommRingCat.{u}
  /-- Original diagram objects are the recorded strict henselizations. -/
  rings_obj : ∀ J, rings.obj J = Scheme.strictHenselizationRing (point J)
  /-- Completed diagram objects are the recorded strict henselizations. -/
  completedRings_obj : ∀ J,
    completedRings.obj J = Scheme.strictHenselizationRing (completedPoint J)
  /-- Original arrows are the canonical strict-local pullbacks. -/
  rings_map : ∀ {J K : AdmissibleBlowupIndex I} (f : J ⟶ K),
    rings.map f = eqToHom (rings_obj J) ≫
      pointedStrictLocalRingMap (AdmissibleBlowupIndex.domination f)
        (point K) (point J) (point_naturality f) ≫
        eqToHom (rings_obj K).symm
  /-- Completed arrows are the canonical strict-local pullbacks. -/
  completedRings_map : ∀ {J K : AdmissibleBlowupIndex I} (f : J ⟶ K),
    completedRings.map f = eqToHom (completedRings_obj J) ≫
      pointedStrictLocalRingMap (completedDomination f) (completedPoint K)
        (completedPoint J) (completed_point_naturality f) ≫ eqToHom (completedRings_obj K).symm
  /-- The comparison of diagrams. -/
  comparison : rings ⟶ completedRings
  /-- Its components are the actual canonical strict-local comparison maps. -/
  comparison_app : ∀ J, comparison.app J = eqToHom (rings_obj J) ≫
    pointedStrictLocalRingMap (AffineBlowup.hom (algebraMap A (AdicCompletion I A)) rfl)
      (completedPoint J) (point J) (comparison_point J) ≫ eqToHom (completedRings_obj J).symm
  /-- The A-algebra structure of the original ring diagram. -/
  base : (Functor.const (AdmissibleBlowupIndex I)).obj (CommRingCat.of A) ⟶ rings
  /-- Its components are the actual structural ring maps. -/
  base_app : ∀ J, base.app J =
    strictLocalBaseRingMap (AffineBlowup.toSpec J.ideal) (point J) ≫
      eqToHom (rings_obj J).symm

namespace AdmissibleCompletionPointSystem

/-- The original strict-local colimit B.
Source: ILO XX 4.4, p.373
(blueprint: def-per-admissible-completion-point-system). -/
noncomputable def sourceRing {A : Type u} [CommRing A] {I : Ideal A}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (S : AdmissibleCompletionPointSystem I Ω) :
    CommRingCat.{u} := colimit S.rings

/-- The completed strict-local colimit C.
Source: ILO XX 4.4, p.373
(blueprint: def-per-admissible-completion-point-system). -/
noncomputable def targetRing {A : Type u} [CommRing A] {I : Ideal A}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (S : AdmissibleCompletionPointSystem I Ω) :
    CommRingCat.{u} := colimit S.completedRings

/-- The induced, canonical homomorphism u : B → C.
Source: ILO XX 4.4, pp.373--374
(blueprint: def-per-admissible-completion-point-system). -/
noncomputable def colimitMap {A : Type u} [CommRing A] {I : Ideal A}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (S : AdmissibleCompletionPointSystem I Ω) :
    S.sourceRing ⟶ S.targetRing := colimMap S.comparison

/-- The structural map A → B, descending the canonical stage structural maps.
Source: ILO XX 4.4, p.373
(blueprint: def-per-admissible-completion-point-system). -/
noncomputable def sourceBaseMap {A : Type u} [CommRing A] {I : Ideal A}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (S : AdmissibleCompletionPointSystem I Ω)
    (hI : I.FG) : CommRingCat.of A ⟶ S.sourceRing :=
  S.base.app (op ⟨I, hI, rfl⟩) ≫ colimit.ι S.rings (op ⟨I, hI, rfl⟩)

end AdmissibleCompletionPointSystem

end AlgebraicGeometry
