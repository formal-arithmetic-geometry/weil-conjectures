/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.SixFunctors.ScalarSixDirectImage
public import Sheaf.SixFunctors.ScalarSixPullback
public import Sheaf.Paper.CompactificationCoherenceCocycle
public import Sheaf.Paper.ProEtaleProperOpenInterchange
import Sheaf.Paper.OpenExtensionConstructibleFiniteTor
import Sheaf.Paper.ConstantModelTorAmplitude
import all Sheaf.Paper.ProEtaleProperOpenInterchange
import all Sheaf.Paper.LocalizingLowerShriekCompositionModel
import Sheaf.SixFunctors.ScalarCompositeModelPasting
import Sheaf.SixFunctors.ScalarDenseRefinementSquare

/-! # Coefficient comparison for compactly supported direct image

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six/
det-prop-scalar-six-compact-support.md and its proof.
(blueprint: det-prop-scalar-six-compact-support).

Independence is the square for every map from a dense refinement to any model.
The common-refinement normalization of compactification_coherence_cocycle identifies
these squares with independence under every canonical model comparison. Composition
is written on the proper/open models defining its canonical compositor; independence
then transports this equation to any model of the composite.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The specified comparison T Rp_* j_! to Rp_* j_! T: the direct-image counit mate,
then Rp_* of the canonical open scalar isomorphism. No invertibility is assumed here.
Source: blueprint compact-support displayed composite
(blueprint: det-prop-scalar-six-compact-support). -/
def scalarCompactSupportMap {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) :
    (openImmersionLowerShriek Λ.X j).mapDerivedCategory ⋙
        RootCoordinateFace.lower Λ.X p ⋙ scalarSixChange a Y ⟶
      scalarSixChange a X ⋙ (openImmersionLowerShriek Λ'.X j).mapDerivedCategory ⋙
        RootCoordinateFace.lower Λ'.X p :=
  Functor.whiskerLeft (openImmersionLowerShriek Λ.X j).mapDerivedCategory
      (scalarDirectImageMate a p) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j).hom
      (RootCoordinateFace.lower Λ'.X p) ≫
    (Functor.associator _ _ _).hom

/-- The canonical open-extension compositor, obtained from the published exact open
adjunctions and the published pullback compositor by uniqueness of left adjoints.
Source: blueprint compact-support proof, Composition
(blueprint: det-prop-scalar-six-compact-support). -/
def scalarCompactSupportOpenComp (Λ : ScalarSixRing.{u})
    {X Z W : Scheme.{u}} (j : X ⟶ Z) (i : Z ⟶ W)
    [IsOpenImmersion j] [IsOpenImmersion i] :
    (openImmersionLowerShriek Λ.X j).mapDerivedCategory ⋙
        (openImmersionLowerShriek Λ.X i).mapDerivedCategory ≅
      (openImmersionLowerShriek Λ.X (j ≫ i)).mapDerivedCategory :=
  Adjunction.leftAdjointUniq
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X i))
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X (j ≫ i)).ofNatIsoRight
      (Functor.mapDerivedCategoryNatIso (upperStarComp Λ.X j i) ≪≫
        Functor.mapDerivedCategoryCompIso _ _))

/-- The pointwise canonical model compositor. Its input m is the proper/open interchange
at j_!K; the theorem below imposes its published identity-on-restriction normalization.
The remaining factors are the inverse derived proper compositor and exact open compositor.
Source: blueprint compact-support proof, Composition
(blueprint: det-prop-scalar-six-compact-support). -/
def scalarCompactSupportModelComp (Λ : ScalarSixRing.{u})
    {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    (cf : Compactification f) (cg : Compactification g)
    (cr : Compactification.BoundaryCompactification (cf.g ≫ cg.i))
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))
    (m : (openImmersionLowerShriek Λ.X cg.i).mapDerivedCategory.obj
        ((RootCoordinateFace.lower Λ.X cf.g).obj
          ((openImmersionLowerShriek Λ.X cf.i).mapDerivedCategory.obj K)) ⟶
      (RootCoordinateFace.lower Λ.X cr.obj.obj.g).obj
        ((openImmersionLowerShriek Λ.X cr.obj.obj.i).mapDerivedCategory.obj
          ((openImmersionLowerShriek Λ.X cf.i).mapDerivedCategory.obj K))) :
    (rightDerivedLowerShriekOfCompactification Λ.X cg).obj
        ((rightDerivedLowerShriekOfCompactification Λ.X cf).obj K) ⟶
      (RootCoordinateFace.lower Λ.X (cr.obj.obj.g ≫ cg.g)).obj
        ((openImmersionLowerShriek Λ.X (cf.i ≫ cr.obj.obj.i)).mapDerivedCategory.obj K) :=
  (RootCoordinateFace.lower Λ.X cg.g).map m ≫
    (RootCoordinateFace.lowerComp Λ.X cr.obj.obj.g cg.g).inv.app
      ((openImmersionLowerShriek Λ.X cr.obj.obj.i).mapDerivedCategory.obj
        ((openImmersionLowerShriek Λ.X cf.i).mapDerivedCategory.obj K)) ≫
    (RootCoordinateFace.lower Λ.X (cr.obj.obj.g ≫ cg.g)).map
      ((scalarCompactSupportOpenComp Λ cf.i cr.obj.obj.i).hom.app K)

-- Match the derived-category interfaces without expanding their localization models.
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

private theorem scalarCompactSupportMap_app {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (p : Z ⟶ Y) (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    (scalarCompactSupportMap a j p).app K = sfbScalarCompactComparison a j p K := by
  simp only [scalarCompactSupportMap, sfbScalarCompactComparison, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Category.id_comp, Category.comp_id]

private theorem leftAdjointUniq_ofNatIsoRight
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (e : R' ≅ R) :
    a.leftAdjointUniq (b.ofNatIsoRight e) = (conjugateIsoEquiv b a).symm e := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply (a.homEquiv _ _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]
  exact unit_conjugateEquiv_symm b a e.hom K

private theorem scalarCompactSupportOpenComp_eq (Λ : ScalarSixRing.{u})
    {X Z W : Scheme.{u}} (j : X ⟶ Z) (i : Z ⟶ W)
    [IsOpenImmersion j] [IsOpenImmersion i] :
    scalarCompactSupportOpenComp Λ j i = sfbScalarOpenComp Λ j i := by
  exact leftAdjointUniq_ofNatIsoRight
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X i))
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X (j ≫ i))
    (RootCoordinateFace.upperComp Λ.X j i)

private theorem scalarCompactSupportModelComp_eq (Λ : ScalarSixRing.{u})
    {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    (cf : Compactification f) (cg : Compactification g)
    (cr : Compactification.BoundaryCompactification (cf.g ≫ cg.i))
    (t : RootCoordinateFace.lower Λ.X cf.g ⋙
        (openImmersionLowerShriek Λ.X cg.i).mapDerivedCategory ⟶
      (openImmersionLowerShriek Λ.X cr.obj.obj.i).mapDerivedCategory ⋙
        RootCoordinateFace.lower Λ.X cr.obj.obj.g)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    scalarCompactSupportModelComp Λ cf cg cr K
        (t.app ((openImmersionLowerShriek Λ.X cf.i).mapDerivedCategory.obj K)) =
      sfbScalarModelCompositor Λ cf.i cf.g cg.i cg.g cr t K := by
  exact congrArg (fun e ↦
    (RootCoordinateFace.lower Λ.X cg.g).map
        (t.app ((openImmersionLowerShriek Λ.X cf.i).mapDerivedCategory.obj K)) ≫
      (RootCoordinateFace.lowerComp Λ.X cr.obj.obj.g cg.g).inv.app
        ((openImmersionLowerShriek Λ.X cr.obj.obj.i).mapDerivedCategory.obj
          ((openImmersionLowerShriek Λ.X cf.i).mapDerivedCategory.obj K)) ≫
      (RootCoordinateFace.lower Λ.X (cr.obj.obj.g ≫ cg.g)).map
        (e.hom.app K)) (scalarCompactSupportOpenComp_eq Λ cf.i cr.obj.obj.i)

attribute [local irreducible] scalarDirectImageMate
  derivedOpenImmersionShriekIso scalarCompactSupportMap scalarCompactSupportModelComp
  sfbScalarCompactComparison sfbScalarModelCompositor
  compositionInterchangeIsNormalized

set_option maxHeartbeats 2000000 in
-- The three coefficient squares compare several derived adjunction presentations.
/-- The compact-support coefficient comparison is invertible in Dctf, independent of
compactification, and compatible with geometric composition. The refinement square
expresses independence using the canonical comparison family's common-dense-refinement
normalization. The last square is the canonical compositor on a proper/open composition
model, for both coefficient rings; it therefore also gives the equation for any models.

Source: blueprint latest, det-prop-scalar-six-compact-support, displayed composite,
Independence and Composition (blueprint: det-prop-scalar-six-compact-support).

Proof:
1. Regard the compactification's middle scheme as a standing k-scheme via its
proper structural map. The open-extension constructibility/Tor-amplitude theorem
puts j_!K in Dctf. Apply scalarSixDirectImage to the proper map. Its coefficient
mate and Rp_* of the canonical open coefficient isomorphism are invertible.
The former theorem gives Dctf for the two intermediate endpoints; transport
the second endpoint along the open comparison using isomorphism invariance.
2. Apply scalarDenseRefinementSquare, whose argument factors an arbitrary
refinement through the schematic closure and pastes its two coefficient squares.
Unfolding the pointwise comparison identifies it with the second clause.
3. Put all proper/open composition models over k and check the standing and
quasi-compactness hypotheses. The proved normalized-interchange existence and
uniqueness theorem, together with exists_interchangeNatTrans, supplies natural
families. Uniqueness identifies their components with the given m and m'. Apply
scalarCompositeModelPasting. The open compositor defined by uniqueness of left
adjoints agrees with the conjugate compositor by the adjunction hom-equivalence
and its unit identity. Substitution gives the stated model-composition equation.
-/
theorem scalarSixCompactSupport
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (_ha : ListedCoefficientMap ell a)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) :
    (∀ (c : Compactification f.left)
      (K : ConstantModelConstructibleFiniteTor Λ.X X.left),
      IsIso ((scalarCompactSupportMap a c.i c.g).app K.obj) ∧
      (constantModelBoundedConstructible Λ'.X Y.left
          ((scalarSixChange a Y.left).obj
            ((rightDerivedLowerShriekOfCompactification Λ.X c).obj K.obj)) ∧
        DerivedCategory.finiteTorAmplitude _
          ((scalarSixChange a Y.left).obj
            ((rightDerivedLowerShriekOfCompactification Λ.X c).obj K.obj))) ∧
      (constantModelBoundedConstructible Λ'.X Y.left
          ((rightDerivedLowerShriekOfCompactification Λ'.X c).obj
            ((scalarSixChange a X.left).obj K.obj)) ∧
        DerivedCategory.finiteTorAmplitude _
          ((rightDerivedLowerShriekOfCompactification Λ'.X c).obj
            ((scalarSixChange a X.left).obj K.obj)))) ∧
    (∀ (c : Compactification.BoundaryCompactification f.left)
      (d : Compactification.DenseBoundaryCompactification f.left) (h : d.obj ⟶ c)
      (K : ConstantModelConstructibleFiniteTor Λ.X X.left),
      (scalarSixChange a Y.left).map
          (compactificationRefinementComponent Λ.X h K.obj) ≫
        (scalarCompactSupportMap a d.obj.obj.obj.i d.obj.obj.obj.g).app K.obj =
      (scalarCompactSupportMap a c.obj.obj.i c.obj.obj.g).app K.obj ≫
        compactificationRefinementComponent Λ'.X h
          ((scalarSixChange a X.left).obj K.obj)) ∧
    (∀ (S : Over (Spec (.of k)))
      [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
      (g : Y ⟶ S) (cf : Compactification f.left) (cg : Compactification g.left)
      (cr : Compactification.BoundaryCompactification (cf.g ≫ cg.i))
      [IsSchemeTheoreticallyDominant cr.obj.obj.i]
      (K : ConstantModelConstructibleFiniteTor Λ.X X.left)
      (m : (openImmersionLowerShriek Λ.X cg.i).mapDerivedCategory.obj
          ((RootCoordinateFace.lower Λ.X cf.g).obj
            ((openImmersionLowerShriek Λ.X cf.i).mapDerivedCategory.obj K.obj)) ⟶
        (RootCoordinateFace.lower Λ.X cr.obj.obj.g).obj
          ((openImmersionLowerShriek Λ.X cr.obj.obj.i).mapDerivedCategory.obj
            ((openImmersionLowerShriek Λ.X cf.i).mapDerivedCategory.obj K.obj)))
      (m' : (openImmersionLowerShriek Λ'.X cg.i).mapDerivedCategory.obj
          ((RootCoordinateFace.lower Λ'.X cf.g).obj
            ((openImmersionLowerShriek Λ'.X cf.i).mapDerivedCategory.obj
              ((scalarSixChange a X.left).obj K.obj))) ⟶
        (RootCoordinateFace.lower Λ'.X cr.obj.obj.g).obj
          ((openImmersionLowerShriek Λ'.X cr.obj.obj.i).mapDerivedCategory.obj
            ((openImmersionLowerShriek Λ'.X cf.i).mapDerivedCategory.obj
              ((scalarSixChange a X.left).obj K.obj))))
      (_hm : compositionInterchangeIsNormalized Λ.X cf.g cg.i cr
        ((openImmersionLowerShriek Λ.X cf.i).mapDerivedCategory.obj K.obj) m)
      (_hm' : compositionInterchangeIsNormalized Λ'.X cf.g cg.i cr
        ((openImmersionLowerShriek Λ'.X cf.i).mapDerivedCategory.obj
          ((scalarSixChange a X.left).obj K.obj)) m'),
      (scalarSixChange a S.left).map
          (scalarCompactSupportModelComp Λ cf cg cr K.obj m) ≫
        (scalarCompactSupportMap a (cf.i ≫ cr.obj.obj.i) (cr.obj.obj.g ≫ cg.g)).app K.obj =
      (scalarCompactSupportMap a cg.i cg.g).app
          ((rightDerivedLowerShriekOfCompactification Λ.X cf).obj K.obj) ≫
        (rightDerivedLowerShriekOfCompactification Λ'.X cg).map
          ((scalarCompactSupportMap a cf.i cf.g).app K.obj) ≫
        scalarCompactSupportModelComp Λ' cf cg cr ((scalarSixChange a X.left).obj K.obj) m') := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro c K
    let Z : Over (Spec (.of k)) := Over.mk (c.g ≫ Y.hom)
    have : LocallyOfFiniteType Z.hom := inferInstanceAs
      (LocallyOfFiniteType (c.g ≫ Y.hom))
    have : QuasiCompact Z.hom := inferInstanceAs (QuasiCompact (c.g ≫ Y.hom))
    have : IsSeparated Z.hom := inferInstanceAs (IsSeparated (c.g ≫ Y.hom))
    let j : X ⟶ Z := Over.homMk c.i (by
      change c.i ≫ c.g ≫ Y.hom = X.hom
      rw [← Category.assoc, ← c.comm, f.w])
    have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion c.i)
    let p : Z ⟶ Y := Over.homMk c.g
    obtain ⟨m, n, hcoh⟩ :=
      (DerivedCategory.exists_homologyConcentratedIn_iff_bounded K.obj).mpr K.property.1.1
    obtain ⟨b, e, htor⟩ := K.property.2
    have hopen := (openExtension_constructible_finiteTor ell k Λ.X j K
      m n b e hcoh htor).1
    obtain ⟨hi, hl, hr⟩ := (scalarSixDirectImage ell k a _ha p).1 _ hopen
    let J := (openImmersionLowerShriek Λ.X c.i).mapDerivedCategory.obj K.obj
    let d := (derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom c.i)
    have : IsIso ((scalarDirectImageMate a c.g).app J) := hi
    refine ⟨?_, hl, ?_⟩
    · simpa only [scalarCompactSupportMap, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
        Functor.associator_hom_app, Category.id_comp, Category.comp_id] using
        (inferInstance : IsIso ((scalarDirectImageMate a c.g).app J ≫
          (RootCoordinateFace.lower Λ'.X c.g).map (d.hom.app K.obj)))
    · have := (constantModelConstructibleFiniteTor_wellDefined Λ'.X Y.left).2.1
      have := (constantModelConstructibleFiniteTor_wellDefined Λ'.X Y.left).2.2.2.1
      let q := (RootCoordinateFace.lower Λ'.X c.g).mapIso (d.app K.obj)
      exact ⟨ObjectProperty.prop_of_iso _ q hr.1,
        ObjectProperty.prop_of_iso _ q hr.2⟩
  · intro c d h K
    let u := (scalarSixChange a Y.left).map
      (compactificationRefinementComponent Λ.X h K.obj)
    let v := compactificationRefinementComponent Λ'.X h
      ((scalarSixChange a X.left).obj K.obj)
    have hd := scalarCompactSupportMap_app a d.obj.obj.obj.i d.obj.obj.obj.g K.obj
    have hc := scalarCompactSupportMap_app a c.obj.obj.i c.obj.obj.g K.obj
    exact (congrArg (u ≫ ·) hd).trans
      ((scalarDenseRefinementSquare ell k a _ha f c d h K).trans
        (congrArg (· ≫ v) hc.symm))
  · intro S hSl hSq hSs g cf cg cr hcr K m m' hm hm'
    let B : Over (Spec (.of k)) := Over.mk (cf.g ≫ Y.hom)
    let C : Over (Spec (.of k)) := Over.mk (cg.g ≫ S.hom)
    have : LocallyOfFiniteType B.hom := inferInstanceAs
      (LocallyOfFiniteType (cf.g ≫ Y.hom))
    have : QuasiCompact B.hom := inferInstanceAs (QuasiCompact (cf.g ≫ Y.hom))
    have : IsSeparated B.hom := inferInstanceAs (IsSeparated (cf.g ≫ Y.hom))
    have : LocallyOfFiniteType C.hom := inferInstanceAs
      (LocallyOfFiniteType (cg.g ≫ S.hom))
    have : QuasiCompact C.hom := inferInstanceAs (QuasiCompact (cg.g ≫ S.hom))
    have : IsSeparated C.hom := inferInstanceAs (IsSeparated (cg.g ≫ S.hom))
    let j : X ⟶ B := Over.homMk cf.i (by
      change cf.i ≫ cf.g ≫ Y.hom = X.hom
      rw [← Category.assoc, ← cf.comm, f.w])
    let p : B ⟶ Y := Over.homMk cf.g
    let i : Y ⟶ C := Over.homMk cg.i (by
      change cg.i ≫ cg.g ≫ S.hom = Y.hom
      rw [← Category.assoc, ← cg.comm, g.w])
    let q : C ⟶ S := Over.homMk cg.g
    have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion cf.i)
    have : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion cg.i)
    have : IsProper p.left := inferInstanceAs (IsProper cf.g)
    have : IsProper q.left := inferInstanceAs (IsProper cg.g)
    have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
    have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
    have : IsLocallyNoetherian C.left := LocallyOfFiniteType.isLocallyNoetherian C.hom
    have : QuasiCompact j.left := inferInstance
    have : QuasiCompact i.left := inferInstance
    let crOver : cr.obj.obj.Z.Over (Spec (.of k)) := ⟨cr.obj.obj.g ≫ C.hom⟩
    have : LocallyOfFiniteType (cr.obj.obj.Z ↘ Spec (.of k)) := inferInstanceAs
      (LocallyOfFiniteType (cr.obj.obj.g ≫ C.hom))
    have : QuasiCompact (cr.obj.obj.Z ↘ Spec (.of k)) := inferInstanceAs
      (QuasiCompact (cr.obj.obj.g ≫ C.hom))
    have : IsSeparated (cr.obj.obj.Z ↘ Spec (.of k)) := inferInstanceAs
      (IsSeparated (cr.obj.obj.g ≫ C.hom))
    have hgOver : cr.obj.obj.g.IsOver (Spec (.of k)) := ⟨rfl⟩
    have hiOver : cr.obj.obj.i.IsOver (Spec (.of k)) := ⟨by
      change cr.obj.obj.i ≫ cr.obj.obj.g ≫ C.hom = B.hom
      rw [← Category.assoc, ← cr.obj.obj.comm]
      change (cf.g ≫ cg.i) ≫ (cg.g ≫ S.hom) = cf.g ≫ Y.hom
      rw [Category.assoc, ← Category.assoc cg.i, ← cg.comm, g.w]⟩
    set_option backward.isDefEq.respectTransparency.types true in
    set_option backward.isDefEq.respectTransparency true in
    have hτ := exists_interchangeNatTrans Λ.X cf.g cg.i cr
      (properOpenInterchange_normalized Λ.X cf.g cg.i cr)
    let t := hτ.choose
    have ht := hτ.choose_spec
    set_option backward.isDefEq.respectTransparency.types true in
    set_option backward.isDefEq.respectTransparency true in
    have hτ' := exists_interchangeNatTrans Λ'.X cf.g cg.i cr
      (properOpenInterchange_normalized Λ'.X cf.g cg.i cr)
    let t' := hτ'.choose
    have ht' := hτ'.choose_spec
    set_option backward.isDefEq.respectTransparency.types true in
    set_option backward.isDefEq.respectTransparency true in
    have em : m = t.app ((openImmersionLowerShriek Λ.X cf.i).mapDerivedCategory.obj K.obj) :=
      (properOpenInterchange_normalized Λ.X cf.g cg.i cr _).choose_spec.2 _ hm |>.trans
        ((properOpenInterchange_normalized Λ.X cf.g cg.i cr _).choose_spec.2 _ (ht _)).symm
    set_option backward.isDefEq.respectTransparency.types true in
    set_option backward.isDefEq.respectTransparency true in
    have em' : m' = t'.app ((openImmersionLowerShriek Λ'.X cf.i).mapDerivedCategory.obj
        ((scalarSixChange a X.left).obj K.obj)) :=
      (properOpenInterchange_normalized Λ'.X cf.g cg.i cr _).choose_spec.2 _ hm' |>.trans
        ((properOpenInterchange_normalized Λ'.X cf.g cg.i cr _).choose_spec.2 _ (ht' _)).symm
    set_option backward.isDefEq.respectTransparency.types true in
    set_option backward.isDefEq.respectTransparency true in
    subst m
    set_option backward.isDefEq.respectTransparency.types true in
    set_option backward.isDefEq.respectTransparency true in
    subst m'
    set_option backward.isDefEq.respectTransparency.types true in
    set_option backward.isDefEq.respectTransparency true in
    have hpaste := @scalarCompositeModelPasting ell _ k _ _ _ Λ Λ' a _ha X B Y C S
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j p i q _ _ _ _ _ _ cr
      crOver _ _ _ hiOver hgOver hcr t ht t' ht' K
    have hmcomp := scalarCompactSupportModelComp_eq Λ cf cg cr t K.obj
    have hmcomp' := scalarCompactSupportModelComp_eq Λ' cf cg cr t'
      ((scalarSixChange a X.left).obj K.obj)
    have hmodelLeft := congrArg (fun z ↦ (scalarSixChange a S.left).map z ≫
      (scalarCompactSupportMap a (cf.i ≫ cr.obj.obj.i)
        (cr.obj.obj.g ≫ cg.g)).app K.obj) hmcomp
    have hmodelRight := congrArg (fun z ↦
      (scalarCompactSupportMap a cg.i cg.g).app
          ((rightDerivedLowerShriekOfCompactification Λ.X cf).obj K.obj) ≫
        (rightDerivedLowerShriekOfCompactification Λ'.X cg).map
          ((scalarCompactSupportMap a cf.i cf.g).app K.obj) ≫ z) hmcomp'
    set_option backward.isDefEq.respectTransparency.types true in
    set_option backward.isDefEq.respectTransparency true in
    have hleft := congrArg
      ((scalarSixChange a S.left).map
        (sfbScalarModelCompositor Λ cf.i cf.g cg.i cg.g cr t K.obj) ≫ ·)
      (scalarCompactSupportMap_app a (cf.i ≫ cr.obj.obj.i)
        (cr.obj.obj.g ≫ cg.g) K.obj)
    set_option backward.isDefEq.respectTransparency.types true in
    set_option backward.isDefEq.respectTransparency true in
    have hright₁ := congrArg (fun v ↦ v ≫
        (rightDerivedLowerShriekOfCompactification Λ'.X cg).map
          ((scalarCompactSupportMap a cf.i cf.g).app K.obj) ≫
        sfbScalarModelCompositor Λ' cf.i cf.g cg.i cg.g cr t'
          ((scalarSixChange a X.left).obj K.obj))
      (scalarCompactSupportMap_app a cg.i cg.g
        ((rightDerivedLowerShriekOfCompactification Λ.X cf).obj K.obj))
    set_option backward.isDefEq.respectTransparency.types true in
    set_option backward.isDefEq.respectTransparency true in
    have hright₂ := congrArg (fun v ↦
        sfbScalarCompactComparison a cg.i cg.g
          ((rightDerivedLowerShriekOfCompactification Λ.X cf).obj K.obj) ≫
        (rightDerivedLowerShriekOfCompactification Λ'.X cg).map v ≫
        sfbScalarModelCompositor Λ' cf.i cf.g cg.i cg.g cr t'
          ((scalarSixChange a X.left).obj K.obj))
      (scalarCompactSupportMap_app a cf.i cf.g K.obj)
    set_option backward.isDefEq.respectTransparency.types true in
    set_option backward.isDefEq.respectTransparency true in
    exact hmodelLeft.trans (hleft.trans
      (hpaste.trans ((hmodelRight.trans (hright₁.trans hright₂)).symm)))

end AlgebraicGeometry.ProEtale.CondensedRing
