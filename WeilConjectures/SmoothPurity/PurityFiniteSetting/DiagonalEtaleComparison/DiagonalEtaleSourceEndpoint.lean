/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalEtaleComparison.DiagonalEtaleFactorization
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionRestrictionEtaleFunctorial
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.SectionRestriction.PuritySectionBaseComparisonLaws
import WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence

/-! # The source endpoint of the Cartesian-centre span

Source: diagonal-dualizing proof Step 1; orientation-charts proof Step 3.
(blueprint: lem-pur-diagonal-etale-span-source-endpoint).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.DiagonalEtaleComparison
open SectionRestriction
open AlgebraicGeometry.ProEtale.FiniteEtaleNormalization

attribute [local irreducible] Etale.upperStar Etale.lowerStar
  Etale.rightDerivedUpperShriek Etale.rightDerivedUpperShriekAdjunction
  Functor.mapDerivedCategory Functor.rightDerivedFunctor conjugateIsoEquiv

private def rawRestriction (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} {d : ℕ} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (X' X : Pair B d)
    (a : X'.V ⟶ X.V) [Etale a] [IsSeparated a] [QuasiCompact a]
    (ha : a ≫ X.g = X'.g) (hs : X'.s ≫ a = X.s) :
    sectionEtale P aB X' ≅ sectionEtale P aB X :=
  letI := SmoothOfRelativeDimension.smooth d X.g
  letI := SmoothOfRelativeDimension.smooth d X'.g
  letI : B.Over (Spec (.of P.field.k)) := ⟨aB⟩
  letI : LocallyOfFiniteType (B ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aB)
  letI : QuasiCompact (B ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aB)
  letI : X.V.Over (Spec (.of P.field.k)) := ⟨X.g ≫ aB⟩
  letI : X'.V.Over (Spec (.of P.field.k)) := ⟨X'.g ≫ aB⟩
  letI : X.g.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : X'.g.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : a.IsOver (Spec (.of P.field.k)) := ⟨by
    change a ≫ (X.g ≫ aB) = X'.g ≫ aB
    rw [← Category.assoc, ha]⟩
  letI : LocallyOfFiniteType (X.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (X.g ≫ aB))
  letI : QuasiCompact (X.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (X.g ≫ aB))
  letI : LocallyOfFiniteType (X'.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (X'.g ≫ aB))
  letI : QuasiCompact (X'.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (X'.g ≫ aB))
  letI := Dnc.compactifiable P X.g aB
  letI := Dnc.compactifiable P X'.g aB
  (AlgebraicGeometry.ProEtale.FiniteEtaleNormalization.pull P X'.s).mapIso
      ((AlgebraicGeometry.ProEtale.FiniteEtaleNormalization.congr P X'.g
          (a ≫ X.g) ha.symm).app (𝟙_ _) ≪≫
        AlgebraicGeometry.ProEtale.FiniteEtaleNormalization.sourceEtale P a X.g) ≪≫
    ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      X'.s a X.s hs.symm).app _).symm

private theorem rawRestriction_comp (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] {d : ℕ}
    (X'' X' X : Pair B d)
    (b : X''.V ⟶ X'.V) [Etale b] [IsSeparated b] [QuasiCompact b]
    (a : X'.V ⟶ X.V) [Etale a] [IsSeparated a] [QuasiCompact a]
    (ha : a ≫ X.g = X'.g) (hb : b ≫ X'.g = X''.g)
    (hs : X'.s ≫ a = X.s) (ht : X''.s ≫ b = X'.s) :
    rawRestriction P aB X'' X (b ≫ a)
        (by rw [Category.assoc, ha, hb])
        (by rw [← Category.assoc, ht, hs]) =
      rawRestriction P aB X'' X' b hb ht ≪≫ rawRestriction P aB X' X a ha hs := by
  let := SmoothOfRelativeDimension.smooth d X.g
  let := SmoothOfRelativeDimension.smooth d X'.g
  let := SmoothOfRelativeDimension.smooth d X''.g
  let : B.Over (Spec (.of P.field.k)) := ⟨aB⟩
  let : LocallyOfFiniteType (B ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aB)
  let : QuasiCompact (B ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aB)
  let : X.V.Over (Spec (.of P.field.k)) := ⟨X.g ≫ aB⟩
  let : X'.V.Over (Spec (.of P.field.k)) := ⟨X'.g ≫ aB⟩
  let : X''.V.Over (Spec (.of P.field.k)) := ⟨X''.g ≫ aB⟩
  let : X.g.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : X'.g.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : X''.g.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : a.IsOver (Spec (.of P.field.k)) := ⟨by
    change a ≫ (X.g ≫ aB) = X'.g ≫ aB
    rw [← Category.assoc, ha]⟩
  let : b.IsOver (Spec (.of P.field.k)) := ⟨by
    change b ≫ (X'.g ≫ aB) = X''.g ≫ aB
    rw [← Category.assoc, hb]⟩
  let : LocallyOfFiniteType (X.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (X.g ≫ aB))
  let : QuasiCompact (X.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (X.g ≫ aB))
  let : LocallyOfFiniteType (X'.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (X'.g ≫ aB))
  let : QuasiCompact (X'.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (X'.g ≫ aB))
  let : LocallyOfFiniteType (X''.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (X''.g ≫ aB))
  let : QuasiCompact (X''.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (X''.g ≫ aB))
  have he := source_comp_eq P b a X.g X'.g X''.g
    ha.symm hb.symm
  exact section_comp P.Coefficient a b X.s X'.s X''.s
    hs.symm ht.symm (omega P X.g) (omega P X'.g) (omega P X''.g)
    _ _ _ he

private def rawLocality (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} {d : ℕ} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (X' X : Pair B d)
    (a : X'.V ⟶ X.V) [Etale a] [IsSeparated a] [QuasiCompact a]
    (ha : a ≫ X.g = X'.g) (hs : X'.s ≫ a = X.s) :
    sectionEtale P aB X ≅ sectionEtale P aB X' :=
  letI := SmoothOfRelativeDimension.smooth d X.g
  letI := SmoothOfRelativeDimension.smooth d X'.g
  letI := P.noetherian aB
  letI := P.noetherian (X.g ≫ aB)
  letI := P.noetherian (X'.g ≫ aB)
  letI := Dnc.compactifiable P X.g aB
  letI := Dnc.compactifiable P X'.g aB
  (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      X'.s a X.s hs.symm).app _ ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) X'.s).leftDerivedFunctor.mapIso
      (Etale.sectionStructuralLocalityIso P.Coefficient a X.g X'.g ha)

private theorem rawRestriction_locality (P : PurityFiniteSetting.{u})
    {B : Scheme.{u}} {d : ℕ} (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] (X' X : Pair B d)
    (a : X'.V ⟶ X.V) [Etale a] [IsSeparated a] [QuasiCompact a]
    (ha : a ≫ X.g = X'.g) (hs : X'.s ≫ a = X.s) :
    rawRestriction P aB X' X a ha hs = (rawLocality P aB X' X a ha hs).symm := by
  let := SmoothOfRelativeDimension.smooth d X.g
  let := SmoothOfRelativeDimension.smooth d X'.g
  let : B.Over (Spec (.of P.field.k)) := ⟨aB⟩
  let : LocallyOfFiniteType (B ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aB)
  let : QuasiCompact (B ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aB)
  let : X.V.Over (Spec (.of P.field.k)) := ⟨X.g ≫ aB⟩
  let : X'.V.Over (Spec (.of P.field.k)) := ⟨X'.g ≫ aB⟩
  let : X.g.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : X'.g.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : a.IsOver (Spec (.of P.field.k)) := ⟨by
    change a ≫ (X.g ≫ aB) = X'.g ≫ aB
    rw [← Category.assoc, ha]⟩
  let : LocallyOfFiniteType (X.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (X.g ≫ aB))
  let : QuasiCompact (X.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (X.g ≫ aB))
  let : LocallyOfFiniteType (X'.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (X'.g ≫ aB))
  let : QuasiCompact (X'.V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (X'.g ≫ aB))
  have he := sourceEtale_locality_congr P a X.g X'.g ha
  dsimp only [rawRestriction, rawLocality]
  rw [he]
  simp only [Iso.trans_symm, Functor.mapIso_symm]

private theorem locality_tensorMate (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : Etale.EtaleCompactSupportNormalization A)
    {U X B : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian B]
    (a : U ⟶ X) [Etale a] [IsSeparated a] [QuasiCompact a]
    (g : X ⟶ B) [HasCompactification g] [HasCompactification (a ≫ g)] :
    Etale.sectionStructuralLocalityIso A a g (a ≫ g) rfl =
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) a).app _ ≪≫
        (Etale.tensorMateEtalePrecompLocalityIso A N a g).app (𝟙_ _) := by
  let adjA := Etale.derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) a inferInstance
  let adjF := Etale.rightDerivedUpperShriekAdjunction A g
  let adjG := Etale.rightDerivedUpperShriekAdjunction A (a ≫ g)
  let H := Etale.existsUnique_etaleAmbientAdjointLocalityIso A a g
    (HasCompactification.compactification g) (HasCompactification.compactification (a ≫ g))
    (Etale.rightDerivedUpperShriek A g)
    (Etale.rightDerivedUpperShriek A (a ≫ g)) adjF adjG
  have he : Classical.choose H = Etale.tensorMateEtalePrecompLocalityIso A N a g := by
    apply ((Classical.choose_spec H).2 _ ?_).symm
    intro N' K
    have hN : Etale.etaleAmbientLeftComparison A N' a g
        (HasCompactification.compactification g)
        (HasCompactification.compactification (a ≫ g)) =
      Etale.etaleAmbientLeftComparison A N a g
        (HasCompactification.compactification g)
        (HasCompactification.compactification (a ≫ g)) := by
      unfold Etale.etaleAmbientLeftComparison
      rw [Etale.normalization_comparison_eq A N' N]
    rw [hN]
    have hc := conjugateEquiv_counit (adjA.comp adjF) adjG
      (Etale.etaleAmbientLeftComparison A N a g
        (HasCompactification.compactification g)
        (HasCompactification.compactification (a ≫ g))).inv K
    simpa only [Etale.tensorMateEtalePrecompLocalityIso, Iso.symm_hom,
      conjugateIsoEquiv_apply_inv, derivedAdj_eq, Adjunction.comp_counit_app,
      adjA, adjF, adjG, Etale.rightDerivedLowerShriek, Functor.comp_obj] using hc
  change _ ≪≫ (Classical.choose H).app _ = _
  rw [he]
  rfl

private theorem locality_tensorMate_congr (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : Etale.EtaleCompactSupportNormalization A)
    {U X B : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian B]
    (a : U ⟶ X) [Etale a] [IsSeparated a] [QuasiCompact a]
    (g : X ⟶ B) [HasCompactification g] [HasCompactification (a ≫ g)]
    (g' : U ⟶ B) [HasCompactification g'] (hg : a ≫ g = g') :
    Etale.sectionStructuralLocalityIso A a g g' hg =
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) a).app _ ≪≫
        (Etale.tensorMateEtalePrecompLocalityIso A N a g).app (𝟙_ _) ≪≫
        eqToIso (show Etale.dualizingComplex A (a ≫ g) =
            Etale.dualizingComplex A g' from by cases hg; rfl) := by
  subst g'
  simpa only [eqToIso_refl, Iso.trans_refl] using locality_tensorMate A N a g

/-- The source endpoint is normalized etale locality followed by inverse smooth exchange.
This statement concerns only section invariants; it contains no deformation comparison.
Source: diagonal-dualizing Step 1; orientation-charts Step 3.

Proof: express each restriction as the inverse of the section pullback of its
counit-normalized structural locality. The equality of the two ambient composites
in D.factorization and composition coherence cancel the restriction to the common
neighbourhood. The remaining map is locality for sourceLift. For every N its
compact-support left comparison is the same: normalization_comparison_eq identifies
the proper-support/sum comparisons. Uniqueness of right-adjoint conjugacy therefore
identifies its locality with tensorMateEtalePrecompLocalityIso for N. Pull back by
the diagonal and insert the equality sourceLift followed by the projection equals
the source projection. The remaining baseComparison inverse is exactly the inverse
smooth section exchange in sourceOrdinary. Conjugate by the canonical site
comparisons, using their naturality to cancel the intermediate comparisons. This
is the displayed formula, including the empty source and dimension zero.
(blueprint: lem-pur-diagonal-etale-span-source-endpoint). -/
theorem span_source_endpoint (P : PurityFiniteSetting.{u}) {U X Y : Scheme.{u}}
    (d : ℕ) (g : X ⟶ Y) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d g]
    (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ X) [Etale e] (w : e ≫ g = h)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (D : CentreSpan d g h e w) :
    (restriction P (h ≫ aY) D.left).symm ≪≫ restriction P (h ≫ aY) D.right ≪≫
        (baseComparison P (g ≫ aY) (h ≫ aY) (baseSquare d g e)).symm =
      source P d g h aY e w N := by
  have hgeom := sourceLift_geometry d g h e w
  let := hgeom.1
  let := hgeom.2.1
  let := hgeom.2.2.1
  let A := diagonalPair d h
  let B := basePair d g e
  let t := sourceLift d g h e w
  have ht : t ≫ B.g = A.g := pullback.lift_snd _ _ _
  have hs : A.s ≫ t = B.s := hgeom.2.2.2
  have hc := rawRestriction_comp P (h ≫ aY) D.pair A B D.left.map t
    ht D.left.over_eq hs D.left.section_eq
  have hc' : rawRestriction P (h ≫ aY) D.pair B D.right.map
      D.right.over_eq D.right.section_eq =
    rawRestriction P (h ≫ aY) D.pair A D.left.map D.left.over_eq D.left.section_eq ≪≫
      rawRestriction P (h ≫ aY) A B t ht hs := by
    simpa only [t, D.factorization] using hc
  let := SmoothOfRelativeDimension.smooth d A.g
  let := SmoothOfRelativeDimension.smooth d B.g
  let := P.noetherian aY
  let := P.noetherian (h ≫ aY)
  let := P.noetherian (g ≫ aY)
  let := P.noetherian (B.g ≫ h ≫ aY)
  let := P.noetherian (A.g ≫ h ≫ aY)
  let := P.noetherian (pullback.fst h h ≫ h ≫ aY)
  let := P.noetherian (pullback.snd (pullback.fst g g) e ≫ h ≫ aY)
  let := Dnc.compactifiable P B.g (h ≫ aY)
  let := Dnc.compactifiable P A.g (h ≫ aY)
  let : HasCompactification (t ≫ B.g) := HasCompactification.of_eq ht.symm
  have hsOrd : rawRestriction P (h ≫ aY) A B t ht hs ≪≫
      (sectionBaseComparison P (g ≫ aY) (h ≫ aY) (baseSquare d g e)).symm =
      sourceOrdinary P d g h aY e w N := by
    rw [rawRestriction_locality]
    dsimp only [rawLocality]
    rw [locality_tensorMate_congr P.Coefficient N t B.g A.g ht]
    simp only [sourceOrdinary, sectionBaseComparison, baseSquare, basePair, diagonalPair,
      A, B, t, Iso.trans_symm, Functor.mapIso_trans, Iso.trans_assoc,
      Etale.dualizingComplex]
  have hl : restrictionEtale P (h ≫ aY) D.left =
      rawRestriction P (h ≫ aY) D.pair A D.left.map D.left.over_eq
        D.left.section_eq := rfl
  have hr : restrictionEtale P (h ≫ aY) D.right =
      rawRestriction P (h ≫ aY) D.pair B D.right.map D.right.over_eq
        D.right.section_eq := rfl
  have hk := congrArg (fun q ↦
    Dnc.sourceComparison P d A.g (h ≫ aY) A.s ≪≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso q ≪≫
      (Dnc.pullComparison P e (sectionEtale P (g ≫ aY) (diagonalPair d g))).symm ≪≫
      (OrientationRefinement.pull P e).mapIso
        (Dnc.sourceComparison P d (diagonalPair d g).g (g ≫ aY)
          (diagonalPair d g).s).symm) hsOrd
  dsimp only [restriction, baseComparison, source]
  rw [hl, hr, hc']
  simpa only [Iso.trans_symm, Iso.symm_symm_eq, Functor.mapIso_symm,
    Functor.mapIso_trans, Iso.trans_assoc, Iso.symm_self_id_assoc,
    Iso.self_symm_id_assoc, sectionBaseComparison, A, diagonalPair, sectionEtale,
    invariant, OrientationRefinement.pull] using hk

end WeilConjectures.PurityFiniteSetting.DiagonalEtaleComparison
