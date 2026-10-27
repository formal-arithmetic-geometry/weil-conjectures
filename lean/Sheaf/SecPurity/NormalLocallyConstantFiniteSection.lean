/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.NormalGeometricCoverUniverseDescent
import Sheaf.AlgebraicGeometry.ProEtaleLocalSystemRepresentability

/-!
# Finite-cover sections of locally constant pro-étale sheaves on a normal scheme

Source: Bhatt--Scholze, *The pro-étale topology for schemes*, Lemma 7.3.9 (Loc_X = Cov_X),
pp. 67--68, and the proof of Lemma 7.4.10, p. 71 (blueprint:
lem-a1-normal-locally-constant-finite-section).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

private theorem nonempty_schemeUniverseLift (X : Scheme.{u}) [Nonempty X] :
    Nonempty (schemeUniverseLift.{u, u + 1} X) := by
  let x : X := Classical.arbitrary X
  let j : CostructuredArrow Scheme.Spec X :=
    CostructuredArrow.mk (X.fromSpecResidueField x)
  have := schemeUniverseDiagram_hasColimit.{u, u + 1} X
  let y : Spec (.of (ULift.{u + 1} (X.residueField x))) := Classical.arbitrary _
  exact ⟨colimit.ι (schemeUniverseDiagram.{u, u + 1} X) j y⟩

private noncomputable def pullbackRestrictionIso (X : Scheme.{u}) (U : X.ProEt)
    (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) :
    (Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom) (Type (u + 1))
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology U.left)).obj F ≅
        (Scheme.proEtaleSetRestriction X U).obj F := by
  let a := (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.hom
    U.prop trivial).op.whiskerLeft (Type (u + 1))
  let b := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom).op.lanAdjunction
    (Type (u + 1))
  let e := (a.leftAdjointUniq b).app F.obj
  exact ((presheafToSheaf (Scheme.ProEt.topology U.left) (Type (u + 1))).mapIso e).symm ≪≫
    (sheafificationIso ((Scheme.proEtaleSetRestriction X U).obj F)).symm

private theorem proEtaleCover_coversTop (X : Scheme.{u})
    (𝒰 : Scheme.Cover Scheme.proetalePrecoverage X) :
    (Scheme.ProEt.topology X).CoversTop
      (fun i ↦ MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme) (𝒰.f i)
        (Scheme.proetalePrecoverage_le_precoverage_weaklyEtale X 𝒰.mem₀ ⟨i⟩)) := by
  let U (i : 𝒰.I₀) : X.ProEt :=
    MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme) (𝒰.f i)
      (Scheme.proetalePrecoverage_le_precoverage_weaklyEtale X 𝒰.mem₀ ⟨i⟩)
  let T : X.ProEt := Scheme.ProEt.mk (𝟙 X)
  let f (i : 𝒰.I₀) : U i ⟶ T := MorphismProperty.Over.homMk (𝒰.f i) (by exact Category.comp_id _)
  have ht : IsTerminal T := IsTerminal.ofUniqueHom
    (fun V ↦ MorphismProperty.Over.homMk V.hom (by exact Category.comp_id _)) (by
      intro V g
      apply MorphismProperty.Over.Hom.ext
      have hg := MorphismProperty.Over.w g
      exact (Category.comp_id g.left).symm.trans hg)
  apply ((Scheme.ProEt.topology X).coversTop_iff_of_isTerminal T ht U).mpr
  apply (Scheme.ProEt.topology X).superset_covering _
    (Precoverage.generate_mem_toGrothendieck (J := Scheme.ProEt.precoverage X) (by
      change (Presieve.ofArrows U f).map
        (Scheme.ProEt.forget X ⋙ Over.forget X) ∈ Scheme.proetalePrecoverage X
      rw [Presieve.map_ofArrows]
      exact 𝒰.mem₀))
  apply (Sieve.generate_le_iff _ _).mpr
  intro V g hg
  obtain ⟨i⟩ := hg
  exact ⟨i, ⟨𝟙 (U i)⟩⟩

/-- A locally nonempty locally constant pro-étale sheaf on a normal connected Noetherian scheme
has a section after a finite étale surjective cover.

Source: Bhatt--Scholze, *The pro-étale topology for schemes*, Lemma 7.3.9 and the proof of
Lemma 7.4.10 (blueprint: lem-a1-normal-locally-constant-finite-section).
Proof: shrink the index of the trivializing cover and identify inverse-image restriction
with restriction by composition using uniqueness of left adjoints. Lemma 7.3.9 represents
F over the canonical universe enlargement of X. Local nonemptiness supplies a morphism
from a nonempty enlarged cover member, so the representing geometric covering is nonempty.
Apply normalGeometricCover_universeDescent: the normal-base component argument of
Lemma 7.4.10 and finite-algebra descent give a finite etale surjection Y over the original
X and a morphism from its enlargement into the representing scheme. Etaleness makes Y
a pro-etale site object. The inverse representing isomorphism at Y turns this morphism
into the required section. -/
theorem exists_finiteEtale_section_of_normal_locallyConstant
    (X : Scheme.{u}) [Nonempty X] [ConnectedSpace X] [IsLocallyNoetherian X]
    [CompactSpace X]
    (hnormal : ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (hlocal : ∃ (𝒰 : Scheme.Cover Scheme.proetalePrecoverage X),
      ∀ i : 𝒰.I₀, ∃ (S : Type (u + 1)),
        Nonempty ((Functor.sheafPullbackConstruction.sheafPullback
          (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (𝒰.f i)) (Type (u + 1))
            (Scheme.ProEt.topology X) (Scheme.ProEt.topology (𝒰.X i))).obj F ≅
          (constantSheaf (Scheme.ProEt.topology (𝒰.X i)) (Type (u + 1))).obj S))
    (hnonempty : ∃ (𝒱 : Scheme.Cover Scheme.proetalePrecoverage X),
      ∀ j : 𝒱.I₀, Nonempty (F.obj.obj
        (op (MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme) (𝒱.f j)
          (Scheme.proetalePrecoverage_le_precoverage_weaklyEtale X 𝒱.mem₀ ⟨j⟩))))) :
    ∃ (Y : Scheme.ProEt X), IsFinite Y.hom ∧ Etale Y.hom ∧ Surjective Y.hom ∧
      Nonempty (F.obj.obj (op Y)) := by
  classical
  obtain ⟨𝒰₀, h𝒰₀⟩ := hlocal
  let 𝒰 := 𝒰₀.restrictIndexOfSmall.{u + 1}
  have h𝒰 : ∀ i : 𝒰.I₀, ∃ S : Type (u + 1), Nonempty
      ((Functor.sheafPullbackConstruction.sheafPullback
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (𝒰.f i)) (Type (u + 1))
          (Scheme.ProEt.topology X) (Scheme.ProEt.topology (𝒰.X i))).obj F ≅
        (constantSheaf (Scheme.ProEt.topology (𝒰.X i)) (Type (u + 1))).obj S) := by
    intro i
    exact h𝒰₀ _
  let U (i : 𝒰.I₀) : X.ProEt :=
    MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme) (𝒰.f i)
      (Scheme.proetalePrecoverage_le_precoverage_weaklyEtale X 𝒰.mem₀ ⟨i⟩)
  let S (i : 𝒰.I₀) : Type (u + 1) := (h𝒰 i).choose
  have htriv (i : 𝒰.I₀) : Nonempty
      (((Scheme.proEtaleSetRestriction X (U i)).obj F) ≅
        (constantSheaf (Scheme.ProEt.topology (U i).left) (Type (u + 1))).obj (S i)) := by
    obtain ⟨e⟩ := (h𝒰 i).choose_spec
    exact ⟨(pullbackRestrictionIso X (U i) F).symm ≪≫ e⟩
  obtain ⟨Z, q, hq, ⟨e⟩, hval⟩ := Scheme.proEtale_localSystem_representability
    X F 𝒰.I₀ U (proEtaleCover_coversTop X 𝒰) S htriv
  obtain ⟨𝒱, h𝒱⟩ := hnonempty
  have hsurj := (Scheme.presieve₀_mem_precoverage_iff 𝒱.toPreZeroHypercover).mp
    (Scheme.proetalePrecoverage_le_fpqcPrecoverage X 𝒱.mem₀).2
  obtain ⟨j, v, hv⟩ := hsurj.1 (Classical.arbitrary X)
  let V : X.ProEt :=
    MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme) (𝒱.f j)
      (Scheme.proetalePrecoverage_le_precoverage_weaklyEtale X 𝒱.mem₀ ⟨j⟩)
  let f : (Scheme.proEtaleUniverseLiftToOver X).obj V ⟶ Over.mk q :=
    e.hom.app (op V) (h𝒱 j).some
  have : Nonempty V.left := ⟨v⟩
  have : Nonempty (schemeUniverseLift.{u, u + 1} V.left) :=
    nonempty_schemeUniverseLift V.left
  have : Nonempty Z := by
    unfold Scheme.proEtaleUniverseLiftToOver at f
    refine ⟨f.left (Classical.arbitrary (schemeUniverseLift.{u, u + 1} V.left))⟩
  obtain ⟨Y, p, hp, he, hs, i, hi⟩ :=
    normalGeometricCover_universeDescent hnormal q hq hval
  have : Etale p := he
  let Y' : X.ProEt := Scheme.ProEt.mk p
  refine ⟨Y', hp, he, hs, ⟨e.inv.app (op Y') ?_⟩⟩
  unfold Scheme.proEtaleUniverseLiftToOver
  exact Over.homMk i hi

end AlgebraicGeometry
