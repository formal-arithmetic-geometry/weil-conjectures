/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Exact symmetric monoidal inverse image on a site

Source: Stacks Project, Sites, Tag 00X6; Modules on Sites, Tag 03EL;
RefactorInstruction.tex, Section 4, prop:pX
(blueprint: lem-weil-pbc-left-exact-site-inverse-image-tensor).

Integer-module sheaves encode abelian sheaves by the unique integer action.
The comparison of their pullbacks follows from the sectionwise coinduction adjunction.
The tensor is the existing sheafification of the sectionwise module tensor, with the
canonical oplax comparison of sheaf pullback. Heterogeneous equalities fix the monoidal
structures without introducing file-local instances.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

-- Continuity is consumed by instance synthesis in the unchanged existential signature.
set_option linter.unusedVariables false in
/-- Source: Stacks, Tags 00X6 and 03EL; RefactorInstruction.tex Section 4 prop:pX
(blueprint: lem-weil-pbc-left-exact-site-inverse-image-tensor).

The Kan-extension inverse image, its exactness, and its normalized tensor structure.

Proof:
1. Use `isContinuous_toGrothendieck_of_pullbacksPreservedBy`: finite-limit
   preservation supplies the covering pullback comparisons, and `hUcover` supplies
   cover preservation. The constructed sheaf pullback has its canonical adjunction.
2. `flat_of_preservesFiniteLimits` makes the comma categories filtered.
   `preservesFiniteLimits_op_lan_of_flat` applies in the stated, unequal universes:
   filtered colimits are exact in sets and abelian groups. Composing with the
   limit-preserving sheaf inclusion and left-exact sheafification gives finite-limit
   preservation. The adjunctions give colimits. Abelian pushforward is additive
   sectionwise, so its left adjoint is additive and preserves short exact sequences.
3. On either site, forgetting module structure is left adjoint to sectionwise
   coinduction (`Sheaf.forget₂CoinduceAdj`). Compose these with the two pullback
   adjunctions. Their right adjoints agree because coinduction and precomposition
   commute. `Adjunction.leftAdjointUniq` gives the required module/abelian comparison.
4. Take the existing localized sheaf tensor and braiding. Filtered comma categories
   are sifted and tensoring in modules preserves their colimits, so
   `sheafPullbackMonoidal` supplies a strong monoidal structure whose oplax structure
   is definitionally the prescribed one. Transposing the braided axiom through the
   monoidal adjunction (`Adjunction.μ_comp_map_braiding`) proves braidedness.
-/
theorem siteInverseImage_tensor
    {C D : Type (u + 1)}
    [Category.{u} C] [Small.{u} C] [EssentiallySmall.{u + 1} C]
    [Category.{u} D] [Small.{u} D] [EssentiallySmall.{u + 1} D]
    (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (K : Precoverage D)
    [K.HasIsos] [K.IsStableUnderComposition]
    [K.IsStableUnderBaseChange] [K.HasPullbacks]
    [HasFiniteLimits C] (U : C ⥤ D) [PreservesFiniteLimits U]
    (hUcover : ∀ (X : C) (S : Presieve X), S ∈ J X → S.map U ∈ K (U.obj X))
    : ∃ (hU : U.IsContinuous J.toGrothendieck K.toGrothendieck),
      Nonempty ((sheafPullback U (Type (u + 1)) J.toGrothendieck K.toGrothendieck) ⊣
        (U.sheafPushforwardContinuous (Type (u + 1)) J.toGrothendieck K.toGrothendieck)) ∧
      PreservesFiniteLimits (sheafPullback U (Type (u + 1)) J.toGrothendieck K.toGrothendieck) ∧
      PreservesColimitsOfSize.{u + 1, u + 1} (sheafPullback U (Type (u + 1)) J.toGrothendieck
        K.toGrothendieck) ∧
      Nonempty ((sheafPullback U AddCommGrpCat.{u + 1} J.toGrothendieck K.toGrothendieck) ⊣
        (U.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J.toGrothendieck K.toGrothendieck)) ∧
      ∃ (_ : (sheafPullback U AddCommGrpCat.{u + 1} J.toGrothendieck K.toGrothendieck).Additive),
        PreservesFiniteLimits (sheafPullback U AddCommGrpCat.{u + 1} J.toGrothendieck
        K.toGrothendieck) ∧
        PreservesFiniteColimits (sheafPullback U AddCommGrpCat.{u + 1} J.toGrothendieck
        K.toGrothendieck) ∧
        (∀ S : ShortComplex (Sheaf J.toGrothendieck AddCommGrpCat.{u + 1}),
          S.ShortExact → (S.map (sheafPullback U AddCommGrpCat.{u + 1} J.toGrothendieck
        K.toGrothendieck) ).ShortExact) ∧
        Nonempty
          (sheafPullback U (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
              J.toGrothendieck K.toGrothendieck ⋙
            sheafCompose K.toGrothendieck
              (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}) ≅
            sheafCompose J.toGrothendieck
              (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}) ⋙
              sheafPullback U AddCommGrpCat.{u + 1}
                J.toGrothendieck K.toGrothendieck) ∧
        ∃ (mJ : MonoidalCategory (Sheaf J.toGrothendieck (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))))
          (mK : MonoidalCategory (Sheaf K.toGrothendieck (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))),
          mJ = Sheaf.monoidalCategory J.toGrothendieck (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) ∧
          mK = Sheaf.monoidalCategory K.toGrothendieck (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) ∧
          ∃ (bJ : BraidedCategory (Sheaf J.toGrothendieck (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))))
            (bK : BraidedCategory (Sheaf K.toGrothendieck (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))),
            HEq bJ (Sheaf.braidedCategory J.toGrothendieck (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) ∧
            HEq bK (Sheaf.braidedCategory K.toGrothendieck (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) ∧
            ∃ (mU : (sheafPullback U (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) J.toGrothendieck
        K.toGrothendieck).Monoidal),
              HEq mU.toOplaxMonoidal (sheafPullbackOplaxMonoidal U (ModuleCat.{u + 1} (ULift.{u + 1}
        ℤ)) J.toGrothendieck K.toGrothendieck) ∧
              Nonempty (sheafPullback U (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) J.toGrothendieck
        K.toGrothendieck).Braided := by
  let : J.PullbacksPreservedBy U := inferInstance
  let hU : U.IsContinuous J.toGrothendieck K.toGrothendieck :=
    U.isContinuous_toGrothendieck_of_pullbacksPreservedBy J K (by
      intro X R hR
      exact hUcover X R hR)
  let : U.IsContinuous J.toGrothendieck K.toGrothendieck := hU
  have : RepresentablyFlat U := flat_of_preservesFiniteLimits U
  have : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
    AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
  have : AB5OfSize.{u, u + 1} AddCommGrpCat.{u + 1} :=
    AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
  have hsetadj := sheafAdjunctionContinuous U (Type (u + 1)) J.toGrothendieck K.toGrothendieck
  have hsetlim : PreservesFiniteLimits
      (sheafPullback U (Type (u + 1)) J.toGrothendieck K.toGrothendieck) := by infer_instance
  have hsetcol : PreservesColimitsOfSize.{u + 1, u + 1}
      (sheafPullback U (Type (u + 1)) J.toGrothendieck K.toGrothendieck) :=
    hsetadj.leftAdjoint_preservesColimits
  let Fab := sheafPullback U AddCommGrpCat.{u + 1} J.toGrothendieck K.toGrothendieck
  let abadj := sheafAdjunctionContinuous U AddCommGrpCat.{u + 1}
    J.toGrothendieck K.toGrothendieck
  let : (U.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      J.toGrothendieck K.toGrothendieck).Additive := ⟨by
    intro X Y f g
    ext W
    rfl⟩
  have : Fab.Additive := abadj.left_adjoint_additive
  have : PreservesColimitsOfSize.{0, 0} Fab := abadj.leftAdjoint_preservesColimits
  have : PreservesFiniteColimits Fab := inferInstance
  have : PreservesFiniteLimits Fab := by dsimp [Fab]; infer_instance
  refine ⟨hU, ⟨hsetadj⟩, hsetlim, hsetcol, ⟨abadj⟩, inferInstance,
    inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro S hS
    exact hS.map_of_exact Fab
  · let a := (sheafAdjunctionContinuous U (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
        J.toGrothendieck K.toGrothendieck).comp
        (Sheaf.forget₂CoinduceAdj K.toGrothendieck (ULift.{u + 1} ℤ))
    let b := (Sheaf.forget₂CoinduceAdj J.toGrothendieck (ULift.{u + 1} ℤ)).comp abadj
    exact ⟨a.leftAdjointUniq b⟩
  · refine ⟨Sheaf.monoidalCategory _ _, Sheaf.monoidalCategory _ _, rfl, rfl,
      Sheaf.braidedCategory _ _, Sheaf.braidedCategory _ _, HEq.rfl, HEq.rfl, ?_⟩
    let : MonoidalCategory (Sheaf J.toGrothendieck
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) := Sheaf.monoidalCategory _ _
    let : MonoidalCategory (Sheaf K.toGrothendieck
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) := Sheaf.monoidalCategory _ _
    let : BraidedCategory (Sheaf J.toGrothendieck
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) := Sheaf.braidedCategory _ _
    let : BraidedCategory (Sheaf K.toGrothendieck
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) := Sheaf.braidedCategory _ _
    let m := sheafPullbackMonoidal U (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      J.toGrothendieck K.toGrothendieck
    refine ⟨m, HEq.rfl, ?_⟩
    exact ⟨{ braided := (sheafAdjunctionContinuous U
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) J.toGrothendieck
      K.toGrothendieck).μ_comp_map_braiding }⟩

-- Continuity is consumed by instance synthesis in the unchanged existential signature.
set_option linter.unusedVariables false in
/-- Source: Stacks, Tags 00X6 and 03EL; RefactorInstruction.tex Section 4 prop:pX
(blueprint: lem-weil-pbc-left-exact-site-inverse-image-tensor).

The adjunction-compatible composition and identity comparisons are monoidal.

Proof:
1. Establish continuity for both functors by covering pullbacks and then compose
   it. Their finite-limit preservation gives representable flatness. Use the
   canonical `sheafPullbackMonoidal` structures for both functors, their composite,
   and the identity; all four prescribed oplax equalities are reflexive.
2. Compose the pullback adjunctions. The source library proves that the canonical
   pushforward composition isomorphism is monoidal. Its conjugate gives an
   isomorphism from composite-site pullback to the iterated pullback, and
   `isMonoidal_conjugateEquiv_symm` proves that it is monoidal.
3. `unit_conjugateEquiv_symm` gives the composition unit equation. The canonical
   pushforward comparison for a strict composite has identity components, leaving
   exactly the iterated adjunction unit in the statement.
4. Conjugate the inverse of the monoidal pushforward identity comparison between
   the identity adjunction and the identity-site pullback adjunction. The same
   conjugate-unit equation, and its identity components, give the required unit
   equation. No componentwise description of pullback sections is assumed.
-/
theorem siteInverseImage_tensor_coherence
    {C D E : Type (u + 1)}
    [Category.{u} C] [Small.{u} C] [EssentiallySmall.{u + 1} C]
    [Category.{u} D] [Small.{u} D] [EssentiallySmall.{u + 1} D]
    [Category.{u} E] [Small.{u} E] [EssentiallySmall.{u + 1} E]
    (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition]
    [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (K : Precoverage D)
    [K.HasIsos] [K.IsStableUnderComposition]
    [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (T : Precoverage E)
    [T.HasIsos] [T.IsStableUnderComposition]
    [T.IsStableUnderBaseChange] [T.HasPullbacks]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (U : C ⥤ D) (V : D ⥤ E) [PreservesFiniteLimits U] [PreservesFiniteLimits V]
    (hUcover : ∀ (X : C) (S : Presieve X), S ∈ J X → S.map U ∈ K (U.obj X))
    (hVcover : ∀ (X : D) (S : Presieve X), S ∈ K X → S.map V ∈ T (V.obj X))
    : ∃ (hU : U.IsContinuous J.toGrothendieck K.toGrothendieck)
      (hV : V.IsContinuous K.toGrothendieck T.toGrothendieck)
      (hUV : (U ⋙ V).IsContinuous J.toGrothendieck T.toGrothendieck)
      (mJ : MonoidalCategory (Sheaf J.toGrothendieck (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))))
      (mK : MonoidalCategory (Sheaf K.toGrothendieck (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))))
      (mT : MonoidalCategory (Sheaf T.toGrothendieck (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))),
      mJ = Sheaf.monoidalCategory J.toGrothendieck (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) ∧
      mK = Sheaf.monoidalCategory K.toGrothendieck (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) ∧
      mT = Sheaf.monoidalCategory T.toGrothendieck (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) ∧
      ∃ (mU : (sheafPullback U (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) J.toGrothendieck
          K.toGrothendieck).Monoidal)
        (mV : (sheafPullback V (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) K.toGrothendieck
          T.toGrothendieck).Monoidal)
        (mUV : (sheafPullback (U ⋙ V) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) J.toGrothendieck
          T.toGrothendieck).Monoidal)
        (mId : (sheafPullback (𝟭 C) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) J.toGrothendieck
          J.toGrothendieck).Monoidal),
        HEq mU.toOplaxMonoidal (sheafPullbackOplaxMonoidal U (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
          J.toGrothendieck K.toGrothendieck) ∧
        HEq mV.toOplaxMonoidal (sheafPullbackOplaxMonoidal V (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
          K.toGrothendieck T.toGrothendieck) ∧
        HEq mUV.toOplaxMonoidal (sheafPullbackOplaxMonoidal (U ⋙ V) (ModuleCat.{u + 1} (ULift.{u +
          1} ℤ)) J.toGrothendieck T.toGrothendieck) ∧
        HEq mId.toOplaxMonoidal (sheafPullbackOplaxMonoidal (𝟭 C) (ModuleCat.{u + 1} (ULift.{u + 1}
          ℤ)) J.toGrothendieck J.toGrothendieck) ∧
        (∃ e : (sheafPullback (U ⋙ V) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) J.toGrothendieck
          T.toGrothendieck) ≅ (sheafPullback U (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
          J.toGrothendieck K.toGrothendieck) ⋙ (sheafPullback V (ModuleCat.{u + 1} (ULift.{u + 1}
          ℤ)) K.toGrothendieck T.toGrothendieck),
          NatTrans.IsMonoidal e.hom ∧
          ∀ F : Sheaf J.toGrothendieck (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)),
            (sheafAdjunctionContinuous (U ⋙ V) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
          J.toGrothendieck T.toGrothendieck).unit.app F ≫
              ((U ⋙ V).sheafPushforwardContinuous (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
          J.toGrothendieck T.toGrothendieck).map (e.hom.app F) =
            (sheafAdjunctionContinuous U (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) J.toGrothendieck
          K.toGrothendieck).unit.app F ≫
              (U.sheafPushforwardContinuous (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) J.toGrothendieck
          K.toGrothendieck).map
                ((sheafAdjunctionContinuous V (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) K.toGrothendieck
          T.toGrothendieck).unit.app ((sheafPullback U (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
          J.toGrothendieck K.toGrothendieck).obj F))) ∧
        (∃ e : (sheafPullback (𝟭 C) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) J.toGrothendieck
          J.toGrothendieck) ≅ 𝟭 (Sheaf J.toGrothendieck (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))),
          NatTrans.IsMonoidal e.hom ∧
          ∀ F : Sheaf J.toGrothendieck (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)),
            (sheafAdjunctionContinuous (𝟭 C) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) J.toGrothendieck
          J.toGrothendieck).unit.app F ≫
              ((𝟭 C).sheafPushforwardContinuous (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
          J.toGrothendieck J.toGrothendieck).map (e.hom.app F) =
            (Functor.sheafPushforwardContinuousId (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
          J.toGrothendieck).inv.app F) := by
  let : J.PullbacksPreservedBy U := inferInstance
  let : K.PullbacksPreservedBy V := inferInstance
  let hU : U.IsContinuous J.toGrothendieck K.toGrothendieck :=
    U.isContinuous_toGrothendieck_of_pullbacksPreservedBy J K (by
      intro X R hR
      exact hUcover X R hR)
  let hV : V.IsContinuous K.toGrothendieck T.toGrothendieck :=
    V.isContinuous_toGrothendieck_of_pullbacksPreservedBy K T (by
      intro X R hR
      exact hVcover X R hR)
  let : U.IsContinuous J.toGrothendieck K.toGrothendieck := hU
  let : V.IsContinuous K.toGrothendieck T.toGrothendieck := hV
  let hUV : (U ⋙ V).IsContinuous J.toGrothendieck T.toGrothendieck :=
    Functor.isContinuous_comp U V J.toGrothendieck K.toGrothendieck T.toGrothendieck
  let : (U ⋙ V).IsContinuous J.toGrothendieck T.toGrothendieck := hUV
  have : RepresentablyFlat U := flat_of_preservesFiniteLimits U
  have : RepresentablyFlat V := flat_of_preservesFiniteLimits V
  have : RepresentablyFlat (𝟭 C) := flat_of_preservesFiniteLimits (𝟭 C)
  let A := ModuleCat.{u + 1} (ULift.{u + 1} ℤ)
  let : MonoidalCategory (Sheaf J.toGrothendieck A) := Sheaf.monoidalCategory _ _
  let : MonoidalCategory (Sheaf K.toGrothendieck A) := Sheaf.monoidalCategory _ _
  let : MonoidalCategory (Sheaf T.toGrothendieck A) := Sheaf.monoidalCategory _ _
  let : BraidedCategory (Sheaf J.toGrothendieck A) := Sheaf.braidedCategory _ _
  let : BraidedCategory (Sheaf K.toGrothendieck A) := Sheaf.braidedCategory _ _
  let : BraidedCategory (Sheaf T.toGrothendieck A) := Sheaf.braidedCategory _ _
  let mU := sheafPullbackMonoidal U A J.toGrothendieck K.toGrothendieck
  let mV := sheafPullbackMonoidal V A K.toGrothendieck T.toGrothendieck
  let mUV := sheafPullbackMonoidal (U ⋙ V) A J.toGrothendieck T.toGrothendieck
  let mId := sheafPullbackMonoidal (𝟭 C) A J.toGrothendieck J.toGrothendieck
  refine ⟨hU, hV, hUV, Sheaf.monoidalCategory _ _, Sheaf.monoidalCategory _ _,
    Sheaf.monoidalCategory _ _, rfl, rfl, rfl, mU, mV, mUV, mId,
    HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, ?_, ?_⟩
  · let a := (sheafAdjunctionContinuous U A J.toGrothendieck K.toGrothendieck).comp
      (sheafAdjunctionContinuous V A K.toGrothendieck T.toGrothendieck)
    let b := sheafAdjunctionContinuous (U ⋙ V) A J.toGrothendieck T.toGrothendieck
    let e := (conjugateIsoEquiv a b).symm
      (Functor.sheafPushforwardContinuousComp' (Iso.refl (U ⋙ V)) A
        J.toGrothendieck K.toGrothendieck T.toGrothendieck)
    refine ⟨e, ?_, ?_⟩
    · exact isMonoidal_conjugateEquiv_symm a b _
    · intro F
      have h := unit_conjugateEquiv_symm a b
        (Functor.sheafPushforwardContinuousComp' (Iso.refl (U ⋙ V)) A
          J.toGrothendieck K.toGrothendieck T.toGrothendieck).hom F
      calc
        _ = a.unit.app F ≫
            (Functor.sheafPushforwardContinuousComp' (Iso.refl (U ⋙ V)) A
              J.toGrothendieck K.toGrothendieck T.toGrothendieck).hom.app
                ((sheafPullback U A J.toGrothendieck K.toGrothendieck ⋙
                  sheafPullback V A K.toGrothendieck T.toGrothendieck).obj F) := h.symm
        _ = _ := by
          change a.unit.app F ≫ _ = a.unit.app F
          have he : (Functor.sheafPushforwardContinuousComp' (Iso.refl (U ⋙ V)) A
              J.toGrothendieck K.toGrothendieck T.toGrothendieck).hom.app
                ((sheafPullback U A J.toGrothendieck K.toGrothendieck ⋙
                  sheafPullback V A K.toGrothendieck T.toGrothendieck).obj F) = 𝟙 _ := by
            ext X
            simp [Functor.sheafPushforwardContinuousComp',
              Functor.sheafPushforwardContinuousComp]
            rfl
          rw [he]
          exact Category.comp_id _
  · let a := Adjunction.id (C := Sheaf J.toGrothendieck A)
    let b := sheafAdjunctionContinuous (𝟭 C) A J.toGrothendieck J.toGrothendieck
    let e := (conjugateIsoEquiv a b).symm
      (Functor.sheafPushforwardContinuousId' (Iso.refl (𝟭 C)) A J.toGrothendieck).symm
    refine ⟨e, ?_, ?_⟩
    · have : NatTrans.IsMonoidal
          (Functor.sheafPushforwardContinuousId' (Iso.refl (𝟭 C)) A J.toGrothendieck).inv :=
        inferInstance
      exact isMonoidal_conjugateEquiv_symm a b
        (Functor.sheafPushforwardContinuousId' (Iso.refl (𝟭 C)) A J.toGrothendieck).inv
    · intro F
      have h := unit_conjugateEquiv_symm a b
        (Functor.sheafPushforwardContinuousId' (Iso.refl (𝟭 C)) A J.toGrothendieck).inv F
      calc
        _ = a.unit.app F ≫
            (Functor.sheafPushforwardContinuousId' (Iso.refl (𝟭 C)) A
              J.toGrothendieck).inv.app F := h.symm
        _ = _ := by
          change 𝟙 _ ≫ _ = _
          rw [Category.id_comp]
          ext X
          simp [Functor.sheafPushforwardContinuousId', Functor.sheafPushforwardContinuousId]
          rfl

end CategoryTheory
