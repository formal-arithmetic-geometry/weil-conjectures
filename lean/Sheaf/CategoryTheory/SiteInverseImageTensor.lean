/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.CategoryTheory.SiteContinuousPushforwardSheaf
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.CategoryTheory.SitePullbackAbelianUnderlying
import Sheaf.CategoryTheory.SiteMorphismComposition
public import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses

/-!
# Exact symmetric monoidal inverse image on a site

Source: Stacks Project, Sites, Tag 00X6; Modules on Sites, Tag 03EL;
RefactorInstruction.tex, Section 4, prop:pX
(blueprint: lem-weil-pbc-left-exact-site-inverse-image-tensor).

Integer-module sheaves encode abelian sheaves by the unique integer action, transported
along `ULift.ringEquiv`. The tensor is the existing sheafification of the sectionwise
module tensor, with the canonical oplax comparison of sheaf pullback. Heterogeneous
equalities fix the monoidal structures without introducing file-local instances.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Source: Stacks, Tags 00X6 and 03EL; RefactorInstruction.tex Section 4 prop:pX
(blueprint: lem-weil-pbc-left-exact-site-inverse-image-tensor).

The Kan-extension inverse image, its exactness, and its normalized tensor structure.

Proof:
1. Cover preservation and finite-limit preservation imply Stacks continuity, by
   lem-weil-pbc-site-continuous-pushforward-sheaf. Small comma categories give the
   left Kan extension and the sheafification adjunction
   (lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction).
2. The comma categories are filtered. Thus the set Kan extension preserves finite
   limits (lem-weil-pbc-presheaf-pullback-sets-left-exact). Inclusion of sheaves
   preserves limits (lem-weil-pbc-site-sheaf-sets-limits-sectionwise), and
   sheafification is left exact (lem-weil-pbc-sheafification-sets-exact).
   The composite is left exact; its adjunction gives all colimits
   (lem-weil-pbc-left-adjoint-preserves-colimits). This is a geometric morphism.
3. On abelian sheaves, apply lem-weil-pbc-site-pullback-abelian-exact and
   lem-weil-pbc-site-pullback-abelian-underlying: the functor is additive and exact,
   and its underlying set sheaf is the set inverse image. The unique integer
   action identifies this with the integer-module construction.
4. The tensor represents sectionwise bilinear maps followed by sheafification
   (def-pur-sheaf-tensor-product and def-weil-pbc-sheafification). Transpose a
   bilinear map through the adjunction using the product comparison; addition,
   zero, and integer scalar multiplication transpose because finite products
   are preserved. Yoneda gives the tensor comparison, normalized by sending
   the adjunction-unit images of a pair to their tensor.
5. Maps from the integer unit are maps from the terminal set sheaf to the
   underlying set sheaf. The set and abelian adjunctions and preservation of
   the terminal object identify the two unit objects, carrying 1 to 1.
6. The composition comparison of lem-weil-pbc-site-morphism-composition carries
   the composite unit to the iterated units; the identity comparison carries
   its unit to the identity. After transposing and precomposing with universal
   bilinear maps, both composition routes send a pair to the tensor of its
   iterated unit images. Both identity routes send it to its original tensor.
   Unit routes send 1 to 1. The associativity routes agree on triples of pure
   tensors, symmetry interchanges the pair, and the unitor routes send (n,s)
   to n times s. The universal properties determine all maps, proving strong
   symmetric monoidality and monoidality of composition and identity.
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
  sorry

/-- Source: Stacks, Tags 00X6 and 03EL; RefactorInstruction.tex Section 4 prop:pX
(blueprint: lem-weil-pbc-left-exact-site-inverse-image-tensor).

The adjunction-compatible composition and identity comparisons are monoidal.

Proof:
1. Cover preservation and finite-limit preservation imply Stacks continuity, by
   lem-weil-pbc-site-continuous-pushforward-sheaf. Small comma categories give the
   left Kan extension and the sheafification adjunction
   (lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction).
2. The comma categories are filtered. Thus the set Kan extension preserves finite
   limits (lem-weil-pbc-presheaf-pullback-sets-left-exact). Inclusion of sheaves
   preserves limits (lem-weil-pbc-site-sheaf-sets-limits-sectionwise), and
   sheafification is left exact (lem-weil-pbc-sheafification-sets-exact).
   The composite is left exact; its adjunction gives all colimits
   (lem-weil-pbc-left-adjoint-preserves-colimits). This is a geometric morphism.
3. On abelian sheaves, apply lem-weil-pbc-site-pullback-abelian-exact and
   lem-weil-pbc-site-pullback-abelian-underlying: the functor is additive and exact,
   and its underlying set sheaf is the set inverse image. The unique integer
   action identifies this with the integer-module construction.
4. The tensor represents sectionwise bilinear maps followed by sheafification
   (def-pur-sheaf-tensor-product and def-weil-pbc-sheafification). Transpose a
   bilinear map through the adjunction using the product comparison; addition,
   zero, and integer scalar multiplication transpose because finite products
   are preserved. Yoneda gives the tensor comparison, normalized by sending
   the adjunction-unit images of a pair to their tensor.
5. Maps from the integer unit are maps from the terminal set sheaf to the
   underlying set sheaf. The set and abelian adjunctions and preservation of
   the terminal object identify the two unit objects, carrying 1 to 1.
6. The composition comparison of lem-weil-pbc-site-morphism-composition carries
   the composite unit to the iterated units; the identity comparison carries
   its unit to the identity. After transposing and precomposing with universal
   bilinear maps, both composition routes send a pair to the tensor of its
   iterated unit images. Both identity routes send it to its original tensor.
   Unit routes send 1 to 1. The associativity routes agree on triples of pure
   tensors, symmetry interchanges the pair, and the unitor routes send (n,s)
   to n times s. The universal properties determine all maps, proving strong
   symmetric monoidality and monoidality of composition and identity.
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
  sorry

end CategoryTheory
