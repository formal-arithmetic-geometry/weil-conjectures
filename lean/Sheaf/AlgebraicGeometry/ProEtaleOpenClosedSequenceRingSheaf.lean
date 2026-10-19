/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf

/-!
# Open–closed localization with arbitrary ring-sheaf coefficients

Source: blueprint `det-sf-open-closed-sequence-ring-sheaf`, clauses (1)–(4);
Stacks Project, Tags 09AA, 09BM, 09BN, 09AH, 09AG, 03D3, 03DI and 03DJ
(blueprint: det-sf-open-closed-sequence-ring-sheaf).

A ring sheaf is a monoid object in abelian sheaves, without a commutativity assumption.
Its modules are the existing `Mod` objects, as in `closed_inverseImage_preserves_limits`.
The helpers specialize the published module-object functors and adjunctions to these
coefficients. Base-change coefficient transport uses the specified composition isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Module inverse image, with inverse-image coefficients and the transported action.
Source: Stacks, Tags 03D2 and 09A5
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafInverseImage {T X : Scheme.{u}} (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :=
  (upperStar Ab.{u + 1} f).mapMod B

/-- Module direct image, with scalars restricted through the canonical ring unit.
Source: Stacks, Tag 03D3 and Pro-etale Cohomology, section 09A5
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafDirectImage {T X : Scheme.{u}} (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :=
  (lowerStar Ab.{u + 1} f).mapMod ((upperStar Ab.{u + 1} f).obj B) ⋙
    Mod.comap ((upperStarLowerStarAdjunction Ab.{u + 1} f).unitAlgHom B)

/-- The actual inverse-image/direct-image module adjunction.
Source: Stacks, Tag 03D3
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafAdjunction {T X : Scheme.{u}} (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    ringSheafInverseImage f B ⊣ ringSheafDirectImage f B :=
  (upperStarLowerStarAdjunction Ab.{u + 1} f).mapModAdjunction B

/-- Extension by zero with its coefficient action supplied by the existing projection
formula linearization. Its carrier is the sheafification of extension by zero of the
underlying abelian presheaf, and its action is the sheafified original action.
Source: Stacks, Tags 03DI, 03DJ and 09AE
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafOpenExtension {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :=
  (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeft B

/-- The extension-by-zero adjunction with its specified underlying abelian unit and counit.
Source: Stacks, Tag 03DI
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafOpenAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    ringSheafOpenExtension j B ⊣ ringSheafInverseImage j B :=
  (openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).mapModLeftAdjunction

/-- The fixed inverse-image composition comparison on a pullback square.
Source: Stacks, Tags 03CB and 03CC; blueprint clause (4)
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafSquareComparison {X' T X : Scheme.{u}} (g : X' ⟶ X) (f : T ⟶ X) :=
  upperStarCompIso Ab.{u + 1} (pullback.condition (f := g) (g := f))

/-- The canonical coefficient identification, with the two successive inverse-image
ring structures made explicit, rather than the structure on a composite functor.
Source: Stacks, Tags 03CB and 03CC; blueprint clause (4)
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
def ringSheafSquareCoefficient {X' T X : Scheme.{u}} (g : X' ⟶ X) (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
    (upperStar Ab.{u + 1} (pullback.fst g f)).obj ((upperStar Ab.{u + 1} g).obj B) ⟶
      (upperStar Ab.{u + 1} (pullback.snd g f)).obj ((upperStar Ab.{u + 1} f).obj B) :=
  (ringSheafSquareComparison g f).hom.app B

/-- Pullback along the fibre projection, with scalars identified by the fixed canonical
composition comparison. Multiplicativity of this comparison is concluded in the theorem.
Source: Stacks, Tags 03CB and 03CC; blueprint clause (4)
(blueprint: det-sf-open-closed-sequence-ring-sheaf). -/
abbrev ringSheafSquarePullback {X' T X : Scheme.{u}} (g : X' ⟶ X) (f : T ⟶ X)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B]
    [IsMonHom (ringSheafSquareCoefficient g f B)] :
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) ((upperStar Ab.{u + 1} f).obj B) ⥤
      Mod (Sheaf (Scheme.ProEt.topology (pullback g f)) Ab.{u + 1})
        ((upperStar Ab.{u + 1} (pullback.fst g f)).obj
          ((upperStar Ab.{u + 1} g).obj B)) :=
  ringSheafInverseImage (pullback.snd g f) ((upperStar Ab.{u + 1} f).obj B) ⋙
    Mod.comap (ringSheafSquareCoefficient g f B)

/-- The open–closed sequence over an arbitrary ring sheaf, and canonical base change.
The square restriction comparisons are normalized on underlying sheaves. The open
comparison is characterized by its transpose of the open unit; the closed comparison
by its transpose of the closed counit. The final two equations identify both sequence
arrows, rather than merely identifying its three terms.

Source: blueprint `det-sf-open-closed-sequence-ring-sheaf`, clauses (1)–(4);
Stacks, Tags 09AA, 09BM, 09BN, 09AH, 09AG, 03D3, 03DI, 03DJ, 03CB and 03CC
(blueprint: det-sf-open-closed-sequence-ring-sheaf).

Proof:
1. Apply inverse image to the ring operations and module actions. Direct image is
   evaluation on fibre products with its scalar action through the ring unit. Identify
   the open site with the localized site by lem-weil-proetale-weakly-etale-localization.
   The sheafification of def-weil-extension-by-zero-presheaf is the open extension.
   Forgetting actions preserves and reflects kernels, cokernels and isomorphisms by
   lem-weil-pbc-module-sheaves-colimits-forgetful, so exactness can be checked there.
2. The abelian inverse/direct-image Hom bijection restricts to linear maps: naturality
   of its unit on the action map identifies the two linearity equations, in both
   directions. This is the displayed lifted adjunction, including its actual maps.
3. Apply lem-weil-pbc-proetale-ringed-open-closed with the constant integer ring sheaf
   to obtain the abelian localization statements. Every abelian sheaf has its canonical
   integer action. The open unit and closed counit are the actual adjunction maps:
   use the localization sequence on j_!N and i_*G and their triangle identities.
4. The extension-presheaf Hom bijection and module sheafification give the open module
   adjunction. Its carrier is the abelian extension by zero, so it is exact and its
   unit is invertible. Inverse image is exact on carriers by
   lem-weil-pbc-site-pullback-abelian-exact, hence on these module categories.
5. Reflect the abelian closed counit, exactness and vanishing through the forgetful
   functor. The resulting counit–unit sequence is short exact. It also shows that open
   and closed restriction jointly detect zero objects and isomorphisms, by applying
   exact restriction to kernels and cokernels.
6. Base change preserves open and closed immersions and quasi-compactness of j, by
   lem-weil-pbc-open-immersion-base-change, lem-weil-pbc-closed-immersion-base-change
   and lem-pc-quasi-compact-base-change. The pulled-back immersions are complementary.
   The adjunction-compatible composition comparison of
   lem-weil-pbc-site-morphism-composition respects actions and gives delta and gamma.
7. Sectionwise j^*g_* = g_U* j'^* yields open base change by the composite adjunction
   Hom bijections. Its inverse is exactly the transpose of the pulled-back open unit
   written below; naturality gives inverse isomorphisms.
8. Define closed base change as the transpose of gamma followed by the pulled-back
   closed counit. Its open restriction has zero source and target. Its closed
   restriction is invertible by the counit equation and invertible closed counits.
   Joint detection from step 5 proves it is invertible for arbitrary g.
9. Under the same adjunction Hom bijections, the two open sequence maps have the same
   transpose by the triangle identities and step 7. For the closed maps, the counit
   equation of step 8 and the closed triangle identity give the same transpose gamma.
   These are the last two equations. Exactness of g^* therefore carries the entire
   short exact sequence to that for g^*M, with the specified arrows.
-/
theorem proEtale_openClosed_sequence_ring_sheaf
    {X Z U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    [QuasiCompact j] (_hU : Set.range j = (Set.range i)ᶜ)
    (B : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj B] :
    PreservesFiniteLimits (ringSheafInverseImage j B) ∧
    PreservesFiniteColimits (ringSheafInverseImage j B) ∧
    PreservesFiniteLimits (ringSheafOpenExtension j B) ∧
    PreservesFiniteColimits (ringSheafOpenExtension j B) ∧
    (∀ N, IsIso ((ringSheafOpenAdjunction j B).unit.app N)) ∧
    PreservesFiniteLimits (ringSheafDirectImage i B) ∧
    PreservesFiniteColimits (ringSheafDirectImage i B) ∧
    (∀ G, IsIso ((ringSheafAdjunction i B).counit.app G)) ∧
    (∀ G, IsZero ((ringSheafInverseImage j B).obj ((ringSheafDirectImage i B).obj G))) ∧
    (∀ M, Mono ((ringSheafOpenAdjunction j B).counit.app M) ∧
      Epi ((ringSheafAdjunction i B).unit.app M) ∧
      (ComposableArrows.mk₂ ((ringSheafOpenAdjunction j B).counit.app M)
        ((ringSheafAdjunction i B).unit.app M)).Exact) ∧
    (∀ {X' : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X'] (g : X' ⟶ X),
      Exists fun [hu : IsMonHom (ringSheafSquareCoefficient g j B)] ↦
      Exists fun [hz : IsMonHom (ringSheafSquareCoefficient g i B)] ↦
      ∃ delta : ringSheafInverseImage g B ⋙
            ringSheafInverseImage (pullback.fst g j) ((upperStar Ab.{u + 1} g).obj B) ≅
          ringSheafInverseImage j B ⋙ ringSheafSquarePullback g j B,
      ∃ gamma : ringSheafInverseImage g B ⋙
            ringSheafInverseImage (pullback.fst g i) ((upperStar Ab.{u + 1} g).obj B) ≅
          ringSheafInverseImage i B ⋙ ringSheafSquarePullback g i B,
        (∀ M, (delta.hom.app M).hom = (ringSheafSquareComparison g j).hom.app M.X) ∧
        (∀ M, (gamma.hom.app M).hom = (ringSheafSquareComparison g i).hom.app M.X) ∧
        (∀ M, Mono ((ringSheafOpenAdjunction (pullback.fst g j)
              ((upperStar Ab.{u + 1} g).obj B)).counit.app
                ((ringSheafInverseImage g B).obj M)) ∧
          Epi ((ringSheafAdjunction (pullback.fst g i)
              ((upperStar Ab.{u + 1} g).obj B)).unit.app
                ((ringSheafInverseImage g B).obj M)) ∧
          (ComposableArrows.mk₂
            ((ringSheafOpenAdjunction (pullback.fst g j)
              ((upperStar Ab.{u + 1} g).obj B)).counit.app
                ((ringSheafInverseImage g B).obj M))
            ((ringSheafAdjunction (pullback.fst g i)
              ((upperStar Ab.{u + 1} g).obj B)).unit.app
                ((ringSheafInverseImage g B).obj M))).Exact) ∧
        ∃ alpha : ringSheafOpenExtension j B ⋙ ringSheafInverseImage g B ≅
            ringSheafSquarePullback g j B ⋙
              ringSheafOpenExtension (pullback.fst g j) ((upperStar Ab.{u + 1} g).obj B),
        ∃ beta : ringSheafDirectImage i B ⋙ ringSheafInverseImage g B ≅
            ringSheafSquarePullback g i B ⋙
              ringSheafDirectImage (pullback.fst g i) ((upperStar Ab.{u + 1} g).obj B),
          (∀ N, (ringSheafOpenAdjunction (pullback.fst g j)
                ((upperStar Ab.{u + 1} g).obj B)).homEquiv _ _ (alpha.inv.app N) =
            (ringSheafSquarePullback g j B).map ((ringSheafOpenAdjunction j B).unit.app N) ≫
              delta.inv.app ((ringSheafOpenExtension j B).obj N)) ∧
          (∀ G, ((ringSheafAdjunction (pullback.fst g i)
                ((upperStar Ab.{u + 1} g).obj B)).homEquiv _ _).symm (beta.hom.app G) =
            gamma.hom.app ((ringSheafDirectImage i B).obj G) ≫
              (ringSheafSquarePullback g i B).map ((ringSheafAdjunction i B).counit.app G)) ∧
          (∀ M, (ringSheafInverseImage g B).map ((ringSheafOpenAdjunction j B).counit.app M) =
            alpha.hom.app ((ringSheafInverseImage j B).obj M) ≫
              (ringSheafOpenExtension (pullback.fst g j)
                ((upperStar Ab.{u + 1} g).obj B)).map (delta.inv.app M) ≫
              (ringSheafOpenAdjunction (pullback.fst g j)
                ((upperStar Ab.{u + 1} g).obj B)).counit.app
                  ((ringSheafInverseImage g B).obj M)) ∧
          (∀ M, (ringSheafInverseImage g B).map ((ringSheafAdjunction i B).unit.app M) ≫
              beta.hom.app ((ringSheafInverseImage i B).obj M) =
            (ringSheafAdjunction (pullback.fst g i)
                ((upperStar Ab.{u + 1} g).obj B)).unit.app
                  ((ringSheafInverseImage g B).obj M) ≫
              (ringSheafDirectImage (pullback.fst g i)
                ((upperStar Ab.{u + 1} g).obj B)).map (gamma.hom.app M))) := by
  sorry

end AlgebraicGeometry.ProEtale
