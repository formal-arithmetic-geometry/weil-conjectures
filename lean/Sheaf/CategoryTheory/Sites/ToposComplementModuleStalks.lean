/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q153
-/
module

public import Sheaf.CategoryTheory.Sites.ToposComplementFactorization
public import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.Sites.OrientedClosedBaseLocalization
import Sheaf.CategoryTheory.Sites.ToposLocalizationSitePresentation
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems

/-!
# Module support and stalks for complementary subtopoi

Source: Stacks Project, Modules on Sites, Tags 03DI, 04EQ and 0710;
Sites and Sheaves, Tags 00YV, 08LW, 08LY and 08M1
(blueprint: lem-trf-topos-complement-module-stalks).

Every topos is represented on an arbitrary small presenting site, and the open
embedding is identified with the slice morphism. Modules are the recorded
`ConstantLeftModuleInverseImage.Modules`, i.e. genuine modules over the sheafified
constant ring. All inverse images use the recorded normalized module lifts.
A point is represented on any small site whose sheaf topos is equivalent to sets;
this permits exactly the geometric points `Set → E`, without requiring a special
choice of a presentation of sets. All stalk comparisons are natural isomorphisms,
normalized by their underlying set comparisons and the actual adjunction maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe w

open CategoryTheory CategoryTheory.Limits
open ConstantLeftModuleInverseImage

namespace CategoryTheory.ToposComplementModules

/-- The existing normalized lift of a geometric morphism to constant-ring modules.
Its fields include the scalar comparison, actual adjunction, and exactness.
Source: Stacks, Sites, Tag 00YV
(blueprint: lem-trf-topos-complement-module-stalks). -/
abbrev Lift {C D : Type w} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (Λ : Type w) [CommRing Λ]
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w))) :=
  ConstantLeftModuleInverseImageLift J K Λ f.inverse f.direct f.adj f.leftExact

/-- Normalize a module composition comparison by the inverse-image mate of the
specified direct-image factorization. This pins the comparison on every underlying
section, hence determines it uniquely. Source: Stacks, Sites, Tag 00YV
(blueprint: lem-trf-topos-complement-module-stalks). -/
def IsCompositionComparison
    {C D P : Type w} [SmallCategory C] [SmallCategory D] [SmallCategory P]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {S : GrothendieckTopology P} {Λ : Type w} [CommRing Λ]
    {f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w))}
    {g : GeometricMorphism (Sheaf S (Type w)) (Sheaf K (Type w))}
    {p : GeometricMorphism (Sheaf S (Type w)) (Sheaf J (Type w))}
    (df : Lift Λ f) (dg : Lift Λ g) (dp : Lift Λ p)
    (q : (g.comp f).direct ≅ p.direct)
    (c : dp.moduleFunctor ≅ df.moduleFunctor ⋙ dg.moduleFunctor) : Prop :=
  ∀ F : Modules J Λ,
    (W S Λ).map (c.hom.app F) ≫
        dg.moduleSetIso.hom.app (df.moduleFunctor.obj F) ≫
        g.inverse.map (df.moduleSetIso.hom.app F) =
      dp.moduleSetIso.hom.app F ≫
        (GeometricMorphism.inverseIso q).hom.app ((W J Λ).obj F)

/-- The point assertions, with their natural and normalized stalk identifications.
The open identity is expressed by the equation carrying the stalk of the counit
to the identity under `openStalk` and `c`. The closed identity is the analogous
unit equation under `closedStalk` and `c`. The two stalk isomorphisms are fixed
by composition and by the actual open unit or closed counit, not chosen freely.

Source: Stacks, Modules on Sites, Tags 0710 and 04EQ; Sites, Tags 00YV, 08LW and 08LY
(blueprint: lem-trf-topos-complement-module-stalks). -/
def PointAssertion
    {C D O : Type w} [SmallCategory C] [SmallCategory D] [SmallCategory O]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : GrothendieckTopology O} {Λ : Type w} [CommRing Λ]
    (U : Sheaf J (Type w))
    (j : GeometricMorphism (Sheaf L (Type w)) (Sheaf J (Type w)))
    (k : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    (dj : Lift Λ j) (dk : Lift Λ k)
    (jShriek : Modules L Λ ⥤ Modules J Λ) (adj : jShriek ⊣ dj.moduleFunctor)
    (openUnit : 𝟭 (Modules L Λ) ≅ jShriek ⋙ dj.moduleFunctor)
    (closedCounit : dk.moduleDirect ⋙ dk.moduleFunctor ≅ 𝟭 (Modules K Λ)) : Prop :=
  ∀ (P : Type w) [SmallCategory P] (S : GrothendieckTopology P)
    (_eSet : Sheaf S (Type w) ≌ Type w)
    (p : GeometricMorphism (Sheaf S (Type w)) (Sheaf J (Type w))),
    ∃ dp : Lift Λ p,
      Xor (Nonempty (IsTerminal (p.inverse.obj U)))
        (Nonempty (IsInitial (p.inverse.obj U))) ∧
      (Nonempty (IsTerminal (p.inverse.obj U)) →
        ∃ (po : GeometricMorphism (Sheaf S (Type w)) (Sheaf L (Type w)))
          (q : (po.comp j).direct ≅ p.direct) (dpo : Lift Λ po)
          (c : dp.moduleFunctor ≅ dj.moduleFunctor ⋙ dpo.moduleFunctor)
          (openStalk : jShriek ⋙ dp.moduleFunctor ≅ dpo.moduleFunctor),
          IsCompositionComparison dj dpo dp q c ∧
          (∀ G : Modules L Λ,
            openStalk.hom.app G = c.hom.app (jShriek.obj G) ≫
              dpo.moduleFunctor.map (openUnit.inv.app G)) ∧
          (∀ H : Modules K Λ, IsZero (dp.moduleFunctor.obj (dk.moduleDirect.obj H))) ∧
          (∀ F : Modules J Λ,
            dp.moduleFunctor.map (adj.counit.app F) ≫ c.hom.app F =
              openStalk.hom.app (dj.moduleFunctor.obj F))) ∧
      (Nonempty (IsInitial (p.inverse.obj U)) →
        ∃ (pc : GeometricMorphism (Sheaf S (Type w)) (Sheaf K (Type w)))
          (q : (pc.comp k).direct ≅ p.direct) (dpc : Lift Λ pc)
          (c : dp.moduleFunctor ≅ dk.moduleFunctor ⋙ dpc.moduleFunctor)
          (closedStalk : dk.moduleDirect ⋙ dp.moduleFunctor ≅ dpc.moduleFunctor),
          IsCompositionComparison dk dpc dp q c ∧
          (∀ H : Modules K Λ,
            closedStalk.hom.app H = c.hom.app (dk.moduleDirect.obj H) ≫
              dpc.moduleFunctor.map (closedCounit.hom.app H)) ∧
          (∀ G : Modules L Λ, IsZero (dp.moduleFunctor.obj (jShriek.obj G))) ∧
          (∀ F : Modules J Λ,
            dp.moduleFunctor.map (dk.moduleAdj.unit.app F) ≫
                closedStalk.hom.app (dk.moduleFunctor.obj F) = c.hom.app F))

end CategoryTheory.ToposComplementModules

namespace CategoryTheory

/-- Module adjunctions, closed support, zero restrictions and point formulas for
complementary subtopoi, on arbitrary small-site presentations. The first conjunct
supplies exact module inverse image for every geometric morphism; the module lift
includes both finite-limit and finite-colimit preservation. In the second conjunct
`j.inverse ⋙ e.functor ≅ Over.star U` identifies the open slice, and the essential
image of `k.direct` identifies the complementary closed topos. These presentation
conditions express exactly the embeddings in the node, not extra geometric assumptions.

Source: Stacks, Modules on Sites, Tags 03DI, 04EQ and 0710; Sites, Tags 00YV, 08LW,
08LY and 08M1 (blueprint: lem-trf-topos-complement-module-stalks).

Proof plan:
1. Use `lem-pe-constant-left-module-inverse-image` to transport the constant scalar
   action along every geometric inverse image. Its normalized lift is exact and
   compatible with composition and change of presentation (Tag 00YV).
2. Apply `lem-trf-topos-localization-site-presentation` to the subterminal object.
   The slice is represented by C/U and the subterminality gives at most one arrow
   from any V to U. Use `lem-pur-site-restriction-module-adjunction-exact` and the
   coefficient comparison to construct the module left adjoint jShriek (03DI).
3. The extension presheaf of `def-weil-extension-by-zero-presheaf` has precisely
   the summand G(V → U) at V → U. Its unit is inclusion of that sole summand.
   Restriction commutes with the sheafification of
   `def-weil-presheaf-modules-sheafification`, because covers and refinements have
   their unique maps to U. Thus the actual open unit is a natural isomorphism.
4. Apply `lem-trf-oriented-closed-base-localization` to obtain fully faithful
   closed module direct image, the invertible counit, and its support criterion.
5. By `lem-trf-topos-complement-factorization`, a point factors through exactly
   one complement: a subterminal set is empty or singleton, never both.
6. The support criterion gives jStar kDirect = 0. The two adjunctions identify
   Hom(kStar jShriek G,H) with Hom(G,jStar kDirect H), so taking H=kStar jShriek G
   makes its identity zero. Hence kStar jShriek G=0 without using enough points.
7. Use the normalized composition comparison in step 1 and the open unit or
   closed counit in steps 3 and 4 to obtain the two natural stalk isomorphisms.
   Applying exact point inverse image to step 6 gives the two zero stalks (0710).
8. The open triangle identity makes jStar of the open counit the inverse open
   unit. The closed triangle identity makes kStar of the closed unit the inverse
   closed counit. Applying the factored point functor gives precisely the two
   equations in PointAssertion, under its specified natural identifications.
9. The point inverse images, including the factors po and pc, are exact by step 1.
10. All arguments include U=0, U=1, the zero coefficient ring, and topoi without
    points: the non-stalk vanishing was obtained by adjunction, not conservativity.
-/
theorem topos_complement_module_stalks :
    (∀ (C D : Type w) [SmallCategory C] [SmallCategory D]
      (J : GrothendieckTopology C) (K : GrothendieckTopology D)
      (Λ : Type w) [CommRing Λ]
      (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w))),
      Nonempty (ToposComplementModules.Lift Λ f)) ∧
    (∀ (C D O : Type w) [SmallCategory C] [SmallCategory D] [SmallCategory O]
      (J : GrothendieckTopology C) (K : GrothendieckTopology D)
      (L : GrothendieckTopology O) (U : Sheaf J (Type w)), IsSubterminal U →
      ∀ (j : GeometricMorphism (Sheaf L (Type w)) (Sheaf J (Type w)))
        (k : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w))),
      (∃ e : Sheaf L (Type w) ≌ Over U,
        Nonempty (j.inverse ⋙ e.functor ≅ Over.star U)) →
      Nonempty k.direct.FullyFaithful →
      (∀ A : Sheaf J (Type w), k.direct.essImage A ↔ closedComplementObjects U A) →
      ∀ (Λ : Type w) [CommRing Λ],
      ∃ (dj : ToposComplementModules.Lift Λ j)
        (dk : ToposComplementModules.Lift Λ k)
        (jShriek : Modules L Λ ⥤ Modules J Λ) (adj : jShriek ⊣ dj.moduleFunctor)
        (openUnit : 𝟭 (Modules L Λ) ≅ jShriek ⋙ dj.moduleFunctor)
        (closedCounit : dk.moduleDirect ⋙ dk.moduleFunctor ≅ 𝟭 (Modules K Λ)),
        openUnit.hom = adj.unit ∧ closedCounit.hom = dk.moduleAdj.counit ∧
        dk.moduleDirect.Full ∧ dk.moduleDirect.Faithful ∧
        (∀ F : Modules J Λ,
          dk.moduleDirect.essImage F ↔ IsZero (dj.moduleFunctor.obj F)) ∧
        (∀ G : Modules L Λ, IsZero (dk.moduleFunctor.obj (jShriek.obj G))) ∧
        (∀ H : Modules K Λ, IsZero (dj.moduleFunctor.obj (dk.moduleDirect.obj H))) ∧
        ToposComplementModules.PointAssertion U j k dj dk jShriek adj openUnit closedCounit) := by
  sorry

end CategoryTheory
