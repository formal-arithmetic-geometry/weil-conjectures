/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.CoverLifting
import Sheaf.CategoryTheory.ContinuousCocontinuousToposAdjunctionForCoverings
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Mathlib.CategoryTheory.Adjunction.Triple

/-!
# Retraction from a fully faithful bigger site

Source: Stacks Project, Sites, Tags 00XU, 00XT, 00XR and 00X6
(blueprint: lem-trf-bigger-site-retraction).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A fully faithful continuous and cocontinuous inclusion of sites gives the
associated site morphism and its geometric retraction.

Source: Stacks Project, Sites, Tags 00XU (lemma-bigger-site), 00XT
(lemma-back-and-forth), 00XR (lemma-when-shriek), and 00X6
(proposition-get-morphism) (blueprint: lem-trf-bigger-site-retraction).

The hypotheses are: two small sites, cocontinuity and continuity of `u`,
full faithfulness of `u`, existence and preservation of fibre products, and
final objects carried to isomorphic final objects.  The first geometric
morphism has inverse image the sheafified left adjoint of restriction and
direct image restriction.  The second has inverse image restriction.  The
two adjunctions have the canonical invertible unit and counit, respectively;
the composite is isomorphic to the identity and the first inverse image is
fully faithful. Mathlib continuity is concluded from the covering formulation,
not assumed in addition to it. The sheaf-value universe may contain the sites.

Proof (the seven steps of the node):
1. A final object and pullbacks give products; pulling back a diagonal gives
   equalizers. Preservation of pullbacks and of the final object therefore
   gives preservation of finite limits.
2. Apply lem-weil-pbc-left-exact-site-inverse-image-tensor, set-sheaf clause,
   to obtain the sheafified left Kan extension, its adjunction to restriction,
   and its preservation of finite limits and colimits. This defines the site
   morphism f and its associated geometric morphism.
3. Apply lem-weil-pbc-continuous-cocontinuous-topos-adjunction. Its left adjoint
   is restriction R, and its right adjoint is g_*. Its compatible families
   give the canonical counit by evaluation at (X, id).
4. Full faithfulness writes every arrow u(A) to u(X) uniquely as u(a).
   Send t in F(X) to the family F(a)(t). Functoriality gives compatibility;
   the compatibility equation at (X, id) shows this is inverse to evaluation.
   The same equations give naturality in X and F, so the counit is invertible.
5. Apply lem-trf-adjoint-triple-unit-counit to the actual adjunctions L ⊣ R
   and R ⊣ g_*. The invertible counit makes the canonical sheafified unit
   invertible.
6. The direct image of f composed with g is g_* followed by R. The counit
   gives its natural isomorphism to the identity, hence the invertible
   geometric 2-morphism of def-trf-geometric-morphism.
7. For b : L(F) to L(G), the inverse to L on Hom sets sends b to the
   composite eta_F, R(b), eta_G inverse. Unit naturality and the adjunction
   bijection show both inverse equations, so L is fully faithful.
-/
theorem biggerSiteRetraction
    {C : Type u} [SmallCategory C] [HasPullbacks C]
    {D : Type u} [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D)
    (hJ : J.IsSiteForCoverings) (hK : K.IsSiteForCoverings)
    (u : C ⥤ D)
    [u.IsCocontinuous J.toGrothendieck K.toGrothendieck]
    [u.Full] [u.Faithful]
    (hcover : ∀ (X : C) (R : Presieve X), R ∈ J X → R.map u ∈ K (u.obj X))
    (hpullback : ∀ (X Y Z : C) (R : Presieve X), R ∈ J X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) u)
    (eC : C) (eD : D) (hfinalC : IsTerminal eC) (hfinalD : IsTerminal eD)
    (hfinal : u.obj eC ≅ eD)
    (hpreserve : ∀ (X Y Z : C) (a : X ⟶ Z) (b : Y ⟶ Z),
      PreservesLimit (cospan a b) u) :
    ∃ (hcontinuous : u.IsContinuous J.toGrothendieck K.toGrothendieck),
    ∃ (siteMorphism : GeometricMorphism
        (Sheaf K.toGrothendieck (Type (max u v))) (Sheaf J.toGrothendieck (Type (max u v))))
      (toposMorphism : GeometricMorphism
        (Sheaf J.toGrothendieck (Type (max u v))) (Sheaf K.toGrothendieck (Type (max u v)))),
      siteMorphism.inverse =
          Functor.sheafPullbackConstruction.sheafPullback u (Type (max u v))
            J.toGrothendieck K.toGrothendieck ∧
        siteMorphism.direct =
          u.sheafPushforwardContinuous (Type (max u v))
            J.toGrothendieck K.toGrothendieck ∧
        toposMorphism.inverse =
          u.sheafPushforwardContinuous (Type (max u v))
            J.toGrothendieck K.toGrothendieck ∧
        toposMorphism.direct =
          u.sheafPushforwardCocontinuous (Type (max u v))
            J.toGrothendieck K.toGrothendieck ∧
        IsIso (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u
          (Type (max u v)) J.toGrothendieck K.toGrothendieck).unit ∧
        IsIso (u.sheafAdjunctionCocontinuous (Type (max u v))
          J.toGrothendieck K.toGrothendieck).counit ∧
        Nonempty ((toposMorphism.comp siteMorphism).direct ≅
          𝟭 (Sheaf J.toGrothendieck (Type (max u v)))) ∧
        Nonempty siteMorphism.inverse.FullyFaithful := by
  sorry

end CategoryTheory
