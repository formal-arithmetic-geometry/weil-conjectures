/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.AB

/-!
# Higher direct images along a morphism of sites are sheafified cohomology presheaves

Source: literature/stacks-project/sites-cohomology.tex, Lemma Tag 072W
(blueprint: lem-weil-pbc-site-higher-direct-image-sheafified-presheaf).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

attribute [local instance] Functor.additive_of_preserves_binary_products

set_option synthInstance.maxSize 2048 in
/-- Source: Stacks Project, Lemma Tag 072W
(blueprint: lem-weil-pbc-site-higher-direct-image-sheafified-presheaf).

The sites are precoverages (Stacks 00VH); `hcover`/`hpullback` are the two conditions
of continuity (00WV) and the exactness of `sheafPullback u` makes `u` a morphism of
sites `f` (00X1), with `f_* = u.sheafPushforwardContinuous`. For an injective
resolution `I` of `F`, the complex `f_*I` lives in abelian sheaves on `D`; the presheaf
`P^q_F` is the `q`-th cohomology of the complex of presheaves underlying `f_*I`, i.e.
`V ↦ H^q(I(u V)) = H^q(u V, F)` with restriction maps induced by those of `I`. The map
below is the canonical comparison `(P^q_F)^# → H^q(f_*I) ≅ R^q f_* F`: sheafification
commutes with homology, then the counit of the sheafification adjunction on the complex
`f_*I`, then the resolution isomorphism. Its adjoint `P^q_F → R^q f_* F` sends the class of a
cocycle `s ∈ I^q(u V)` to the section it defines. The statement is that this comparison is
an isomorphism; in particular `R^q f_* F = 0` iff `(P^q_F)^# = 0`. The values
`H^q(I(u V))` are `H^q(u V, F)` by the resolution description of def-weil-pbc-sites-and-cohomology
(2); their identification with `Sheaf.H' F q (u.obj V)` is the comparison theorem recorded there.

Proof: `f_*` is additive and preserves kernels, so it is left exact and `R^q f_* F` is the
`q`-th cohomology of `f_*I` in sheaves. Evaluation at `V` on presheaves is exact, so the
presheaf cohomology of `f_*I` is `P^q_F` with its restriction maps. Sheafification is exact,
so it commutes with taking cohomology, and on the sheaf complex `f_*I` the counit is an
isomorphism; hence the comparison is an isomorphism. -/
theorem siteHigherDirectImageSheafifiedPresheaf
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (u : D ⥤ C)
    (hcover : ∀ (X : D) (R : Presieve X), R ∈ K X → R.map u ∈ J (u.obj X))
    (hpullback : ∀ (X Y Z : D) (R : Presieve X), R ∈ K X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) u)
    [u.IsContinuous K.toGrothendieck J.toGrothendieck]
    [PreservesFiniteLimits (sheafPullback u (Type u) K.toGrothendieck J.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback u (Type u) K.toGrothendieck J.toGrothendieck)]
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{u}) (I : InjectiveResolution F) (q : ℕ) :
    IsIso
      ((((((sheafToPresheaf K.toGrothendieck AddCommGrpCat.{u}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
          (((u.sheafPushforwardContinuous AddCommGrpCat.{u} K.toGrothendieck
            J.toGrothendieck).mapHomologicalComplex (ComplexShape.up ℕ)).obj
              I.cocomplex)).sc q).mapHomologyIso
          (presheafToSheaf K.toGrothendieck AddCommGrpCat.{u})).inv ≫
        (HomologicalComplex.homologyFunctor (Sheaf K.toGrothendieck AddCommGrpCat.{u})
          (ComplexShape.up ℕ) q).map
          ((NatTrans.mapHomologicalComplex
            (sheafificationAdjunction K.toGrothendieck AddCommGrpCat.{u}).counit
            (ComplexShape.up ℕ)).app
            (((u.sheafPushforwardContinuous AddCommGrpCat.{u} K.toGrothendieck
              J.toGrothendieck).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)) ≫
        (I.isoRightDerivedObj
          (u.sheafPushforwardContinuous AddCommGrpCat.{u} K.toGrothendieck J.toGrothendieck)
            q).inv) := by
  -- Continuity is already supplied as an instance; retain the covering witnesses.
  have _ := hcover
  have _ := hpullback
  -- The sheafification counit is a natural isomorphism, also on complexes.
  have : IsIso (NatTrans.mapHomologicalComplex
      (sheafificationAdjunction K.toGrothendieck AddCommGrpCat.{u}).counit
      (ComplexShape.up ℕ)) :=
    (NatIso.mapHomologicalComplex
      (asIso (sheafificationAdjunction K.toGrothendieck AddCommGrpCat.{u}).counit)
      (ComplexShape.up ℕ)).isIso_hom
  -- Homology preserves isomorphisms; the other two factors are inverse isomorphisms.
  infer_instance

end CategoryTheory
