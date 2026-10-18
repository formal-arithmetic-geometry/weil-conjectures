/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import WeilConjectures.RingTheory.ProEtale.WContractible
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.FiniteWContractible
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Exact pro-etale direct image for finite locally finitely presented morphisms

Source: Stacks Project, Tag 09A8, `proetale-lemma-finite`, and its module consequence
by forgetting scalars (blueprint: lem-zl-finite-fp-proetale-pushforward-exact).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Direct image on the small pro-etale sites is exact for a finite morphism locally
of finite presentation, both for abelian sheaves and for modules over arbitrary
commutative ring sheaves with a specified inverse-image ring map. Exactness is expressed
as preservation of finite limits and finite colimits; in these abelian categories this
is equivalent to preservation of every short exact sequence. The module action is
restriction of scalars along the actual adjoint of `c`, with no invertibility assumption.

Source: Stacks Project, Tag 09A8, `proetale-lemma-finite`; Modules on Sites, Tag 03D7
(blueprint: lem-zl-finite-fp-proetale-pushforward-exact).

Proof:
1. Cover each object W of Y_proet by affine opens W' over affine opens Spec A of Y.
   Weak-etale source locality makes these objects of the site; quasi-compactness of
   affine opens makes the resulting family a pro-etale cover. Over Spec A the finite
   morphism is Spec B -> Spec A with B a finite A-module and a finitely presented
   A-algebra, by LocallyOfFinitePresentation.finitePresentation_appLE.
2. Choose a faithfully flat ind-etale w-contractible A'-algebra D for W'=Spec A'
   by exists_isWContractibleRing. Ind-etale stability makes Spec D a site object and
   its surjective affine map to W' a cover. The pullback of X is Spec C with
   C=D tensor_A B. Finite generation and finite presentation survive this base change.
   The finite-w-contractibility lemma (Tag 0986) makes C w-contractible, including C=0.
3. An epimorphism of abelian sheaves is locally surjective. Weak contractibility of
   Spec C makes evaluation on this pullback surjective. By sectionwise direct image,
   the pushed epimorphism is therefore surjective on sections over each Spec D.
4. The composites Spec D -> W cover every W. Thus the pushed map is locally
   surjective and hence epi by the abelian-sheaf epi criterion. Kernels are computed
   sectionwise, so direct image also preserves kernels. It is additive, hence exact,
   equivalently preserves finite limits and finite colimits.
5. For modules, the underlying abelian sheaf of SheafOfModules.pushforward is this
   same direct image. Its scalar action is through the adjoint of c, as in the
   ringed-topoi module adjunction. The faithful exact forgetful functor
   moduleSheaves_colimits_forgetful reflects exactness. Apply steps 1--4 to the
   underlying sequence. No constructibility, torsion or flatness is used. -/
theorem finite_fp_proEtale_pushforward_exact
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [LocallyOfFinitePresentation f] :
    PreservesFiniteLimits (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}) ∧
    PreservesFiniteColimits (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}) ∧
    ∀ (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
      (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
      (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ⟶ R_X),
      PreservesFiniteLimits
        (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
          (J := ProEt.topology Y) (K := ProEt.topology X)
          (S := (sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y)
          (R := (sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
          ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
              ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv R_Y R_X c))) ∧
      PreservesFiniteColimits
        (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
          (J := ProEt.topology Y) (K := ProEt.topology X)
          (S := (sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y)
          (R := (sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_X)
          ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
              ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv R_Y R_X c))) := by
  sorry

end AlgebraicGeometry.Scheme
