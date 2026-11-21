/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.RouteInverseImageConstantRingOperations
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.CategoryTheory.RouteInverseImageConstantRingAssembly
import WeilConjectures.CategoryTheory.RouteInverseImageConstantSetComparison

/-!
# Constant-sheaf comparison for a ring lift

Source: Stacks Project, `sites.tex`, Tags 0H7J and 00YV.

The ring-level operation graph records exactly the compatibility required of the
underlying set-sheaf isomorphisms.  The theorem then supplies the natural
constant-ring comparison and its underlying canonical constant-set comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/--
For a left-exact inverse-image functor, compatible ring lifts carry constants
canonically to constants.  The first isomorphism in the conclusion is natural
in commutative-ring morphisms; the second is the set-level comparison obtained
from the coproduct presentation of a constant sheaf by copies of the terminal
sheaf.  Its first displayed equation identifies the underlying component with the
inverse of the supplied ring comparison followed by that canonical map.  The last
clause pins that map: it carries `L` of every map whose sections are the sheafified
constant section of `a` (in particular `L` of the coprojection `i_a`) to the
sheafified constant section of `a`.

Source: Stacks Project, `sites.tex`, Tags 0H7J and 00YV. -/
theorem inverseImageConstantComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    [HasWeakSheafify JC CommRingCat.{u}] [HasWeakSheafify JD CommRingCat.{u}]
    (L : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (V : Sheaf JD (Type u) ⥤ Sheaf JC (Type u)) (adj : L ⊣ V)
    (hL : PreservesFiniteLimits L)
    (rings : Sheaf JC CommRingCat.{u} ⥤ Sheaf JD CommRingCat.{u})
    (e : ∀ R : Sheaf JC CommRingCat.{u},
      RingInverseImage L R (rings.obj R))
    (enat : ∀ {R S : Sheaf JC CommRingCat.{u}} (φ : R ⟶ S),
      L.map ((sheafCompose JC (forget CommRingCat)).map φ) ≫
          (e S).ringUnderlying.hom =
        (e R).ringUnderlying.hom ≫
          (sheafCompose JD (forget CommRingCat)).map (rings.map φ)) :
    ∃ (constants : constantSheaf JC CommRingCat.{u} ⋙ rings ≅
        constantSheaf JD CommRingCat.{u})
      (kappa : (constantSheaf JC CommRingCat.{u} ⋙
          sheafForget JC ⋙ L) ≅
        constantSheaf JD CommRingCat.{u} ⋙ sheafForget JD),
      ∀ A : CommRingCat.{u},
        (sheafCompose JD (forget CommRingCat)).map
            ((constants.app A).hom) =
          (e ((constantSheaf JC CommRingCat.{u}).obj A)).ringUnderlying.inv ≫
            (kappa.app A).hom ∧
      ∀ (a : A) (T : Sheaf JC (Type u))
        (s : T ⟶ (sheafCompose JC (forget CommRingCat)).obj
          ((constantSheaf JC CommRingCat.{u}).obj A)),
        (∀ (U : Cᵒᵖ) (x : T.obj.obj U),
          (@id (((constantSheaf JC CommRingCat.{u}).obj A).obj.obj U) (s.hom.app U x)) =
            (toSheafify JC ((Functor.const Cᵒᵖ).obj A)).app U a) →
        ∀ (W : Dᵒᵖ) (y : (L.obj T).obj.obj W),
          (@id (((constantSheaf JD CommRingCat.{u}).obj A).obj.obj W)
            ((kappa.hom.app A).hom.app W ((L.map s).hom.app W y))) =
            (toSheafify JD ((Functor.const Dᵒᵖ).obj A)).app W a := by
  obtain ⟨kappa⟩ := canonicalConstantSetComparison JC JD L V adj hL
  obtain ⟨constants, hconstants⟩ := constantRingComparisonAssembly JC JD L hL rings e enat kappa
  refine ⟨constants, constantRingSetComparison JC JD L kappa, ?_⟩
  intro A
  refine ⟨hconstants A, ?_⟩
  intro a T s hs W y
  exact canonicalConstantSectionComparison JC JD L kappa A a T s hs W y

end CategoryTheory
