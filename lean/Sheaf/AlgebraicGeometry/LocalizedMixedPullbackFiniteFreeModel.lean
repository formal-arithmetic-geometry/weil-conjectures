/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Sheaf.AlgebraicGeometry.LocalizedMixedDerivedPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Termwise finite-free models under localized derived pullback
Source: Stacks Project, Tags 06YD, 06YJ and 08DW.
(blueprint: lem-pc-localized-mixed-pullback-finite-free-model).
-/

@[expose] public section
set_option autoImplicit false
universe u wX wS wT wW wY
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Compute the localized derived pullback of an exact open restriction termwise.
Source: Stacks Project, Tags 06YD, 06YJ and 08DW.
Proof: the finite free terms of P are flat, including rank zero, and the bounded-above
complex P is K-flat by Tag 06YD. Exact restriction to W preserves its bound and
identifies its terms with finite free modules on W of the same ranks, so the
restricted complex is also K-flat. The localization uniqueness isomorphism intertwines
Qh, and quotientCompQhIso converts it to Q. The exact-functor factorization identifies
the transported restriction of Q(P) with Q of the termwise restricted complex in the
standard localization on W. Apply flatComplexDerivedPullback to this restricted
complex and g, then use its homotopy-quotient factorization to identify the answer
with Q of termwise tensor pullback. The tensor pullback composition isomorphism and
the identification of open restriction with open tensor pullback identify this
complex with pullback along g followed by W.ι. The exact inverse overEquiv V and its
factorization transport this identification to the localized module site. Finally
map the supplied natural isomorphism eL termwise and through Q. These operations
are valid for any bound, for empty opens and for zero complexes; no morphism p or
coefficient sheaf M occurs in this assertion.
(blueprint: lem-pc-localized-mixed-pullback-finite-free-model). -/
theorem localizedMixedDerivedPullback_finiteFree_model
    {S T : Scheme.{u}}
    [HasDerivedCategory.{wT}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (U : S.Opens) (V : U.toScheme.Opens) (W : T.Opens)
    [HasDerivedCategory.{wW}
      (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (g : V.toScheme ⟶ W.toScheme)
    (L : T.Modules ⥤ SheafOfModules.{u}
      ((moduleRings U.toScheme.toRingedSpace).over V))
    (eL : Nonempty (L ≅ Scheme.Modules.tensorPullback (g ≫ W.ι) ⋙
      (Scheme.Modules.overEquiv V).inverse)) [L.Additive]
    (P : CochainComplex T.Modules ℤ)
    (hP : ∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P.X i))
    (hfree : ∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
      (R := moduleRings T.toRingedSpace) (ULift.{u} (Fin r))))
 :
    Nonempty ((localizedMixedDerivedPullback U V W g).obj
      ((schemeOpenRestriction T W).mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≅
      DerivedCategory.Q.obj ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
  by sorry

end AlgebraicGeometry
