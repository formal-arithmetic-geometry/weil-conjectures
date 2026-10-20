/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.FiniteTorAmplitude
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Compactification.BaseChange

/-!
# The canonical composition arrow for a finite-horizontal compact-support square

Source: blueprint main-20261015, proof (β) of `lem-trf-weil-shriek-operator-fibres`,
normalized equation (C) in the proof of `lem-trf-finite-horizontal-shriek-mate`
(blueprint: def-trf-finite-horizontal-shriek-composition).

The proper/open arrow is the published `sfProperOpenDerivedComparison`, independently
of any exceptional-base-change theorem. This module reexports that construction and
uses it to construct χ. Positive-level coefficient finiteness is supplied directly
by `Padic.finite_coefficientExtensionRing` where the chosen coefficients are introduced.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The existing intrinsic pro-etale finite-Tor predicate, reexported without changing it.
Source: blueprint `def-weil-finite-tor-amplitude`, intrinsic finite-level clause
(blueprint: def-trf-finite-horizontal-shriek-composition). -/
abbrev finiteHorizontalFiniteTorConstructible
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (Y : Scheme.{u}) :
    ObjectProperty (proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n)) :=
  finiteTorConstructible l E n hn Y

/-- The canonical proper/open comparison used by the composition construction.
Source: blueprint `prop-exc-base-change-proper`, Steps 2--3
(blueprint: def-trf-finite-horizontal-shriek-composition). -/
noncomputable def finiteHorizontalProperOpenComparison
    (A : Type u) [CommRing A] [Finite A]
    {U V W T : Scheme.{u}}
    (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k]
    (sq : IsPullback r k i p) :
    proEtaleConstantDerivedDirectImage r A ⋙ sfIntrinsicDerivedOpen A i ⟶
      sfIntrinsicDerivedOpen A k ⋙ proEtaleConstantDerivedDirectImage p A :=
  sfProperOpenDerivedComparison A r k i p sq

/-- The composition/proper-coincidence arrow χ in its chosen-compactification model.
Source: blueprint proof (β), normalized equation (C) in the node proof;
Stacks Tags 0F7B and 0F7J (blueprint: def-trf-finite-horizontal-shriek-composition).

For `c = (j,b)` and its Cartesian base change `(j',b')`, this is `Rb_*(γ)` followed
by the canonical direct-image square isomorphism σ. Here γ is the published
open-adjunction transpose of inverse sectionwise restriction, and σ is the conjugate
of the specified pullback square under the two composite adjunctions. On the stated
finite-horizontal constructible domain this is precisely the composition isomorphism
`Rf_! Rp_* ≅ R(fp)_! = R(gf')_! ≅ Rg_* Rf'_!`, with the identity-open proper normalization.
The formula defines its arrow without presupposing its invertibility. -/
def finiteHorizontalShriekComposition (A : Type u) [CommRing A] [Finite A]
    {X' X Y' Y : Scheme.{u}} {p : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback p f' f g)
    (c : Compactification f) :
    proEtaleConstantDerivedDirectImage p A ⋙ sfIntrinsicCompactSupport c A ⟶
      sfIntrinsicCompactSupport (c.ofIsPullback sq) A ⋙
        proEtaleConstantDerivedDirectImage g A := by
  let c' := c.ofIsPullback sq
  let q : c'.Z ⟶ c.Z := pullback.fst c.g g
  let γ := finiteHorizontalProperOpenComparison A p c'.i c.i q
    (c.isPullback_i_ofIsPullback sq)
  let σ := conjugateIsoEquiv
    (((sfIntrinsicConstantModuleAdjunction c.g A).mapDerivedCategoryRightDerivedAdjunction).comp
      (sfIntrinsicConstantModuleAdjunction q A).mapDerivedCategoryRightDerivedAdjunction)
    (((sfIntrinsicConstantModuleAdjunction g A).mapDerivedCategoryRightDerivedAdjunction).comp
      (sfIntrinsicConstantModuleAdjunction c'.g A).mapDerivedCategoryRightDerivedAdjunction)
    (sfIntrinsicDerivedSquarePullback A q c'.g c.g g
      (c.isPullback_g_ofIsPullback sq).flip.w).symm
  exact (Functor.associator _ _ _).inv ≫ Functor.whiskerRight γ _ ≫
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft _ σ.hom ≫
    (Functor.associator _ _ _).inv

end WeilConjectures
