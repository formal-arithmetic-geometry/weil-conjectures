/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Condensed.Discrete.Characterization
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.LeftTExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# The first cohomology of a bounded below complex

Let `F : C ⥤ D` be a left exact functor between abelian categories, `C` with enough injectives
and K-injective resolutions. If `E ∈ D(C)` has no homology in degrees `< i`, then
`H^i(RF(E)) ≅ F(H^i(E))`: the truncation triangle `τ_{≤ i} E ⟶ E ⟶ τ_{> i} E` gives, as
`RF(τ_{> i} E)` has no homology in degrees `≤ i`, an isomorphism
`H^i(RF(τ_{≤ i} E)) ≅ H^i(RF(E))`, and `τ_{≤ i} E` is `H^i(E)` placed in degree `i`.

## Main statements

- `CategoryTheory.Functor.homologyRightDerivedFunctorObjSingleFunctorIsoSelf`:
  `H^n(RF(X[-n])) ≅ F(X)`.
- `CategoryTheory.Functor.nonempty_homology_rightDerivedFunctor_obj_iso_of_isGE`: the
  statement above.
- `AlgebraicGeometry.Etale.nonempty_homology_rightDerivedGlobalSections_obj_iso_of_isGE`
  (`lem-kun-minimal-cohomology`): `H^i(X_ét, E) ≅ H^0(X_ét, ℋ^i(E))` for
  `E ∈ D^{≥ i}(X_ét)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
  [PreservesFiniteLimits F]

/-- For a left exact functor `F`, the `n`-th homology of `RF` applied to `X` placed in degree `n`
is `F(X)`. -/
noncomputable def homologyRightDerivedFunctorObjSingleFunctorIsoSelf (X : C) (n : ℤ) :
    (DerivedCategory.homologyFunctor D n).obj
        (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C n).obj X)) ≅ F.obj X :=
  (DerivedCategory.homologyFunctor D n).mapIso
      (F.rightDerivedFunctor.mapIso
        (((DerivedCategory.singleFunctors C).shiftIso (-n) n 0 (by omega)).app X).symm) ≪≫
    (DerivedCategory.homologyFunctor D n).mapIso
      ((F.rightDerivedFunctor.commShiftIso (-n)).app
        ((DerivedCategory.singleFunctor C 0).obj X)) ≪≫
    ((DerivedCategory.homologyFunctor D 0).shiftIso (-n) n 0 (by omega)).app
      (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj X)) ≪≫
    F.homologyRightDerivedFunctorObjSingleFunctorIso X 0 ≪≫ F.rightDerivedZeroIsoSelf.app X

/-- **The first cohomology of a bounded below complex.** For a left exact functor `F` and an
object `E` of `D(C)` without homology in degrees `< i`, `H^i(RF(E)) ≅ F(H^i(E))`. -/
theorem nonempty_homology_rightDerivedFunctor_obj_iso_of_isGE (E : DerivedCategory C) (i : ℤ)
    [E.IsGE i] :
    Nonempty ((DerivedCategory.homologyFunctor D i).obj (F.rightDerivedFunctor.obj E) ≅
      F.obj ((DerivedCategory.homologyFunctor C i).obj E)) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let T := (t.triangleLTGE (i + 1)).obj E
  have hT : T ∈ distTriang _ := t.triangleLTGE_distinguished (i + 1) E
  let R := F.rightDerivedFunctor
  have hRT := R.map_distinguished T hT
  have h₃ : (R.obj T.obj₃).IsGE (i + 1) := F.isGE_rightDerivedFunctor_obj _ _
  have hmono : Mono ((DerivedCategory.homologyFunctor D i).map (R.map T.mor₁)) :=
    ((DerivedCategory.homologyFunctor D 0).homologySequence_mono_shift_map_mor₁_iff _ hRT
      (i - 1) i (by lia)).2
        (IsZero.eq_of_src (DerivedCategory.isZero_of_isGE (R.obj T.obj₃) (i + 1) _ (by lia)) _ _)
  have hepi : Epi ((DerivedCategory.homologyFunctor D i).map (R.map T.mor₁)) :=
    ((DerivedCategory.homologyFunctor D 0).homologySequence_epi_shift_map_mor₁_iff _ hRT i).2
      (IsZero.eq_of_tgt (DerivedCategory.isZero_of_isGE (R.obj T.obj₃) (i + 1) _ (by lia)) _ _)
  have : IsIso ((DerivedCategory.homologyFunctor D i).map (R.map T.mor₁)) :=
    isIso_of_mono_of_epi _
  have : T.obj₁.IsGE i := (inferInstance : ((t.truncLT (i + 1)).obj E).IsGE i)
  have : T.obj₁.IsLE i := t.isLE_of_le _ (i + 1 - 1) i (by lia)
  obtain ⟨A, ⟨e⟩⟩ := T.obj₁.exists_iso_singleFunctor_obj_of_isGE_of_isLE i
  have : IsIso ((DerivedCategory.homologyFunctor C i).map T.mor₁) :=
    DerivedCategory.isIso_homologyFunctor_map_truncLTι_app E (i + 1) i (by lia)
  let eA : A ≅ (DerivedCategory.homologyFunctor C i).obj E :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso C i).app A).symm ≪≫
      (DerivedCategory.homologyFunctor C i).mapIso e.symm ≪≫
        asIso ((DerivedCategory.homologyFunctor C i).map T.mor₁)
  exact ⟨(asIso ((DerivedCategory.homologyFunctor D i).map (R.map T.mor₁))).symm ≪≫
    (DerivedCategory.homologyFunctor D i).mapIso (R.mapIso e) ≪≫
      F.homologyRightDerivedFunctorObjSingleFunctorIsoSelf A i ≪≫ F.mapIso eA⟩

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `lem-kun-minimal-cohomology`: **first cohomology of a bounded below complex.**
Let `X` be a scheme and `E ∈ D(X_ét, Λ)` with `ℋ^q(E) = 0` for `q < i` (for instance `i`
minimal with `ℋ^i(E) ≠ 0`). Then `H^i(X_ét, E) ≅ H^0(X_ét, ℋ^i(E)) = Γ(X, ℋ^i(E))`. The
blueprint uses the hypercohomology spectral sequence; here the truncation triangle
`τ_{≤ i} E ⟶ E ⟶ τ_{> i} E` is used directly
(`CategoryTheory.Functor.nonempty_homology_rightDerivedFunctor_obj_iso_of_isGE`). -/
theorem nonempty_homology_rightDerivedGlobalSections_obj_iso_of_isGE (X : Scheme.{u})
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (i : ℤ)
    [E.IsGE i] :
    Nonempty ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj E) ≅
      (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        ((_root_.DerivedCategory.homologyFunctor _ i).obj E)) :=
  (Sheaf.Γ X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)).nonempty_homology_rightDerivedFunctor_obj_iso_of_isGE E i

end AlgebraicGeometry.Etale
