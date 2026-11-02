/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralUnderived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClUnderived

import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Finite filtration induction for a proper heart bound

The finite lisse-stratum filtration from the coefficient-heart theorem reduces the
bound to short exact sequences. The total derived pushforward preserves their
triangles, and exact homology passes vanishing from the outer terms to the middle.
(blueprint: det-proper-heart-bound-filtration).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Finite-stratum devissage for the proper heart bound.

Source: blueprint `sk-lem-proper-heart-bound-reduction.proof.md`, paragraphs Extensions and
Strata.

Proof in words. The hypothesis `hbound` is the bound `R^q p_* (a_! N) = 0` for `q > c` for every
locally closed stratum `a : S → X` and every lisse `Λ_S`-module `N`, with `a_!` the canonical
extension `coefficientHeartLocallyClosedExtension`. Since `X` is Noetherian and `M` constructible,
[det-lem-coefficient-heart-closure] and [det-lem-coefficient-heart-common-stratification] give a
finite stratification adapted to `M` with open initial unions, and
[det-lem-coefficient-heart-filtration] gives the finite open-prefix filtration
`0 = M_0 ⊆ ⋯ ⊆ M_m = M` with `M_j / M_{j-1} ≅ (b_j)_!(M|_{T_j})` and every `M|_{T_j}` lisse.
Each subquotient satisfies the bound by `hbound`. For the short exact sequences
`0 → M_{j-1} → M_j → (b_j)_!(M|_{T_j}) → 0` the long exact sequence of `R p_*`
[lem-weil-pbc-derived-functor-long-exact] gives the bound for `M_j` from those of its outer
terms; induction from `M_0 = 0` gives it for `M`.
(blueprint: det-proper-heart-bound-filtration). -/
theorem det_proper_heart_bound_filtration
    (l : ℕ) [Fact l.Prime] (pchar : ℕ) [Fact pchar.Prime]
    (k : Type u) [Field k] [CharP k pchar] (hpchar : 0 < pchar) (hpl : pchar ≠ l)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (E : PadicAlgCl.FiniteIntermediateField l)
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X]
    (hΛ : Λ = Mon.mk (Profinite.continuousMapRingObj E.1) ∨
      Λ = Mon.mk (Profinite.padicAlgClRingObj l))
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] (c : ℤ)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X))
    (hM : IsConstantModelConstructible Λ.X X M)
    [IsNoetherian X]
    (hbound : ∀ {S : Scheme.{u}} (a : S ⟶ X) [IsImmersion a]
      (N : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ.X S)),
      IsLisseCoefficientModule Λ.X N →
      ∀ q : ℤ, c < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((moduleObjectDerivedPushforward Λ.X p).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((coefficientHeartLocallyClosedExtension Λ.X a inferInstance).obj N))))) :
    ∀ q : ℤ, c < q → IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((moduleObjectDerivedPushforward Λ.X p).obj
        ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  classical
  have _hpchar := hpchar
  have hfil : CoefficientHeartFiltrationAssertions Λ.X X := by
    rcases hΛ with rfl | rfl
    · have h := coefficientHeart l (Profinite.padicSubfieldCondensedRing l E.1)
        (Or.inl ⟨E.1, E.2, rfl⟩) k pchar hpl X
      exact h.2.2.2.2.2.2.2.2.2.2.1
    · have h := coefficientHeart l (Profinite.padicAlgClCondensedRing l)
        (Or.inr rfl) k pchar hpl X
      exact h.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨m, B, hbot, htop, hle, hquot⟩ := hfil ⟨M, hM⟩
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)
  let C := Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ.X Y)
  let F := (lowerStar Λ.X p).rightDerivedFunctor
  intro q hq
  let H : A ⥤ C := DerivedCategory.singleFunctor A 0 ⋙ F ⋙
    DerivedCategory.homologyFunctor C q
  have hgraded (a : Fin m) :
      IsZero (H.obj (cokernel (Subobject.ofLE (B a.castSucc) (B a.succ) (hle a)))) := by
    obtain ⟨S, j, hj, L, hL, ⟨e⟩⟩ := hquot a
    let : IsImmersion j := hj
    exact (hbound j L hL q hq).of_iso (H.mapIso e)
  have tower (n : ℕ) (hn : n < m + 1) : IsZero (H.obj (B ⟨n, hn⟩ : A)) := by
    induction n with
    | zero =>
      have hz : IsZero (B 0 : A) :=
        (isZero_zero A).of_iso
          (Subobject.isoOfEq _ _ hbot ≪≫ Subobject.botCoeIsoZero)
      exact H.map_isZero hz
    | succ n ih =>
      let a : Fin m := ⟨n, by omega⟩
      let f := Subobject.ofLE (B a.castSucc) (B a.succ) (hle a)
      let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
      have hS : S.ShortExact :=
        ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel f)
          inferInstance inferInstance
      have hex := (F ⋙ DerivedCategory.homologyFunctor C q).map_distinguished_exact
        _ hS.singleTriangle_distinguished
      exact hex.isZero_of_both_isZero (ih (by omega)) (hgraded a)
  have e : (B (Fin.last m) : A) ≅ M :=
    Subobject.isoOfEq _ _ htop ≪≫ Subobject.underlyingIso (𝟙 M)
  exact (tower m (Nat.lt_succ_self m)).of_iso (H.mapIso e).symm

end AlgebraicGeometry.ProEtale.CondensedRing
