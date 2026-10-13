/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.AlgebraicGeometry.PerfectUniversalH0LocalChainModel
import Sheaf.AlgebraicGeometry.BottomChainModelPullbackTransport
import Sheaf.Topology.SheafIsomorphismLocalOpenCover

/-! # Canonical truncation on a universally free lowest-cohomology locus

Source: Stacks Project, Tag 0BDL, matrix-chart proof and pullback clause.
(blueprint: lem-sc-perfect-universal-h0-truncation-pullback).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem bottom_homologyMap_isIso
    {C : Type*} [Category C] [Abelian C]
    {P Q : CochainComplex C ℤ} (β : P ⟶ Q)
    (hPnegative : IsZero (P.X (-1))) (hQnegative : IsZero (Q.X (-1)))
    (hPzero : P.d 0 1 = 0) (hQzero : Q.d 0 1 = 0)
    (hβ : IsIso (β.f 0)) : IsIso (HomologicalComplex.homologyMap β 0) := by
  have hp : (ComplexShape.up ℤ).prev 0 = -1 :=
    (ComplexShape.up ℤ).prev_eq' (by decide)
  have hn : (ComplexShape.up ℤ).next 0 = 1 :=
    (ComplexShape.up ℤ).next_eq' (by decide)
  let φ := (HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) 0).map β
  have hfP : (P.sc 0).f = 0 := by
    change P.d ((ComplexShape.up ℤ).prev 0) 0 = 0
    rw [hp]
    exact hPnegative.eq_of_src _ _
  have hfQ : (Q.sc 0).f = 0 := by
    change Q.d ((ComplexShape.up ℤ).prev 0) 0 = 0
    rw [hp]
    exact hQnegative.eq_of_src _ _
  have hgP : (P.sc 0).g = 0 := by
    change P.d 0 ((ComplexShape.up ℤ).next 0) = 0
    rw [hn]
    exact hPzero
  have hgQ : (Q.sc 0).g = 0 := by
    change Q.d 0 ((ComplexShape.up ℤ).next 0) = 0
    rw [hn]
    exact hQzero
  change IsIso (ShortComplex.homologyMap φ)
  rw [(ShortComplex.LeftHomologyMapData.ofZeros φ hfP hgP hfQ hgQ).homologyMap_eq]
  change IsIso (_ ≫ β.f 0 ≫ _)
  infer_instance

/-- Pulling back a degree-zero truncation preserves its degree-zero isomorphism on
an open cover with universally constant free lowest cohomology.
Source: Stacks Project, Tag 0BDL, matrix-chart proof and pullback clause; Tag 0BCD.
(blueprint: lem-sc-perfect-universal-h0-truncation-pullback).

Proof:
1. At a point choose the given open U and rank r. Test its universal freeness
   condition at the residue field. The lowest fibre dimension is r. Choose the
   bounded finite-free residue model from Tag 0BCD, shrinking inside U.
   The negative derived-fibre vanishing makes every negative term zero.
2. The first term has rank r and its kernel is H0(K), also locally free of rank r
   by the identity test. Trivialize this kernel locally. Its inclusion into the
   first term is an injective square free map. Its cokernel has zero dual by
   Tag 0EWY; each coordinate of the outgoing differential factors through that
   cokernel and is therefore zero. Thus d0 is zero, including over nonreduced bases.
3. The H0 isomorphism makes M finite locally free on this chart. Trivialize M
   and represent a by a chain map from M[0] into the bounded finite-free model,
   using the affine perfect-map representative theorem (Tag 08CR). Because there
   are no negative terms and d0 is zero, its degree-zero component is exactly its
   H0 map, hence an isomorphism. Termwise pullback computes derived pullback of
   both bounded finite-free complexes. It retains the zero outgoing differential
   and absence of negative terms. Its H0 map is the pullback of that invertible
   component. This proves invertibility locally.
4. Restrict to inverse images of these opens on Y. Derived pullback and exact open
   restriction commute. These opens cover Y, and a map of module sheaves is an
   isomorphism if it is one on this cover. Empty schemes and rank zero are included.
No comparison with an ordinary direct-image map is asserted here. -/
theorem perfect_universalH0_truncation_pullback_isIso
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (S : Scheme.{u})
    [∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (K : schemeDerivedCategory S) (hK : IsPerfect S K)
    (hnegative : ∀ (Y : Scheme.{u}) (k : Y ⟶ S) (i : ℤ), i < 0 →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj
          ((derivedPullback k).obj K)))
    (hloc : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ r : ℕ,
      ∀ (Y : Scheme.{u}) (k : Y ⟶ U.toScheme),
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((derivedPullback (k ≫ U.ι)).obj K)) r)
    (M : S.Modules)
    (a : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj M ⟶ K)
    (ha : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map a))
    {Y : Scheme.{u}} (k : Y ⟶ S) :
    IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map
        ((derivedPullback k).map a)) := by
  classical
  let g := (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map
      ((derivedPullback k).map a)
  have hlocal : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ IsIso (g.over V) := by
    intro y
    obtain ⟨U, hy, A, B, hA, hB, hAzero, hBnegative, hBzero,
      α, hα, eA, eB, hsquare⟩ :=
      perfect_universalH0_local_chain_model S K hK hnegative hloc M a ha (k.base y)
    obtain ⟨V, hyV, P, Q, hPnegative, hQnegative, hPzero, hQzero,
      β, hβ, eP, eQ, hβsquare⟩ :=
      bottom_chain_model_pullback_transport S _ K a U A B hA hB hAzero
        hBnegative hBzero α hα eA eB hsquare k y hy
    have := bottom_homologyMap_isIso β hPnegative hQnegative hPzero hQzero hβ
    have : IsIso (g.over V ≫ eQ.hom) := by
      rw [hβsquare]
      infer_instance
    exact ⟨V, hyV, IsIso.of_isIso_comp_right (g.over V) eQ.hom⟩
  choose V hV hIso using hlocal
  have hcover : ⨆ y, V y = ⊤ := by
    ext y
    change y ∈ (⨆ y, V y : Y.Opens) ↔ y ∈ (⊤ : Y.Opens)
    constructor
    · intro _
      trivial
    · intro _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hV y⟩
  exact (sheaf_module_isIso_iff_isIso_over_open_cover.{u, u, u}
    Y.toRingedSpace Y V hcover _ _ g).2 hIso

end AlgebraicGeometry.Scheme
