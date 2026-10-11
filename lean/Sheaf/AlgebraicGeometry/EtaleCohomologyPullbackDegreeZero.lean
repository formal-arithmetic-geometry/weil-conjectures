/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.Single

/-!
# Degree-zero étale cohomology and pullback

Source: Stacks Project, Tags 05TD and 01FA
(blueprint: lem-weil-pbc-cohomology-pullback-degree-zero).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

namespace AlgebraicGeometry.Etale

/-- The augmentation of any K-injective resolution induces the canonical isomorphism
from global sections to degree-zero cohomology. The factor `z` records well-definedness:
its composite with the inclusion of cycles is precisely the augmentation on sections.
Source: Stacks Tag 05TD (blueprint: lem-weil-pbc-cohomology-pullback-degree-zero).

Proof:
1. The chain-map identity for `s` makes its degree-zero component a cocycle, giving `z`.
2. A homotopy between lifts of a sheaf map makes their difference a boundary; this gives
   naturality and compatibility with comparisons (cohomology-pullback-functorial).
3. Global sections preserve kernels. Choose a nonnegative injective resolution; then its
   degree-zero cycles are the sections of `G`, with no boundaries (left-exact-injective-
   resolution-degree-zero). It is K-injective (dplus-injective-representative).
4. Transport that isomorphism to `I` by the homotopy equivalence between K-injective
   resolutions (cohomology-resolution-independent). Negative terms of `I` are allowed. -/
theorem exists_degreeZeroCohomology_cycles_iso (T : Scheme.{u})
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (s : (CochainComplex.singleFunctor _ 0).obj G ⟶ I)
    [QuasiIso s] [I.IsKInjective] :
    ∃ z : (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj G ⟶
        (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I).cycles 0,
      z ≫ (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).iCycles 0 =
        (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          ((singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫ s.f 0) ∧
      IsIso (z ≫ (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).homologyπ 0) := by
  sorry

/-- Naturality of the augmentation-to-cohomology map for arbitrary K-injective resolutions.
Taking `G' = G` and `φ = 𝟙 G` gives compatibility with resolution identifications.
Source: Stacks Tag 05TD (blueprint: lem-weil-pbc-cohomology-pullback-degree-zero).

Proof: Lift `φ` to `a` between the resolutions (cohomology-pullback-functorial).
The given homotopy in degree zero says that `a⁰ s⁰ - s'⁰ φ` is `d⁻¹ h⁰`.
After global sections it is a boundary, hence zero in homology. For the identity sheaf
map, the lift induces the resolution comparison (cohomology-resolution-independent).
The existence and bijectivity of the augmentation map are established by the preceding
four-step argument using a nonnegative injective resolution and transport. -/
theorem degreeZeroCohomology_resolution_naturality (T : Scheme.{u})
    (G G' : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (φ : G ⟶ G')
    (I I' : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (s : (CochainComplex.singleFunctor _ 0).obj G ⟶ I)
    (s' : (CochainComplex.singleFunctor _ 0).obj G' ⟶ I')
    [QuasiIso s] [QuasiIso s'] [I.IsKInjective] [I'.IsKInjective]
    (a : I ⟶ I')
    (h : Homotopy (s ≫ a) ((CochainComplex.singleFunctor _ 0).map φ ≫ s'))
    (z : (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj G ⟶
      (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).cycles 0)
    (z' : (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj G' ⟶
      (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I').cycles 0)
    (hz : z ≫ (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).iCycles 0 =
      (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫ s.f 0))
    (hz' : z' ≫ (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I').iCycles 0 =
      (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((singleObjXSelf (ComplexShape.up ℤ) 0 G').inv ≫ s'.f 0)) :
    z ≫ (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).homologyπ 0 ≫
      homologyMap (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).map a) 0 =
    (Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).map φ ≫ z' ≫
      (((Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I').homologyπ 0 := by
  sorry

/-- The degree-zero pullback formula on the actual complexes computing cohomology.
Source: Stacks Tag 01FA (blueprint: lem-weil-pbc-cohomology-pullback-degree-zero).

Proof: The chain map on sections is the unit followed by the pushforward/global-sections
identification and the comparison `r`. The chain-map identity makes `s(g)` a cycle.
Naturality of the unit at `s⁰` gives `r(η(s(g))) = (r ∘ u⁻¹s)(η(g))`.
Passing to homology proves the equality. The four-step bounded-below/transport argument
above makes both augmentation maps isomorphisms; homotopy naturality proves compatibility
with every choice of resolution (cohomology-pullback-functorial and
cohomology-resolution-independent). No vanishing of negative terms is assumed. -/
theorem degreeZeroCohomology_resolution_pullback {X Y : Scheme.{u}} (u : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (J : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (s : (CochainComplex.singleFunctor _ 0).obj G ⟶ I)
    (r : ((upperStar AddCommGrpCat.{u + 1} u).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J)
    [QuasiIso s] [I.IsKInjective] [QuasiIso r] [J.IsKInjective]
    (z : (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj G ⟶
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).cycles 0)
    (z' : (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      ((upperStar AddCommGrpCat.{u + 1} u).obj G) ⟶
      (((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J).cycles 0)
    (hz : z ≫ (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).iCycles 0 =
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫ s.f 0))
    (hz' : z' ≫ (((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J).iCycles 0 =
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((upperStar AddCommGrpCat.{u + 1} u).map
          ((singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫ s.f 0) ≫ r.f 0)) :
    z ≫ (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).homologyπ 0 ≫
      homologyMap
        ((NatTrans.mapHomologicalComplex
          (Functor.whiskerRight (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} u).unit
              (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}) ≫
            (Functor.associator (upperStar AddCommGrpCat.{u + 1} u)
              (lowerStar AddCommGrpCat.{u + 1} u)
              (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1})).hom ≫
            Functor.whiskerLeft (upperStar AddCommGrpCat.{u + 1} u)
              (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} u).hom)
          (ComplexShape.up ℤ)).app I ≫
          ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
            (ComplexShape.up ℤ)).map r) 0 =
    globalSectionsUpperStarMap AddCommGrpCat.{u + 1} u G ≫ z' ≫
      (((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J).homologyπ 0 := by
  sorry

/-- Under the canonical degree-zero identification, pullback on étale cohomology is
pullback of a global section by the adjunction unit.
Source: Stacks Tag 01FA (blueprint: lem-weil-pbc-cohomology-pullback-degree-zero).

Proof: For resolutions `s : G[0] → I` and `r : u⁻¹I → J`, the pullback of `[s(g)]` is
`[r(η(s(g)))]`. Naturality of the inverse-image unit gives
`η(s(g)) = (u⁻¹s)(η(g))`, so this is `[t(η(g))]` for `t = r ∘ u⁻¹s`.
The preceding naturality computation permits every choice of K-injective resolution,
by cohomology-pullback-functorial and cohomology-resolution-independent. In the recorded
Ext encoding of cohomology-pullback, the same identity follows by the degree-zero Ext/Hom
identification and the constant-sheaf adjunction defining `Sheaf.H.equiv₀`. -/
theorem cohomologyMap_zero_eq_globalSectionsUpperStarMap {X Y : Scheme.{u}}
    (u : Y ⟶ X) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (g : (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj G) :
    cohomologyMap u G 0
      ((Sheaf.H.equiv₀ G terminalIsTerminal).symm
        ((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app G g)) =
    (Sheaf.H.equiv₀ ((upperStar AddCommGrpCat.{u + 1} u).obj G) terminalIsTerminal).symm
      ((Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
        terminalIsTerminal).hom.app ((upperStar AddCommGrpCat.{u + 1} u).obj G)
        (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} u G g)) := by
  sorry

end AlgebraicGeometry.Etale
