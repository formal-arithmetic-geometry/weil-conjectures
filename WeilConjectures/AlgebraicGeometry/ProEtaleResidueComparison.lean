/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleProEtaleExceptionalTransport
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf

/-! Comparison of residue maps across the étale/pro-étale site comparison.
(blueprint: lem-sf-proetale-residue-comparison)

The helper transports a residue isomorphism through the natural derived tensor comparison of the
exact strong monoidal site comparison, and reflects it to the étale model on every cohomology
sheaf, using that the site comparison is exact and fully faithful.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

-- The exact conservative argument works without the retained origin and boundedness hypotheses.
set_option linter.unusedVariables false in
/-- Residue isomorphisms of a morphism between exceptional étale origins follow from the
corresponding residue isomorphisms after comparison to the pro-étale site.

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-lem-sf-kunneth-star/
sk-lem-sf-kunneth-star.proof.md, residue comparison component
(blueprint: lem-sf-proetale-residue-comparison).

Proof: let `F` be the site comparison `ν^*`. Fix a maximal ideal `m` and let `N` be the
constant étale sheaf `A/m` in degree `0`. Since `F` is exact and preserves constant sheaves,
`D(F) N` is isomorphic to the constant pro-étale sheaf `A/m` in degree `0`. Tensoring
`D(F) w = e.hom ≫ u ≫ e'.inv` with the latter gives an isomorphism by `hres`; transported along
this isomorphism, `D(F) w ⊗ D(F) N` is an isomorphism. The natural isomorphism
`D(F)(X ⊗ N) ≅ D(F) X ⊗ D(F) N` (`F` is strong monoidal and preserves flat sheaves) and its
naturality in `w` show that `D(F)(w ⊗ N)` is an isomorphism. For every `i`, `H^i ∘ D(F) ≅ F ∘ H^i`
since `F` is exact, so `F (H^i (w ⊗ N))` is an isomorphism; `F` is fully faithful (its unit is
invertible), hence reflects isomorphisms, so every `H^i (w ⊗ N)` is an isomorphism and `w ⊗ N`,
the residue map `reductionModIdeal m` applied to `w`, is an isomorphism. No boundedness or
flatness of `A/m` is used; the origin and boundedness hypotheses are kept for the callers. -/
theorem etale_residue_isIso_of_pro_residue_isIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    {E E' : Etale.DerivedCategoryModule A S}
    (hE : exceptionalTransportEtaleObjects A S E)
    (hE' : exceptionalTransportEtaleObjects A S E')
    (hplusE : _root_.DerivedCategory.TStructure.t.plus E)
    (hplusE' : _root_.DerivedCategory.TStructure.t.plus E')
    (w : E ⟶ E')
    {K K' : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A))}
    (e : (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj E ≅ K)
    (e' : (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj E' ≅ K')
    (u : K ⟶ K')
    (hw : (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.map w =
      e.hom ≫ u ≫ e'.inv)
    (hres : ∀ m : Ideal A, m.IsMaximal →
      IsIso (((derivedTensor (ModuleCat.{u + 1} A) S).map u).app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)).obj
            (ModuleCat.of A (A ⧸ m)))))) :
    ∀ m : Ideal A, m.IsMaximal → IsIso ((Etale.reductionModIdeal A S m).map w) := by
  let F := comparisonUpperStar (ModuleCat.{u + 1} A) S
  intro m hm
  let M := ModuleCat.of A (A ⧸ m)
  let N := (_root_.DerivedCategory.singleFunctor _ 0).obj
    ((constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)
  let N' := (_root_.DerivedCategory.singleFunctor _ 0).obj
    ((constantSheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A)).obj M)
  let c : F.mapDerivedCategory.obj N ≅ N' :=
    (F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso
        ((constantSheafCompComparisonUpperStarIso (ModuleCat.{u + 1} A) S).app M)
  have hpro : IsIso (((curriedTensor _).flip.obj N').map
      (F.mapDerivedCategory.map w)) := by
    change IsIso (((derivedTensor (ModuleCat.{u + 1} A) S).map
      (F.mapDerivedCategory.map w)).app N')
    rw [hw, Functor.map_comp, Functor.map_comp, NatTrans.comp_app, NatTrans.comp_app]
    have := hres m hm
    infer_instance
  have hproN : IsIso (((curriedTensor _).flip.obj (F.mapDerivedCategory.obj N)).map
      (F.mapDerivedCategory.map w)) :=
    (NatIso.isIso_map_iff ((curriedTensor _).flip.mapIso c)
      (F.mapDerivedCategory.map w)).2 hpro
  have hn := congr_app (F.mapDerivedCategoryTensorComparison.naturality w) N
  change F.mapDerivedCategory.map (((curriedTensor _).flip.obj N).map w) ≫
      (F.mapDerivedCategoryTensorComparison.app E').app N =
    (F.mapDerivedCategoryTensorComparison.app E).app N ≫
      ((curriedTensor _).flip.obj (F.mapDerivedCategory.obj N)).map
        (F.mapDerivedCategory.map w) at hn
  have : IsIso (F.mapDerivedCategory.map (((curriedTensor _).flip.obj N).map w) ≫
      (F.mapDerivedCategoryTensorComparison.app E').app N) := by
    rw [hn]
    infer_instance
  have hi : IsIso (F.mapDerivedCategory.map (((curriedTensor _).flip.obj N).map w)) :=
    IsIso.of_isIso_comp_right _ ((F.mapDerivedCategoryTensorComparison.app E').app N)
  change IsIso (((curriedTensor _).flip.obj N).map w)
  rw [_root_.DerivedCategory.isIso_iff]
  intro i
  have : IsIso (F.map ((_root_.DerivedCategory.homologyFunctor _ i).map
      (((curriedTensor _).flip.obj N).map w))) :=
    (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso i)
      (((curriedTensor _).flip.obj N).map w)).2
        (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ F

end AlgebraicGeometry.ProEtale
