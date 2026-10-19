/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.RingedSiteDualityMaps
import Sheaf.CategoryTheory.RingedSitePerfectOrdinaryDual
import Sheaf.CategoryTheory.RingedSitePerfectDualLocalComparison

/-! # RingedSitePerfectDualLocalModel

Source: Stacks Project, Tag 08JJ (blueprint: lem-sfb-perfect-dual-local-model).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- The fixed K-injective model of the coefficient dual is locally strictly perfect.
Source: Stacks Project, sites-cohomology.tex, Tag 08JJ, proof paragraphs 1 and 2;
Tags 08JH, 08FI and 070I for the Hom comparison and actual local maps.
Proof: for each object V use the covering sieve in hK. On a member U choose the
bounded finite-free-retract model E and its quasi-isomorphism to K restricted to U.
Exact restriction and internal-Hom restriction identify the restriction of the
stated model with RHom(E,O). Splitting each term of E off a finite free sheaf
shows that Hom(E^i,-) is exact. The bounded-exact-source Hom lemma therefore
computes this derived Hom by D=Hom(E,O[0]). Its degree q term is the dual of
E^(-q), with differential (-1)^(q+1) times the dual differential. Dualizing the
chosen splitting makes each term a finite free retract, and bounds [a,b] become
[-b,-a]. The outer fixed replacement is K-injective; restriction to U preserves
K-injectivity. The derived isomorphism QD to this restriction lifts to an actual
chain map by the K-injective Hom comparison. Since its localization is an
isomorphism it is a quasi-isomorphism. This D and chain map, on the same covering
sieve, satisfy every clause of local strict perfectness. Empty intervals and
rank zero give zero complexes and the same construction.
(blueprint: lem-sfb-perfect-dual-local-model). -/
theorem ringedSitePerfectDual_localModel
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (K : CochainComplex (SheafOfModules.{max c v r} ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (hK : SheafOfModules.IsLocallyStrictPerfectComplexOfUniverses.{c, v, r} R K) :
    SheafOfModules.IsLocallyStrictPerfectComplexOfUniverses.{c, v, r} R
      ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj
        (homComplex (R := R) K
          ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj
            (ringedSiteDualityUnitComplex.{c, v, r} J R))))  := by
  intro V
  obtain ⟨S, hS, hmodels⟩ := hK V
  refine ⟨S, hS, ?_⟩
  intro U f hf
  obtain ⟨E, hbound, ⟨pkg⟩, α, hα⟩ := hmodels U f hf
  obtain ⟨hdualBound, hdualPkg⟩ :=
    ringedSitePerfect_ordinaryDual.{max c v, v, r} (R.over U) E hbound pkg
  obtain ⟨β, hβ⟩ :=
    ringedSitePerfectDual_localComparison.{c, v, r, w} J R K U E hbound pkg α hα
  exact ⟨_, hdualBound, hdualPkg, β, hβ⟩

end CategoryTheory
