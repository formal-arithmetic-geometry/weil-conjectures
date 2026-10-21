/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Paper.CompletedConstantSheafReduction
public import Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.CategoryTheory.FiniteTypeConstantExact
import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
import Sheaf.RingTheory.IndEtaleStability
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
import Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk

/-! # Uniform bounds and finite reductions of stratified perfect models

Source: Bhatt--Scholze, Lemma 6.6.10(1), Proposition 6.6.11, reverse implication;
Stacks Tags 06YS, 06YT, 06YU and 093J.
(blueprint: lem-weil-pbc-perfect-strata-uniform-reductions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Uniform bounds for K and all positive finite reductions, intrinsic constructibility,
and finite constant models on every member of the original stratum covers.
Source: Bhatt--Scholze, Lemma 6.6.10(1), Proposition 6.6.11, reverse implication;
Stacks Tags 06YS, 06YT, 06YU and 093J
(blueprint: lem-weil-pbc-perfect-strata-uniform-reductions).

Proof, following the seven steps of the DAG node:
1. Represent each perfect A-complex by a bounded finite-projective complex. Each term
splits off a finite free module. Constants and scalar extension preserve the splitting;
these sheaves are flat and the bounded complexes are K-flat by
lem-pc-bounded-above-flat-kflat-site. Their term bounds are local cohomology bounds.
2. Apply lem-weil-pbc-stratum-completion-unit-restriction to the immersion followed by
the chosen covering member. Its exact restrictions commute with cohomology, identify
the completed and quotient coefficients, and commute with derived reduction. No
completion unit is used.
3. Compute reduction by the preceding K-flat model, using
lem-pur-derived-change-of-rings. The balancing map sends (b tensor p) tensor c to
p tensor pi_n(b)c. It is invertible for finite free modules and hence for their
retracts, and commutes with differentials. Thus the reduced local complex is the
constant complex P tensor_A A/I^(n+1), with the same term bounds for every n.
4. By lem-weil-pbc-finite-type-constant-exact, its cohomology is the constant module
H^q(P tensor_A A/I^(n+1)). Its terms are retracts of finite powers of the finite
quotient ring, so its cycles and cohomology are finite sets and finite modules.
5. Apply lem-sfb-stratified-local-cohomological-bounds to select finitely many
quasi-compact opens in the given covering members. Weakly etale stability and
lem-weil-pbc-qcqs-morphism-permanence make these a pro-etale cover of each stratum.
Take the minimum lower and maximum upper term bounds. The same selection works
for every n, and lem-weil-pbc-noetherian-stratum-detection detects global vanishing
for K and every reduction. For empty X choose [0,0].
6. By lem-weil-pbc-noetherian-scheme-closed-subsets-minimal the underlying space is
Noetherian, so its locally closed strata are constructible. Step 4 supplies finite
constant models on the original covers. Together with step 7 these give exactly
intrinsic constructibility. Use one empty stratum if X is empty.
7. Every geometric point lifts to a covering member: the fibre is nonempty by
joint surjectivity and has a section by lem-fix-weakly-etale-algclosed-section.
Pointed fibre-product neighbourhoods are cofinal. Thus its stalk is the stalk of
the finite constant model, finite by lem-weil-proetale-constant-sheaf-stalk.
No completeness or compatible etale-origin witness is concluded. -/
theorem perfect_strata_uniform_reductions
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : d.derived X) (S : FiniteLocallyClosedStratification X)
    (J : Fin S.n → Type (u + 1)) (U : ∀ i : Fin S.n, J i → (S.domain i).ProEt)
    (f : ∀ (i : Fin S.n) (j : J i), U i j ⟶ ProEt.mk (𝟙 (S.domain i)))
    (_hcover : ∀ i : Fin S.n,
      Presieve.ofArrows (U i) (f i) ∈ (ProEt.precoverage (S.domain i)).coverings _)
    (_hmodel : ∀ (i : Fin S.n) (j : J i),
      ∃ P : @DerivedCategory (ModuleCat.{u + 1} A) _ _ (HasDerivedCategory.standard _),
        @DerivedCategory.IsPerfectRingComplex A _ (HasDerivedCategory.standard _) P ∧
          Nonempty
            (@ringedSiteDerivedRestrictionOfUniverses (S.domain i).ProEt _
                (ProEt.topology (S.domain i))
                ((adicLisseForget (S.domain i)).obj
                  ((adicTowerInverseImage (S.immersion i)).obj (d.completedRing X)))
                (U i j) _ _ _ _ _ (HasDerivedCategory.standard _)
                ((adicTowerPullback (S.immersion i) (d.completedRing X)).obj K) ≅
              @ringedSiteDerivedRestrictionOfUniverses (S.domain i).ProEt _
                (ProEt.topology (S.domain i))
                ((adicLisseForget (S.domain i)).obj
                  ((adicTowerInverseImage (S.immersion i)).obj (d.completedRing X)))
                (U i j) _ _ _ _ _ (HasDerivedCategory.standard _)
                ((adicTowerPullback (S.immersion i) (d.completedRing X)).obj
                  ((pbcDerivedExtend (CompletedConstantReduction.base X d.ideal ≫
                    (pbcCompletedComparison X d).hom)).obj
                      (DerivedCategory.Q.obj
                        ((CompletedConstantReduction.constantComplex X A).obj
                          ((@DerivedCategory.Q (ModuleCat.{u + 1} A) _ _
                            (HasDerivedCategory.standard _)).objPreimage P))))))) :
    (∃ a b : ℤ, a ≤ b ∧
      (∀ q : ℤ, q < a ∨ b < q →
        IsZero ((DerivedCategory.homologyFunctor
          (reductionModules X (d.completedRing X)) q).obj K)) ∧
      ∀ (n : ℕ) (q : ℤ), q < a ∨ b < q →
        IsZero ((DerivedCategory.homologyFunctor (reductionModules X (d.finiteRing X n)) q).obj
          ((d.reduction X n).obj K))) ∧
    (∀ (n : ℕ) (q : ℤ), IsConstructibleProEtaleCoefficientModuleSheaf X
      (A ⧸ d.ideal ^ (n + 1))
      ((pbcRestrict (pbcLevelConstantComparison X d n).hom).obj
        ((DerivedCategory.homologyFunctor (reductionModules X (d.finiteRing X n)) q).obj
          ((d.reduction X n).obj K)))) ∧
    ∀ (n : ℕ) (q : ℤ) (i : Fin S.n) (j : J i),
      ∃ M : ModuleCat.{u + 1} (A ⧸ d.ideal ^ (n + 1)), Finite M ∧
        Nonempty
          ((SheafOfModules.overFunctor _ (U i j)).obj
            ((proEtaleModuleInverseImage (S.immersion i)
              (adicLisseConstantRing X (A ⧸ d.ideal ^ (n + 1)))).obj
                ((pbcRestrict (pbcLevelConstantComparison X d n).hom).obj
                  ((DerivedCategory.homologyFunctor
                    (reductionModules X (d.finiteRing X n)) q).obj
                      ((d.reduction X n).obj K)))) ≅
            (SheafOfModules.overFunctor _ (U i j)).obj
              ((proEtaleModuleInverseImage (S.immersion i)
                (adicLisseConstantRing X (A ⧸ d.ideal ^ (n + 1)))).obj
                  ((adicLisseConstantModules X (A ⧸ d.ideal ^ (n + 1))).obj M))) := by
  sorry

end AlgebraicGeometry.Scheme
