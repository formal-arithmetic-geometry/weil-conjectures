/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.ConstructibleSheaf.Defs
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheaf
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.Paper.ProjectionMateExact
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.Paper.BoundedFlatReplacement
import Sheaf.Paper.EtaleKFlatCriteria

/-!
# The projection formula with a finitely presented constant module

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-rf-shriek-preservation,
lemma lem-sf-projection-finite-constant (blueprint: lem-sf-projection-finite-constant).
The ordinary, uncompleted tensor and K-injective direct image are those of the recorded
unbounded etale framework. The constant inverse-image comparison identifies the target
with `Rf_*(K ⊗^L M_X)`. No properness or torsion hypothesis is imposed.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The canonical projection map for a constant module, as a natural transformation in
that module. Its source is `Rf_*K ⊗^L M_Y` and its target is `Rf_*(K ⊗^L M_X)`.
It is the recorded adjunction-mate projection map, followed by the canonical identification
of the derived inverse image of the constant sheaf with the constant sheaf on the source.
Source: blueprint sec-six-functors/sk-prop-sf-rf-shriek-preservation,
lemma lem-sf-projection-finite-constant, first proof paragraph
(blueprint: lem-sf-projection-finite-constant). -/
noncomputable def finiteConstantProjectionMap
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategoryModule A X) :
    (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      _root_.DerivedCategory.singleFunctor _ 0) ⋙
        (derivedTensor (ModuleCat.{u + 1} A) Y).obj
          ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj K) ⟶
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      _root_.DerivedCategory.singleFunctor _ 0) ⋙
        (derivedTensor (ModuleCat.{u + 1} A) X).obj K ⋙
          (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor := by
  let C_Y := constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)
  let C_X := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let S_Y := _root_.DerivedCategory.singleFunctor
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) 0
  let S_X := _root_.DerivedCategory.singleFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) 0
  let R := (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor
  let L := (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
  let T_X := (derivedTensor (ModuleCat.{u + 1} A) X).obj K
  let T_Y := (derivedTensor (ModuleCat.{u + 1} A) Y).obj (R.obj K)
  let π : (C_Y ⋙ S_Y) ⋙ T_Y ⟶ (C_Y ⋙ S_Y) ⋙ L ⋙ T_X ⋙ R :=
    Functor.whiskerLeft (C_Y ⋙ S_Y)
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app K)
  let α : C_Y ⋙ S_Y ⋙ L ⟶ C_Y ⋙ upperStar (ModuleCat.{u + 1} A) f ⋙ S_X :=
    Functor.whiskerLeft C_Y
      (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f).hom
  let β : (C_Y ⋙ upperStar (ModuleCat.{u + 1} A) f) ⋙ S_X ⟶ C_X ⋙ S_X :=
    Functor.whiskerRight (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).hom
      S_X
  -- Explicit reassociation keeps kernel checking from unfolding the derived functors.
  exact π ≫
    (Functor.associator (C_Y ⋙ S_Y) L (T_X ⋙ R)).inv ≫
    Functor.whiskerRight (Functor.associator C_Y S_Y L).hom (T_X ⋙ R) ≫
    Functor.whiskerRight α (T_X ⋙ R) ≫
    Functor.whiskerRight
      (Functor.associator C_Y (upperStar (ModuleCat.{u + 1} A) f) S_X).inv (T_X ⋙ R) ≫
    Functor.whiskerRight β (T_X ⋙ R)

/-- With a uniform all-sheaf cohomological-dimension bound and Noetherian coefficients,
the canonical projection map is an isomorphism for a bounded-above complex and a finitely
presented constant module. Naturality in `M` is built into `finiteConstantProjectionMap`.
Source: blueprint sec-six-functors/sk-prop-sf-rf-shriek-preservation,
lemma lem-sf-projection-finite-constant
(blueprint: lem-sf-projection-finite-constant).

Proof plan:
1. Constant sheaves are exact by exact sheafification
   (lem-weil-pbc-site-r-module-presheaf-sheafification-exact). The constant inverse-image
   isomorphism respects addition and scalars (lem-weil-pbc-sets-etale-inverse-image-constant-sheaf);
   inverse image is exact (prop-weil-pbc-inverse-image-modules-exact). Thus the mate is natural
   on constant complexes and its value on `M[0]` is the displayed map.
2. The projection mate is compatible with distinguished triangles and is the identity at
   the tensor unit (lem-weil-pbc-ringed-projection-mate-exact). Finite sums and shifts give
   the assertion for finite free modules. Brutal truncations, the cohomology long exact
   sequence (lem-sf-derived-homology-long-exact), the five lemma (lem-weil-pbc-five-lemma),
   and cohomological detection of isomorphisms (lem-weil-pbc-unbounded-derived-iso-cohomology)
   extend it to bounded finite free complexes.
3. Resolve `M` by finite free modules in nonpositive degrees. Noetherian submodules are
   finite (lem-weil-pbc-noetherian-submodule-finite), so all syzygies can be covered by finite
   free modules. For `P_m = σ_{≥-m} P`, the cone of `P_m → M` has cohomology at most `-m-1`:
   its degree zero cohomology vanishes by surjectivity, also for `m = 0`, and exactness
   kills degrees `-m` through `-1` for `m > 0`. Only the bottom kernel can survive.
4. Direct image is additive and left exact (lem-weil-pbc-module-direct-image-left-exact),
   and module sheaves have enough injectives (lem-weil-pbc-module-sheaves-enough-injectives).
   The uniform bound and lem-sf-finite-cd-derived-upper-bound (Stacks 07K7, (4)(c)) give
   `Rf_* D^{≤t} ⊆ D^{≤t+N}`, in particular `Rf_*K ∈ D^{≤b+N}` for an upper bound `b` of `K`.
5. Bounded-above flat replacements (lem-kun-bounded-flat-replacement) are K-flat
   (lem-kun-kflat-criteria). Their total tensor has no summand above the sum of the upper
   term bounds. Exactness of constant sheaves and Step 4 put both error terms with the
   constant cone in `D^{≤b+N-m-1}`.
6. For a fixed `r`, choose `m ≥ 0` with `b+N-m-1 < r-1`. The long exact sequences show
   that replacing `M` by `P_m` changes neither side's degree `r` cohomology. Naturality
   gives a square whose other three sides are invertible, so the map for `M` is invertible
   on degree `r` cohomology. Do this for every `r` and use cohomological detection of
   isomorphisms. Naturality requires no natural choice of the free resolution. -/
theorem isIso_finiteConstantProjectionMap
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : ℕ)
    (hcd : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ),
      N < q → IsZero ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))))
    (K : DerivedCategoryModule A X)
    (hK : ∃ b : ℤ, ∀ q : ℤ, b < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj K))
    (M : ModuleCat.{u + 1} A) [Module.FinitePresentation A M] :
    IsIso ((finiteConstantProjectionMap A f K).app M) := by
  sorry

end AlgebraicGeometry.Etale
