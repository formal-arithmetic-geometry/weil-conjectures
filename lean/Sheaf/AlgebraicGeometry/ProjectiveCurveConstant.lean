/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Data.ZMod.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Sheaf.AlgebraicGeometry.FiniteConstructibleDirectImage
import Sheaf.AlgebraicGeometry.FiniteGenericCurveModel
import Sheaf.AlgebraicGeometry.ConstantFiniteComparison
import Sheaf.AlgebraicGeometry.ConstructibleSubsheafNoetherian
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.ConstructibleSheaf.Biproduct
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.ProjectiveSmoothCurveFiniteness

/-!
# Constant coefficients on projective families of dimension at most one

Source: blueprint, sec-smooth-purity, sk-prop-sf-cbc,
thm-fin-projective-curve-constant (blueprint: thm-fin-projective-curve-constant).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Every higher direct image of the constant prime field sheaf under a projective
morphism of finite-type schemes over a field with geometric fibres of dimension at most
one is constructible, provided the prime is invertible on the base.

Source: blueprint, sec-smooth-purity, sk-prop-sf-cbc,
thm-fin-projective-curve-constant (blueprint: thm-fin-projective-curve-constant).

Proof:
1. Finite type over the field gives Noetherian schemes, using
   lem-weil-pbc-finite-type-algebra-noetherian. Projectivity gives properness by
   lem-kun-projective-implies-proper and is stable under base change by
   lem-pc-projective-base-change. The constant finite module sheaf is constructible.
   Use lem-weil-pbc-module-abelian-derived-direct-image-comparison whenever applying
   abelian proper base change to module higher direct images; its naturality preserves scalars.
2. For integral base, lem-fin-generic-curve-model supplies, after shrinking, a finite
   surjective integral base change and a finite comparison Y to the reduction T of
   the pulled-back X. It is an isomorphism away from a reduced closed subset finite
   over the new base. Y is a finite disjoint union of smooth projective curve families
   and finite etale families. All schemes remain finite type and the prime stays invertible.
3. Apply thm-fin-projective-smooth-curve-finiteness to curve summands and
   lem-fin-finite-morphism to finite etale summands. Sheaves, resolutions and direct
   images on a finite disjoint union are componentwise. Finite products are finite
   sums and exact. Intersect the finite stratifications and apply
   lemma-constructible-flc-biproduct; the empty union gives the zero sheaf.
4. Apply lem-finrepair-constant-finite-comparison to Y over T. Reduction is a universal
   homeomorphism, so thm-weil-pbc-universal-homeomorphism-invariance and
   lem-weil-derived-direct-image-composition identify these direct images with those
   from the original pulled-back X, preserving the constant coefficients.
5. Apply lemma-weil-pbc-prime-proper-base-change to the open restriction and the finite
   surjective base change. Use prop-weil-pbc-inverse-image-exact and
   lemma-constructible-pullback-constant to identify the pulled-back higher image.
   Its finite direct image is constructible by lem-fin-finite-morphism. The adjunction
   unit is the diagonal into a nonempty finite product on geometric stalks, by
   lemma-weil-pbc-finite-stalk-formula and lem-weil-pbc-inverse-image-stalk-germ.
   Thus lem-weil-pbc-geometric-stalks-detect-mono makes it monic, and
   lem-weil-pbc-constructible-subobjects-noetherian gives constructibility on the dense open.
6. Fix the degree and use lem-weil-pbc-noetherian-scheme-closed-subsets-minimal on
   reduced closed subsets. The empty subset has the empty partition. Proper base
   change identifies restriction with the higher image of the restricted family;
   its geometric fibres satisfy the same bound. Every proper closed subset of a
   minimal counterexample therefore already satisfies the conclusion.
7. An irreducible reduced minimal counterexample is integral. Step 5 gives a nonempty
   constructible open locus; the complement satisfies induction. Combine their finite
   locally closed stratifications to contradict minimality.
8. A reducible minimal counterexample has finitely many irreducible components by
   lem-weil-pbc-noetherian-finite-components. Each satisfies induction. Restrict their
   partitions to each component minus earlier components, using prop-constructible-pullback.
   These disjoint locally closed constructible strata partition the whole scheme.
9. Finally apply reduction invariance to the base. Reduced structures on the strata
   give the same locally closed subsets and preserve finite local constancy, so the
   partition proves constructibility on the original base. Negative-degree images vanish.
-/
theorem isConstructibleEtaleModuleSheaf_higherDirectImage_prime_of_projective_curve
    (k : Type u) [Field k] (X S : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] (f : X ⟶ S) [IsProjective f.left]
    (hdim : ∀ s : S.left,
      topologicalKrullDim (pullback f.left
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.left.residueField s) (AlgebraicClosure (S.left.residueField s)))) ≫
          S.left.fromSpecResidueField s) : Scheme.{u}) ≤ 1)
    (ℓ : ℕ) [Fact ℓ.Prime] (hinv : IsUnit (ℓ : Γ(S.left, ⊤))) (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.left.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) q).obj
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
          f.left).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
            0).obj
            ((constantSheaf X.left.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
              (ModuleCat.of (ULift.{u + 1} (ZMod ℓ)) (ULift.{u + 1} (ZMod ℓ))))))) := by
  sorry

end AlgebraicGeometry
