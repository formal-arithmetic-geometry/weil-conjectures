/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

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
  classical
  let Λ := ULift.{u + 1} (ZMod ℓ)
  have : HasInvertibleExponent Λ S.left := by
    refine ⟨ℓ, (Fact.out : ℓ.Prime).pos, ?_, hinv⟩
    change (ℓ : ULift.{u + 1} (ZMod ℓ)) = 0
    apply ULift.ext
    exact ZMod.natCast_self ℓ
  obtain ⟨n, hn, i, hi, hif⟩ := IsHProjective.exists_isClosedImmersion (f := f.left)
  let := hn
  let := hi
  have hfib : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ S.left),
      topologicalKrullDim (pullback f.left s : Scheme.{u}) ≤ 1 := by
    intro Ω _ _ s
    obtain ⟨⟨t, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω S.left).symm.surjective s
    let c := Spec.map (CommRingCat.ofHom
      (algebraMap (S.left.residueField t) (AlgebraicClosure (S.left.residueField t))))
    have heq (K : Type u) [Field K]
        (a : Spec (.of K) ⟶ Spec (.of (S.left.residueField t))) :
        topologicalKrullDim
          (pullback f.left (a ≫ S.left.fromSpecResidueField t) : Scheme.{u}) =
          topologicalKrullDim (f.left.fiber t) := by
      let e := pullbackLeftPullbackSndIso f.left (S.left.fromSpecResidueField t) a
      rw [← IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph]
      exact topologicalKrullDim_pullback_eq_of_field
        (pullback.snd f.left (S.left.fromSpecResidueField t)) a
    change topologicalKrullDim
      (pullback f.left (Spec.map a ≫ S.left.fromSpecResidueField t) : Scheme.{u}) ≤ 1
    rw [heq Ω (Spec.map a)]
    rw [← heq (AlgebraicClosure (S.left.residueField t)) c]
    exact hdim t
  let F := (constantSheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
    (ModuleCat.of Λ Λ)
  let A := (DerivedCategory.Plus.singleFunctor
    (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F
  apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
  have : Scheme.IsConstructibleSheaf
      ((DerivedCategory.homologyFunctor _ q).obj
        ((DerivedCategory.Plus.ι ⋙
          (Etale.lowerStar (ModuleCat.{u + 1} Λ) f.left).rightDerivedFunctor).obj A)) := by
    change Scheme.IsConstructibleSheaf
      ((DerivedCategory.homologyFunctor _ q).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f.left).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj F)))
    exact Etale.isConstructibleSheaf_homology_rightDerivedLowerStar_zmod
      S.hom f.left i hif hfib ℓ q
  exact Scheme.IsConstructibleSheaf.of_iso
    ((DerivedCategory.homologyFunctor _ q).mapIso
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f.left).rightDerivedFunctorPlusCompatibility.app
        A).symm)

end AlgebraicGeometry
