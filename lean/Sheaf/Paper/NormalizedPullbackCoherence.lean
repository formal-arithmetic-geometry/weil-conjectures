/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U9
-/
module

public import Sheaf.Paper.NormalizedPullbackObjects

/-! # Objectwise normalized pullback of geometric fibres

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4),(6), Remark 6.8.15;
Stacks Tag 03Q1(3) (blueprint: lem-per-normalized-pullback-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.AdicFibreComparison
open ContinuousRational AlgebraicGeometry.ProEtale

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]
  (R : ContinuousRational.Family.{u} l)

/-- The objectwise normalized comparisons respect the actual raw unit and compositor.
Source: BS 6.8.4(1),(4), Remark 6.8.15; Stacks 03Q1(3).
(blueprint: lem-per-normalized-pullback-coherence).

Proof: restrict R.identity.raw and R.composition.raw to the full standard hearts;
this gives e with exactly the required underlying raw component. Apply realization.
Its compatibility with the normalized derived counits identifies these maps with the
ordinary module inverse-image unit and compositor. At every finite reduction level,
the identity comparison sends a pulled section germ to itself. For two successive
pullbacks, the composite and the single pullback comparison both send a twice-pulled
section germ to the original germ. These generators determine the finite stalk maps,
so the two maps agree under the ordinary inverse-image associator. The completed-system
comparisons preserve the finite units and compositors. Equality of the tower maps gives
equality of their inverse-limit maps by all projections. Rationalization preserves these
equations, and the local_normalization clause identifies them with the components of p.
The intrinsic fibre comparisons eliminate chart and lattice choices. The resulting
equalities use precisely the raw comparisons of R, as required; no arbitrary scalar
is introduced in any comparison. Empty strata have no geometric points and rank-zero
fibres have the unique map, so the same argument includes both cases. -/
theorem objectwise_normalized_pullback_coherence
    (ω : Fibres (k := k) l R) (p : ObjectwiseNormalizedPullback l R ω) :
    (∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] (X : FiniteTypeBase k),
    ∃ e : heartPull l A R (𝟙 X.scheme) ≅ 𝟭 _,
      (∀ F, HEq (e.hom.app F).hom ((R.identity A (base l X)).raw.hom.app F.obj)) ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme)
        (F : NormalizedFibre.Heart l A (base l X)),
        HEq ((p.component A (𝟙 X.scheme) κ x F).hom)
          (((ω A X).point κ x).functor.map (e.hom.app F))) ∧
    (∀ (A : Type u) [Field A] [Algebra ℚ_[l] A]
    [FiniteDimensional ℚ_[l] A] (X Y Z : FiniteTypeBase k)
    (g : Y.scheme ⟶ X.scheme) (h : Z.scheme ⟶ Y.scheme),
    ∃ e : heartPull l A R (h ≫ g) ≅ heartPull l A R g ⋙ heartPull l A R h,
      (∀ F, HEq (e.hom.app F).hom
        ((R.composition A (X := base l Y) (Y := base l X) (Z := base l Z) g h).raw.hom.app
          F.obj)) ∧
      ∀ (κ : Type u) [Field κ] [IsAlgClosed κ] (z : Spec (.of κ) ⟶ Z.scheme)
        (F : NormalizedFibre.Heart l A (base l X)),
        HEq ((p.component A (h ≫ g) κ z F).hom)
          (((ω A Z).point κ z).functor.map (e.hom.app F) ≫
            (p.component A h κ z ((heartPull l A R g).obj F)).hom ≫
              (p.component A g κ (z ≫ h) F).hom)) := by sorry

end AlgebraicGeometry.Scheme.AdicFibreComparison
