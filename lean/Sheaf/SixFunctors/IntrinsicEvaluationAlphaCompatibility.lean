/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.SixFunctors.SemilinearProperOpenEvaluationSupport

/-! # Evaluation compatibility of the intrinsic inverse-image clopen word

Source: Stacks Project, Tag 0F7B, open case; Zheng, Construction 4.1 and Lemma 4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 64
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
variable (n : ℕ)

/-- Evaluation preserves the specified inverse-image alpha word, before taking proper mates.
Source: Stacks Project, Tags 03DI and 0F7B; Zheng, Construction 4.1 and Lemma 4.10.
Proof: work on ordinary strict systems. The direct-image comparison is identity on
sections, so its inverse mate is the normalized inverse-image comparison. The open
comparison is its open-adjunction inverse mate. Transpose the cartesian beta square
under the open adjunction: both sides are the same unit and inverse-image square.
For the clopen square lift, the projector is identity on the selected component
and zero on the complementary component; evaluation preserves these two maps.
The normalized inverse-image and open compositors commute with the comparisons,
by adjunction uniqueness. Substitute these three identities in the beta/projector/
compositor expression for alpha. Naturality moves the comparison maps through the
factors, and adjacent inverse pairs cancel. Apply the exact functors termwise to
complexes and localize this equality. The localization composition isomorphisms
are precisely the ones defining evalP; open adjunction uniqueness identifies
its localized open comparison with evalJ. This proves the displayed equation
on whole derived systems, including empty clopen components and noncartesian
proper/open squares. No faithfulness of evaluation on morphisms is used.
(blueprint: lem-sf-intrinsic-evaluation-alpha-compatibility). -/
theorem intrinsicEvaluationAlphaCompatibility
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : Derived C τ S) :
    (E C τ n W).map ((alpha C τ k r p i h).app M) ≫
        (evalJ C τ n k).hom.app ((P C τ r).obj M) ≫
        (StrictTower.J (C n) k).map ((evalP C τ n r).hom.app M) =
      (evalP C τ n p).hom.app ((J C τ i).obj M) ≫
        (StrictTower.G (C n) p).map ((evalJ C τ n i).hom.app M) ≫
        (StrictTower.alpha (C n) k r p i h).app ((E C τ n S).obj M) := by
  sorry

end AlgebraicGeometry.ProEtale.SemilinearProperOpen
