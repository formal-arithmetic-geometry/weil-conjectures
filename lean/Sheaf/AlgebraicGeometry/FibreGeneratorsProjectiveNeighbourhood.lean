/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes
import WeilConjectures.AlgebraicGeometry.NonvanishingTensorPullback
import WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre
import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import WeilConjectures.AlgebraicGeometry.ProjPolynomialTwistChart

/-! # Fibre-generating sections and a proper projective-space morphism

Source: Stacks Project, Coherent, Tag 0D2N, lemma-ample-in-neighbourhood, first paragraph;
Constructions, Tags 01NE and 01NG; Morphisms, Tags 01W4 and 01W6.
(blueprint: lem-trf-fibre-generators-projective-neighbourhood).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Sections generating on one fibre of a proper morphism generate over an affine
neighbourhood and define a proper morphism to projective space, with the specified quotient
and its fibre comparison. Compatible families `us` and `v` encode the pulled-back sections;
their values at the top open fix them uniquely.

Source: Stacks Project, Coherent, Tag 0D2N, lemma-ample-in-neighbourhood, first paragraph;
Constructions, Tags 01NE and 01NG; Morphisms, Tags 01W4 and 01W6.
(blueprint: lem-trf-fibre-generators-projective-neighbourhood).

Proof:
1. Pullback preserves invertibility (lem-weil-pbc-invertible-pullback-tensor). The nonvanishing
opens of the sections are open by lem-weil-pbc-nonvanishing-section-trivializes. By
lem-sc-nonvanishing-tensor-pullback and lem-weil-pbc-invertible-generating-sections-fibre,
their union contains the underlying fibre (def-pc-scheme-fibre).
2. Its complement is closed. Properness makes its image closed and disjoint from s. Choose
an affine open neighbourhood U avoiding that image (lem-weil-pbc-affine-opens-basis).
Pullback compatibility of nonvanishing and the generating-sections criterion show that the
restricted sections generate on the inverse image of U.
3. Apply lem-weil-pbc-projective-space-functor-of-points and
 def-weil-pbc-morphism-to-projective-space-by-sections to this quotient. The standard-chart
and polynomial-twist descriptions (lem-weil-pbc-projective-space-standard-charts,
lem-weil-pbc-proj-polynomial-twist-chart) identify its twist with the specified O(1),
carrying every coordinate to the corresponding restricted section.
4. The restricted structural map is proper by lem-weil-pbc-proper-base-change. Projective
space is proper, hence separated, over U (lemma-nagata-projective-space-base-change-proper).
Apply lem-weil-pbc-proper-over-separated to obtain properness of the associated morphism.
5. The fibre-product universal property identifies the fibre of projective space with
projective space over the residue field (def-pc-fibre-product,
def-nagata-projective-space-base-change). Naturality of the functor of points identifies
the fibre morphism with the one classified by the pulled-back tuple. Pulling back the
quotient isomorphism gives the fibre quotient isomorphism: both send each coordinate to
the specified section. Such an isomorphism is unique because these sections generate.
The last equality records this compatibility using the normalized composition comparisons.
-/
theorem fibre_generators_projective_neighbourhood {Z S : Scheme.{u}} (f : Z ⟶ S)
    [IsProper f] (s : S) (M : Z.Modules) [M.IsInvertible] (r : ℕ)
    (a : ULift.{u} (Fin (r + 1)) → M.sections)
    (us : ULift.{u} (Fin (r + 1)) → ((tensorPullback (f.fiberι s)).obj M).sections)
    (hus : ∀ j, (us j).val (op ⊤) =
      ((tensorPullbackSectionAdjunction (f.fiberι s)).unit.app M).app ⊤
        ((a j).val (op ⊤)))
    (hgen : Epi (((tensorPullback (f.fiberι s)).obj M).freeHomEquiv.symm us)) :
    ∃ U : S.Opens, s ∈ U ∧ IsAffineOpen U ∧
      ∃ (hMU : ((tensorPullback (f ⁻¹ᵁ U).ι).obj M).IsInvertible)
        (v : ULift.{u} (Fin (r + 1)) → ((tensorPullback (f ⁻¹ᵁ U).ι).obj M).sections),
        (∀ j, (v j).val (op ⊤) =
          ((tensorPullbackSectionAdjunction (f ⁻¹ᵁ U).ι).unit.app M).app ⊤
            ((a j).val (op ⊤))) ∧
        ∃ hv : Epi (((tensorPullback (f ⁻¹ᵁ U).ι).obj M).freeHomEquiv.symm v),
          ∃ φ : (f ⁻¹ᵁ U).toScheme ⟶ ℙ(ULift.{u} (Fin (r + 1)); U.toScheme),
            φ = @ProjectiveSpace.homOfGeneratingSections (ULift.{u} (Fin (r + 1))) _ _ _ (f ∣_ U)
              ((tensorPullback (f ⁻¹ᵁ U).ι).obj M) hMU v hv ∧
            IsProper φ ∧
            ∃ e : (tensorPullback φ).obj
                (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) U.toScheme 1) ≅
                  (tensorPullback (f ⁻¹ᵁ U).ι).obj M,
              (∀ j, e.hom.app ⊤
                (((tensorPullbackSectionAdjunction φ).unit.app
                  (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) U.toScheme 1)).app ⊤
                    (ProjectiveSpace.twistOneSection (ULift.{u} (Fin (r + 1))) U.toScheme j)) = (v
                      j).val (op ⊤)) ∧
              ∃ (b : Spec (S.residueField s) ⟶ U.toScheme)
                (i : f.fiber s ⟶ (f ⁻¹ᵁ U).toScheme)
                (hi : i ≫ (f ⁻¹ᵁ U).ι = f.fiberι s),
                b ≫ U.ι = S.fromSpecResidueField s ∧
                IsPullback i (f.fiberToSpecResidueField s) (f ∣_ U) b ∧
                ∃ (φs : f.fiber s ⟶ ℙ(ULift.{u} (Fin (r + 1));
                    Spec (S.residueField s)))
                  (hc : φs ≫ ProjectiveSpace.map (ULift.{u} (Fin (r + 1))) b = i ≫ φ),
                  φs = @ProjectiveSpace.homOfGeneratingSections (ULift.{u} (Fin (r + 1))) _ _ _
                    (f.fiberToSpecResidueField s) ((tensorPullback (f.fiberι s)).obj M)
                    ((invertible_pullback_tensor (f.fiberι s)).1 M).2 us hgen ∧
                  ∃ β : (tensorPullback (ProjectiveSpace.map (ULift.{u} (Fin (r + 1))) b)).obj
                      (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) U.toScheme 1) ≅
                        ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) (Spec (S.residueField s)) 1,
                    (∀ j, β.hom.app ⊤
                      (((tensorPullbackSectionAdjunction (ProjectiveSpace.map (ULift.{u} (Fin (r +
                        1))) b)).unit.app
                        (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) U.toScheme 1)).app ⊤
                          (ProjectiveSpace.twistOneSection (ULift.{u} (Fin (r + 1))) U.toScheme j))
                            =
                            ProjectiveSpace.twistOneSection (ULift.{u} (Fin (r + 1))) (Spec
                              (S.residueField s)) j) ∧
                    ∃ es : (tensorPullback φs).obj
                        (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) (Spec (S.residueField s))
                          1) ≅
                          (tensorPullback (f.fiberι s)).obj M,
                      (∀ j, es.hom.app ⊤
                        (((tensorPullbackSectionAdjunction φs).unit.app
                          (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) (Spec (S.residueField
                            s)) 1)).app ⊤
                            (ProjectiveSpace.twistOneSection (ULift.{u} (Fin (r + 1))) (Spec
                              (S.residueField s)) j)) =
                              (us j).val (op ⊤)) ∧
                      (tensorPullback φs).mapIso β ≪≫ es =
                        ((tensorPullbackSectionComp φs (ProjectiveSpace.map (ULift.{u} (Fin (r +
                          1))) b)).app
                          (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) U.toScheme 1)).symm ≪≫
                        eqToIso (congrArg (fun h ↦ (tensorPullback h).obj
                          (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) U.toScheme 1)) hc) ≪≫
                        (tensorPullbackSectionComp i φ).app
                          (ProjectiveSpace.twist (ULift.{u} (Fin (r + 1))) U.toScheme 1) ≪≫
                        (tensorPullback i).mapIso e ≪≫
                        ((tensorPullbackSectionComp i (f ⁻¹ᵁ U).ι).app M).symm ≪≫
                        eqToIso (congrArg (fun h ↦ (tensorPullback h).obj M) hi) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
