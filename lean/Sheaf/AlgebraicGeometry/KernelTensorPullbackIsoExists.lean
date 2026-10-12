/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Comparison of pulled back kernel ideals under an ambient isomorphism

Source: Stacks Project, Morphisms, Section 01R1, Lemmas 29.32.2 and 29.32.3;
Sheaves, Definition 0095 and Lemma 0096.
(blueprint: lem-weil-pbc-kernel-tensor-pullback-iso-exists).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- An isomorphism between ambient schemes fixing a common closed subscheme induces
an isomorphism of the pulled back kernel ideals, with the canonical section formula.
No square-zero or universal property assumption is needed, and uniqueness is not
asserted here.
Source: Stacks Project, Section 01R1, Lemmas 29.32.2 and 29.32.3, and Tags 0095, 0096.
(blueprint: lem-weil-pbc-kernel-tensor-pullback-iso-exists).
Proof: Write Iⱼ = iⱼ.ker.toModules and Mⱼ = iⱼ* Iⱼ. For every open U of Z₂,
φ.app U maps the structure-sheaf image of s₂ in I₂(U) into the kernel of
 i₁.app (φ⁻¹ U), by the equation i₁ ≫ φ = i₂. The kernel inclusion is
injective, so there is a unique section β_U(s₂) of I₁(φ⁻¹ U) with that image.
The maps β_U are additive, φ.app U-linear, and commute with restrictions:
apply the injective kernel inclusion to check each identity in the structure
sheaf. They define an O_Z₂-linear map β : I₂ → φ_* I₁.
Compose β with φ_* of the normalized pullback unit I₁ → i₁_* M₁.
The pushforward composition comparison and hc identify its target with
 i₂_* M₁. Take its adjoint under the normalized i₂ pullback adjunction,
obtaining e_hom : M₂ → M₁. The unit/Hom-equivalence identity says on U that
 e_hom sends the i₂ unit of s₂ to the i₁ unit of β_U(s₂), transported
along the equality i₂⁻¹ U = i₁⁻¹(φ⁻¹ U). Thus if s₁ satisfies the displayed
kernel equation it equals β_U(s₂). Naturality of e_hom and the units gives
the required equation on every smaller W; the transports commute with both
restriction maps because the category of opens is a preorder.
Repeat this construction with inv φ, using i₂ ≫ inv φ = i₁. Applying the
kernel inclusions shows that the two β maps compose to the identity after
inverse-image transports. Consequently each composite of the two adjoint
module maps agrees with the identity on all pullback-unit sections. The
adjunction Hom bijection is injective, so both composites are identities.
These maps define the desired module isomorphism with the section formula.
Edge cases: identity φ gives the identity map; zero ideals and the empty closed
subscheme give zero modules. General closed immersions are allowed since
pullback of I is the conormal module I/I² (Lemma 29.32.2). -/
theorem exists_kernelTensorPullbackIso {Z Z₁ Z₂ : Scheme.{u}}
    (i₁ : Z ⟶ Z₁) (i₂ : Z ⟶ Z₂) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (φ : Z₁ ⟶ Z₂) [IsIso φ] (hc : i₁ ≫ φ = i₂) :
    ∃ e : (Scheme.Modules.tensorPullback i₂).obj i₂.ker.toModules ≅
        (Scheme.Modules.tensorPullback i₁).obj i₁.ker.toModules,
          ∀ (U : Z₂.Opens) (s₂ : Γ(i₂.ker.toModules, U))
            (s₁ : Γ(i₁.ker.toModules, φ ⁻¹ᵁ U)),
            i₁.ker.toModulesι.app (φ ⁻¹ᵁ U) s₁ =
              φ.app U (i₂.ker.toModulesι.app U s₂) →
            ∀ (W : Z.Opens) (a : W ≤ i₂ ⁻¹ᵁ U) (b : W ≤ i₁ ⁻¹ᵁ (φ ⁻¹ᵁ U)),
              e.hom.app W
                  (((Scheme.Modules.tensorPullback i₂).obj i₂.ker.toModules).val.map (homOfLE a).op
                    (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
                      i₂)).unit.app i₂.ker.toModules).app U s₂)) =
                ((Scheme.Modules.tensorPullback i₁).obj i₁.ker.toModules).val.map (homOfLE b).op
                  (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
                    i₁)).unit.app i₁.ker.toModules).app (φ ⁻¹ᵁ U) s₁) := by sorry

end AlgebraicGeometry
