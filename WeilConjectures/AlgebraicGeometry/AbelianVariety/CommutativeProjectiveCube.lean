/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Projective
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube

/-! # Commutativity, projectivity and the cube

Source: the current blueprint, sec-abelian-varieties/sk-prop-av-mult-n-pullback/_section.md
and its proof; Stacks Project, Tags 0BFD, 0BFA and 0BFF.
(blueprint: sk-prop-av-mult-n-pullback)

The symmetric ample invertible module is chosen once, independently of the positive
multiplication index. Pullback is the existing explicit tensor-pullback construction.
-/

@[expose] public section

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

open Scheme.Modules

private noncomputable def tensorPullbackOverPullbackIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    tensorPullback g ≅ Scheme.Modules.pullback g :=
  (nonempty_tensorPullbackAdjunction g).some.leftAdjointUniq
    (pullbackPushforwardAdjunction g)

/-- An abelian variety is commutative and projective and admits a symmetric ample invertible
module whose pullback by multiplication by every positive `n` is its `n²`-th tensor power.

Source: the current blueprint, sec-abelian-varieties/sk-prop-av-mult-n-pullback/_section.md;
Stacks Project, Tags 0BFD, 0BFA and 0BFF.
(blueprint: sk-prop-av-mult-n-pullback)

Proof: apply `lem-sc-av-commutative` to obtain commutativity. By
`lem-sc-abelian-variety-projective`, choose an ample invertible module `L` and a closed
immersion into finite-dimensional projective space. The latter gives `IsHProjective A.hom`;
properness gives quasi-compactness, hence `IsProjective A.hom`. Set
`N = L ⊗ [-1]^* L` before choosing any multiplication index. Pullback preserves invertibility
by `lem-weil-pbc-invertible-pullback-invertible`, and tensoring local frames proves that `N`
is invertible. The abelian-variety clause of `lem-sc-ample-tensor` gives ampleness and
symmetry of `N`. For each positive `n`, apply `lem-sc-mult-n-pullback` to this fixed symmetric
invertible `N` to obtain the quadratic tensor-power formula. These input theorems use
`overPullback`, the abstract left adjoint to pushforward; its comparison with the explicit
`tensorPullback` used here is the isomorphism of left adjoints to the same pushforward,
using `tensorPullbackSectionAdjunction` and `pullbackPushforwardAdjunction`. Transporting
along its component gives exactly the displayed isomorphisms. -/
theorem IsAbelianVariety.commutative_projective_exists_symmetric_ample
    {K : Type u} [Field K] (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A] :
    IsCommMonObj A ∧ IsProjective A.hom ∧
      ∃ N : A.left.Modules, N.IsInvertible ∧ IsAmple A.hom N ∧
        Nonempty ((tensorPullback ι[A].left).obj N ≅ N) ∧
        ∀ n : ℕ, 0 < n →
          Nonempty ((tensorPullback (𝟙 A ^ n).left).obj N ≅ N.tensorPow (n ^ 2)) := by
  have hcomm : IsCommMonObj A := inferInstance
  obtain ⟨α, hα, j, hj, hjA⟩ := IsAbelianVariety.exists_isClosedImmersion_projectiveSpace A
  have hHproj : IsHProjective A.hom := ⟨α, hα, j, hj, hjA⟩
  have hproj : IsProjective A.hom := IsHProjective.isProjective A.hom
  obtain ⟨L, hL⟩ := IsAbelianVariety.exists_isAmple A
  have hLinv : L.IsInvertible := hL.isInvertible
  have hNinv : L.symmetrisation.IsInvertible := by
    exact inferInstanceAs (Scheme.Modules.tensorObj L (overPullback ι[A] L)).IsInvertible
  have hNample : IsAmple A.hom L.symmetrisation :=
    IsAbelianVariety.isAmple_symmetrisation A L hL
  have hNsymm : Nonempty ((tensorPullback ι[A].left).obj L.symmetrisation ≅
      L.symmetrisation) := by
    obtain ⟨e⟩ := IsAbelianVariety.nonempty_iso_overPullback_inv_symmetrisation A L
    exact ⟨(tensorPullbackOverPullbackIso ι[A].left).app L.symmetrisation ≪≫ e⟩
  refine ⟨hcomm, hproj, L.symmetrisation, hNinv, hNample, hNsymm, ?_⟩
  intro n hn
  obtain ⟨e⟩ := nonempty_iso_overPullback_npow_id A L.symmetrisation
    (IsAbelianVariety.nonempty_iso_overPullback_inv_symmetrisation A L) n
  exact ⟨(tensorPullbackOverPullbackIso (𝟙 A ^ n).left).app L.symmetrisation ≪≫ e⟩

end AlgebraicGeometry
