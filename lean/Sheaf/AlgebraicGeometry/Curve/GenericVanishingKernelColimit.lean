/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.GenericComparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Generic-vanishing sheaves as filtered colimits of affine-open kernels

Source: the blueprint of the Weil conjectures, `sec-curve-estimates/sk-prop-cd`,
`lem-sc-generic-cohomology-comparison`, proof, acyclicity sentence;
`WeilConjectures/AlgebraicGeometry/Curve/GenericComparison.lean`, lines 156–201
(blueprint: lem-sc-generic-vanishing-kernel-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.IsCurve

/-- Source: blueprint `lem-sc-generic-cohomology-comparison`, proof, acyclicity sentence;
`GenericComparison.lean`, lines 156–201
(blueprint: lem-sc-generic-vanishing-kernel-colimit).

The nonempty affine opens, ordered by reverse inclusion, index a cocone of kernels into `G`.
Each leg is characterized as a kernel by its universal property, so the cocone is independent
of the choice of kernel objects. Its canonical colimit map is an isomorphism when all sections
of `G` vanish locally under some affine-open unit.

Proof: (1) Integrality and the affine-open basis give a nonempty filtered index poset. The
factorization of the units for nested opens gives the kernel inclusions and their functor
laws. (2) Apply exactness of filtered colimits of abelian sheaves to the sequences
`0 → K_U → G → G/K_U → 0`. The constant middle diagram has colimit `G`, so the canonical
map is monic. (3) The covering hypothesis lifts every section locally to some kernel;
therefore the canonical map is locally surjective and hence epic. (4) An abelian-category
morphism which is both monic and epic is an isomorphism. -/
theorem exists_kernel_cocone_isIso_colimitDesc_of_genericVanishing
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve f] [IsIntegral C]
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : ∀ (V : C.Etale) (s : G.obj.obj (op V)),
      C.genericVanishingSieve G s ∈ C.smallEtaleTopology V) :
    ∃ (D : C.NonemptyAffineOpensᵒᵖ ⥤ Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
      (ι : D ⟶ (Functor.const C.NonemptyAffineOpensᵒᵖ).obj G)
      (hι : ∀ U : C.NonemptyAffineOpensᵒᵖ, ι.app U ≫ C.affineOpenUnit U.unop G = 0),
      (∀ U : C.NonemptyAffineOpensᵒᵖ,
        Nonempty (IsLimit (KernelFork.ofι (ι.app U) (hι U)))) ∧
      IsIso (colimit.desc D { pt := G, ι := ι }) := sorry

end AlgebraicGeometry.IsCurve
