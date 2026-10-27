/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F7
-/
module

public import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
public import Sheaf.CategoryTheory.RingedSiteDualityMaps
public import Sheaf.Topology.ProfiniteCondensedRing

/-! # Monoidal normalization of the derived section equivalence

Source: Stacks Project, Tags 06YU and 08J9; blueprint, the first paragraph of
`det-lem-int-tensor-product.proof.md`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [instance 50000] HasDerivedCategory.ofIsGrothendieckAbelian
universe u
open CategoryTheory CategoryTheory.MonoidalCategory Opposite WeilConjectures
open AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison

/-- The normalized section tensor comparison has the ordinary associator, unitors,
and Koszul symmetry, and its closed comparison preserves the actual counit.

Source: Stacks Project, Tags 06YU and 08J9; blueprint first paragraph of
`det-lem-int-tensor-product.proof.md`.
(blueprint: lem-sfb-internal-section-monoidal-normalization).

Proof: apply the exact section-action equivalence and its inverse termwise to
K-flat complexes. Its tensor and unit maps are multiplication on pure sections.
The associativity, unit, and symmetry equations therefore hold on complexes.
Descend through the K-flat localization; its universal property gives the strong
monoidal structure and the normalized tensor comparison. The representative
associator, unitors, and Koszul swap give a RingedSiteDualityModel on the target.
Use the evaluation-normalized derived Hom comparison: its defining evaluation
identity is exactly the final equation below. Equality on K-flat representatives
identifies its tensor comparison with the one used in the monoidal descent.
No boundedness or flatness of the coefficient ring is involved. -/
theorem internal_section_monoidal_normalization
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (X : Scheme.{u}) :
    ∃ (S : RingedSiteDualityModel.{u + 1, u, u, u + 1}
        (Scheme.ProEt.topology X) (ring Λ.X X))
      (t : TensorComparison Λ.X X S.closed S.models)
      (m : @Functor.CoreMonoidal _ _ _ _ _ S.closed.monoidal (forward Λ.X X))
      (θ : Functor.uncurry.obj (CondensedRing.derivedHom Λ.X X) ⋙ forward Λ.X X ≅
        ((forward Λ.X X).op.prod (forward Λ.X X)) ⋙ hom Λ.X X),
      (∀ K N, (@Functor.CoreMonoidal.μIso _ _ _ _ _ S.closed.monoidal
        (forward Λ.X X) m K N).inv = t.iso.hom.app (K, N)) ∧
      (∀ K N, (@Functor.CoreMonoidal.μIso _ _ _ _ _ S.closed.monoidal
          (forward Λ.X X) m K N).hom ≫
          (forward Λ.X X).map (β_ K N).hom =
        (S.symmetric.braiding _ _).hom ≫
          (@Functor.CoreMonoidal.μIso _ _ _ _ _ S.closed.monoidal
            (forward Λ.X X) m N K).hom) ∧
      (∀ K N, (forward Λ.X X).map
          ((β_ ((ihom K).obj N) K).hom ≫ (ihom.ev K).app N) =
        t.iso.hom.app ((ihom K).obj N, K) ≫
          S.closed.tensor.map
            (X := ((forward Λ.X X).obj ((ihom K).obj N), (forward Λ.X X).obj K))
            (Y := ((hom Λ.X X).obj (op ((forward Λ.X X).obj K),
              (forward Λ.X X).obj N), (forward Λ.X X).obj K))
            (θ.hom.app (op K, N), 𝟙 _) ≫
          S.closed.evaluation ((forward Λ.X X).obj K) ((forward Λ.X X).obj N)) := by
  sorry

end AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
