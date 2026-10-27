/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R6
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleCoefficientSliceComparisonData

/-! # Closed slice comparison with transported coefficients

Source: Hemo--Richarz--Scholbach, Lemma 4.5; Stacks 03CE, 07A4, 08J9, 08JB.
(blueprint: lem-zl-proetale-coefficient-slice-closed-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.Scheme

/-- Exact monoidal descent along a pro-etale object, with transported coefficients.
Given the normalized ordinary comparison, this assertion constructs total tensor complexes,
their K-flat
localization and the signed symmetry. It makes no assertion about internal Hom.

Source: Stacks, sites.tex, Tag 03CE (lemma-localize-given-products),
sites-modules.tex, Tag 03EL (lemma-tensor-product-pullback), and
sites-cohomology.tex, Tags 07A4 and 0FPT
(blueprint: lem-zl-proetale-slice-monoidal-descent).

Proof: use the supplied ordinary comparison i with its distinguished-section
normalization hi. Identify the source small site with the slice by ProEt.sliceEquiv.
Tensor comparison
for restriction is the sheafification of x tensor y mapped to x tensor y. Scalar
transport has the same formula because its two balancing relations agree under b.
The inverse maps have the identical formulas. The regular-module maps are identity
for restriction and b for scalar transport; composing them with the ordinary
comparison defines the pullback unit. Apply the tensor comparisons degreewise and
sum over p+q=n. The differential commutes with them, with its usual signed second
term. Exact restriction and invertible scalar change preserve K-flatness. Descend
using the K-flat localization equivalence and the supplied representative models
T, TR, TB. Both paths in the tensor compatibility square on extended pure factors
send (x tensor s) tensor (y tensor t) to b inverse(st) times (delta(x) tensor delta(y)).
Thus the square agrees with the canonical pullback comparison, whose normalization
characterizes it. The analogous degree-zero square proves the unit equation. On
each (p,q) summand the two symmetry paths send x tensor y to (-1)^(pq)y tensor x.
The supplied coherence witnesses identify these signed swaps with beta and betaB;
naturality and K-flat localization extend the equation to all derived inputs.
The same argument applies to empty sites and zero coefficient rings; no nonzero
scalar or geometric finiteness is used. -/
theorem proEtaleSlice_monoidal_descent {X : Scheme.{u}} (U : X.ProEt)
    (O : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (B : Sheaf (ProEt.topology U.left) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj O ≅ B)
    (delta : ProEtaleObjectRestrictionComparison U CommRingCat.{u + 1})
    (S : CoefficientClosedStructure (proEtaleCoefficientHom X O))
    (SR : CoefficientClosedStructure (proEtaleCoefficientHom U.left (proEtaleSliceRing U O)))
    (SB : CoefficientClosedStructure (proEtaleCoefficientHom U.left B))
    (T : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology X) O S)
    (TR : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology U.left)
      (proEtaleSliceRing U O) SR)
    (TB : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology U.left) B SB)
    (beta : @SymmetricCategory (DerivedCategory (proEtaleRingModules X O)) _ S.monoidal)
    (betaB : @SymmetricCategory (DerivedCategory (proEtaleRingModules U.left B)) _ SB.monoidal)
    (_coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology X) O S T beta)
    (_coherenceB : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology U.left) B SB TB betaB)
    (i : proEtaleRingModulePullback U.hom O B c ≅
      proEtaleSliceModuleRestriction U O ⋙
        ProEtaleCoefficientSliceComparison.e U O B c delta)
    (hi : ∀ (N : proEtaleRingModules X O) (V : U.left.ProEt)
      (m : N.val.obj
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V))),
      (i.hom.app N).val.app (op V)
        (proEtaleSlicePullbackSection U O B c N V m) = m) :
    ∃ d : ProEtaleCoefficientSliceComparison.TensorData U O B c delta S SR SB T TR TB,
      d.ordinary = i ∧
      ProEtaleCoefficientSliceComparison.TensorNormalized U O B c delta S SR SB T TR TB d ∧
      ∀ L M : DerivedCategory (proEtaleRingModules X O),
        (proEtaleRingDerivedPullback U.hom O B c).map
            (beta.toBraidedCategory.braiding L M).hom ≫
            (ProEtaleCoefficientSliceComparison.rho U O B c S SB T TB).hom.app (M, L) =
          (ProEtaleCoefficientSliceComparison.rho U O B c S SB T TB).hom.app (L, M) ≫
            (betaB.toBraidedCategory.braiding
              ((proEtaleRingDerivedPullback U.hom O B c).obj L)
              ((proEtaleRingDerivedPullback U.hom O B c).obj M)).hom := by
  sorry

end AlgebraicGeometry.Scheme
