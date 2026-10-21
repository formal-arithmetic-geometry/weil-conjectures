/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel

import Sheaf.AlgebraicGeometry.ContractibleLisseEvaluation
import Sheaf.AlgebraicGeometry.CondensedComponentInverseImage
import Sheaf.AlgebraicGeometry.CondensedComponentPullbackCompatibility
import Sheaf.AlgebraicGeometry.CondensedProfiniteScalarCompatibility
import Sheaf.CategoryTheory.Sites.ContractibleDerivedSectionsTensor
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

/-! # Evaluation and connected components of lisse condensed sheaves

Source: Hemo--Richarz--Scholbach, Section 3, (3.1)--(3.2), Remark 3.2,
Lemma 4.1 and Proposition 4.3(3)
(blueprint: lem-zl-condensed-wcontractible-lisse-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open SheafOfModules in
private theorem affine_evaluation_statement (T : Scheme.{u}) [IsAffine T]
    [IsWContractibleRing Γ(T, ⊤)]
    (O : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj O] [IsCommMonObj O] :
    Evaluation.Statement (Scheme.ProEt.topology T) O (Scheme.ProEt.mk (𝟙 T))
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale T) := by
  let J := Scheme.ProEt.topology T
  let := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, 0}
    J (Evaluation.ringSheaf J O)).1
  let : HasDerivedCategory.{u + 1} (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (Evaluation.ringSheaf J O))) := HasDerivedCategory.ofIsGrothendieckAbelian _
  exact contractible_lisse_evaluation J O _ _
    (AlgebraicGeometry.contractible_derived_sections_tensor.{0, u}.1 T _)

open SheafOfModules in
private theorem profinite_evaluation_statement (S : Profinite.{u}) [ExtremallyDisconnected S]
    (O : Sheaf ((coherentTopology Profinite.{u}).over S) Ab.{u + 1})
    [MonObj O] [IsCommMonObj O] :
    Evaluation.Statement ((coherentTopology Profinite.{u}).over S) O
      (Over.mk (𝟙 S)) Over.mkIdTerminal := by
  let J := (coherentTopology Profinite.{u}).over S
  let := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, 0}
    J (Evaluation.ringSheaf J O)).1
  let : HasDerivedCategory.{u + 1} (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (Evaluation.ringSheaf J O))) := HasDerivedCategory.ofIsGrothendieckAbelian _
  exact contractible_lisse_evaluation J O _ _
    (AlgebraicGeometry.contractible_derived_sections_tensor.{0, u}.2 S _)

/-- Evaluation, perfect/lisse equivalence, and component pullback for canonical coefficients.

Source: Hemo--Richarz--Scholbach, Section 3 (3.1)--(3.2), Remark 3.2,
Lemma 4.1(1)--(2), construction (4.1), and Proposition 4.3(3)
(blueprint: lem-zl-condensed-wcontractible-lisse-evaluation).

Proof for stage 3 (the nine steps of the DAG node).
1. For either allowed base, `lem-zl-contractible-derived-sections-tensor` makes evaluation
   exact and colimit-preserving and identifies derived evaluation with termwise sections.
   Its tensor comparison is strong symmetric monoidal, including the unit comparison.
   Thus sections preserve evaluation, coevaluation, and both duality identities.
2. The global-sections morphism with the constant-section counit gives the module
   extension/sections adjunction (`lem-weil-pbc-ringed-topoi-module-adjunction`).
   Derive it on flat-term K-flat models (`lem-weil-pbc-ringed-topoi-derived-pullback`,
   `def-sfb-site-derived-constant-module-functor`, `lem-sc-derived-adjunction-from-underived`).
   This is precisely F ⊣ G. Derived tensor pullback and F(A)=Λ give strong symmetry;
   derived pullback preserves distinguished triangles, without asserting t-exactness.
3. On a free module the adjunction unit is the identity: both sides preserve coproducts
   and send A to its coefficient sheaf and back to A. Present an arbitrary module by
   free modules. Exactness of sections and right exactness of extension prove that its
   unit is invertible. Naturality makes this independent of the presentation.
4. Resolve an arbitrary unbounded Q by a flat-term K-flat complex P
   (`lem-pc-kflat-resolution`). The derived pullback comparison represents F(Q) by E(P),
   and step 1 computes G termwise. Step 3 is a chain isomorphism P → Γ(E(P)).
   Derived-adjunction normalization identifies it with the unit, proving full faithfulness
   of F on all D(A).
5. For dualizable M,N, the two duality identities transpose Hom(M,N) to
   Hom(Λ,Mᵛ tensor N). Strong symmetry of G takes these exact formulas to the analogous
   transpositions over A. The adjunction at A identifies Hom(Λ,Z) with Hom(A,GZ).
   Consequently the map on Hom induced by G is bijective on dualizable objects.
6. `lem-zl-ring-derived-dualizable-perfect` identifies dualizable ring complexes with
   perfect complexes. Both functors restrict. The unit is invertible by step 4.
   For lisse M the triangle identity makes G of the counit inverse to the unit.
   Step 5 reflects isomorphisms on lisse objects, so the counit is invertible as well.
   The restricted unit and counit give Perf(A) ≃ D_lis with inverse RΓ.
7. For w-contractible affine T, `sk-def-pe-wlocal` makes π₀T extremally disconnected.
   `lem-zl-component-relative-profinite-site` supplies the relative test functor and
   factorization p_T = q_S π_T. The corresponding monoidal inverse-image comparison
   supplies the ring-object identification π_T⁻¹Λ_S ≅ Λ_T, including constant sections.
   `lem-trf-geometric-inverse-image-exact` gives exact module pullback; derive termwise.
   Derived tensor pullback makes it strong symmetric monoidal. The point-basis evaluation
   theorem identifies A_T with Λ(π₀T); the finite-clopen refinement theorem
   `det-pe-wcb-clopen-partition` verifies its topos weak-contractibility hypothesis.
8. Inverse image preserves constants. On flat-term K-flat representatives, pullback
   preserves K-flatness (`lem-weil-pbc-ringed-pullback-preserves-kflat`) and commutes
   with derived tensor. This identifies π_T^* F_S with F_T after the section-ring
   comparison, naturally in every chain map. Descend by
   `lem-weil-pbc-site-derived-tensor-descent`. Step 6 for S and T identifies this square
   on lisse objects with the identity equivalence of Perf(A), proving the component
   equivalence. The same factorization identifies the realizations from R=Γ(*,Λ).
9. Resolve any P in D(R) by a flat-term K-flat complex. Scalar extension R→A_T and
   constant realization preserve the required models. The balanced chain maps
   b tensor (a tensor p) ↦ ba tensor p and b tensor p ↦ b tensor (1 tensor p)
   are inverse, commute with differentials and are natural in chain maps.
   `lem-sfb-constant-realization-derived-scalar-extension` handles constants in the
   first extension; tensor descent localizes these maps. This is the natural
   identification Λ_T tensor_R^L P ≅ F_T(A_T tensor_R^L P), also for the profinite case. -/
theorem condensed_wcontractible_lisse_evaluation
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] :
    (∀ (T : Scheme.{u}) [IsAffine T] [IsWContractibleRing Γ(T, ⊤)],
      Evaluation.Statement (Scheme.ProEt.topology T) (condensedRingObj Λ.X T)
        (Scheme.ProEt.mk (𝟙 T))
        (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale T) ∧
      componentClause Λ.X T) ∧
    (∀ (S : Profinite.{u}), ExtremallyDisconnected S →
      Evaluation.Statement ((coherentTopology Profinite.{u}).over S)
        (profiniteCoefficient Λ.X S) (Over.mk (𝟙 S)) Over.mkIdTerminal ∧
      profiniteScalarClause Λ.X S) := by
  constructor
  · intro T _ _
    obtain ⟨hC, ⟨hB⟩, hlim, hcolim⟩ := condensed_component_inverse_image T
    let := hC
    let := hB
    let := hlim
    let := hcolim
    exact ⟨affine_evaluation_statement T (condensedRingObj Λ.X T),
      hC, hB, hlim, hcolim, condensed_component_pullback_compatibility Λ T⟩
  · intro S hS
    let := hS
    exact ⟨profinite_evaluation_statement S (profiniteCoefficient Λ.X S),
      condensed_profinite_scalar_compatibility Λ S⟩

end AlgebraicGeometry.ProEtale.CondensedRing
