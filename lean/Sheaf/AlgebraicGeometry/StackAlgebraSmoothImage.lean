/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import Sheaf.AlgebraicGeometry.StackQuasiCoherentSchemeRestriction
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Shapes.Images

import Sheaf.AlgebraicGeometry.StackQcohAbelian
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.CategoryTheory.CommAlgebraSheafImage
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage

/-! # Image factorization of quasi-coherent algebras on smooth tests

Source: Stacks Project, stacks-sheaves.tex, Tag 06WV(1)--(5), and
stacks-cohomology.tex, Tags 076X and 0GQF
(blueprint: lem-sfb-stack-algebra-smooth-image).

The underlying image is taken in quasi-coherent modules. Its ordinary scheme image
comparison is expressed by an isomorphism of image factorizations, commuting with both
arrows. Global sections of a restricted algebra are the compatible families of its
literal precomposition presheaf.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w v' w'

open AlgebraicGeometry CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The underlying module map in the algebra image factorization, with the original
section maps and scalar action. Source: Stacks Tags 06WG and 06WV
(blueprint: lem-sfb-stack-algebra-smooth-image). -/
def moduliAlgebraImageModuleMap {S : Scheme.{u}}
    {X : BasedCategory.{v, w} (Over S)} {hX : IsFibredInGroupoids X}
    {A B : ModuliAlgebraSheaf X hX} (f : A ⟶ B) :
    moduliAlgebraModule A ⟶ moduliAlgebraModule B where
  val := PresheafOfModules.homMk
    (Functor.whiskerRight f.right.hom
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) (by
      intro U r a
      change A.right.obj.obj U at a
      change (moduliStructureSheaf X hX).obj.obj U at r
      change (f.right.hom.app U).hom ((A.hom.hom.app U).hom r * a) =
        (B.hom.hom.app U).hom r * (f.right.hom.app U).hom a
      rw [map_mul]
      congr 1
      exact congrArg (fun t ↦ t.hom.app U r) (Under.w f))

/-- Regard the canonical underlying algebra map in the existing full quasi-coherent
subcategory. Source: Stacks Tag 06WV(2)
(blueprint: lem-sfb-stack-algebra-smooth-image). -/
def moduliAlgebraImageQCohMap {S : Scheme.{u}}
    {X : BasedCategory.{v, w} (Over S)} {hX : IsFibredInGroupoids X}
    {A B : ModuliAlgebraSheaf X hX} (f : A ⟶ B)
    (hA : IsQuasicoherentModuliAlgebra A) (hB : IsQuasicoherentModuliAlgebra B) :
    (⟨moduliAlgebraModule A, hA⟩ : ModuliQCoh X hX) ⟶
      (⟨moduliAlgebraModule B, hB⟩ : ModuliQCoh X hX) :=
  ObjectProperty.homMk (moduliAlgebraImageModuleMap f)

/-- Quasi-coherent algebra images, their ordinary smooth-scheme image factorization,
and injectivity on global sections after every smooth algebraic-stack pullback.
Source: Stacks 06WV(1)--(5), 076X and 0GQF
(blueprint: lem-sfb-stack-algebra-smooth-image).

Proof:
1. In QCoh(X), form K = ker(u) and C = coker(K -> A). The abelian coimage-image
   comparison (lem-sfb-stack-qcoh-abelian) gives u = jq, with j the categorical
   image inclusion. By lem-sfb-stack-qcoh-flat-atlas-exactness, q is the ambient
   fppf module-sheaf cokernel, hence locally surjective. No ambient monicity of j
   on nonflat tests is asserted.
2. Put h = q mu_A. Monicity of j and multiplicativity of u give h(i tensor 1) = 0
   and h(1 tensor i) = 0, where i : K -> A. By
   lem-weil-pbc-independent-sheaf-tensor-colimits, descend h through q tensor 1
   and then 1 tensor q to mu_C; the second vanishing follows after precomposing
   with the epimorphism q tensor 1_K. Set eta_C = q eta_A. Precompose with the
   tensor powers of q to verify associativity, commutativity, units, and that q
   and j preserve multiplication and units. Tensor closure follows from
   lem-sfb-stack-qcoh-flat-atlas-exactness.
3. On a smooth scheme test, lem-sfb-stack-smooth-qcoh-exact preserves the kernel,
   cokernel and image. The restriction comparison identifies these module maps
   and tensors with the ordinary ones. The scheme kernel and cokernel-image
   theorems (lem-weil-pbc-quasi-coherent-module-kernel and
   lem-weil-pbc-quasi-coherent-module-cokernel-image) identify this with the image
   in all ordinary modules. By lem-weil-pbc-ringed-space-algebra-image its algebra
   structure is the ordinary image algebra: both multiplications become q mu_A
   after q tensor q, and both units become q eta_A. The image inclusion is
   injective on every open, in particular on the whole scheme, which is C(T)
   by lem-sfb-stack-quasi-coherent-scheme-restriction.
4. For a smooth Z -> X, the same restriction lemma identifies precomposition
   with tensor pullback. Exact smooth pullback preserves j's QCoh monicity.
   Pull back further to a smooth surjective scheme atlas U -> Z. Step 3 makes
   the induced section map injective on U. Two global sections with equal images
   therefore agree on U; lem-sfb-smooth-cover-section-descent gives their equality
   on Z. This applies to every smooth morphism, including nonrepresentable ones:
   smoothness below is expanded as a smooth source atlas whose composite is smooth.
-/
theorem exists_moduliAlgebraSmoothImage (k : Type u) [Field k]
    (X : BasedCategory.{v, w} (Over (Spec (.of k)))) (hX : IsAlgebraicModuliStack X)
    {A B : ModuliAlgebraSheaf X hX.1.1} (f : A ⟶ B)
    (hA : IsQuasicoherentModuliAlgebra A) (hB : IsQuasicoherentModuliAlgebra B) :
    ∃ (C : ModuliAlgebraSheaf X hX.1.1) (hC : IsQuasicoherentModuliAlgebra C)
      (q : A ⟶ C) (j : C ⟶ B),
      q ≫ j = f ∧ IsSurjectiveModuliAlgebra q ∧
      (∃ (I : ImageFactorisation (moduliAlgebraImageQCohMap f hA hB))
        (e : (⟨moduliAlgebraModule C, hC⟩ : ModuliQCoh X hX.1.1) ≅ I.F.I),
        e.hom ≫ I.F.m = moduliAlgebraImageQCohMap j hC hB ∧
        moduliAlgebraImageQCohMap q hA hC ≫ e.hom = I.F.e) ∧
      (∀ (T : Over (Spec (.of k)))
        (a : BasedFunctor (discreteModuli (yoneda.obj T)) X),
        ModuliSpaceTest @Smooth a →
        ∀ R : ModuliSchemeRestriction X hX.1.1,
        ∃ (I : ImageFactorisation
          ((R.restriction (a.obj (CostructuredArrow.mk (𝟙 (yoneda.obj T))))).map
            (moduliAlgebraImageQCohMap f hA hB)))
          (e : (R.restriction (a.obj (CostructuredArrow.mk (𝟙 (yoneda.obj T))))).obj
            ⟨moduliAlgebraModule C, hC⟩ ≅ I.F.I),
          e.hom ≫ I.F.m =
            (R.restriction (a.obj (CostructuredArrow.mk (𝟙 (yoneda.obj T))))).map
              (moduliAlgebraImageQCohMap j hC hB) ∧
          (R.restriction (a.obj (CostructuredArrow.mk (𝟙 (yoneda.obj T))))).map
            (moduliAlgebraImageQCohMap q hA hC) ≫ e.hom = I.F.e) ∧
      (∀ (T : Over (Spec (.of k)))
        (a : BasedFunctor (discreteModuli (yoneda.obj T)) X),
        ModuliSpaceTest @Smooth a → Function.Injective
          (j.right.hom.app (op (a.obj (CostructuredArrow.mk (𝟙 (yoneda.obj T))))))) ∧
      (∀ (Z : BasedCategory.{v', w'} (Over (Spec (.of k))))
        (_ : IsAlgebraicModuliStack Z) (a : BasedFunctor Z X),
        (∃ (U : Over (Spec (.of k))) (p : BasedFunctor (discreteModuli (yoneda.obj U)) Z),
          IsSmoothModuliAtlas Z U p ∧ ModuliSpaceTest @Smooth (p.comp a)) →
        Function.Injective ((Functor.sectionsFunctor Z.objᵒᵖ).map
          (Functor.whiskerRight (Functor.whiskerLeft a.toFunctor.op j.right.hom)
            (forget CommRingCat)))) := by
  sorry

end CategoryTheory
