/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G7
-/
module

public import Sheaf.Paper.SupportedImageGenerationHull
public import Sheaf.Paper.LocalizingAdmissibleCoefficients

/-! # Kernel generation before support extension

Source: steps 1--5 of lem-sfb-supported-image-bounded-derived-generation, an
agent-formulated structural input below blueprint refinement (2), first paragraph.
Exact reference WANTED; HRS Section 4.1 supplies the component-site setting only.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The actual kernel of a map between finite scalar local models lies in the
supported derived hull on its own source, before any support extension.
Source: steps 1--5 of lem-sfb-supported-image-bounded-derived-generation;
HRS Section 4.1 for component reduction, exact hull-generation reference WANTED.
(blueprint: lem-sfb-finite-model-kernel-generation).

Proof: refine the model covers of L and M simultaneously by affine weakly
contractible pro-etale charts W. Their exact pullbacks are scalar models.
On W, the component inverse image from Prof/pi_0(W) is exact and fully faithful
on derived module categories. Finite scalar presentations identify both models
with component pullbacks, and full faithfulness lifts the actual morphism to a
module morphism v on that component site. Exactness identifies the restricted
kernel with the pullback of ker v. The component functor preserves products:
its evaluation on a weakly contractible affine is evaluation at its profinite
component space, where sheaf products are sectionwise; conservativity on this
basis detects the comparison. Termwise products compute derived products on W,
and full faithfulness detects the corresponding product on the component site.
The functor also preserves filtered sheaf colimits as an inverse-image left
adjoint, and exactness preserves the common termwise lower bound. It preserves
triangles, shifts, retracts, and the finite scalar generators. Hence minimality
of the component finite-model hull and the profinite relation-kernel theorem
put the restricted kernel in the supported hull on W. Compare finite support
chains with the tree paths by adding complementary sibling leaves; their
ordinary extension functors agree. Supported-hull pro-etale descent then puts
the kernel in the hull on the qcqs source. This uses hull-membership descent,
not just conservative restriction. Zero and identity maps yield the source
model and zero respectively; the empty scheme and zero ring cause no exception.
-/
theorem finite_model_kernel_mem_supported_generation
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (L M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S))
    (hL : HasFiniteConstantLocalModel Λ S L)
    (hM : HasFiniteConstantLocalModel Λ S M) (f : L ⟶ M) :
    supportedImageGenerationHull Λ S
      ((DerivedCategory.singleFunctor _ 0).obj (kernel f)) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
