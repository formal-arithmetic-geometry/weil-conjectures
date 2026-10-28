/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.Paper.FiniteQuotientCoefficientLayerData
public import Sheaf.Paper.FiniteQuotientLayerTensorComplex
public import Sheaf.Paper.FiniteCoefficientLocalHomologyModels

/-! # The actual coefficient kernel as a constant residue module

Source: Stacks Project, sites-cohomology.tex, Tag 094I.
(blueprint: lem-weil-pbc-finite-quotient-layer-kernel-constant-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The actual successor coefficient kernel is the constant ideal-power layer,
with its scalar action restricted from the residue coefficient sheaf.

Source: Stacks Project, sites-cohomology.tex, Tag 094I, the
identification of the successive-power ideal layer in the coefficient filtration.
(blueprint: lem-weil-pbc-finite-quotient-layer-kernel-constant-comparison).

Proof: write B=A/I^(n+2), C=A/I and L=I^(n+1)/I I^(n+1). The map sending the
class of x in L to the class of x in B is additive and injective: its kernel is
exactly I I^(n+1)=I^(n+2). Its image is ker(B -> A/I^(n+1)). Multiplication by I
annihilates that kernel, so this is a C-linear identification, restricted along
B -> C. Constant module sheafification is exact, and the coefficient maps phi
are isomorphisms. Thus they carry the algebraic kernel to the kernel of the
actual coefficient-unit map. The scalar-compatibility equation hc.2, cancelled
against the constant quotient map from A, identifies the successor-to-residue
coefficient square. Consequently the transported B-action is exactly the
restriction displayed here. The proof includes I=0, I=top and the zero ring;
exact sheafification also covers an empty site. -/
theorem finiteQuotient_layer_kernel_constant_comparison
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ k : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (k + 1)) ⟶
      completedAdicFiniteCommRing X d k)
    (hφ : ∀ k : ℕ, IsIso (φ k))
    (hc : FinitePerfectModelsCompatible X d φ) (n : ℕ) :
    Nonempty (kernel (finiteQuotientUnitMap X d n) ≅
      (SheafOfModules.restrictScalars.{t + 1}
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
            (completedAdicQuotientCommMap X d (n + 1) 0 (Nat.zero_le _)))).obj
        ((finiteCoefficientConstantFunctor X (A ⧸ d.ideal ^ (0 + 1)) (φ 0)).obj
          (finiteQuotientLayerModule d.ideal n))) := by sorry

end AlgebraicGeometry.Scheme
