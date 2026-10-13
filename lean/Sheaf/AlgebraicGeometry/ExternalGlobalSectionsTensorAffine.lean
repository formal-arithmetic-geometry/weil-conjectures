/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.ScalarGlobalSectionsComparison
public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # External global sections on two affine factors

Source: Stacks Project, Tag 0BED, affine charts of equation-kunneth-on-cech.
(blueprint: lem-sc-external-global-sections-tensor-affine).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

/-- On two affine schemes the canonical external tensor comparison is bijective.
Source: Stacks Project, Tag 0BED, affine computation in lemma-kunneth.
(blueprint: lem-sc-external-global-sections-tensor-affine).

Proof: Write A = Gamma(X,O), B = Gamma(Y,O), M = Gamma(X,F), N = Gamma(Y,G).
The affine chart isomorphisms identify the product with Spec(A tensor_k B). The affine
pullback-section comparisons identify the two pulled-back modules with the scalar
extensions of M and N to A tensor_k B. The affine tensor-section comparison identifies
the external coefficient sections with their tensor product over A tensor_k B.
The algebraic isomorphism from this tensor product to M tensor_k N sends
(m tensor b) tensor (a tensor n) to (a*m) tensor (b*n). Its inverse sends m tensor n
to (m tensor 1) tensor (1 tensor n). The balance relations over A, B and A tensor_k B
make these well-defined, and tensor induction proves the two inverse identities.
The pure-tensor formulas for the pullback-section comparisons and tensor-section map
show that the composite inverse is precisely the external section map: it takes
s tensor t to the tensor of the two projection pullbacks. Tensor induction identifies
these linear maps on all inputs. Thus the canonical map is bijective. Zero rings,
empty affine schemes and zero coefficients satisfy the same algebraic identities. -/
theorem externalGlobalSectionsTensor_bijective_of_isAffine
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [IsAffine X] [IsAffine Y]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Function.Bijective (externalGlobalSectionsTensor f g F G) := by sorry

end AlgebraicGeometry.Scheme.Modules
