/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PicardConstantSectionsTensor
public import Sheaf.Paper.PQFCohomology
public import Sheaf.AlgebraicGeometry.ExternalSectionsComponents

/-! # The ordinary external section map on constant tensor coefficients

Source: Stacks Project, Varieties, Tag 0BED, degree-zero tensor calculation.
(blueprint: lem-sc-external-constant-sections-tensor-map).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option autoImplicit false

/-- Scalar extension and tensor balance lift the external section map to an O_Y-linear
presheaf morphism. Its component is bijective exactly when the corresponding k-linear
external section component is bijective.
Source: Stacks Project, Varieties, Tag 0BED, affine-open degree-zero calculation.
(blueprint: lem-sc-external-constant-sections-tensor-map).

Proof: At any open V, identity-functor presheaf pullback is extension of scalars.
The balanced map (a tensor s) tensor t maps to s tensor (a*t), with inverse
s tensor t mapping to (1 tensor s) tensor t. These formulas give an isomorphism
of underlying k-modules between the constant coefficient tensor object at V and
Gamma(X,F) tensor_k G(V), with O_Y(V) acting on the second factor.
Compose this isomorphism with externalSectionsComponent. Multiplication on tensor
sections and O_Y-linearity of the second projection's adjunction unit prove
O_Y(V)-linearity of the composite. Naturality of scalar extension and the proved
externalSectionsComponent_naturality show that these composites form a morphism
of presheaves of modules. The k-action on the direct image agrees with the action
through the first projection because the pullback square commutes. Consequently
its underlying component is the external section component composed with a
bijection, proving the displayed equivalence. This construction uses no affine,
compactness or quasi-coherence hypothesis. Empty opens and zero coefficients
are covered by the same mutually inverse balanced maps. -/
theorem exists_external_constant_sections_tensor_map
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) :
    ∃ φ : picardConstantSectionsTensor k Y g (scalarObj f F (op ⊤)) G ⟶
      ((RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom).obj
        (externalCupCoefficients f g F G)).val,
      ∀ V : Y.Opens, Function.Bijective (φ.app (op V)) ↔
        Function.Bijective (externalSectionsComponent f g F G V) := by sorry

end AlgebraicGeometry.Scheme.Modules
