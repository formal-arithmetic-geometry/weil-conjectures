/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.PicardConstantSectionsTensor
public import Sheaf.Paper.PQFCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.ExternalSectionsOpenComparison
import Sheaf.AlgebraicGeometry.ExternalGlobalSectionsTensorAffineRight

/-! # Affine comparison with the constant global-sections tensor presheaf

Source: Stacks Project, Varieties, Tag 0BED, affine-open degree-zero calculation.
(blueprint: lem-sc-picard-external-coefficients-pushforward-tensor-comparison).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option autoImplicit false

/-- Compare the external direct image with the tensor presheaf, without choosing a basis.
Source: Stacks Project, Varieties, Tag 0BED, first isomorphism in the ordinary
pushforward calculation, restricted to affine opens.
(blueprint: lem-sc-picard-external-coefficients-pushforward-tensor-comparison).

Proof: On an affine V, the identity-functor presheaf pullback defining scalar extension
is computed sectionwise. Its value is O_Y(V) tensor_k Gamma(X,F). Tensoring this over
O_Y(V) with G(V) identifies the value with Gamma(X,F) tensor_k G(V). The forward map
sends (a tensor s) tensor t to s tensor (a*t); its inverse sends s tensor t to
(1 tensor s) tensor t. Tensor balance proves inverse identities and O_Y(V)-linearity.
Identify the inverse image of V under pr2 with X times V. The open-immersion
module pullback-restriction comparison identifies the restriction of the external
coefficients with F external G|V, with pure-section compatibility. Apply the
external global-section tensor comparison for the affine right factor V. Its
bijection sends s tensor t to the product of their projection pullbacks. It is
O_Y(V)-linear by pure-tensor multiplication and tensor induction. These maps commute
with all inclusions between affine opens: scalar extension restricts a and t, leaves
s unchanged, and the external section formula restricts to the same pure section.
Tensor induction proves naturality. Assemble component module isomorphisms using
PresheafOfModules.isoMk. The empty affine open and zero modules give zero tensor
modules; no basis, coproduct or sheafification is used in this argument. -/
theorem exists_external_constant_sections_tensor_comparison
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [IsAffineHom (pullback.diagonal f)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Nonempty ((PresheafOfModules.pushforward₀
        (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V)) Y.ringCatSheaf.obj).obj
        (picardConstantSectionsTensor k Y g (scalarObj f F (op ⊤)) G) ≅
      (PresheafOfModules.pushforward₀
        (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V)) Y.ringCatSheaf.obj).obj
        ((RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom).obj
          (externalCupCoefficients f g F G)).val) := by sorry

end AlgebraicGeometry.Scheme.Modules
