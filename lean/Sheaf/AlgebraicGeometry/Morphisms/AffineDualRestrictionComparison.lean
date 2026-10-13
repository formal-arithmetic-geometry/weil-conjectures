/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.LinearAlgebra.Dual.Defs
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-! # Affine dual and restriction

Source: Stacks Project, Tag 0583 (algebra-lemma-localize-hom), as used in
Tag 0EY6, proof of (1).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Localization of Hom identifies the restriction of the associated sheaf of the
module dual with the sheaf dual of the restriction.
Source: Stacks Project, Tag 0583, as used in Tag 0EY6, proof of (1).
(blueprint: new-affine-dual-restriction-comparison)

Proof: A finite module over a Noetherian ring is finitely presented. For each
basic open D(f), localization of Hom identifies (Hom_A(M,A))_f with
Hom_{A_f}(M_f,A_f). The affine tilde equivalence identifies the latter with
morphisms of the restricted associated sheaves. These maps send a localized
functional to its action on localized sections, so commute with further
localization. Basic opens contained in W form a basis, hence the compatible
isomorphisms glue uniquely to the sheaf internal Hom on W. This argument
also applies to the empty open and the zero module. -/
theorem affine_dual_restriction_comparison
    (A : CommRingCat.{u}) [IsNoetherianRing A] (W : (Spec A).Opens)
    (M : ModuleCat.{u} A) [Module.Finite A M] :
    Nonempty (Modules.restrict (tilde (ModuleCat.of A (Module.Dual A M))) W.ι ≅
      SheafOfModules.homObj.{u} (R := W.toScheme.sheaf) (Modules.restrict (tilde M) W.ι)
        (SheafOfModules.unit W.toScheme.ringCatSheaf)) := by sorry

end AlgebraicGeometry.Scheme
