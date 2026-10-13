/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed

/-!
# Internal Hom turns coproducts into products

Source: Stacks Project, Modules on Sites, Section 03EK and Lemma 03EO.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max u v})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Mod" => SheafOfModules.{max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)

/-- Internal Hom into a fixed sheaf takes any coproduct cofan to a product fan.
Source: Stacks Project, Modules on Sites, Section 03EK and Lemma 03EO
(blueprint: lem-sc-internal-hom-coproduct-fan).

Proof: For any test module A, maps A → homObj X N correspond naturally to maps
X ⊗ A → N by the tensor-Hom adjunction of Lemma 03EO. Tensoring with A
preserves coproducts: by symmetry it is a left adjoint, with right adjoint
homObj A. Thus a family A → homObj (M i) N corresponds to a family
M i ⊗ A → N, which uniquely descends to c.pt ⊗ A → N. Currying that descent
constructs the unique lift A → homObj c.pt N. Naturality in the first tensor
factor gives its composites with homObjMap (c.inj i) (identity N), proving
both the fan factorization and uniqueness. The adjunction is constructed by
restriction-compatible local bilinear maps and sheafification; it applies
with separate site-object and site-morphism universes and coefficients in
max u v. For the empty family, c.pt is initial and the resulting internal
Hom is terminal; zero summands require no exception. The universal property
determines every lift uniquely, so the Nonempty conclusion involves no
arbitrary choice of mathematical data. -/
theorem internalHomCoproductFanIsLimit {I : Type w} (M : I → Mod)
    (c : Cofan M) (hc : IsColimit c) (N : Mod) :
    Nonempty (IsLimit (Fan.mk (homObj (R := R) c.pt N)
      (fun i ↦ homObjMap (R := R) (c.inj i) (𝟙 N)))) := by sorry

end SheafOfModules
