/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.CategoryTheory.InternalRestrictionModuleTensorData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorTrilinearUniversal

/-! # Tensor coherence for normalized precomposition pullback

Source: Stacks 03EK and the bilinear and trilinear universal properties.
(blueprint: lem-sfb-normalized-precomposition-tensor).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open SheafOfModules

namespace CategoryTheory.InternalActionSite

variable {C : Type u} [SmallCategory C]

attribute [local irreducible] SheafOfModules.monoidalCategory

/-- A normalized precomposition pullback has the canonical coherent tensor
structure, on the same specified scalar-extension core.

Source: Stacks Project, Modules on Sites, Tag 03EK; steps 5--6 of
lem-sfb-internal-restriction-module-tensor.
(blueprint: lem-sfb-normalized-precomposition-tensor).

Proof: the inverse image in p is precomposition on sets and maps, and its ring map
is the identity. On presheaf modules the identity on sectionwise pure tensors
therefore compares the tensor of the two inverse images with the inverse image of
the tensor. Inverse image is a left adjoint and preserves finite products; the
sheaf tensor is the sheafification of the balanced presheaf tensor. Its universal
property thus sheafifies this comparison to an isomorphism. Transport it along
core.unitor. The multiplication and insertion equations in laws show that the
scalar insertion is m ↦ 1 tensor m and the comparison satisfies the generalized
pure-tensor equation for every test sheaf; this constructs the recorded
CanonicalRingedTensorComparison, including naturality. The section identifications
in laws give tensor_pure. Use the regular ring for the unit: after multiplication
its unit comparison is the identity on every section. Naturality and symmetry
are checked on x tensor y, and the two unit equations are scalar multiplication.
Bilinear uniqueness proves these equations on the sheaf tensors. Both associativity
composites send (x tensor y) tensor z to x tensor (y tensor z); trilinear uniqueness
proves equality. These equations define the Monoidal structure with μ equal to the
inverse of the recorded comparison. Package the original core and laws with these
tensor data, so the resulting core equals the input core. The proof uses no action
presentation, faithful points, flatness assumption, or nonzero ring hypothesis. -/
theorem normalizedPrecompositionTensor {D : Type u} [SmallCategory D]
    {J : GrothendieckTopology C} {T : GrothendieckTopology D} {F : D ⥤ C}
    {R : Sheaf J CommRingCat.{u}} {hR : Presheaf.IsSheaf T (F.op ⋙ R.obj)}
    (p : InternalPrecompositionMorphism J T F R hR)
    (core : InternalModulePullback p) (laws : InternalModulePullbackLaws core) :
    ∃ P : InternalExactTensorPullback p, P.core = core := by
  sorry

end CategoryTheory.InternalActionSite
