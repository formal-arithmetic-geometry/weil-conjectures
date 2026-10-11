/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import Sheaf.Algebra.Homology.ModuleStalkFunctor

/-!
# Stalks and germs of the tensor pullback of modules

Source: Stacks Project, Sheaves, Lemma 6.26.4 (Tag 0098)
(blueprint: lem-weil-pbc-module-stalk-pullback).

Stalks of module sheaves are taken with the recorded stalk functor
`RingedSpace.moduleStalkFunctor` (def-pc-module-stalk-functor). Mathlib writes extension of
scalars as `O_{X,x} ⊗ G_{f(x)}`. This is the tensor product in the node via its canonical
symmetry; the corresponding pure tensor is `1 ⊗ s_{f(x)}`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The stalk of tensor pullback is naturally the extension of scalars of the original
stalk along `f.stalkMap x`; a pulled-back section has germ `1 ⊗ s_{f(x)}`.
Source: Stacks Project, Tag 0098 (blueprint: lem-weil-pbc-module-stalk-pullback).

Proof:
0. By def-pc-module-pullback and the canonical adjunction (Tag 0096), the unit sends
   a section `s` to the sheafification of `1 ⊗ η(s)`, where `η` is the inverse-image unit.
1. By lem-weil-pbc-topological-inverse-image-stalk (008H), inverse-image stalks are the
   original stalks, naturally and compatibly with germs. The module identification is
   semilinear over the corresponding ring-stalk identification, since the inverse-image
   unit respects the scalar action on sections.
2. The stalk of the adjoint ring map composed with that ring-stalk identification is
   `f.stalkMap x`: on every germ this follows from the ring-map adjunction identity.
3. By lem-weil-pbc-stalk-change-of-rings-tensor (008B), the stalk of the change of rings
   is the change of rings of the stalk, naturally and with the pure-tensor germ formula.
4. Transport this tensor along the identifications in steps 1 and 2. The balanced map
   sends `b ⊗ m` to `b ⊗ c(m)`; its inverse uses `c⁻¹`, so it is an isomorphism.
5. Combining the germ formulas in steps 0, 1 and 3 sends the germ of the pulled-back
   section to `1 ⊗ s_{f(x)}`.
6. The identifications of inverse-image stalks and tensor stalks are natural. Their
   composite is therefore a natural isomorphism between the two composite functors. -/
theorem exists_tensorPullback_stalk_iso {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    ∃ e : tensorPullback f ⋙ RingedSpace.moduleStalkFunctor X.toRingedSpace x ≅
        RingedSpace.moduleStalkFunctor Y.toRingedSpace (f x) ⋙
          ModuleCat.extendScalars (f.stalkMap x).hom,
      ∀ (G : Y.Modules) (V : Y.Opens) (hx : f x ∈ V) (s : G.val.obj (op V)),
        (e.hom.app G)
            (TopCat.Presheaf.germ ((tensorPullback f).obj G).val.presheaf (f ⁻¹ᵁ V) x hx
              (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app G).val.app
                (op V) s)) =
          (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x), (f.stalkMap x).hom]
            (TopCat.Presheaf.germ G.val.presheaf V (f x) hx s) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
