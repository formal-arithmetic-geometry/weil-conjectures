/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.LocalDirectImageStalkClassMap

/-! # Scalar compatibility of the local direct-image class map

Source: Stacks Project, Tags 02OD and 01E4.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
attribute [local instance] Scheme.Modules.enoughInjectives

/-- Scalar compatibility of the specified additive cohomology-to-stalk map.
Source: Stacks Project, Tag 01E4, Lemma 20.7.3, the section-complex comparison;
Tag 02OD, Lemma 30.20.7, the displayed local-stalk/global-cohomology equality.
(blueprint: lem-weil-pbc-local-direct-image-stalk-class-smul)

Proof: Put A = O_{Y,y}, c = fromSpecStalk y, f' = pullback.fst c f, and
F' = (tensorPullback (pullback.snd c f)).obj F. Represent r by a structure-sheaf
section a on a neighborhood V of y. The inverse image c^{-1}V is the entire
local spectrum. The germ/stalk-map square for c, followed by the canonical
closed-point ring isomorphism, identifies c.app V a with Gamma-Spec.inv r,
after transporting the inverse-image open to top. Thus multiplication by r
on the source cohomology is multiplication by f'.appTop (Gamma-Spec.inv r)
on the global section complex of the fixed injective resolution of F'.
The resolution-to-derived isomorphism is a morphism of global-section modules.
The forgetful homology comparison and the identity of the two section complexes
respect the indicated scalar actions as follows. For a fixed base section t,
multiplication by its pullback is a chain endomorphism, since every differential
is linear. Naturality of each mapHomologyIso with respect to this endomorphism
identifies the induced map on homology with multiplication by t. This applies
both to forgetting module scalars and to evaluating presheaf modules on top;
the identity of the section complexes intertwines the same endomorphisms. Evaluation of presheaf
homology is linear over the ring of sections on top. The sheafification comparison
and its adjoint theta are morphisms of presheaves of modules, hence their component
on top is linear. The higher-direct-image resolution comparison is a morphism of
module sheaves and therefore linear on sections. Finally restrict its top section
to V. The inverse image is still top, and the restriction is the identity under
this identification. The module germ identity sends a times this section to
r times its germ. Composing these identities proves the displayed equation for
the actual localDirectImage_stalk_class construction, not an arbitrarily chosen
comparison. The argument works in degree zero, for the zero module, and for an
empty local base change, since it uses only linear maps and their induced homology.
-/
theorem localDirectImage_stalk_class_smul {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (F : X.Modules) (p : ℕ) (r : Y.presheaf.stalk y)
    (x : (RingedSpace.moduleCohomology (pullback (Y.fromSpecStalk y) f).toRingedSpace p ⋙
      ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫
          (pullback.fst (Y.fromSpecStalk y) f).appTop).hom).obj
      ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)) :
    localDirectImage_stalk_class f y F p (r • x) =
      r • localDirectImage_stalk_class f y F p x := by sorry

end AlgebraicGeometry
