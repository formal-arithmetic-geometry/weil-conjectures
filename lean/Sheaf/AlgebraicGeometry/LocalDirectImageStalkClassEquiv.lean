/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.LocalDirectImageStalkClassMap
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.AlgebraicGeometry.SpecLocalRingCanonicalMorphism

/-! # Local direct-image stalks and total cohomology

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

/-- The canonical class map is an A-linear equivalence.
Source: Stacks Project, Tag 02OD, the local-stalk/global-cohomology identification;
Tag 01E4, the cocycle-to-cohomology-sheaf comparison.
(blueprint: lem-weil-pbc-local-direct-image-stalk-cohomology-equiv)

Proof: Set A = O_{Y,y}, c : Spec A → Y, f' : X' → Spec A, F' = g'^*F.
For every neighborhood V of y, c^{-1}V is top. Thus taking the germ identifies
Gamma(Spec A,N) with (c_*N)_y. Every open of Spec A containing its closed point
is top, so Gamma(Spec A,-) is closed-point stalk evaluation and is exact.
Apply this evaluation to f'_*K for the specified injective resolution K of F'.
It commutes with homology. The sectionCohomologyTheta map on top is precisely
this homology comparison: sheafification induces an isomorphism at the closed
point, and the counit on the already sheaf-valued complex is an isomorphism.
The termwise identity Gamma(Spec A,f'_*K) = Gamma(X',K), together with the
right-derived resolution comparisons in localDirectImage_stalk_class, proves
that this particular additive map is bijective. To check A-linearity, represent
a scalar by a structure-sheaf germ on V; its action on the class map is the action
on Gamma(X',K) via Gamma-Spec followed by f'.appTop, because c^{-1}V is top and
the structure-sheaf germ square commutes. All resolution and homology maps are
linear for that action. Equip this same bijective map with its linear structure.
The equation in the conclusion determines e pointwise, hence uniquely. -/
theorem localDirectImage_stalk_cohomology_equiv {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (F : X.Modules) (p : ℕ) :
    ∃ e : (RingedSpace.moduleCohomology (pullback (Y.fromSpecStalk y) f).toRingedSpace p ⋙
        ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫
            (pullback.fst (Y.fromSpecStalk y) f).appTop).hom).obj
        ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)
      ≃ₗ[Y.presheaf.stalk y]
      (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
      ((Scheme.Modules.pushforward (Y.fromSpecStalk y)).obj
        (((Scheme.Modules.pushforward (pullback.fst (Y.fromSpecStalk y) f)).rightDerived
          p).obj
          ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))),
      ∀ x, e x = localDirectImage_stalk_class f y F p x := by sorry

end AlgebraicGeometry
