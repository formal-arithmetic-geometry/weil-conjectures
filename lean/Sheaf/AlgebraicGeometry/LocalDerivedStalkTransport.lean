/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Stalk
public import Sheaf.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs

/-! # Transport of an arbitrary sheaf comparison to local total cohomology

Source: Stacks Project, Tags 02OD, 01E4, 01J7 and 0098.
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

/-- An arbitrary isomorphism beta from the local pullback of G to the local higher
 direct image transports the stalk of G to total cohomology. If its adjoint sends
 a section s to the canonical class of xi, the transported germ restricts to xi.
Source: Stacks Project, Tag 02OD, the local-stalk and global-cohomology identifications;
Tags 01J7 and 0098 for the pullback-unit germ formula, and Tag 01E4 for section classes.
(blueprint: lem-weil-pbc-local-derived-stalk-transport)

Proof: Set A = O_y, c : Spec A → Y, and let z be the closed point. The unit on module
stalks gives G_y ≅ (c^*G)_z because c induces an isomorphism on local rings at z.
Apply the stalk functor to beta to identify this with (R^p f'_*F')_z. Every open of
Spec A containing z is the whole spectrum: every prime specializes to z. Hence
closed-point stalks equal global sections, and evaluation on Spec A is exact.
Apply this exact evaluation to the direct-image complex of a resolution K of F'.
Homology commutes with evaluation and global sections of f'_*K are those of K.
The resolution comparisons give Gamma(Spec A,R^p f'_*F') ≅ H^p(X',F'). Normalize
scalars by Gamma-Spec and f'.appTop. Since c is the identity on the normalized closed
stalk ring, the resulting composite is A-linear.
For V containing y, c^{-1}V is the whole local spectrum, and the fibre-product square
identifies W = g'^{-1}(f^{-1}V) with f'^{-1}(c^{-1}V), hence with X'. The germ formula
for the pullback unit and naturality of the stalk map of beta send the germ of s to
the closed-point germ of its adjoint's value on V. If that value is D.targetClass xi,
exact evaluation inverts this section-class map: expand resolutionSectionClass and
cancel its evaluation-homology, sheafification, and resolution comparisons. Restricting
the resulting total class to W gives xi. Resolution comparison lifts are homotopic,
so the formula holds for all I, K and D. No claim about what beta does to source
cohomology classes is assumed here; that is supplied separately by base change.
No properness, coherence or Noetherian hypothesis is used. This works in degree zero,
for zero modules and for empty local base change. The germ formula determines the
transport uniquely, so no arbitrary mathematical data are introduced. -/
theorem localDerived_stalk_transport {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (F : X.Modules) (p : ℕ) (G : Y.Modules)
    (beta : (Scheme.Modules.tensorPullback (Y.fromSpecStalk y)).obj G ⟶
      ((Scheme.Modules.pushforward (pullback.fst (Y.fromSpecStalk y) f)).rightDerived p).obj
        ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))
    [IsIso beta] :
    ∃ e : (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj G ≃ₗ[Y.presheaf.stalk y]
      (RingedSpace.moduleCohomology (pullback (Y.fromSpecStalk y) f).toRingedSpace p ⋙
        ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫
            (pullback.fst (Y.fromSpecStalk y) f).appTop).hom).obj
        ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F),
      ∀ (I : InjectiveResolution F)
        (K : InjectiveResolution
          ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))
        (V : Y.Opens) (hy : y ∈ V)
        (D : Scheme.Modules.FlatBaseChangeOpenChoices f (Y.fromSpecStalk y) F I K V)
        (xi : (forget₂ _ AddCommGrpCat.{u}).obj
          ((RingedSpace.moduleCohomology
            ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).toScheme.toRingedSpace p).obj
            ((Scheme.Modules.restrictFunctor
              ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).obj
              ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))))
        (s : G.presheaf.obj (op V)),
        Scheme.Modules.Hom.app
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
            (Y.fromSpecStalk y))).homEquiv _ _ beta) V s = D.targetClass p xi →
        Scheme.Modules.moduleCohomologyFMap
          ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι
          ((Scheme.Modules.restrictAdjunction
            ((pullback.snd (Y.fromSpecStalk y) f) ⁻¹ᵁ (f ⁻¹ᵁ V)).ι).unit.app
              ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)) p
          (e.toLinearMap (TopCat.Presheaf.germ G.presheaf V y hy s)) = xi := by sorry

end AlgebraicGeometry
