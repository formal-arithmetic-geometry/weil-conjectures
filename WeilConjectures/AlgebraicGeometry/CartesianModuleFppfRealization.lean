/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StackQuasiCoherentAlgebra
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.SchemeBigFppfQuasicoherentEquivalence

/-! # Fppf realization of compatible scheme modules

Source: Stacks Project, stacks-sheaves.tex, Tags 06WK and 06WI
(blueprint: lem-sfb-cartesian-module-fppf-realization).

The section coordinates in the conclusion specify both the module operations and every
restriction map. Thus the realized sheaf is the prescribed section presheaf, expressed by
additive equivalences to avoid definitional identifications across coefficient universes.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory Opposite AlgebraicGeometry

namespace CategoryTheory

/-- Compatible quasi-coherent modules on the scheme objects realize as a quasi-coherent
module sheaf, with exactly the specified pullback-of-sections restrictions.
Source: Stacks Project, stacks-sheaves.tex, Tags 06WK and 06WI
(blueprint: lem-sfb-cartesian-module-fppf-realization).

Proof: (1) The tensor-pullback unit sends s to 1 tensor s. Applying theta gives additive,
semilinear restriction maps; the identity and cocycle hypotheses give presheaf laws
(def-pc-module-pullback, def-sfb-stack-quasi-coherent-algebra).
(2) For each x, the functor C/x to Sch/p(x) is essentially surjective by cartesian lifts,
and fully faithful by their unique factorization property
(def-sfb-stable-pointed-moduli-groupoids). It preserves the fppf covers and structure rings.
(3) On this slice compare the section presheaf with the associated big-fppf sheaf of M x
using lem-sfb-scheme-big-fppf-quasicoherent-equivalence. At a:y to x the comparison is
Gamma(theta a). For every section of a^*(M x), its naturality is the naturality of tensor
section pullback followed by the cocycle equation; this includes sections not pulled back
from global sections on p(x). These comparisons are linear and include the identity case.
(4) Matching families on a cover of x are matching families on C/x, so the slice comparison
gives unique amalgamation and proves the sheaf condition on C.
(5) Transport the local free presentations of the associated scheme sheaves through the
ringed slice equivalence. These are precisely the local presentations required by
SheafOfModules.IsQuasicoherent (def-trf-space-quasi-coherent-module). No algebraicity,
representability, flatness of arbitrary arrows, or finiteness assumption is used. -/
theorem cartesian_module_fppf_realization {S : Scheme.{u}}
    (C : BasedCategory.{v, w} (Over S)) (hC : IsFibredInGroupoids C)
    (M : ∀ x : C.obj, ((moduliSchemeForget C).obj x).Modules)
    (hM : ∀ x : C.obj, SheafOfModules.IsQuasicoherent (M x))
    (theta : ∀ {y x : C.obj} (a : y ⟶ x),
      (Scheme.Modules.tensorPullback ((moduliSchemeForget C).map a)).obj (M x) ≅ M y)
    (theta_id : ∀ x : C.obj,
      (theta (𝟙 x)).hom =
        eqToHom (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj (M x))
          ((moduliSchemeForget C).map_id x)) ≫
        (Scheme.Modules.tensorPullbackSectionId ((moduliSchemeForget C).obj x)).hom.app
          (M x))
    (theta_comp : ∀ {z y x : C.obj} (b : z ⟶ y) (a : y ⟶ x),
      (theta (b ≫ a)).hom =
        eqToHom (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj (M x))
          ((moduliSchemeForget C).map_comp b a)) ≫
        (Scheme.Modules.tensorPullbackSectionComp ((moduliSchemeForget C).map b)
          ((moduliSchemeForget C).map a)).hom.app (M x) ≫
        (Scheme.Modules.tensorPullback ((moduliSchemeForget C).map b)).map (theta a).hom ≫
        (theta b).hom) :
    ∃ G : SheafOfModules.{max (u + 1) v w} (moduliModuleRings C hC),
      ∃ e : ∀ x : C.obj, G.val.obj (op x) ≃+ Γ(M x, ⊤),
        SheafOfModules.IsQuasicoherent G ∧
        (∀ (x : C.obj) (r : (moduliModuleRings C hC).obj.obj (op x))
          (s : G.val.obj (op x)), e x (r • s) =
            (eqToHom (Scheme.Γ_obj_op ((moduliSchemeForget C).obj x)) r.down) • e x s) ∧
        (∀ {y x : C.obj} (a : y ⟶ x) (s : G.val.obj (op x)),
          e y (G.val.map a.op s) =
            (theta a).hom.app ⊤
              (((Scheme.Modules.tensorPullback ((moduliSchemeForget C).map a)).obj
                  (M x)).presheaf.map
                (homOfLE ((moduliSchemeForget C).map a).preimage_top.ge).op
                (((Scheme.Modules.tensorPullbackSectionAdjunction
                  ((moduliSchemeForget C).map a)).unit.app (M x)).app ⊤ (e x s)))) := by
  sorry

end CategoryTheory
