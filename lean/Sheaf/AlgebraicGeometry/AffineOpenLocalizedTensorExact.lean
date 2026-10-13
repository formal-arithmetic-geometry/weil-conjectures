/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.AffineTorAmplitudeCriterion
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.Algebra.Homology.BoundedFlatKFlat

/-! # Tensor exactness on principal opens

Source: Stacks Project, Tags 08E9 and 09U8.
(blueprint: lem-sc-affine-open-localized-tensor-exact).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wU

open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory

namespace AlgebraicGeometry

/-- Tensoring the localized finite-free complex with any module is exact below
its lower Tor-amplitude bound on an open subscheme.
Source: Stacks Project, Tag 09U8 (pullback preserves Tor amplitude) and Tag 08E9
(the affine Tor-amplitude criterion).
(blueprint: lem-sc-affine-open-localized-tensor-exact).

Proof. Fix D(f) contained in U. Its inclusion is an open immersion, hence its
pullback is exact and agrees with derived pullback. For a sheaf H on D(f),
its ordinary direct image j_*H on U restricts back to H: on every open V in
D(f), (j_*H)(V) = H(V). Apply the hypothesis with G = j_*H and restrict
the vanishing cohomology. The derived tensor/open-restriction comparison
identifies this restriction with the tensor of the restricted object and H.
Thus every sheaf on D(f) is tested, giving the restriction case of Tag 09U8.
The restriction of the termwise associated-sheaf complex is the tilde
complex of the localization of P. Apply the affine Tor-amplitude criterion,
widening the upper bound to max(a,b). Localization preserves boundedness above
and free terms. Thus the localized complex is K-flat and computes its derived
tensor by ordinary termwise tensor. Cohomology vanishes in each degree i < a,
which is precisely ExactAt i of the termwise tensor complex. The Shrink used by
ModuleCat.localizedModuleFunctor is canonically linearly equivalent to ordinary
localization and does not change exactness. -/
theorem affine_open_localized_tensor_exact
    (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
    (hfree : ∀ i : ℤ, Module.Free A (P.X i) ∧ Module.Finite A (P.X i))
    (U : (Spec (.of A)).Opens) (hU : IsCompact (U : Set (Spec (.of A))))
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{wU}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (a b : ℤ)
    (hamp : ∀ G : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i →
        schemeDerivedTensorCohomologyVanishes U.toScheme
          ((@Functor.mapDerivedCategory
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) _ _ _
            (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) _ _ _
            ((SheafOfModules.overFunctor.{u}
                (moduleRings (Spec (.of A)).toRingedSpace) U) ⋙
              Equivalence.functor
                (C := SheafOfModules.{u}
                  ((moduleRings (Spec (.of A)).toRingedSpace).over U))
                (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
                (Scheme.Modules.overEquiv U))
            (Functor.additive_of_preserves_binary_products _)
            (comp_preservesFiniteLimits _ _) (comp_preservesFiniteColimits _ _)).obj
            (DerivedCategory.Q.obj
              ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
                (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) _ _ _ _
                (tilde.functor (.of A)) ⟨fun _ _ ↦ tilde.map_zero⟩
                (ComplexShape.up ℤ)).obj P))) G i) :
    ∀ f : A, PrimeSpectrum.basicOpen f ≤ U →
      ∀ N : ModuleCat.{u} (Localization.Away f), ∀ i : ℤ, i < a →
        (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj
          (((ModuleCat.localizedModuleFunctor (Submonoid.powers f)).mapHomologicalComplex
            (.up ℤ)).obj P)).ExactAt i := by sorry

end AlgebraicGeometry
