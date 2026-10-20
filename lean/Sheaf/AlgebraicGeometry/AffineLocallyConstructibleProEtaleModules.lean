/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q129
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.Paper.ProEtaleLocallyConstantSheaf

/-!
# Affine-local constructibility for discrete pro-etale coefficients

Source: Stacks Project, proetale.tex, Tag 09AJ, definition-constructible
(blueprint: def-sfb-affine-locally-constructible-proetale-modules).
- a finite constructible locally closed partition on each affine open;
- intrinsic module inverse image to its strata;
- local constant module models of finite presentation, equivalently finite type
  over the Noetherian coefficient ring.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Affine-local constructibility over a discrete Noetherian coefficient ring. The finite
partition is in the affine open, and local models are isomorphisms of module sheaves on
localized sites. All site objects are tested, so no chosen points or slice identification
for a closed stratum is used. The module inverse image includes the canonical constant
coefficient map and tensor extension. `ULift` only places scalars in the module universe.
Source: Stacks Project, Tag 09AJ, definition-constructible, and Tag 00IK for the equivalence
of finite generation and finite presentation over a Noetherian ring
(blueprint: def-sfb-affine-locally-constructible-proetale-modules). -/
def IsAffineLocallyConstructibleProEtaleModuleSheaf
    (X : Scheme.{u}) (R : Type u) [CommRing R] [IsNoetherianRing R]
    (F : proEtaleRingModules X (proEtaleConstantRing X R)) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U →
    ∃ S : Stratification U.toScheme,
      (∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) ∧
      ∀ (a : Fin S.n) (V : (S.domain a).ProEt),
        ∃ T : Sieve V, T ∈ ProEt.topology (S.domain a) V ∧
          ∀ (W : (S.domain a).ProEt) (f : W ⟶ V), T f →
            ∃ M : ModuleCat.{u + 1} (ULift.{u + 1, u} R),
              Module.FinitePresentation (ULift.{u + 1, u} R) M ∧
                Nonempty
                  ((proEtaleConstantModulePullback (S.immersion a ≫ U.ι) R F).over W ≅
                    proEtaleConstantModuleSheafOver (S.domain a) R W M)

end AlgebraicGeometry.Scheme
