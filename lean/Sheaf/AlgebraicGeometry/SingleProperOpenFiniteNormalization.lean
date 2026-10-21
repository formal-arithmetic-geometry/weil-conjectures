/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.SingleProperOpenArrows
public import Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport
public import Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence

/-!
# Finite etale normalization of the single-level intrinsic mate

Source: Stacks Project, Tags 0F7B, 09AF, 099R and 03DA.
(blueprint: lem-cbc-single-proper-open-finite-normalization)
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- The source comparison for finite etale coefficients, before specifying an origin.
Source: Stacks Tags 09AF and 099R
(blueprint: lem-cbc-single-proper-open-finite-normalization). -/
noncomputable def singleFiniteSource {V S T : Scheme.{u}} (r : V ⟶ S) (i : S ⟶ T)
    [IsProper r] [IsOpenImmersion i] (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ)
    (L : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (HD B T Λ φ).obj
        (((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus).obj
          ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r).obj L)) ≅
      (moduleJ B i).mapDerivedCategory.obj
        ((moduleDirectImage B r).rightDerivedFunctor.obj ((HD B V Λ φ).obj L)) :=
  (hJ B i Λ φ).app _ ≪≫
    (moduleJ B i).mapDerivedCategory.mapIso
      ((@asIso _ _ _ _ (hR B r Λ φ) (hR_isIso B r Λ φ)).app L)

/-- The target comparison for finite etale coefficients, before specifying an origin.
Source: Stacks Tags 09AF and 099R
(blueprint: lem-cbc-single-proper-open-finite-normalization). -/
noncomputable def singleFiniteTarget {V W T : Scheme.{u}} (k : V ⟶ W) (p : W ⟶ T)
    [IsOpenImmersion k] [IsProper p] (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ)
    (L : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (HD B T Λ φ).obj
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p).obj
          (((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus).obj
            L)) ≅
      (moduleDirectImage B p).rightDerivedFunctor.obj
        ((moduleJ B k).mapDerivedCategory.obj ((HD B V Λ φ).obj L)) :=
  (@asIso _ _ _ _ (hR B p Λ φ) (hR_isIso B p Λ φ)).app _ ≪≫
    (moduleDirectImage B p).rightDerivedFunctor.mapIso ((hJ B k Λ φ).app L)

/-- The intrinsic single-level mate is the specified finite etale interchange.
Source: Stacks Tags 0F7B, 09AF, 099R and 03DA
(blueprint: lem-cbc-single-proper-open-finite-normalization).
Proof: on the etale site, the support-composition isomorphism is the ordinary
proper mate of the clopen alpha. To check this, restrict along the lower open:
open base change identifies the source with direct image from the clopen lift.
Both transposes retain the same component section and vanish on its complement.
The open-adjunction Hom bijection is injective, so the two ordinary maps agree.
For a bounded-below etale complex choose a K-injective representative. Direct
image preserves K-injectives because inverse image is exact. The derived mate
is represented by this ordinary support map followed by the chosen resolution
of the open extension. The derived-unit normalization in
`properOpenInterchangeCoherence` specifies precisely that map, including its
refinement case. Site comparison carries the clopen projector to the same
identity/zero projector; its proper direct-image comparison satisfies the
specified counit mate equation. Restriction of coefficient scalars preserves
sections and these projectors and uses the same counit-normalized comparison.
Apply coefficient/exchange mate pasting to these two alpha squares. The two
proper adjunction triangle identities cancel the inserted unit-counit pairs,
leaving the displayed source and target comparisons. Properness supplies the
qcqs hypotheses needed by hR. This argument uses no assertion that scalar
restriction preserves K-injectives and no faithfulness on derived morphisms. -/
theorem singleGamma_finite_normalization {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    [TopologicalSpace Λ] [DiscreteTopology Λ] (φ : B →+* Λ)
    (L : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (singleFiniteSource B r i Λ φ L).hom ≫
        (singleGamma B k r p i h).app ((HD B V Λ φ).obj L) =
      (HD B T Λ φ).map
          (((Etale.properOpenInterchangeCoherence Λ).choose_spec.choose k i r p h).hom.app L) ≫
        (singleFiniteTarget B k p Λ φ L).hom := by
  sorry

end AlgebraicGeometry.ProEtale.StrictTower
