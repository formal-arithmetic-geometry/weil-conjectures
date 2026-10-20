/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses

/-! The canonical comparison underlying the pro-etale stratum internal-Hom map. -/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The evaluation-mate comparison for the pro-etale locally closed immersion.

Proof: the ten-step proof of `lem-weil-stratum-ambient-hom`, steps 8--10
(blueprint: lem-weil-stratum-ambient-hom).  Choose K-flat representatives in
both tensor variables and K-injective representatives in the internal-Hom
variable.  The Hom-complex currying map, followed by the open and closed
projection comparisons and the two derived adjunctions, gives a map between
the displayed bifunctors.  The same chain calculation with the inverse
projection comparisons gives a two-sided inverse on every component.  The
construction is natural in the two variables because every comparison used
is natural.  This theorem records the canonical comparison before its final
`NatIso.ofComponents` packaging, and is therefore a strict sub-result of the
ambient internal-Hom assertion.
(blueprint: lem-weil-stratum-ambient-hom-comparison) -/
theorem stratumAmbientHomComparison
    (A : Type u) [CommRing A] [Finite A]
    {S U X : Scheme.{u}} [IsNoetherian X]
    (i : S ⟶ U) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] :
    ∃ α :
      ((((sfConstantModuleDirectImage i A).rightDerivedFunctor ⋙
          (sfIntrinsicExtensionByZero j A).mapDerivedCategory).op.prod
          (𝟭 (proEtaleDerivedCategory X A))) ⋙
          derivedInternalHomOfUniverses.{u + 1, u, u}
            (ProEt.topology X) (proEtaleConstantRing X A)) ⟶
        (((𝟭 (proEtaleDerivedCategory S A)ᵒᵖ).prod
          ((sfConstantModulePullback j A).mapDerivedCategory ⋙
            (sfIntrinsicClosedUpperShriek i
              (Scheme.Opens.ι (X := U) (⟨(Set.range i)ᶜ,
                (IsClosedImmersion.isClosedEmbedding i).isClosed_range.isOpen_compl⟩ :
                  U.Opens)) A).rightDerivedFunctor)) ⋙
          derivedInternalHomOfUniverses.{u + 1, u, u}
            (ProEt.topology S) (proEtaleConstantRing S A) ⋙
            (sfConstantModuleDirectImage (i ≫ j) A).rightDerivedFunctor),
      ∀ p, IsIso (α.app p) := by
  sorry

end AlgebraicGeometry.ProEtale
