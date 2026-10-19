/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.BoundedConstructibleLocalizingClosure
public import Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Sheaf.AlgebraicGeometry.EllAdicIndConstructibleHeartClosure
import Sheaf.AlgebraicGeometry.EllAdicProperUpperAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts

/-! # Uniform upper bound for the discarded lower tail

Source: blueprint `sk-lem-proper-unbounded-window` and
`det-prop-int-compactness-direct-sums` (1)-(2).
(blueprint: lem-sfb-adic-proper-truncation-bound)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

include ℓ k hΛ

/-- The direct image of a sufficiently low lower tail has no cohomology in
degree `q` or above, uniformly on the bounded constructible localizing hull.

Source: blueprint `sk-lem-proper-unbounded-window` (arbitrary-complex clause)
and `det-prop-int-compactness-direct-sums` (1)-(2).
(blueprint: lem-sfb-adic-proper-truncation-bound)

Proof: the ind-constructible heart is a weak Serre class closed under ambient
coproducts. Homology preserves these coproducts, so the complexes with
ind-constructible cohomology form a replete triangulated localizing class.
This class contains every bounded constructible complex, hence contains the
bounded constructible localizing hull by its universal property.

Choose a uniform bound c on proper images of ind-constructible heart objects.
The rational cases use proper finiteness, the comparison with finite constant
models, and continuous coefficient transport. The integral case uses the
proper bound for torsion reductions and its Milnor sequence; bounded-below
filtered continuity extends the constructible bound to the ind heart.
Finite truncation triangles give the upper bound b+c for the image of a
bounded complex supported in degrees at most b. Exact countable products
reconstruct an arbitrary complex from its canonical lower truncations.
Proper direct image preserves their product, and homology in the target
commutes with this product. The image Postnikov triangle therefore gives
the upper bound b+c+1, allowing one additional degree without needing
stabilization of the output tower. The upper-amplitude theorem absorbs
this extra degree into its existential natural constant.

Good truncation preserves ind-constructible cohomology. Apply that theorem
to the lower tail tau_lt(q-c) K, supported in degrees at most q-c-1.
Its image is supported in degrees at most q-1 by integer arithmetic.
The constant is independent of K and q; zero complexes and empty fibres
satisfy the same argument.
-/
theorem ellAdic_proper_lowerTail_bound :
    ∃ c : ℕ, ∀ (q : ℤ)
      (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
        (condensedRingObj Λ Z.left))),
      boundedConstructibleLocalizingClosure Λ Z.left K →
      ((R((g.left)_*⟦Λ⟧)).obj
        ((DerivedCategory.TStructure.t.truncLT (q - (c : ℤ))).obj K)).IsLE (q - 1) := by
  let A := Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
    (condensedRingObj Λ Z.left)
  let P : ObjectProperty A := ObjectProperty.ind.{u + 1}
    (IsConstructibleModuleObject (condensedRingObj Λ Z.left))
  obtain ⟨hzero, hker, hcoker, hext, hcoprod⟩ :=
    ellAdic_indConstructible_heart_closure Λ ℓ Z hΛ
  have : P.ContainsZero := hzero
  have : P.IsClosedUnderKernels := hker
  have : P.IsClosedUnderCokernels := hcoker
  have : P.IsClosedUnderExtensions := hext
  have : ∀ I : Type (u + 1), P.IsClosedUnderColimitsOfShape (Discrete I) := hcoprod
  have : HasColimitsOfSize.{u + 1, u + 1} A := IsGrothendieckAbelian.hasColimits A
  have : HasCoproducts.{u + 1} A := fun I ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete I)
  have hderived (I : Type (u + 1)) :
      (DerivedCategory.homologyProperty P).IsClosedUnderColimitsOfShape (Discrete I) := by
    constructor
    intro K hK n
    obtain ⟨c⟩ := hK
    exact P.prop_of_isColimit
      (isColimitOfPreserves (DerivedCategory.homologyFunctor A n) c.isColimit)
      (fun j ↦ c.prop_diag_obj j n)
  have : ∀ I : Type (u + 1),
      (DerivedCategory.homologyProperty P).IsClosedUnderColimitsOfShape (Discrete I) :=
    hderived
  have hhull : boundedConstructibleLocalizingClosure Λ Z.left ≤
      DerivedCategory.homologyProperty P := by
    apply boundedConstructibleLocalizingClosure_le
    intro K hK n
    exact ObjectProperty.le_ind _ _ (hK.2 n)
  obtain ⟨c, hamp⟩ := ellAdic_proper_pushforward_isLE_of_isLE Λ ℓ g hΛ
  refine ⟨c, ?_⟩
  intro q K hK
  let a := q - (c : ℤ)
  have htr : DerivedCategory.homologyProperty P
      ((DerivedCategory.TStructure.t.truncLT a).obj K) := by
    have hle := DerivedCategory.homologyProperty_truncLE (hhull K hK) (a - 1)
    exact (DerivedCategory.homologyProperty P).prop_of_iso
      ((DerivedCategory.TStructure.t.truncLEIsoTruncLT (a - 1) a (by omega)).app K) hle
  have hLE : ((DerivedCategory.TStructure.t.truncLT a).obj K).IsLE
      (a - 1) := inferInstance
  have h := hamp (a - 1) ((DerivedCategory.TStructure.t.truncLT a).obj K) htr hLE
  have heq : a - 1 + (c : ℤ) = q - 1 := by dsimp [a]; omega
  rwa [heq] at h

end AlgebraicGeometry.ProEtale.CondensedRing
