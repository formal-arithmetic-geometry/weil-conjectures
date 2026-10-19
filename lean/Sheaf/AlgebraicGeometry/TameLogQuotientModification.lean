/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q111
-/
module

public import Sheaf.AlgebraicGeometry.LogRegularPair
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.CategoryTheory.Endomorphism
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.AlgebraicGeometry.FiniteOverProjective
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.AlgebraicGeometry.GabberEquivariantLogModification
import Sheaf.AlgebraicGeometry.ProjectiveFiniteGroupQuotient
import Sheaf.AlgebraicGeometry.VeryTameQuotientLogRegular

/-!
# A log regular modification of a tame quotient

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, VIII Theorem 1.1,
VI Theorem 3.2, and IX 2.3--2.4, printed pp. 85, 74, 134
(blueprint: lem-per-tame-log-quotient-modification).

The boundary is represented by the complement of a dense open. The finite quotient
is specified by its orbit topology and the canonical map onto invariant sections.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- A finite tame quotient of an integral excellent log regular pair has a proper
birational log regular modification containing the inverse image of the quotient boundary.
Source: ILO VIII Theorem 1.1, VI Theorem 3.2, IX 2.3--2.4
(blueprint: lem-per-tame-log-quotient-modification).

Proof:
1. Geometric stabilizer orders divide the invertible group order, so the action is tame.
Apply `lem-per-gabber-equivariant-log-modification` to obtain a projective equivariant
modification with a very tame action and log regular boundary. Intersect the translates
of its isomorphism locus and remove the original boundary and nonfree locus to obtain
an invariant dense open V; its inverse image remains dense.
2. Above each affine open of X, use `lem-fin-finite-over-projective` and
`lem-trf-h-projective-composition`, then `lem-per-projective-finite-group-quotient`,
to obtain the finite quotient with a projective map to that affine open.
3. Quotient restriction and categorical uniqueness give compatible identifications on
intersections. Apply `lem-weil-pbc-relative-glueing-affine-opens` to glue the quotients
and maps. Finiteness locally makes the modified action admissible.
4. `lem-kun-projective-implies-proper` and `lemma-nagata-projective-target-local`
make the descended map proper. The dense image of the irreducible isomorphism locus,
and local reducedness, give integrality. Finite type over excellent affine rings and
`lem-exc-finite-type-localization-excellent` give excellence and Noetherianness.
5. Set the new boundary to the image of the modified boundary. Apply
`lem-per-very-tame-quotient-log-regular`; its dense triviality locus makes that boundary
nowhere dense and closed.
6. The invariant open V is saturated. Its quotient is open and dense, and the equivariant
isomorphism above V descends to an isomorphism on dense opens, proving birationality.
7. If rho(m) belongs to pi(B), lift m to the modified cover. Equivariance and the orbit
fibres give that its image in C belongs to B, so the lift belongs to the modified
boundary and m to its quotient image. This proves the required boundary inclusion. -/
theorem exists_logRegular_modification_of_tame_quotient
    (C X : Scheme.{u}) [IsIntegral C] [IsNoetherian C] [C.IsSeparated]
    [IsIntegral X] [IsNoetherian X]
    (_hC : ∀ W : C.Opens, IsAffineOpen W → IsExcellent Γ(C, W))
    (_hX : ∀ W : X.Opens, IsAffineOpen W → IsExcellent Γ(X, W))
    (U : C.Opens) (hU : DenseRange U.ι)
    (_hlog : IsDivisorialFineSaturatedLogRegularPair C U.toScheme U.ι hU)
    (G : Type v) [Group G] [Finite G] (a : G →* Aut C)
    (_horder : ∀ x : C, IsUnit (Nat.card G : C.presheaf.stalk x))
    (_hboundary : ∀ (g : G) (x : C), (a g).hom x ∈ U ↔ x ∈ U)
    (_hfree : ∃ V : C.Opens, Dense (V : Set C) ∧
      (∀ (g : G) (x : C), (a g).hom x ∈ V ↔ x ∈ V) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (t : Spec (.of Ω) ⟶ C) (g : G),
        t default ∈ V → t ≫ (a g).hom = t → g = 1)
    (_hadmissible : ∀ x : C, ∃ W : C.Opens,
      IsAffineOpen W ∧ ∀ g : G, (a g).hom x ∈ W)
    (π : C ⟶ X) [IsFinite π] (hπ : ∀ g : G, (a g).hom ≫ π = π)
    (_hquot : Topology.IsQuotientMap π)
    (_horbits : ∀ x y : C, π x = π y ↔ ∃ g : G, (a g).hom x = y)
    (_hsheaf : ∀ W : X.Opens, Function.Injective (π.app W) ∧
      ∀ s : Γ(C, π ⁻¹ᵁ W),
        (∀ g : G, (a g).hom.app (π ⁻¹ᵁ W) s =
          C.presheaf.map
            (eqToHom (congrArg (fun f : C ⟶ X ↦ f ⁻¹ᵁ W) (hπ g))).op s) ↔
          ∃ t : Γ(X, W), π.app W t = s) :
    ∃ (M : Scheme.{u}) (_ : IsIntegral M) (hM : IsNoetherian M) (ρ : M ⟶ X),
      IsProper ρ ∧
      (∀ W : M.Opens, IsAffineOpen W → IsExcellent Γ(M, W)) ∧
      (∃ e : M.PartialIso X, e.source.ι ≫ ρ = e.iso.hom ≫ e.target.ι) ∧
      ∃ (UM : M.Opens) (hUM : DenseRange UM.ι),
        @IsDivisorialFineSaturatedLogRegularPair M UM.toScheme UM.ι inferInstance
          hM.toIsLocallyNoetherian hUM ∧
        ρ ⁻¹' (π '' ((U : Set C)ᶜ)) ⊆ (UM : Set M)ᶜ := by
  sorry

end AlgebraicGeometry
