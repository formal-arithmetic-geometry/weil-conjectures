/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.MoebiusDecomposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.GaloisTraceInfinite.TowerDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.CoproductRetract

/-!
# Invariant retractions of the derived unit of a Galois tower are unique

Let `T` be a Galois tower over `X` (`AlgebraicGeometry.ProEtale.GaloisTower`) and `K` a bounded
below complex of `Λ_X`-module objects such that, at every term, `g_{∞*} g_∞^* Kⁿ` is the colimit
of the finite levels and `g_∞^* Kⁿ` is `g_{∞*}`-acyclic. Given a Möbius decomposition `D` of
`M∞ = g_{∞*} g_∞^* K` (`AlgebraicGeometry.ProEtale.GaloisTower.MoebiusDecomposition`), two
retractions `R, R'` of the derived unit `K ⟶ Rg_{∞*} Lg_∞^* K` which are invariant under the
derived unit transports along the automorphisms `D.σ i a` are equal
(`AlgebraicGeometry.ProEtale.GaloisTower.MoebiusDecomposition.eq_of_retraction_derivedUnit`,
and `..._of_iso` for an object of the derived category isomorphic to `K`): there are no phantom
invariant maps.

## Proof

Through `CategoryTheory.Adjunction.derivedUnitIso : M∞ ≅ Rg_{∞*} Lg_∞^* K`, the difference
`R - R'` becomes a morphism `δ : Q(M∞) ⟶ Q(K)` killed by the unit `u : K ⟶ M∞` and invariant
under the actions of the `D.σ i a`. We write `M∞` as a retract of the coproduct `∐ᵢ M∞`
(`GaloisTower.MoebiusDecomposition.sigmaSection_comp_sigmaRetraction`): the section has
components `|Aᵢ|⁻¹ eᵢ` (resp. `e_{i₀}`), defined termwise on the colimit of the finite levels
where they form finite sums, and the retraction has components
`cᵢ = |Aᵢ| - ∑ₐ σ i a` (resp. `τ ≫ u`). Each `Q(cᵢ) ≫ δ` vanishes, hence so does `δ`, since
`Q` sends coproducts of complexes to coproducts
(`DerivedCategory.eq_zero_of_Q_map_inj_comp_comp_eq_zero`).
-/

@[expose] public section

-- several declarations do not need all the instances of the section variables
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.GaloisTower

open Scheme CondensedRing

variable {X Yinf : Scheme.{u}} {ginf : Yinf ⟶ X} [WeaklyEtale ginf] {T : GaloisTower ginf}
  {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  {hd : ∀ (j : T.J)
    (N : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      IsIso (Fintype.card (T.Γ j) • 𝟙 N)}
  {K : CochainComplex
    (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ}
  {hc : ∀ n, IsColimit (T.moduleCocone Λ (K.X n))}

-- the complex `M∞ = g_{∞*} g_∞^* K`
set_option quotPrecheck false in
local notation "M∞" => (((ginf)^*⟦Λ⟧ ⋙ (ginf)_*⟦Λ⟧).mapHomologicalComplex _).obj K

namespace MoebiusDecomposition

variable (D : T.MoebiusDecomposition Λ hd K hc)

/-! ### Locally finite sums -/

section LocallyFinite

variable {n : ℤ} {Z : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
  (condensedRingObj Λ X)} (g : D.ι → ((infFunctor Λ ginf).obj (K.X n) ⟶ Z))

end LocallyFinite

/-! ### `M∞` as a retract of a coproduct -/

/-! ### The retraction, for an abstract family of actions

To keep the terms small, the actions of the `σ i a` on `M∞` are an arbitrary family `act` of
endomorphisms which are termwise `GaloisTower.infAction`; it is specialized to the unit transports
only at the end. -/

section Action

end Action

/-! ### Uniqueness of invariant retractions -/

section Derived

variable (a : ℤ) [K.IsStrictlyGE a]
  (hK : ∀ n, ((ginf)_*⟦Λ⟧).rightAcyclic (((ginf)^*⟦Λ⟧).obj (K.X n)))
  {R : R((ginf)_*⟦Λ⟧).obj (L((ginf)^*⟦Λ⟧).obj (DerivedCategory.Q.obj K)) ⟶
    DerivedCategory.Q.obj K}

end Derived

end MoebiusDecomposition

end AlgebraicGeometry.ProEtale.GaloisTower
