/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.GaloisContinuity

/-!

# The projector onto the Galois invariants of nearby cycles

Let `N` be a model of `X` with special fibre `X'`, `h : N.generic ⟶ Spec L`, `Ω/L` a Galois
extension whose finite Galois subextensions have degrees invertible in a finite discrete
commutative ring `T₀`, and `Λ = C(-, T₀)`. For `C` with `Lε^* C` bounded below of étale origin,
the pullback exchange `α : Ψ_N C ⟶ Ψ_{N_Ω} C` of the projection from the Galois layer has a
retraction `r` whose idempotent `e = r ≫ α` is the projector onto *all* the `Gal(Ω/L)`-invariants,
in the following cohomological form: after pullback along any `f' : Z ⟶ X'`, every map out of
`Hᵠ(Lf'^* Ψ_{N_Ω} C)` which is invariant under a family of elements of `Gal(Ω/L)` restricting
onto every finite Galois group `Gal(L'/L)` is fixed by `Hᵠ(Lf'^* e)`
(`exists_retraction_pullbackExchange_galoisLayerHom_of_plusEtaleOrigin_projector`, in the
namespace `NearbyCyclesModel`).

The retraction is induced by the derived normalized trace of the Galois tower
(`AlgebraicGeometry.ProEtale.GaloisTower.derivedTrace`). By continuity
(`NearbyCyclesModel.nonempty_isColimit_homology_nearbyCycles_galoisTower`), the cohomology sheaf is
the colimit of those of the finite layers `L'`, on which `e` acts as the average of the actions of
`Gal(L'/L)` (`AlgebraicGeometry.ProEtale.GaloisTower.map_derivedTrace_comp_unit_comp`); the
averaging argument itself is the abstract `CategoryTheory.map_comp_eq_of_isColimit_mapCocone`.
-/

@[expose] public section

-- several lemmas do not need all the instances of the section variables
set_option linter.unusedSectionVars false

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.GaloisTower

open Scheme CondensedRing

variable {X Yinf : Scheme.{u}} {ginf : Yinf ⟶ X} [WeaklyEtale ginf] (T : GaloisTower ginf)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (hd : ∀ (j : T.J)
    (N : CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      IsIso (Fintype.card (T.Γ j) • 𝟙 N))

variable (K : CochainComplex
    (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)

variable (hc : ∀ n, IsColimit (T.moduleCocone Λ (K.X n))) (a : ℤ) [K.IsStrictlyGE a]
  (hK : ∀ n, ((ginf)_*⟦Λ⟧).rightAcyclic (((ginf)^*⟦Λ⟧).obj (K.X n)))
  (C : DerivedCategory
    (CategoryTheory.Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
  (e : DerivedCategory.Q.obj K ≅ C)

end AlgebraicGeometry.ProEtale.GaloisTower

namespace AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' : Scheme.{u}} (N : NearbyCyclesModel X X') {L : Type u} [Field L]
  (h : N.generic ⟶ Spec (.of L)) (Ω : Type u) [Field Ω] [Algebra L Ω]

variable (T₀ : Type) [TopologicalSpace T₀] [CommRing T₀] [IsTopologicalRing T₀]
  [DiscreteTopology T₀] [Finite T₀] [IsGalois L Ω]

end AlgebraicGeometry.ProEtale.CondensedRing.NearbyCyclesModel
