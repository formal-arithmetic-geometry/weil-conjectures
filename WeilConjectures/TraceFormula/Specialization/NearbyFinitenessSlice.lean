/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.AffineSpaceSlice
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessCases
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSlice
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModel

/-!

# Deligne's induction for the finiteness of nearby cycles

Let `S = Spec k'⟦t⟧` with `k'` separably closed of characteristic `p ≠ ℓ`, and let `Ψ` be the
geometric nearby cycles of the standard model of `𝔸ⁿ⁺¹_S` (`NearbyCyclesModel.affineSpaceModel`).
Deligne proves that `Ψ` preserves bounded constructible complexes by induction on the relative
dimension (SGA 4½, [Th. finitude], proof of Thm. 3.2), using the coordinate generic slices
`hᵢ : 𝔸ⁿ_{K⟦t⟧} ⟶ 𝔸ⁿ⁺¹_S`, `K = k'(x)^alg` (`AlgebraicGeometry.affineSpaceSlice`), with
special fibres `hᵢ,ₛ : 𝔸ⁿ_K ⟶ 𝔸ⁿ⁺¹_{k'}` (`AlgebraicGeometry.affineSpaceSliceSpecial`), the
geometric generic fibres of the coordinate projections of the special fibre. The two steps are:

* **slices** (`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom`):
  the pullback exchange `α : Lhᵢ,ₛ^* Ψ B ⟶ Ψ_K (Lhᵢ^* B)` of the morphism of geometric models
  over the slice (`NearbyCyclesModel.affineSpaceSliceHom`) is a split monomorphism, so `Lhᵢ,ₛ^* Ψ B`
  is a retract of the nearby cycles over the trait `Spec K⟦t⟧`
  (`NearbyCyclesModel.nonempty_retract_upperStar_nearbyCycles_affineSpaceSlice`).
  The slice `Spec K⟦t⟧ ⟶ 𝔸¹_S` is (up to a purely inseparable extension of the residue field) the
  completion of the strict localization `S'` of `𝔸¹_S` at the generic point of
  its special fibre. The nearby cycles over `S` of the base change to `S'` are the invariants
  `(Ψ_{S'})^P` of the nearby cycles over `S'` under the kernel `P` of the surjection of inertia
  groups `I_{S'} ⟶ I_S`, a pro-`p` group (SGA 4½, [Th. finitude], Lemme 3.3), and the nearby
  cycles do not change under the extension of traits `S' ⟶ Spec K⟦t⟧` (loc. cit., 3.7). Since
  `P` is pro-`p` and `p ≠ ℓ`, the averaging over `P` splits the inclusion of the invariants.
* **criterion**
  (`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_lisse_of_slices`): if the
  restrictions `Lhᵢ,ₛ^* Ψ B` to all the coordinate slices are bounded constructible, then so is
  `Ψ B`. It is stated, and needed, only for the extensions by zero `v_! L` of lisse sheaves on
  the generic fibre to which the dévissage reduces, in the case not covered by the proper
  exchange (the support meets the special fibre and is not quasi-finite over `S`). The points of
  `𝔸ⁿ⁺¹_{k'}` outside the images of all the slices `hᵢ,ₛ` are the closed points; by Deligne's
  argument (loc. cit., proof of 3.2; see also the ind-holonomic analogue in D. Abe, *Around the
  nearby cycle functor for arithmetic 𝒟-modules*, §2) the cohomology sheaves of `Ψ B` are
  extensions of sums of skyscrapers at closed points by constructible sheaves, and the skyscraper
  parts are finite by the finiteness of
  `RΓ(ℙⁿ⁺¹_s, Ψ_{ℙⁿ⁺¹} j_! B) = RΓ(ℙⁿ⁺¹_η̄, j_! B)` (proper exchange and Deligne's finiteness
  over the field `η̄`).

Together with the trait case `n = 0`
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpaceModel_zero`), the dévissage to
lisse sheaves and the proper-exchange cases, they prove the finiteness theorem by induction on `n`
(`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_obj`).

## Unfinished

Both steps are `sorry`ed. No blueprint node states them (the blueprint has no node for the
finiteness of nearby cycles). The slice step needs the Galois action of the inertia group on the
nearby cycles, Hochschild–Serre for the pro-`p` kernel `P` and the invariance of nearby cycles
under extensions of strictly henselian traits, none of which exists for pro-étale
`ℚ̄_ℓ`-sheaves in the repository (the slice exchange
`NearbyCyclesModel.isIso_pullbackExchange_sliceHom_of_isPullback` only reduces the comparison
over `S` to base change of `Rj_*` along the slice). The criterion needs that the cohomology
sheaves of `Ψ B` are ind-constructible, which for torsion coefficients holds for every étale
sheaf, but has no analogue for pro-étale `ℚ̄_ℓ`-sheaves without passing through `𝒪_E`-lattices
and their reductions (Bhatt–Scholze, *The pro-étale topology for schemes*, §6.8).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k']

variable (k') in
/-- The coordinate generic slice `hᵢ : 𝔸ⁿ_{K⟦t⟧} ⟶ 𝔸ⁿ⁺¹_S` (`K = k'(x)^alg`,
`AlgebraicGeometry.affineSpaceSlice`) as a morphism of the total spaces of the standard models. -/
noncomputable def affineSpaceSliceTotal (n : ℕ) (i : Fin (n + 1)) :
    (affineSpaceModel (traitSliceField k') n).total ⟶ (affineSpaceModel k' (n + 1)).total :=
  affineSpaceSlice n i (traitSliceCoord k')

variable (k') in
/-- The coordinate generic slice of the special fibre `hᵢ,ₛ : 𝔸ⁿ_K ⟶ 𝔸ⁿ⁺¹_{k'}`
(`AlgebraicGeometry.affineSpaceSliceSpecial`) as a morphism of the special fibres of the standard
models. -/
noncomputable def affineSpaceSliceSpecialFibre (n : ℕ) (i : Fin (n + 1)) :
    (traitStdSpecialFibre (𝔸(ULift.{u} (Fin n); trait (traitSliceField k')) ↘
      trait (traitSliceField k'))).left ⟶
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k')).left :=
  affineSpaceSliceSpecial n i (traitSliceCoord k')

variable (k') in
/-- The coordinate generic slice of the geometric generic fibres
`𝔸ⁿ_{K⟦t⟧} ×_{Spec K⟦t⟧} Spec Ω_K ⟶ 𝔸ⁿ⁺¹_S ×_S Spec Ω`, induced by `hᵢ` and the map
`Spec Ω_K ⟶ Spec Ω` (`AlgebraicGeometry.traitGenericPointMap`) of the geometric generic points of
`Spec K⟦t⟧` and `S`, with fields `Ω_K = (Frac K⟦t⟧)^alg` and `Ω = (Frac k'⟦t⟧)^alg`. -/
noncomputable def affineSpaceSliceGeneric (n : ℕ) (i : Fin (n + 1)) :
    (affineSpaceModel (traitSliceField k') n).generic ⟶
      (affineSpaceModel k' (n + 1)).generic :=
  pullback.lift (pullback.fst _ _ ≫ affineSpaceSliceTotal k' n i)
    (pullback.snd _ _ ≫ traitGenericPointMap k' (traitSliceField k')) (by
      rw [Category.assoc, affineSpaceSliceTotal, affineSpaceSlice_over, pullback.condition_assoc,
        Category.assoc, traitGenericPoint_traitMap])

variable (k') in
/-- The **morphism of geometric models over the coordinate generic slice** `hᵢ`: from the standard
model of `𝔸ⁿ_{K⟦t⟧}` over `Spec K⟦t⟧` to the standard model of `𝔸ⁿ⁺¹_S` over `S`, with the slices
`hᵢ` of the total spaces, `hᵢ,ₛ` of the special fibres, and of the geometric generic fibres. -/
@[simps]
noncomputable def affineSpaceSliceHom (n : ℕ) (i : Fin (n + 1)) :
    (affineSpaceModel (traitSliceField k') n).geometric.Hom
      (affineSpaceModel k' (n + 1)).geometric (affineSpaceSliceTotal k' n i)
      (affineSpaceSliceSpecialFibre k' n i) where
  total := affineSpaceSliceTotal k' n i
  generic := affineSpaceSliceGeneric k' n i
  comm_j := pullback.lift_fst _ _ _
  comm_i := affineSpaceSliceSpecial_fst _ _ _
  comm_ε := pullback.lift_fst _ _ _

variable [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **Nearby cycles on the coordinate generic slices** (SGA 4½, [Th. finitude], Lemme 3.3 and
3.7): for a bounded constructible complex `B` on `𝔸ⁿ⁺¹_S` and a coordinate `i`, the pullback
exchange `α : Lhᵢ,ₛ^* Ψ B ⟶ Ψ_K (Lhᵢ^* B)` of the morphism of models over the slice
(`NearbyCyclesModel.affineSpaceSliceHom`) is a split monomorphism: it is the inclusion of the
invariants of `Ψ_K (Lhᵢ^* B)` under a pro-`p` group `P` (`p ≠ ℓ`), split by averaging over `P`.
See the module docstring; `sorry`ed. -/
theorem isSplitMono_pullbackExchange_app_affineSpaceSliceHom (n : ℕ) (i : Fin (n + 1))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (affineSpaceModel k' (n + 1)).total))}
    (hB : boundedConstructible _ B) :
    IsSplitMono (((affineSpaceSliceHom k' n i).pullbackExchange
      (Profinite.padicAlgClRingObj ℓ)).app B) :=
  sorry

/-- **Nearby cycles on the coordinate generic slices are retracts**: for a bounded constructible
complex `B` on `𝔸ⁿ⁺¹_S` and a coordinate `i`, the restriction `Lhᵢ,ₛ^* Ψ B` of its nearby cycles
to the geometric generic fibre `𝔸ⁿ_K` of the `i`-th coordinate projection of the special fibre is
a retract of the nearby cycles `Ψ_K (Lhᵢ^* B)` of its pullback to the slice `𝔸ⁿ_{K⟦t⟧}`, through
the pullback exchange
(`NearbyCyclesModel.isSplitMono_pullbackExchange_app_affineSpaceSliceHom`). -/
theorem nonempty_retract_upperStar_nearbyCycles_affineSpaceSlice (n : ℕ) (i : Fin (n + 1))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (affineSpaceModel k' (n + 1)).total))}
    (hB : boundedConstructible _ B) :
    Nonempty (Retract
      ((L((affineSpaceSliceSpecialFibre k' n i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
        (((affineSpaceModel k' (n + 1)).geometric.nearbyCycles
          (Profinite.padicAlgClRingObj ℓ)).obj B))
      (((affineSpaceModel (traitSliceField k') n).geometric.nearbyCycles
        (Profinite.padicAlgClRingObj ℓ)).obj
          ((L((affineSpaceSliceTotal k' n i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj B))) :=
  have := isSplitMono_pullbackExchange_app_affineSpaceSliceHom n i hB
  ⟨⟨_, retraction (((affineSpaceSliceHom k' n i).pullbackExchange
    (Profinite.padicAlgClRingObj ℓ)).app B), IsSplitMono.id _⟩⟩

/-- **Deligne's criterion on the coordinate slices, core case** (SGA 4½, [Th. finitude], proof of
Thm. 3.2): suppose that for every coordinate `i` and every bounded constructible complex `B` on
`𝔸ⁿ⁺¹_S`, the restriction `Lhᵢ,ₛ^* Ψ B` of the nearby cycles to the geometric generic fibre of the
`i`-th coordinate projection of the special fibre is bounded constructible. Then the nearby cycles
of the extension by zero `v_! L = Rc_* j_{W!} Rc'_* L` of a lisse sheaf `L` along a locally
closed immersion `v : E ⟶ 𝔸ⁿ⁺¹_S` into the generic fibre are bounded constructible, in the case
not covered by the proper exchange: the closed subscheme `D` meets the special fibre and no
closed subscheme of `D` containing `W` is quasi-finite over `S`. See the module docstring;
`sorry`ed. -/
theorem boundedConstructible_nearbyCycles_affineSpace_lisse_of_slices (n : ℕ)
    (h : ∀ (i : Fin (n + 1))
      (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (affineSpaceModel k' (n + 1)).total)
        Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (affineSpaceModel k' (n + 1)).total))),
      boundedConstructible _ B →
      boundedConstructible _
        ((L((affineSpaceSliceSpecialFibre k' n i)^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
          (((affineSpaceModel k' (n + 1)).geometric.nearbyCycles
            (Profinite.padicAlgClRingObj ℓ)).obj B)))
    (D : Scheme.{u}) (c : D ⟶ (affineSpaceModel k' (n + 1)).total) [IsClosedImmersion c]
    (hc : ¬ Disjoint (Set.range c.base) (Set.range (affineSpaceModel k' (n + 1)).i.base))
    (W : D.Opens)
    (hqf : ¬ ∃ (D' : Scheme.{u}) (ι : D' ⟶ D), IsClosedImmersion ι ∧
      (W : Set D) ⊆ Set.range ι.base ∧
      LocallyQuasiFinite (ι ≫ c ≫ (𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k')))
    (hW : (W : Set D) ⊆ c ⁻¹ᵁ affineSpaceGenericOpen k' (n + 1)) (E : Scheme.{u})
    (c' : E ⟶ W) [IsClosedImmersion c'] (hc' : Surjective c')
    (L : Mod (Sheaf (Scheme.ProEt.topology E) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) E))
    (hL : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) E) L) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
      (traitStdSpecialFibre (𝔸(ULift.{u} (Fin (n + 1)); trait k') ↘ trait k')).left)
      (((affineSpaceModel k' (n + 1)).geometric.nearbyCycles (Profinite.padicAlgClRingObj ℓ)).obj
        ((R((c)_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
          (D((W.ι)_!open⟦Profinite.padicAlgClRingObj ℓ⟧).obj
            ((R((c')_*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj
              ((DerivedCategory.singleFunctor _ 0).obj L))))) :=
  sorry

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
