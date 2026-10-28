/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyEmbedsInAffineSpace
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethBraided
public import WeilConjectures.SixFunctors.NearbyCycles.AutActionTrivial
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethAverage
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethEquivariant
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethRetract
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.PadicAlgClRational
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.Tactic.ExactModProofs
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethClosure
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSlice
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModelAut
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModelHom
public import WeilConjectures.TraceFormula.Specialization.TraitSliceInvariants

/-!

# Gabber's Künneth formula for nearby cycles: the generic-slicing step

Let `P` be the product over the strictly henselian trait `S = Spec k'⟦t⟧` of models `M`, `N` of
finite type, and let `b : 𝒳 ⟶ 𝔸¹_S` be a coordinate of the total space of `M`. Let
`σ : Spec K⟦t⟧ ⟶ 𝔸¹_S` be the generic slice (`K = k'(x)^alg`). The *geometric slice* of the
product along `b` is the product over the trait `Spec K⟦t⟧` of the slice `𝒳 ×_{𝔸¹_S} Spec K⟦t⟧` of
`M` and of the change of trait `𝒴 ×_S Spec K⟦t⟧` of `N`, with total space the slice
`𝒵 ×_{𝔸¹_S} Spec K⟦t⟧` of `P` (`NearbyCyclesModel.sliceFst`, `NearbyCyclesModel.sliceSnd`); the
case of a coordinate of `N` follows by exchanging the factors, the Künneth map being symmetric
(`NearbyCyclesModel.isIso_map_kunnethMap_iff_swap`).

The blueprint proof (`sk-prop-tf-nearby-external-kunneth`, "Finite support") identifies the
restriction of the Künneth map `Π_{A,B}` to the special fibre of the slice of `P` with the
invariants of the Künneth map of the geometric slice under the pro-`p` kernel of the map of
inertia groups, by the generic-slicing description of nearby cycles (SGA 4½, [Th. finitude],
§§3.4, 3.7) and the projection formula for invariants (blueprint `det-nearby-kunneth-invariants`):
if the Künneth map of the geometric slice is an isomorphism, so is the restriction of `Π_{A,B}`
(`NearbyCyclesModel.isIso_map_kunnethMap_of_isIso_sliceFst`). Formally, the pullback of
`Π_{A,B}` is a retract of the Künneth map of the geometric slice
(`NearbyCyclesModel.isIso_map_kunnethMap_of_isTensorRetract`), given the two facts on traits:
the invariance of nearby cycles under change of trait
(`NearbyCyclesModel.isIso_pullbackExchange_baseChangeHom_traitMap`, unfinished) and the
generic-slicing identification with invariants
(`NearbyCyclesModel.exists_sum_autAction_pullbackExchange_sliceFst`, unfinished); the projection
formula for invariants makes the retractions compatible with the Künneth maps
(`NearbyCyclesModel.isTensorRetract_map_kunnethMap_comp_pullbackExchange_sliceFst`).
Since the slice of a local chart `V ⟶ 𝔸ᵐ_S` along one of its coordinates is a local chart of
dimension `m - 1` over `Spec K⟦t⟧` (`AlgebraicGeometry.exists_isImmersion_pullback_reindex`),
the Künneth formula for charts of smaller dimension over `Spec K⟦t⟧`
(`NearbyCyclesModel.KunnethFormula`) makes the restriction of `Π_{A,B}` to the slice an isomorphism
(`NearbyCyclesModel.isIso_map_kunnethMap_baseChangeSpecialMap_fst`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

/-- The field `K = k'(x)^alg` of the generic slices has the characteristic of `k'`. -/
lemma ringChar_traitSliceField (k' : Type u) [Field k'] :
    ringChar (traitSliceField k') = ringChar k' :=
  (Algebra.ringChar_eq k' (traitSliceField k')).symm

namespace ProEtale.CondensedRing.NearbyCyclesModel

open Scheme

/-- **Gabber's Künneth formula in chart dimension `n`** over the trait `Spec k'⟦t⟧`: for every
product `P` over the trait of models `M`, `N` of finite type, with projections compatible with
the structure morphisms to `Spec Ω`, whose total spaces locally embed into `𝔸^{m₁}_S` and
`𝔸^{m₂}_S` with `m₁ + m₂ ≤ n`, and for bounded constructible `A`, `B`, the Künneth map of nearby
cycles `Π_{A,B}` is an isomorphism. -/
def KunnethFormula (ℓ : ℕ) [Fact ℓ.Prime] (k' : Type u) [Field k'] (n : ℕ) : Prop :=
  ∀ {X Y Z : Scheme.{u}} {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
    {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
    {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left} (φ₁ : P.Hom M f₁ f₁')
    (φ₂ : P.Hom N f₂ f₂') {qM : M.total ⟶ trait k'}
    {gM : M.generic ⟶ Spec (.of (traitGenericField k'))} {qN : N.total ⟶ trait k'}
    {gN : N.generic ⟶ Spec (.of (traitGenericField k'))},
    M.IsTraitModelOver qM gM → N.IsTraitModelOver qN gN →
    IsPullback φ₁.total φ₂.total qM qN →
    P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM) →
    φ₂.generic ≫ gN = φ₁.generic ≫ gM → ∀ {m₁ m₂ : ℕ}, m₁ + m₂ ≤ n →
    qM.LocallyEmbedsInAffineSpace m₁ → qN.LocallyEmbedsInAffineSpace m₂ →
    ∀ {eM : M.total ⟶ X}, M.j ≫ eM = M.ε → ∀ {eN : N.total ⟶ Y}, N.j ≫ eN = N.ε →
    ∀ {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
      {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))},
      boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A →
      boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B →
      IsIso (kunnethMap (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B)

variable {ℓ : ℕ} [Fact ℓ.Prime] {k' : Type u} [Field k'] {X Y Z : Scheme.{u}}
  {X' Y' Z' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {N : NearbyCyclesModel Y Y'.left} {P : NearbyCyclesModel Z Z'.left} {f₁ : Z ⟶ X}
  {f₁' : Z'.left ⟶ X'.left} {f₂ : Z ⟶ Y} {f₂' : Z'.left ⟶ Y'.left} {φ₁ : P.Hom M f₁ f₁'}
  {φ₂ : P.Hom N f₂ f₂'} {qM : M.total ⟶ trait k'}
  {gM : M.generic ⟶ Spec (.of (traitGenericField k'))} {qN : N.total ⟶ trait k'}
  {gN : N.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver qM gM) (hN : N.IsTraitModelOver qN gN)
  (hpb : IsPullback φ₁.total φ₂.total qM qN)
  (hP : P.IsTraitModelOver (φ₁.total ≫ qM) (φ₁.generic ≫ gM))
  (hgen : φ₂.generic ≫ gN = φ₁.generic ≫ gM)

/-! ### Slicing along a coordinate of the first factor -/

section Fst

variable {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = qM)

include hb in
lemma comp_coordinate_fst :
    (φ₁.total ≫ b) ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = φ₁.total ≫ qM := by
  rw [Category.assoc, hb]

/-- The first projection of the geometric slice of a product along a coordinate `b` of the first
factor: the slice of `P` along `φ₁ ≫ b` maps to the slice of `M` along `b`. -/
noncomputable abbrev sliceFst :=
  φ₁.baseChange hM hP hb (traitSlice_over (traitSliceCoord k')) (comp_coordinate_fst hb)
    (traitSlice_over (traitSliceCoord k')) (𝟙 _) (Category.comp_id _) (Category.comp_id _) rfl

include hpb hb in
lemma comp_coordinate_fst_eq :
    (φ₁.total ≫ b) ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = φ₂.total ≫ qN := by
  rw [comp_coordinate_fst hb, hpb.w]

/-- The second projection of the geometric slice of a product along a coordinate `b` of the first
factor: the slice of `P` along `φ₁ ≫ b` maps to the change of trait of `N`. -/
noncomputable abbrev sliceSnd :=
  φ₂.baseChange hN hP (Category.comp_id qN) (Category.comp_id (traitMap k' (traitSliceField k')))
    (comp_coordinate_fst hb) (traitSlice_over (traitSliceCoord k'))
    (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k') (comp_coordinate_fst_eq hpb hb)
    (traitSlice_over (traitSliceCoord k')) hgen.symm

variable [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **Invariance of nearby cycles under change of trait** (SGA 4½, [Th. finitude], §3.7; blueprint
`sk-prop-tf-nearby-external-kunneth`, "Facts about traits", first fact): for a model `N` of finite
type over the strictly henselian trait `S = Spec k'⟦t⟧` and the change of trait
`Spec K⟦t⟧ ⟶ S` (`K = k'(x)^alg`), the pullback exchange `α : Lσ^* Ψ_N B ⟶ Ψ_{N''} B` to the
nearby cycles of the base change `N'' = N ×_S Spec K⟦t⟧` (`NearbyCyclesModel.baseChange`) is an
isomorphism for bounded constructible `B`.

Unfinished: the identification of the stalks of `Rj_*` at the points of the special fibre of
`N''` with those of `N` requires base change of `Rj_*` along `𝒴 ×_S Spec K⟦t⟧ ⟶ 𝒴`, which is not
weakly étale, and the comparison of the geometric generic points of the two traits; neither is
formalised for pro-étale `ℚ̄_ℓ`-sheaves. Deligne's proof of this invariance runs the dévissage of
his finiteness theorem (SGA 4½, [Th. finitude], Thm. 3.2), whose lisse generic case is still
`sorry` (`NearbyCyclesModel.boundedConstructible_nearbyCycles_affineSpace_lisse_generic_core`). -/
theorem isIso_pullbackExchange_baseChangeHom_traitMap
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B) :
    IsIso (((baseChangeHom hN qN (Category.comp_id qN) (traitMap k' (traitSliceField k'))
      (Category.comp_id _)).pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app B) :=
  sorry

set_option maxHeartbeats 800000 in
-- the statement involves the nearby cycles of the slice of the product
include hM hP hb in
/-- **The generic-slicing identification of nearby cycles with invariants** (blueprint
`sk-prop-tf-nearby-external-kunneth`, "Facts about traits", identification (2); SGA 4½,
[Th. finitude], §§3.4, 3.7). Let `P'` be the pro-`p` kernel of the map of inertia groups of the
generic slice `Spec K⟦t⟧ ⟶ 𝔸¹_S` and of `S`; it acts on the base change models through
automorphisms of the geometric generic point `Spec Ω_K` over `Spec Ω`
(`NearbyCyclesModel.GenericAut`, `NearbyCyclesModel.baseChangeAut`). The slicing exchanges
`α_M : Lσ^* Ψ_M A ⟶ Ψ_{M''} A` of `M` and `α_P` of the product `P` are the inclusions of the
`P'`-invariants: the action factors through a finite quotient of order `n` (a power of `p`), with
representatives `τ i`, and `α_M`, `α_P` are split monomorphisms whose idempotents are `1/n` times
the sums of the actions of the `τ i`. This is
`NearbyCyclesModel.exists_subgroup_pullbackExchange_baseChangeHom_traitSlice` for `M` and for `P`,
over the intersection of the two subgroups of finite index acting trivially
(`NearbyCyclesModel.sum_autAction_baseChangeAut_eq_relIndex_nsmul`). -/
theorem exists_sum_autAction_pullbackExchange_sliceFst
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B) :
    ∃ (n : ℕ) (τ : Fin n → GenericAut k' (traitSliceField k')), n ≠ 0 ∧
    ∃ (rM : (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
          (baseChange hM b hb (traitSlice (traitSliceCoord k'))
            (traitSlice_over (traitSliceCoord k'))).nearbyCycles
              (Profinite.padicAlgClRingObj ℓ)).obj A ⟶
        (M.nearbyCycles (Profinite.padicAlgClRingObj ℓ) ⋙
          L((baseChangeSpecialMap hM b hb (traitSlice (traitSliceCoord k'))
            (traitSlice_over (traitSliceCoord k')))^*⟦Profinite.padicAlgClRingObj ℓ⟧)).obj A)
      (rP : (L((𝟙 Z)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
          (baseChange hP (φ₁.total ≫ b) (comp_coordinate_fst hb) (traitSlice (traitSliceCoord k'))
            (traitSlice_over (traitSliceCoord k'))).nearbyCycles
              (Profinite.padicAlgClRingObj ℓ)).obj
            (L((f₁)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A ⊗
              L((f₂)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj B) ⟶
        (P.nearbyCycles (Profinite.padicAlgClRingObj ℓ) ⋙
          L((baseChangeSpecialMap hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
            (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k')))^*⟦
              Profinite.padicAlgClRingObj ℓ⟧)).obj
            (L((f₁)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A ⊗
              L((f₂)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj B)),
      ((baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
          (traitSlice_over (traitSliceCoord k'))).pullbackExchange
            (Profinite.padicAlgClRingObj ℓ)).app A ≫ rM = 𝟙 _ ∧
      n • (rM ≫ ((baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
          (traitSlice_over (traitSliceCoord k'))).pullbackExchange
            (Profinite.padicAlgClRingObj ℓ)).app A) =
        ∑ i, (baseChangeAut hM b hb (traitSlice (traitSliceCoord k'))
          (traitSlice_over (traitSliceCoord k')) (τ i)).autAction
            (Profinite.padicAlgClRingObj ℓ) (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A) ∧
      ((baseChangeHom hP (φ₁.total ≫ b) (comp_coordinate_fst hb) (traitSlice (traitSliceCoord k'))
          (traitSlice_over (traitSliceCoord k'))).pullbackExchange
            (Profinite.padicAlgClRingObj ℓ)).app
          (L((f₁)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A ⊗
            L((f₂)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj B) ≫ rP = 𝟙 _ ∧
      n • (rP ≫ ((baseChangeHom hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
          (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k'))).pullbackExchange
            (Profinite.padicAlgClRingObj ℓ)).app
          (L((f₁)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A ⊗
            L((f₂)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj B)) =
        ∑ i, (baseChangeAut hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
          (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k')) (τ i)).autAction
            (Profinite.padicAlgClRingObj ℓ) (L((𝟙 Z)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj
              (L((f₁)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A ⊗
                L((f₂)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj B)) := by
  set Λ := Profinite.padicAlgClRingObj ℓ
  have hPg : boundedConstructible (condensedRingObj Λ P.generic)
      (L((P.ε)^*⟦Λ⟧).obj (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B)) := by
    have : (boundedConstructible (condensedRingObj Λ P.generic)).IsMonoidal :=
      isMonoidal_boundedConstructible (X := Over.mk (φ₁.generic ≫ gM)) (ℓ := ℓ)
    exact (boundedConstructible _).prop_of_iso (Functor.Monoidal.μIso L((P.ε)^*⟦Λ⟧) _ _)
      (ObjectProperty.prop_tensor
        (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ P.ε _
          (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ f₁ A hA))
        (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ P.ε _
          (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ f₂ B hB)))
  obtain ⟨VM, _, htM, rM, hrM, havgM⟩ := exists_subgroup_pullbackExchange_baseChangeHom_traitSlice
    hM hb (boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ M.ε A hA)
  obtain ⟨VP, _, htP, rP, hrP, havgP⟩ := exists_subgroup_pullbackExchange_baseChangeHom_traitSlice
    hP (comp_coordinate_fst hb) hPg
  have : VM.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have : VP.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let V := VM ⊓ VP
  let := Subgroup.fintypeQuotientOfFiniteIndex (H := V)
  have hcard : ∀ (W : Subgroup (GenericAut k' (traitSliceField k'))) (_ : V ≤ W)
      [Fintype (GenericAut k' (traitSliceField k') ⧸ W)],
      Fintype.card (GenericAut k' (traitSliceField k') ⧸ V) =
        V.relIndex W * Fintype.card (GenericAut k' (traitSliceField k') ⧸ W) := by
    intro W hW _
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Subgroup.index,
      ← Subgroup.index, Subgroup.relIndex_mul_index hW]
  let e := (Fintype.equivFin (GenericAut k' (traitSliceField k') ⧸ V)).symm
  refine ⟨Fintype.card (GenericAut k' (traitSliceField k') ⧸ V), fun i ↦ (e i).out,
    Fintype.card_ne_zero, rM, rP, hrM, ?_, hrP, ?_⟩
  · rw [Equiv.sum_comp e (fun σ ↦ (baseChangeAut hM b hb (traitSlice (traitSliceCoord k'))
        (traitSlice_over _) σ.out).autAction Λ (L((𝟙 X)^*⟦Λ⟧).obj A)),
      sum_autAction_baseChangeAut_eq_relIndex_nsmul hM b hb _ _ Λ inf_le_left _ htM, ← havgM,
      hcard VM inf_le_left, mul_nsmul]
  · rw [Equiv.sum_comp e (fun σ ↦ (baseChangeAut hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
        (traitSlice (traitSliceCoord k')) (traitSlice_over _) σ.out).autAction Λ
          (L((𝟙 Z)^*⟦Λ⟧).obj (L((f₁)^*⟦Λ⟧).obj A ⊗ L((f₂)^*⟦Λ⟧).obj B))),
      sum_autAction_baseChangeAut_eq_relIndex_nsmul hP (φ₁.total ≫ b) (comp_coordinate_fst hb) _ _
        Λ inf_le_right _ htP, ← havgP, hcard VP inf_le_right, mul_nsmul]

set_option maxHeartbeats 800000 in
-- the square of the Künneth maps of the slice is a large term
include hM hN hpb hP hgen hb in
/-- **The generic-slicing identification of the Künneth map** (blueprint
`sk-prop-tf-nearby-external-kunneth`, "Finite support", identification (2) and projection formula
(3); Illusie, *Autour du théorème de monodromie locale*, proof of Thm. 4.7). Consider the square
of the Künneth maps and pullbacks (`NearbyCyclesModel.map_kunnethMap_comp_pullbackExchange`) for
the projections from the geometric slice of the product `P` along the coordinate `b` of `M`
(`NearbyCyclesModel.baseChangeHom`, `NearbyCyclesModel.sliceFst`, `NearbyCyclesModel.sliceSnd`):
```
Lσ^* Π_{A,B} ≫ a = δ ≫ (u_M ⊗ u_N) ≫ Π'.
```
Then `u_M` (the slicing exchange of `M`) and `a` (the slicing exchange of `P`) are split
monomorphisms, with retractions whose idempotents are carried into each other by `Π'`
(`CategoryTheory.IsTensorRetract`). The retractions are the averages over a finite quotient of the
pro-`p` kernel `P'` of the map of inertia groups
(`NearbyCyclesModel.exists_sum_autAction_pullbackExchange_sliceFst`); their compatibility with
`Π'` is the projection formula for invariants (blueprint `det-nearby-kunneth-invariants`): `Π'` is
equivariant (`NearbyCyclesModel.kunnethMap_autAction`) and `P'` acts trivially on the nearby
cycles of the change of trait of `N` (`NearbyCyclesModel.Hom.autAction_eq_id_of_isIso`, by the
invariance under change of trait `NearbyCyclesModel.isIso_pullbackExchange_baseChangeHom_traitMap`),
see `NearbyCyclesModel.isTensorRetract_of_average`. -/
theorem isTensorRetract_map_kunnethMap_comp_pullbackExchange_sliceFst
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B) :
    IsTensorRetract (map_kunnethMap_comp_pullbackExchange (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂
      (sliceFst hM hP hb) (sliceSnd hN hpb hP hgen hb)
      (baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
        (traitSlice_over (traitSliceCoord k')))
      (baseChangeHom hN qN (Category.comp_id qN) (traitMap k' (traitSliceField k'))
        (Category.comp_id _))
      (baseChangeHom hP (φ₁.total ≫ b) (comp_coordinate_fst hb) (traitSlice (traitSliceCoord k'))
        (traitSlice_over (traitSliceCoord k')))
      (Hom.baseChange_total_comp hM hP _ _ _ _ φ₁ _ _ _ rfl)
      (Hom.baseChange_generic_comp hM hP _ _ _ _ φ₁ _ _ _ rfl)
      (Hom.baseChange_total_comp hN hP _ _ _ _ φ₂ _ _ _ hgen.symm)
      (Hom.baseChange_generic_comp hN hP _ _ _ _ φ₂ _ _ _ hgen.symm)
      (by simp : f₁ ≫ 𝟙 X = 𝟙 Z ≫ f₁) (Hom.baseChangeSpecial_comp hM hP _ _ _ _ φ₁ _ _ _)
      (by simp : f₂ ≫ 𝟙 Y = 𝟙 Z ≫ f₂) (Hom.baseChangeSpecial_comp hN hP _ _ _ _ φ₂ _ _ _)
      A B) := by
  obtain ⟨n, τ, hn, rM, rP, hrM, havgM, hrP, havgP⟩ :=
    exists_sum_autAction_pullbackExchange_sliceFst hM hP hb hA hB
  have hN' := isIso_pullbackExchange_baseChangeHom_traitMap hN hB
  refine isTensorRetract_of_average (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂
    (sliceFst hM hP hb) (sliceSnd hN hpb hP hgen hb)
    (baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
      (traitSlice_over (traitSliceCoord k')))
    (baseChangeHom hN qN (Category.comp_id qN) (traitMap k' (traitSliceField k'))
      (Category.comp_id _))
    (baseChangeHom hP (φ₁.total ≫ b) (comp_coordinate_fst hb) (traitSlice (traitSliceCoord k'))
      (traitSlice_over (traitSliceCoord k')))
    (Hom.baseChange_total_comp hM hP _ _ _ _ φ₁ _ _ _ rfl)
    (Hom.baseChange_generic_comp hM hP _ _ _ _ φ₁ _ _ _ rfl)
    (Hom.baseChange_total_comp hN hP _ _ _ _ φ₂ _ _ _ hgen.symm)
    (Hom.baseChange_generic_comp hN hP _ _ _ _ φ₂ _ _ _ hgen.symm)
    (by simp : f₁ ≫ 𝟙 X = 𝟙 Z ≫ f₁) (Hom.baseChangeSpecial_comp hM hP _ _ _ _ φ₁ _ _ _)
    (by simp : f₂ ≫ 𝟙 Y = 𝟙 Z ≫ f₂) (Hom.baseChangeSpecial_comp hN hP _ _ _ _ φ₂ _ _ _)
    A B Finset.univ n (fun f g h ↦ nsmul_cancel_padicAlgClRingObj ℓ _ hn h)
    (fun i ↦ baseChangeAut hM b hb _ _ (τ i)) (fun i ↦ baseChangeAut hN qN _ _ _ (τ i))
    (fun i ↦ baseChangeAut hP (φ₁.total ≫ b) _ _ _ (τ i)) (fun i ↦ ?_) (fun i ↦ ?_)
    rM (by exact_mod_proofs hrM) (by exact_mod_proofs havgM) rP (by exact_mod_proofs hrP)
    (by exact_mod_proofs havgP)
  · exact kunnethMap_autAction _ _ _ _ _ _ (by simp)
      (baseChangeAut_generic_comp_baseChange hM hP _ _ _ _ φ₁ _ _ _ rfl (τ i)) (by simp)
      (baseChangeAut_generic_comp_baseChange hN hP _ _ _ _ φ₂ _ _ _ hgen.symm (τ i)) _ _
  · exact @Hom.autAction_eq_id_of_isIso _ _ _ _ _ _ _ _ _ _ _ _ _ (by simp)
      (baseChangeAut_generic_comp hN _ _ _ _ _) B (by exact_mod_proofs hN')

set_option maxHeartbeats 800000 in
-- the square of the Künneth maps of the slice is a large term
include hM hN hpb hP hgen hb in
/-- **The generic-slicing step for the Künneth map** (blueprint
`sk-prop-tf-nearby-external-kunneth`, "Finite support"; Illusie, *Autour du théorème de
monodromie locale*, proof of Thm. 4.7): for the product `P` over the strictly henselian trait
`S = Spec k'⟦t⟧` of models `M`, `N` of finite type and a coordinate `b : 𝒳 ⟶ 𝔸¹_S` of `M`, if
the Künneth map of the geometric slice (`NearbyCyclesModel.sliceFst`,
`NearbyCyclesModel.sliceSnd`) over the trait `Spec K⟦t⟧` is an isomorphism, so is the pullback
of `Π_{A,B}` to the special fibre of the slice of `P`. The pullback of `Π_{A,B}` is a retract of
the Künneth map of the slice (`NearbyCyclesModel.isIso_map_kunnethMap_of_isTensorRetract`), by
the generic-slicing identification
(`NearbyCyclesModel.isTensorRetract_map_kunnethMap_comp_pullbackExchange_sliceFst`) and the
invariance of nearby cycles under change of trait
(`NearbyCyclesModel.isIso_pullbackExchange_baseChangeHom_traitMap`). -/
theorem isIso_map_kunnethMap_of_isIso_sliceFst
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B)
    (h : IsIso (kunnethMap (Profinite.padicAlgClRingObj ℓ) (sliceFst hM hP hb)
      (sliceSnd hN hpb hP hgen hb) A B)) :
    IsIso (L((baseChangeSpecialMap hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
        (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k')))^*⟦
          Profinite.padicAlgClRingObj ℓ⟧).map
      (kunnethMap (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B)) := by
  have hK : IsIso (kunnethMap (Profinite.padicAlgClRingObj ℓ) (sliceFst hM hP hb)
      (sliceSnd hN hpb hP hgen hb) (L((𝟙 X)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj A)
      (L((𝟙 Y)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj B)) :=
    isIso_kunnethMap_of_iso _ _ _ ((leftDerivedUpperStarId _ X).app A)
      ((leftDerivedUpperStarId _ Y).app B) h
  have hN' := isIso_pullbackExchange_baseChangeHom_traitMap hN hB
  have hT :=
    isTensorRetract_map_kunnethMap_comp_pullbackExchange_sliceFst hM hN hpb hP hgen hb hA hB
  exact isIso_map_kunnethMap_of_isTensorRetract (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂
    (sliceFst hM hP hb) (sliceSnd hN hpb hP hgen hb)
    (baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
      (traitSlice_over (traitSliceCoord k')))
    (baseChangeHom hN qN (Category.comp_id qN) (traitMap k' (traitSliceField k'))
      (Category.comp_id _))
    (baseChangeHom hP (φ₁.total ≫ b) (comp_coordinate_fst hb) (traitSlice (traitSliceCoord k'))
      (traitSlice_over (traitSliceCoord k')))
    (Hom.baseChange_total_comp hM hP _ _ _ _ φ₁ _ _ _ rfl)
    (Hom.baseChange_generic_comp hM hP _ _ _ _ φ₁ _ _ _ rfl)
    (Hom.baseChange_total_comp hN hP _ _ _ _ φ₂ _ _ _ hgen.symm)
    (Hom.baseChange_generic_comp hN hP _ _ _ _ φ₂ _ _ _ hgen.symm)
    (by simp : f₁ ≫ 𝟙 X = 𝟙 Z ≫ f₁) (Hom.baseChangeSpecial_comp hM hP _ _ _ _ φ₁ _ _ _)
    (by simp : f₂ ≫ 𝟙 Y = 𝟙 Z ≫ f₂) (Hom.baseChangeSpecial_comp hN hP _ _ _ _ φ₂ _ _ _)
    A B (by exact_mod_proofs hN') (by exact_mod_proofs hT) (by exact_mod_proofs hK)

include hM hN hpb hP hgen in
/-- **The generic-slicing step** (blueprint `sk-prop-tf-nearby-external-kunneth`, "Finite
support"): if Gabber's Künneth formula holds in chart dimension `n` over the trait `Spec K⟦t⟧`
(`NearbyCyclesModel.KunnethFormula`), and the slice of `𝒳` along `b` and the total space of `N`
locally embed into affine spaces of dimensions `m₁`, `m₂` with `m₁ + m₂ ≤ n`, then the pullback of
`Π_{A,B}` to the special fibre of the slice of `P` along `b` is an isomorphism
(`NearbyCyclesModel.isIso_map_kunnethMap_of_isIso_sliceFst`). -/
theorem isIso_map_kunnethMap_baseChangeSpecialMap_fst {n : ℕ}
    (hIH : KunnethFormula ℓ (traitSliceField k') n) {m₁ m₂ : ℕ} (hle : m₁ + m₂ ≤ n)
    (h₁ : (pullback.snd b (traitSlice (traitSliceCoord k'))).LocallyEmbedsInAffineSpace m₁)
    (h₂ : qN.LocallyEmbedsInAffineSpace m₂)
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B) :
    IsIso (L((baseChangeSpecialMap hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
        (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k')))^*⟦
          Profinite.padicAlgClRingObj ℓ⟧).map
      (kunnethMap (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B)) := by
  refine isIso_map_kunnethMap_of_isIso_sliceFst hM hN hpb hP hgen hb hA hB ?_
  have hP'' := IsTraitModelOver.baseChange hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
    (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k'))
  refine hIH (sliceFst hM hP hb) (sliceSnd hN hpb hP hgen hb)
    (IsTraitModelOver.baseChange hM b hb _ (traitSlice_over (traitSliceCoord k')))
    (IsTraitModelOver.baseChange hN qN (Category.comp_id qN) _ (Category.comp_id _))
    (isPullback_baseChange_product hpb b hb _ (traitSlice_over (traitSliceCoord k')))
    (by convert hP'' using 1 <;> simp) (by simp) hle h₁
    (h₂.of_isPullback (IsPullback.of_hasPullback qN (traitMap k' (traitSliceField k'))))
    (eM := pullback.fst _ _ ≫ eM) (by simp [← heM]) (eN := pullback.fst _ _ ≫ eN)
    (by simp [← heN]) hA hB

end Fst

/-! ### Slicing along a coordinate of the second factor -/

section Snd

variable {b : N.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = qN)

include hpb hb in
lemma comp_coordinate_snd :
    (φ₂.total ≫ b) ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = φ₁.total ≫ qM := by
  rw [Category.assoc, hb, hpb.w]

variable [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

include hM hN hpb hP hgen in
/-- **The generic-slicing step, coordinate of the second factor**: the analogue of
`NearbyCyclesModel.isIso_map_kunnethMap_baseChangeSpecialMap_fst` for a coordinate of `N`. It is
that lemma for the product with the two factors exchanged, by the symmetry of the Künneth map
(`NearbyCyclesModel.isIso_map_kunnethMap_iff_swap`). -/
theorem isIso_map_kunnethMap_baseChangeSpecialMap_snd {n : ℕ}
    (hIH : KunnethFormula ℓ (traitSliceField k') n) {m₁ m₂ : ℕ} (hle : m₁ + m₂ ≤ n)
    (h₁ : qM.LocallyEmbedsInAffineSpace m₁)
    (h₂ : (pullback.snd b (traitSlice (traitSliceCoord k'))).LocallyEmbedsInAffineSpace m₂)
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B) :
    IsIso (L((baseChangeSpecialMap hP (φ₂.total ≫ b) (comp_coordinate_snd hpb hb)
        (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k')))^*⟦
          Profinite.padicAlgClRingObj ℓ⟧).map
      (kunnethMap (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B)) := by
  have hP' : P.IsTraitModelOver (φ₂.total ≫ qN) (φ₂.generic ≫ gN) := by
    rw [← hpb.w, hgen]
    exact hP
  have h := isIso_map_kunnethMap_baseChangeSpecialMap_fst hN hM hpb.flip hP' hgen.symm hb hIH
    (m₁ := m₂) (m₂ := m₁) (by omega) h₂ h₁ heN heM hB hA
  have e : baseChangeSpecialMap hP' (φ₂.total ≫ b) (comp_coordinate_fst hb)
      (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k')) =
      baseChangeSpecialMap hP (φ₂.total ≫ b) (comp_coordinate_snd hpb hb)
        (traitSlice (traitSliceCoord k')) (traitSlice_over (traitSliceCoord k')) := by
    refine hP.isPullback_i.hom_ext ?_ ?_
    · simp
    · simp [baseChangeSpecialMap]
  rw [e] at h
  exact (isIso_map_kunnethMap_iff_swap _ _ φ₁ φ₂ A B).1 h

end Snd

end ProEtale.CondensedRing.NearbyCyclesModel

end AlgebraicGeometry
