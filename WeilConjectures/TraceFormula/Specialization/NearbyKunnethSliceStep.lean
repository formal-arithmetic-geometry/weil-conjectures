/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyEmbedsInAffineSpace
public import WeilConjectures.SixFunctors.NearbyCycles.Kunneth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSlice
public import WeilConjectures.TraceFormula.Specialization.TraitBaseChangeModel

/-!

# Gabber's Künneth formula for nearby cycles: the generic-slicing step

Let `P` be the product over the strictly henselian trait `S = Spec k'⟦t⟧` of models `M`, `N` of
finite type, and let `b : 𝒳 ⟶ 𝔸¹_S` be a coordinate of the total space of `M`. Let
`σ : Spec K⟦t⟧ ⟶ 𝔸¹_S` be the generic slice (`K = k'(x)^alg`). The *geometric slice* of the
product along `b` is the product over the trait `Spec K⟦t⟧` of the slice `𝒳 ×_{𝔸¹_S} Spec K⟦t⟧` of
`M` and of the change of trait `𝒴 ×_S Spec K⟦t⟧` of `N`, with total space the slice
`𝒵 ×_{𝔸¹_S} Spec K⟦t⟧` of `P` (`NearbyCyclesModel.sliceFst`, `NearbyCyclesModel.sliceSnd`); the
case of a coordinate of `N` is symmetric (`NearbyCyclesModel.sliceFst'`,
`NearbyCyclesModel.sliceSnd'`).

The blueprint proof (`sk-prop-tf-nearby-external-kunneth`, "Finite support") identifies the
restriction of the Künneth map `Π_{A,B}` to the special fibre of the slice of `P` with the
invariants of the Künneth map of the geometric slice under the pro-`p` kernel of the map of
inertia groups, by the generic-slicing description of nearby cycles (SGA 4½, [Th. finitude],
§§3.4, 3.7) and the projection formula for invariants (blueprint `det-nearby-kunneth-invariants`):
if the Künneth map of the geometric slice is an isomorphism, so is the restriction of `Π_{A,B}`
(`NearbyCyclesModel.isIso_map_kunnethMap_of_isIso_sliceFst`, unfinished). Since the slice of a
local chart `V ⟶ 𝔸ᵐ_S` along one of its coordinates is a local chart of dimension `m - 1` over
`Spec K⟦t⟧` (`AlgebraicGeometry.exists_isImmersion_pullback_reindex`), the Künneth formula for
charts of smaller dimension over `Spec K⟦t⟧` (`NearbyCyclesModel.KunnethFormula`) makes the
restriction of `Π_{A,B}` to the slice an isomorphism
(`NearbyCyclesModel.isIso_map_kunnethMap_baseChangeSpecialMap_fst`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

/-- The field `K = k'(x)^alg` of the generic slices has the characteristic of `k'`. -/
lemma ringChar_sliceField (k' : Type u) [Field k'] : ringChar (sliceField k') = ringChar k' :=
  (Algebra.ringChar_eq k' (sliceField k')).symm

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
  φ₁.baseChange hM hP hb (traitSlice_over (sliceCoord k')) (comp_coordinate_fst hb)
    (traitSlice_over (sliceCoord k')) (𝟙 _) (Category.comp_id _) (Category.comp_id _) rfl

include hpb hb in
lemma comp_coordinate_fst_eq :
    (φ₁.total ≫ b) ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = φ₂.total ≫ qN := by
  rw [comp_coordinate_fst hb, hpb.w]

/-- The second projection of the geometric slice of a product along a coordinate `b` of the first
factor: the slice of `P` along `φ₁ ≫ b` maps to the change of trait of `N`. -/
noncomputable abbrev sliceSnd :=
  φ₂.baseChange hN hP (Category.comp_id qN) (Category.comp_id (traitMap k' (sliceField k')))
    (comp_coordinate_fst hb) (traitSlice_over (sliceCoord k'))
    (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k') (comp_coordinate_fst_eq hpb hb)
    (traitSlice_over (sliceCoord k')) hgen.symm

variable [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **The generic-slicing identification for the Künneth map** (blueprint
`sk-prop-tf-nearby-external-kunneth`, "Facts about traits" and "Finite support"; Illusie,
*Autour du théorème de monodromie locale*, proof of Thm. 4.7): for the product `P` over the
strictly henselian trait `S = Spec k'⟦t⟧` of models `M`, `N` of finite type and a coordinate
`b : 𝒳 ⟶ 𝔸¹_S` of `M`, if the Künneth map of the geometric slice
(`NearbyCyclesModel.sliceFst`, `NearbyCyclesModel.sliceSnd`) over the trait `Spec K⟦t⟧` is an
isomorphism, so is the pullback of `Π_{A,B}` to the special fibre of the slice of `P`.

Unfinished. Let `S'` be the strict localization of `𝔸¹_S` at the generic point of its special
fibre, `I' ⟶ I` the map of inertia groups and `P` its pro-`p` kernel. The generic-slicing
description of nearby cycles (SGA 4½, [Th. finitude], §§3.4, 3.7: invariance of nearby cycles
under the change of trait `Spec K⟦t⟧ ⟶ S'` and the factorisation of the geometric generic point
through that of `S'`) identifies the restrictions of `Ψ_M A` and `Ψ_P (A ⊠ B)` with the
`P`-invariants of the nearby cycles of the slices, and the restriction of `Ψ_N B` with the nearby
cycles of the change of trait (on which `P` acts trivially), compatibly with the Künneth maps; the
projection formula for `P`-invariants (blueprint `det-nearby-kunneth-invariants`, proved for
discrete representations in `Representation.invariantsTensorEquiv`) then identifies the
restriction of `Π_{A,B}` with the `P`-invariants of the Künneth map of the geometric slice.
Neither the action of inertia on nearby cycles nor the invariance of nearby cycles under change
of traits is formalised. -/
theorem isIso_map_kunnethMap_of_isIso_sliceFst
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B)
    (h : IsIso (kunnethMap (Profinite.padicAlgClRingObj ℓ) (sliceFst hM hP hb)
      (sliceSnd hN hpb hP hgen hb) A B)) :
    IsIso (L((baseChangeSpecialMap hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
        (traitSlice (sliceCoord k')) (traitSlice_over (sliceCoord k')))^*⟦
          Profinite.padicAlgClRingObj ℓ⟧).map
      (kunnethMap (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B)) :=
  sorry

include hM hN hpb hP hgen in
/-- **The generic-slicing step** (blueprint `sk-prop-tf-nearby-external-kunneth`, "Finite
support"): if Gabber's Künneth formula holds in chart dimension `n` over the trait `Spec K⟦t⟧`
(`NearbyCyclesModel.KunnethFormula`), and the slice of `𝒳` along `b` and the total space of `N`
locally embed into affine spaces of dimensions `m₁`, `m₂` with `m₁ + m₂ ≤ n`, then the pullback of
`Π_{A,B}` to the special fibre of the slice of `P` along `b` is an isomorphism
(`NearbyCyclesModel.isIso_map_kunnethMap_of_isIso_sliceFst`). -/
theorem isIso_map_kunnethMap_baseChangeSpecialMap_fst {n : ℕ}
    (hIH : KunnethFormula ℓ (sliceField k') n) {m₁ m₂ : ℕ} (hle : m₁ + m₂ ≤ n)
    (h₁ : (pullback.snd b (traitSlice (sliceCoord k'))).LocallyEmbedsInAffineSpace m₁)
    (h₂ : qN.LocallyEmbedsInAffineSpace m₂)
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B) :
    IsIso (L((baseChangeSpecialMap hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
        (traitSlice (sliceCoord k')) (traitSlice_over (sliceCoord k')))^*⟦
          Profinite.padicAlgClRingObj ℓ⟧).map
      (kunnethMap (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B)) := by
  refine isIso_map_kunnethMap_of_isIso_sliceFst hM hN hpb hP hgen hb heM heN hA hB ?_
  have hP'' := IsTraitModelOver.baseChange hP (φ₁.total ≫ b) (comp_coordinate_fst hb)
    (traitSlice (sliceCoord k')) (traitSlice_over (sliceCoord k'))
  refine hIH (sliceFst hM hP hb) (sliceSnd hN hpb hP hgen hb)
    (IsTraitModelOver.baseChange hM b hb _ (traitSlice_over (sliceCoord k')))
    (IsTraitModelOver.baseChange hN qN (Category.comp_id qN) _ (Category.comp_id _))
    (isPullback_baseChange_product hpb b hb _ (traitSlice_over (sliceCoord k')))
    (by convert hP'' using 1 <;> simp) (by simp) hle h₁
    (h₂.of_isPullback (IsPullback.of_hasPullback qN (traitMap k' (sliceField k'))))
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

/-- The first projection of the geometric slice of a product along a coordinate `b` of the
second factor: the slice of `P` along `φ₂ ≫ b` maps to the change of trait of `M`. -/
noncomputable abbrev sliceFst' :=
  φ₁.baseChange hM hP (Category.comp_id qM) (Category.comp_id (traitMap k' (sliceField k')))
    (comp_coordinate_snd hpb hb) (traitSlice_over (sliceCoord k'))
    (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k') (comp_coordinate_snd hpb hb)
    (traitSlice_over (sliceCoord k')) rfl

/-- The second projection of the geometric slice of a product along a coordinate `b` of the
second factor: the slice of `P` along `φ₂ ≫ b` maps to the slice of `N` along `b`. -/
noncomputable abbrev sliceSnd' :=
  φ₂.baseChange hN hP hb (traitSlice_over (sliceCoord k')) (comp_coordinate_snd hpb hb)
    (traitSlice_over (sliceCoord k')) (𝟙 _) (Category.comp_id _) (Category.comp_id _)
    hgen.symm

variable [IsSepClosed k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **The generic-slicing identification for the Künneth map, coordinate of the second factor**
(blueprint `sk-prop-tf-nearby-external-kunneth`, "Facts about traits" and "Finite support"): the
analogue of `NearbyCyclesModel.isIso_map_kunnethMap_of_isIso_sliceFst` for a coordinate
`b : 𝒴 ⟶ 𝔸¹_S` of `N`, with the geometric slice `NearbyCyclesModel.sliceFst'`,
`NearbyCyclesModel.sliceSnd'`.

Unfinished, for the same reason as `NearbyCyclesModel.isIso_map_kunnethMap_of_isIso_sliceFst`:
the generic-slicing description of nearby cycles (SGA 4½, [Th. finitude], §§3.4, 3.7) and the
action of inertia on nearby cycles are not formalised. -/
theorem isIso_map_kunnethMap_of_isIso_sliceSnd'
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B)
    (h : IsIso (kunnethMap (Profinite.padicAlgClRingObj ℓ) (sliceFst' hM hpb hP hb)
      (sliceSnd' hN hpb hP hgen hb) A B)) :
    IsIso (L((baseChangeSpecialMap hP (φ₂.total ≫ b) (comp_coordinate_snd hpb hb)
        (traitSlice (sliceCoord k')) (traitSlice_over (sliceCoord k')))^*⟦
          Profinite.padicAlgClRingObj ℓ⟧).map
      (kunnethMap (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B)) :=
  sorry

include hM hN hpb hP hgen in
/-- **The generic-slicing step, coordinate of the second factor**: the analogue of
`NearbyCyclesModel.isIso_map_kunnethMap_baseChangeSpecialMap_fst` for a coordinate of `N`. -/
theorem isIso_map_kunnethMap_baseChangeSpecialMap_snd {n : ℕ}
    (hIH : KunnethFormula ℓ (sliceField k') n) {m₁ m₂ : ℕ} (hle : m₁ + m₂ ≤ n)
    (h₁ : qM.LocallyEmbedsInAffineSpace m₁)
    (h₂ : (pullback.snd b (traitSlice (sliceCoord k'))).LocallyEmbedsInAffineSpace m₂)
    {eM : M.total ⟶ X} (heM : M.j ≫ eM = M.ε) {eN : N.total ⟶ Y} (heN : N.j ≫ eN = N.ε)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))}
    (hA : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) A)
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) B) :
    IsIso (L((baseChangeSpecialMap hP (φ₂.total ≫ b) (comp_coordinate_snd hpb hb)
        (traitSlice (sliceCoord k')) (traitSlice_over (sliceCoord k')))^*⟦
          Profinite.padicAlgClRingObj ℓ⟧).map
      (kunnethMap (Profinite.padicAlgClRingObj ℓ) φ₁ φ₂ A B)) := by
  refine isIso_map_kunnethMap_of_isIso_sliceSnd' hM hN hpb hP hgen hb heM heN hA hB ?_
  have hP'' := IsTraitModelOver.baseChange hP (φ₂.total ≫ b) (comp_coordinate_snd hpb hb)
    (traitSlice (sliceCoord k')) (traitSlice_over (sliceCoord k'))
  refine hIH (sliceFst' hM hpb hP hb) (sliceSnd' hN hpb hP hgen hb)
    (IsTraitModelOver.baseChange hM qM (Category.comp_id qM) _ (Category.comp_id _))
    (IsTraitModelOver.baseChange hN b hb _ (traitSlice_over (sliceCoord k')))
    (isPullback_baseChange_product hpb.flip b hb _ (traitSlice_over (sliceCoord k'))).flip
    (by convert hP'' using 1 <;> simp) (by simp) hle
    (h₁.of_isPullback (IsPullback.of_hasPullback qM (traitMap k' (sliceField k')))) h₂
    (eM := pullback.fst _ _ ≫ eM) (by simp [← heM]) (eN := pullback.fst _ _ ≫ eN)
    (by simp [← heN]) hA hB

end Snd

end ProEtale.CondensedRing.NearbyCyclesModel

end AlgebraicGeometry
