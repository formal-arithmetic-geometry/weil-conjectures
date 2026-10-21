/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.PoincareDuality.Verdier
public import WeilConjectures.SmoothPurity.Defs
import Sheaf.PoincareDuality.ConstructibleShiftSingle
import Sheaf.PoincareDuality.TateTwistLocalLine
import Sheaf.PoincareDuality.TateTwistOneLocalLine
import WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-!

# Poincaré duality for `ℚ̄_ℓ`-coefficients on the pro-étale site

Let `ℓ` be a prime, `k` a field of characteristic `≠ ℓ` and `p : X ⟶ S` a smooth morphism of
pure relative dimension `d` of separated `k`-schemes of finite type. Smooth purity
(`ProEtale.CondensedRing.smoothPurityIso`) provides the chosen isomorphism
`pur_p : Rp^! ℚ̄_ℓ,S ≅ ℚ̄_ℓ,X(d)[2d]`, and this file defines from it, through the abstract
constructions of `WeilConjectures.PoincareDuality.Abstract`:

* the **trace** `Tr_p : Rp_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,S`, the composite of `Rp_!(pur_p⁻¹)` and the
  counit of `Rp_! ⊣ Rp^!`;
* the **Poincaré duality morphism** `PD_p : Rp_* ℚ̄_ℓ,X(d)[2d] ⟶ RHom(Rp_! ℚ̄_ℓ,X, ℚ̄_ℓ,S)`, the
  composite of `Rp_*(pur_p⁻¹)`, the identification `Rp^! ℚ̄_ℓ,S ≅ RHom(ℚ̄_ℓ,X, Rp^! ℚ̄_ℓ,S)` and
  the Verdier exchange morphism `Φ_{p,ℚ̄_ℓ,X,ℚ̄_ℓ,S}`;
* the **compact-support cup product**
  `cup_c : Rp_! ℚ̄_ℓ,X ⊗ᴸ Rp_* ℚ̄_ℓ,X(d)[2d] ⟶ Rp_! ℚ̄_ℓ,X(d)[2d]`, from the derived exceptional
  projection morphism and the counit of `Lp^* ⊣ Rp_*`.

All three share the normalization of `pur_p`: the transpose of `PD_p` is exactly `Tr_p ∘ cup_c`
(`ProEtale.CondensedRing.uncurry_poincareMap`), and `PD_p` is an isomorphism by Verdier
duality (`ProEtale.CondensedRing.isIso_poincareMap`), which is **Poincaré duality** in the
form `𝔻_S(Rp_! ℚ̄_ℓ,X) ≅ Rp_* ℚ̄_ℓ,X(d)[2d]`.

All objects live in the bounded constructible derived categories `Dᵇc(-)⟦ℚ̲̄_ℓ⟧`, which are
monoidal closed subcategories of the ambient derived categories
(`ProEtale.CondensedRing.isMonoidal_boundedConstructible` and
`ProEtale.CondensedRing.isMonoidalClosed_boundedConstructible`). As in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, `X` and `S` are
objects of `Over (Spec (.of k))` and `p` a morphism of `Over (Spec (.of k))`.

## Not treated here

* The passage from the derived statement to the perfect pairing
  `H^i_c(X, ℚ̄_ℓ) × H^{2d-i}(X, ℚ̄_ℓ(d)) ⟶ ℚ̄_ℓ` on cohomology groups over `S = Spec k̄`, which
  requires the perfectness of `Rp_! ℚ̄_ℓ,X` and the comparison of `RΓ(S, RHom(-, ℚ̄_ℓ,S))` with the
  linear dual.
* The Frobenius equivariance, which belongs to the Weil sheaf formalism.
* The compatibility with the compactly supported base change isomorphism and with the
  compactification and composition comparisons, which are commutativity conditions on the maps
  defined here, to be stated once those comparisons are available.

-/

@[expose] public section


-- Avoid unfolding the K-injective internal-Hom and coefficient pullback constructions.
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.tateModule AlgebraicGeometry.ProEtale.tateTwistOne
  CategoryTheory.ObjectProperty.fullMonoidalClosedSubcategory
  AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStar
  AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleLowerStar
  AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleLowerShriek
  AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperShriek

attribute [local irreducible]
  AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperStarLowerStarAdjunction
  AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleUpperShriekAdjunction
  AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleExceptionalProjection

attribute [local instance 2000] CategoryTheory.ObjectProperty.fullMonoidalSubcategory
  CategoryTheory.ObjectProperty.fullMonoidalClosedSubcategory

universe u

open CategoryTheory MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Obj

universe v w

namespace AlgebraicGeometry.ProEtale

private noncomputable def moduleIhomIso
    {X : Scheme.{u}} (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    ihom M ≅ Mod.ihom' R M :=
  (ihom.adjunction M).rightAdjointUniq
    ((Mod.ihom'Adjunction R M).ofNatIsoLeft
      (Mod.relativeTensorRightIso M ≪≫
        (BraidedCategory.tensorLeftIsoTensorRight M).symm))

private theorem nonempty_pullback_ihom
    {X Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f]
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    Nonempty (((upperStar Ab.{u + 1} f).mapMod R).obj ((ihom M).obj N) ≅
      (ihom (((upperStar Ab.{u + 1} f).mapMod R).obj M)).obj
        (((upperStar Ab.{u + 1} f).mapMod R).obj N)) := by
  let F := ProEtale.upperStar Ab.{u + 1} f
  let Φ := F.mapMod R
  have : ∀ Z, IsIso (Functor.LaxMonoidal.ihomComparison F Z).natTrans :=
    isIso_ihomComparison_upperStar Ab.{u + 1} f
  let Ψ := F.mapMod R ⋙ Mod.comap (𝟙 (F.obj R))
  let e : Ψ ≅ Φ := Functor.isoWhiskerLeft Φ (Mod.comapId (F.obj R)) ≪≫ Φ.rightUnitor
  have : IsIso (Mod.mapIhom'Hom F (𝟙 (F.obj R)) M N) :=
    Mod.isIso_mapIhom'Hom F (𝟙 (F.obj R)) M N
  exact ⟨Φ.mapIso ((moduleIhomIso R M).app N) ≪≫ (e.app _).symm ≪≫
    asIso (Mod.mapIhom'Hom F (𝟙 (F.obj R)) M N) ≪≫
    ((moduleIhomIso (F.obj R) (Ψ.obj M)).app (Ψ.obj N)).symm ≪≫
    (ihom _).mapIso (e.app N) ≪≫ asIso ((pre (e.inv.app M)).app (Φ.obj N))⟩

private theorem powers_image_regular
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {C : Type w} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) ⥤ C) [F.Monoidal]
    (hOne : Nonempty (F.obj (tateTwistOne X ℓ) ≅ 𝟙_ C))
    (hHom : ∀ M, Nonempty (F.obj ((ihom M).obj (𝟙_ _)) ≅
      (ihom (F.obj M)).obj (F.obj (𝟙_ _)))) (d : ℤ) :
    Nonempty (F.obj (tateTwist X ℓ d) ≅ 𝟙_ C) := by
  have hNat (n : ℕ) : Nonempty (F.obj (tateTwistNat X ℓ n) ≅ 𝟙_ C) := by
    induction n with
    | zero => exact ⟨(Functor.Monoidal.εIso F).symm⟩
    | succ n ih =>
      obtain ⟨e⟩ := ih
      obtain ⟨eOne⟩ := hOne
      exact ⟨(Functor.Monoidal.μIso F _ _).symm ≪≫
        (e ⊗ᵢ eOne) ≪≫ (λ_ (𝟙_ C))⟩
  cases d with
  | ofNat n => exact hNat n
  | negSucc n =>
    obtain ⟨e⟩ := hNat (n + 1)
    obtain ⟨eHom⟩ := hHom (tateTwistNat X ℓ (n + 1))
    exact ⟨eHom ≪≫ (ihom _).mapIso (Functor.Monoidal.εIso F).symm ≪≫
      asIso ((pre e.inv).app (𝟙_ C)) ≪≫ unitIsoSelf _⟩

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType S.hom]
  [QuasiCompact S.hom] [IsSeparated S.hom]
  (p : X ⟶ S) (d : ℕ) [SmoothOfRelativeDimension d p.left]

omit [Fact (ringChar k).Prime] in
/-- The coefficient prime is invertible on every scheme over the given base field.

Source: the opening invertibility condition of the blueprint Tate-twist unit. The prime is
nonzero in the field and its unit maps to global sections under the structure morphism.
(blueprint: lem-poincare-ell-unit-over-field) -/
lemma ell_isUnit (Y : Over (Spec (.of k))) : IsUnit (ℓ : Γ(Y.left, ⊤)) := by
  have h : IsUnit (ℓ : k) := isUnit_iff_ne_zero.mpr
    (CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ℓ.Prime) (Fact.out : ringChar k ≠ ℓ))
  simpa using (h.map (Scheme.ΓSpecIso (.of k)).inv.hom).map Y.hom.appTop.hom

/-! ### Smooth purity on bounded constructible complexes -/

/-- Over an ℓ-invertible scheme, the shifted Tate twist `ℚ̄_ℓ,X(d)[n]` is bounded
constructible. (blueprint: nt-target-poincare-tate-bc) -/
lemma boundedConstructible_tateTwistDerived (X : Scheme.{u})
    (hℓ : IsUnit (ℓ : Γ(X, ⊤))) (d n : ℤ) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
      ((shiftFunctor _ n).obj (tateTwistDerived X ℓ d)) := by
  let R := condensedRingObj (Profinite.padicAlgClRingObj ℓ) X
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  apply boundedConstructible_shift_single
  refine ⟨S, fun a ↦ ?_⟩
  obtain ⟨𝒰, h𝒰⟩ := tateTwistOne_pullback_locally_trivial X ℓ hℓ (𝟙 X)
  refine ⟨𝒰, fun i ↦ ?_⟩
  let F := ProEtale.upperStar Ab.{u + 1} (S.immersion a)
  let G := ProEtale.upperStar Ab.{u + 1} (𝒰.f i)
  let Φ := F.mapMod R ⋙ G.mapMod (F.obj R)
  let : F.Braided := ProEtale.CondensedRing.braided_sheafUpperStar _
  let : G.Braided := ProEtale.CondensedRing.braided_sheafUpperStar _
  have : WeaklyEtale (𝒰.f i) :=
    proetalePrecoverage_le_precoverage_weaklyEtale _ 𝒰.mem₀ ⟨i⟩
  have hHom (M) : Nonempty (Φ.obj ((ihom M).obj (𝟙_ _)) ≅
      (ihom (Φ.obj M)).obj (Φ.obj (𝟙_ _))) := by
    obtain ⟨eF⟩ := nonempty_pullback_ihom (S.immersion a) R M (𝟙_ _)
    obtain ⟨eG⟩ := nonempty_pullback_ihom (𝒰.f i) (F.obj R)
      ((F.mapMod R).obj M) ((F.mapMod R).obj (𝟙_ _))
    exact ⟨(G.mapMod (F.obj R)).mapIso eF ≪≫ eG⟩
  obtain ⟨e⟩ := powers_image_regular X ℓ Φ (h𝒰 i) hHom d
  refine ⟨1, 0, 0, ⟨?_⟩⟩
  exact e ≪≫ (Limits.biproductUniqueIso (fun _ : Fin 1 ↦ Mod.regular _)).symm ≪≫
    (Limits.cokernelZeroIsoTarget (X := Mod.finiteFree _ 0)).symm

/-- The shifted Tate twist `ℚ̄_ℓ,X(d)[n]`, as a bounded constructible complex. -/
local syntax "boundedConstructible_tateTwistDerived" term:max term:max term:max term:max : term
local macro_rules
  | `(boundedConstructible_tateTwistDerived $a:term $b:term $c:term $d:term) =>
      `(AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_tateTwistDerived
        $a $b (by assumption) $c $d)
noncomputable def boundedConstructibleTateTwist (X : Scheme.{u})
    (hℓ : IsUnit (ℓ : Γ(X, ⊤))) (d n : ℤ) :
    Dᵇc(X)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  ⟨(shiftFunctor _ n).obj (tateTwistDerived X ℓ d), boundedConstructible_tateTwistDerived ℓ X d n⟩

/-- The chosen purity isomorphism `pur_p : Rp^! ℚ̄_ℓ,S ≅ ℚ̄_ℓ,X(d)[2d]` of
`ProEtale.CondensedRing.smoothPurityIso`, as an isomorphism in `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`: its preimage
under the fully faithful inclusion `Dᵇc ⥤ D`. No new choice is made: this is the same
isomorphism, and it is the only normalization entering the trace and Poincaré duality below. -/
noncomputable def boundedConstructibleSmoothPurityIso :
    (boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ p).obj (𝟙_ _) ≅
      boundedConstructibleTateTwist ℓ X.left (ell_isUnit ℓ X) d (2 * d) :=
  (ObjectProperty.fullyFaithfulι _).preimageIso (smoothPurityIso ℓ p d)

attribute [local irreducible] boundedConstructibleSmoothPurityIso boundedConstructibleTateTwist

-- Use the monoidal structure carried by the same category instance as the abstract maps.
attribute [local instance 2100] MonoidalCategory.toMonoidalCategoryStruct

/-- The existing exceptional projection transformation, with the monoidal structure
inferred from the same category instance as the abstract duality constructions.
This named interface avoids repeatedly converting between definitionally equal structures. -/
noncomputable def poincareProjection :
    curriedTensorInsertFunctor₁
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ p) ⟶
      curriedTensorPost
          (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ p) ⋙
        (Functor.whiskeringLeft
          Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧
          Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧
          Dᵇc(S.left)⟦Profinite.padicAlgClRingObj ℓ⟧).obj
            (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ p) :=
  boundedConstructibleExceptionalProjection _ ℓ p

attribute [local irreducible] poincareProjection

local syntax "boundedConstructibleExceptionalProjection" term:max term:max term:max : term
local macro_rules
  | `(boundedConstructibleExceptionalProjection $_:term $b:term $c:term) =>
      `(AlgebraicGeometry.ProEtale.CondensedRing.poincareProjection $b $c)

/-- The **trace** `Tr_p : Rp_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,S` of a smooth morphism `p : X ⟶ S` of pure
relative dimension `d`: `Rp_!(pur_p⁻¹)` followed by the counit of `Rp_! ⊣ Rp^!`. -/
noncomputable def trace :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ p).obj
      (boundedConstructibleTateTwist ℓ X.left (ell_isUnit ℓ X) d (2 * d)) ⟶ 𝟙_ _ :=
  Verdier.trace (boundedConstructibleUpperShriekAdjunction _ ℓ p)
    (boundedConstructibleSmoothPurityIso ℓ p d)

/-- The **Poincaré duality morphism**
`PD_p : Rp_* ℚ̄_ℓ,X(d)[2d] ⟶ RHom(Rp_! ℚ̄_ℓ,X, ℚ̄_ℓ,S)`: `Rp_*(pur_p⁻¹)`, the identification
`Rp^! ℚ̄_ℓ,S ≅ RHom(ℚ̄_ℓ,X, Rp^! ℚ̄_ℓ,S)`, and the Verdier exchange morphism. -/
noncomputable def poincareMap :
    (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj
        (boundedConstructibleTateTwist ℓ X.left (ell_isUnit ℓ X) d (2 * d)) ⟶
      (ihom ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ p).obj
        (𝟙_ _))).obj (𝟙_ _) :=
  Verdier.poincareMap (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ p)
    (boundedConstructibleUpperShriekAdjunction _ ℓ p)
    (boundedConstructibleExceptionalProjection _ ℓ p)
    (boundedConstructibleSmoothPurityIso ℓ p d)

/-- The **compact-support cup product**
`cup_c : Rp_! ℚ̄_ℓ,X ⊗ᴸ Rp_* ℚ̄_ℓ,X(d)[2d] ⟶ Rp_! ℚ̄_ℓ,X(d)[2d]`: the derived exceptional
projection morphism `PF^!`, the counit `Lp^* Rp_* ⟶ 𝟭` and the left unitor. -/
noncomputable def cupProduct :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ p).obj (𝟙_ _) ⊗
        (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ p).obj
          (boundedConstructibleTateTwist ℓ X.left (ell_isUnit ℓ X) d (2 * d)) ⟶
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ p).obj
        (boundedConstructibleTateTwist ℓ X.left (ell_isUnit ℓ X) d (2 * d)) :=
  Verdier.cupProduct (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ p)
    (boundedConstructibleExceptionalProjection _ ℓ p)

omit [SmoothOfRelativeDimension d p.left] in
/-- **Poincaré duality is the trace–cup pairing**: the transpose
`Rp_! ℚ̄_ℓ,X ⊗ᴸ Rp_* ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,S` of the Poincaré duality morphism is the cup product
followed by the trace. -/
theorem uncurry_poincareMap :
    uncurry (poincareMap ℓ p d) = cupProduct ℓ p d ≫ trace ℓ p d :=
  Verdier.uncurry_poincareMap
    (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ p)
    (boundedConstructibleUpperShriekAdjunction _ ℓ p)
    (poincareProjection ℓ p)
    (boundedConstructibleSmoothPurityIso ℓ p d)

universe v₁ v₂ u₁ u₂

private theorem boundedConstructible_zeroTateTwistDerived (X : Scheme.{u}) (n : ℤ) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)
      ((shiftFunctor _ n).obj (tateTwistDerived X ℓ 0)) := by
  exact boundedConstructible_shift_single _ _ (zeroTwist_constructible X ℓ) n

private theorem poincareMap_isIso_of_exchange
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [MonoidalClosed D]
    {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
    {P : C ⥤ D} {S : D ⥤ C} (adj' : P ⊣ S)
    (pf : curriedTensorInsertFunctor₁ P ⟶
      curriedTensorPost P ⋙ (Functor.whiskeringLeft D C D).obj F)
    {T : C} (pur : S.obj (𝟙_ D) ≅ T)
    (h : IsIso (Verdier.exchange adj adj' pf (𝟙_ C) (𝟙_ D))) :
    IsIso (Verdier.poincareMap adj adj' pf pur) := by
  have := h
  unfold Verdier.poincareMap
  infer_instance

private theorem poincareMap_isIso_of_projection
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [MonoidalClosed D]
    {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
    {P : C ⥤ D} {S : D ⥤ C} (adj' : P ⊣ S)
    (pf : curriedTensorInsertFunctor₁ P ⟶
      curriedTensorPost P ⋙ (Functor.whiskeringLeft D C D).obj F)
    {T : C} (pur : S.obj (𝟙_ D) ≅ T)
    (h : ∀ B, IsIso ((pf.app (𝟙_ C)).app B)) :
    IsIso (Verdier.poincareMap adj adj' pf pur) := by
  have := h
  have := Verdier.isIso_exchange_of_isIso adj adj' pf (𝟙_ C) (𝟙_ D)
  unfold Verdier.poincareMap
  infer_instance

omit [SmoothOfRelativeDimension d p.left] in
/-- **Poincaré duality**: the Poincaré duality morphism
`PD_p : Rp_* ℚ̄_ℓ,X(d)[2d] ⟶ RHom(Rp_! ℚ̄_ℓ,X, ℚ̄_ℓ,S)` is an isomorphism, by Verdier duality. -/
theorem isIso_poincareMap : IsIso (poincareMap ℓ p d) := by
  exact poincareMap_isIso_of_projection
    (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ p)
    (boundedConstructibleUpperShriekAdjunction _ ℓ p)
    (poincareProjection ℓ p)
    (boundedConstructibleSmoothPurityIso ℓ p d)
    (fun B ↦ by
      delta poincareProjection
      exact isIso_boundedConstructibleExceptionalProjection_app_app _ ℓ p (𝟙_ _) B)

end AlgebraicGeometry.ProEtale.CondensedRing
