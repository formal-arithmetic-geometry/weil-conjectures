/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleUnitsSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnityInverseImageSupplement
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralPullbackData
public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

import all WeilConjectures.SecSmoothPurity.CochainTensorCoherenceDataSupplement
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.Algebra.Homology.InverseImageScalarRestriction.InverseImageScalarRestrictionComparison
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Equivariant derived scalar extension and simultaneous integral reduction

Source: latest blueprint, `sk-prop-diagonal-tower-system.proof.md`, (2)--(4)
(blueprint: lem-pur-equivariant-reduction-calculus).

## Main definitions

- `Action.EqMod`: actual semilinear modules before localization.
- `ScalarModel`: the tensor/restriction universal pair and its resolving computations.
- `IntegralReductionModel`: the single strict reduction tower and its derived evaluations.
- `KummerModel`: the whole-system identification with positive-unit normalization.

## Main statements

- `scalarModel_nonempty` and the normalized scalar comparison existence theorems.
- `integralReductionModel_nonempty` and its forgetting and pullback comparisons.
- `kummerModel_nonempty`, `kummer_adjunct`, `kummer_forgetting`, and `kummer_pullback`.

## Node proof steps and their statements

1. `Action.additive`, `Action.isEquivalence`, `Action.isKFlat_iff_equivariantAcyclicTest`,
   and `equivariantKFlatResolution` state the actual equivariant resolving construction.
2. `scalarModel_nonempty`, `scalar_preservesQuasiIso`, and
   `scalarForgettingComparison_nonempty` state scalar derivation, its unit and forgetting.
3. `unitComparison_nonempty` and `compositionComparison_nonempty` fix the scalar constraints.
4. `InverseImage.properties`, `derivedRingedPullback_properties`, and
   `scalarPullbackComparison_nonempty` state equivariant ringed inverse-image compatibility.
5. `reductionModel_nonempty` constructs the one strict system and its left derivation.
6. `integralReductionModel_nonempty`, `reductionCompositionComparison_nonempty`,
   `reductionForgetting_nonempty`, and `reductionPullbackComparison_nonempty` fix its
   evaluations, transitions and comparisons.
7. `constantReduction_nonempty` computes the regular integral source and its unit.
8. `kummerPresentation_nonempty` states exactness and the natural power-transition tower.
9. `kummerModel_nonempty` computes the reductions by the two-term coefficient resolutions.
10. `KummerModel.positive` and `kummerModel_nonempty` fix the positive connecting-map sign.
11. `KummerModel.iso`, `KummerModel.evaluation`, and `kummerModel_nonempty` state the
    truncation identification in the derived category of the entire tower category.
12. `kummer_adjunct`, `kummer_forgetting`, and `kummer_pullback` state arbitrary-arrow
    adjuncts and the whole-system forgetting and pullback equations.
Fixed pairs are formed before localization. Ordinary scalar extension, its pure
sections, and K-flatness are the existing ringed-site constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v r

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Endofunctor

namespace SheafOfModules.EquivariantReduction

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}

variable {σ : Sheaf J (Type r) ≌ Sheaf J (Type r)}

universe uD vD

/-- The universal module-addition graph and naturality of the underlying-sheaf
comparison show that every algebraic inverse image preserves addition of maps.
Source: Stacks 03D2 (blueprint: lem-pur-equivariant-reduction-calculus). -/
private theorem algebraicImage_additive
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{r} D]
    {K : GrothendieckTopology D}
    {L : Sheaf J (Type r) ⥤ Sheaf K (Type r)}
    {R : Sheaf J CommRingCat.{r}} {S : Sheaf K CommRingCat.{r}}
    (E : AlgebraicInverseImage L R S) : E.modules.Additive := by
  let V := toSheaf ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{r})
  constructor
  intro M N f g
  ext U z
  have eval (k : M ⟶ N) :
      (E.moduleUnderlying.inv.app N).hom.app U
          ((L.map (V.map k)).hom.app U
            ((E.moduleUnderlying.hom.app M).hom.app U z)) =
        (E.modules.map k).val.app U z := by
    have h := congrArg
      (fun q ↦ q.hom.app U ((E.moduleUnderlying.hom.app M).hom.app U z))
      (E.moduleUnderlying.inv.naturality k)
    change (E.moduleUnderlying.inv.app N).hom.app U
        ((L.map (V.map k)).hom.app U
          ((E.moduleUnderlying.hom.app M).hom.app U z)) =
      (E.modules.map k).val.app U
        ((E.moduleUnderlying.inv.app M).hom.app U
          ((E.moduleUnderlying.hom.app M).hom.app U z)) at h
    have hz : (E.moduleUnderlying.inv.app M).hom.app U
        ((E.moduleUnderlying.hom.app M).hom.app U z) = z :=
      congrArg (fun q ↦ q.hom.app U z) (E.moduleUnderlying.hom_inv_id_app M)
    rw [hz] at h
    exact h
  have h := E.moduleAdd N (V.obj M)
    (V.map f) (V.map g) (V.map (f + g))
    (fun _ _ ↦ rfl) U ((E.moduleUnderlying.hom.app M).hom.app U z)
  dsimp only [id] at h
  rw [eval (f + g), eval f, eval g] at h
  exact h

/-- Algebraic transport by a topos automorphism is additive.
Source: Stacks 03D2 (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: the universal addition graph in moduleUnderlying turns moduleAdd into
preservation of addition of module maps; its naturality supplies the equality. -/
theorem Action.additive (A : Action σ) : A.lift.modules.Additive := by
  exact algebraicImage_additive A.lift

/-- Algebraic transport by a topos automorphism is an equivalence.
Source: Stacks 03D2 (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: transport ring and module operations through the inverse topos equivalence.
Its unit and counit preserve operation graphs, hence lift to inverse module functors. -/
theorem Action.isEquivalence (A : Action σ) : A.lift.modules.IsEquivalence := by
  sorry

attribute [instance] Action.additive Action.isEquivalence

attribute [local instance] HasDerivedCategory.standard


universe a₀ b₀ a₁ b₁ h₀ k₀ h₁ k₁ w₀ z₀ w₁ z₁

/-- A derived comparison is normalized when its cochain counits give the specified
ordinary comparison on every resolving complex. This reusable equation keeps the
large sheaf presentations out of elaboration of the comparison's definition.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
@[irreducible] def IsNormalizedDerivedSquare
    {A₀ : Type a₀} [Category.{h₀} A₀] [Abelian A₀] [HasDerivedCategory.{w₀} A₀]
    {B₀ : Type b₀} [Category.{k₀} B₀] [Abelian B₀] [HasDerivedCategory.{z₀} B₀]
    {A₁ : Type a₁} [Category.{h₁} A₁] [Abelian A₁] [HasDerivedCategory.{w₁} A₁]
    {B₁ : Type b₁} [Category.{k₁} B₁] [Abelian B₁] [HasDerivedCategory.{z₁} B₁]
    (E : A₀ ⥤ B₀) [E.Additive] (E' : A₁ ⥤ B₁) [E'.Additive]
    (L : A₀ ⥤ A₁) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (V : B₀ ⥤ B₁) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (F : DerivedCategory A₀ ⥤ DerivedCategory B₀)
    (G : DerivedCategory A₁ ⥤ DerivedCategory B₁)
    (ε : DerivedCategory.Q ⋙ F ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (η : DerivedCategory.Q ⋙ G ⟶ E'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (e : E ⋙ V ≅ L ⋙ E')
    (d : F ⋙ V.mapDerivedCategory ≅ L.mapDerivedCategory ⋙ G)
    (resolving : CochainComplex A₀ ℤ → Prop) : Prop :=
  ∀ P : CochainComplex A₀ ℤ, resolving P →
    d.hom.app (DerivedCategory.Q.obj P) ≫
      G.map (L.mapDerivedCategoryFactors.hom.app P) ≫
      η.app ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (L ⋙ E')) (.up ℤ)).hom.app P) =
    V.mapDerivedCategory.map (ε.app P) ≫
      V.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P)

-- Auto-generated `mk.inj`/`mk.injEq`/`SizeOf` lemmas re-check the huge field types in the kernel.
set_option genInjectivity false in
set_option genSizeOfSpec false in
attribute [instance] ScalarModel.additive


-- Auto-generated `mk.inj`/`mk.injEq`/`SizeOf` lemmas re-check the huge field types in the kernel.
set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Scalar identity, normalized on pure tensors and on the common K-flat model.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
structure UnitComparison {A : Action σ} {f : Map A A} (F : ScalarModel f) where
  ordinary : F.E ≅ 𝟭 A.EqMod
  sections : ∀ (M : A.EqMod) (U : Cᵒᵖ) (m : M.carrier.val.obj U)
    (s : A.ring.obj.obj U),
    (ordinary.hom.app M).hom.f.val.app U (F.tmul M U m s) = s • m
  derived : F.T ≅ 𝟭 (DerivedCategory A.EqMod)
  normalized : ∀ (P : CochainComplex A.EqMod ℤ), A.IsKFlat P →
    derived.hom.app (DerivedCategory.Q.obj P) = F.ε.app P ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex ordinary (.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso A.EqMod (.up ℤ)).hom.app P)

-- Auto-generated `mk.inj`/`mk.injEq`/`SizeOf` lemmas re-check the huge field types in the kernel.
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The actual scalar functor preserves quasi-isomorphisms between full
acyclic-test equivariant K-flat complexes.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: the derived functor T of the scalar model sends the localization of the
quasi-isomorphism p to an isomorphism. Naturality of the counit ε gives
ε_P ≫ Q(E p) = T(Q p) ≫ ε_Q, and ε_P, ε_Q are invertible on the K-flat complexes P, Q
(`computes`). Hence Q(E p) is invertible, i.e. E p is a quasi-isomorphism. -/
theorem scalar_preservesQuasiIso {A B : Action σ} {f : Map A B} (F : ScalarModel f)
    {P Q : CochainComplex A.EqMod ℤ} (p : P ⟶ Q)
    (hP : A.IsKFlat P) (hQ : A.IsKFlat Q) (hp : QuasiIso p) :
    QuasiIso ((F.E.mapHomologicalComplex (.up ℤ)).map p) := by
  have hp' : QuasiIso p := hp
  have hm : IsIso (F.T.map (DerivedCategory.Q.map p)) := by infer_instance
  have hεP : IsIso (F.ε.app P) := F.computes P hP
  have hεQ : IsIso (F.ε.app Q) := F.computes Q hQ
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso B.EqMod _).1
  rw [← isIso_comp_left_iff (F.ε.app P)]
  change IsIso (F.ε.app P ≫
    (F.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).map p)
  rw [← F.ε.naturality p]
  change IsIso (F.T.map (DerivedCategory.Q.map p) ≫ F.ε.app Q)
  infer_instance

-- Auto-generated `mk.inj`/`mk.injEq`/`SizeOf` lemmas re-check the huge field types in the kernel.
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- One strict quotient system, before localization, and its derived universal pair.
The cokernel universal properties fix the quotient action; the transition equation
fixes the actual quotient transitions. The natural counit is a map of whole systems.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
structure ReductionModel {A B : Action σ} {f : Map A B}
    (l : ℕ) (F : ScalarModel f) where
  E : A.EqMod ⥤ (ℕᵒᵖ ⥤ B.EqMod)
  [additive : E.Additive]
  π : ∀ n : ℕ, F.E ⟶ E ⋙ (CategoryTheory.evaluation ℕᵒᵖ B.EqMod).obj (op n)
  zero : ∀ (n : ℕ) (M : A.EqMod),
    (l ^ (n + 1) • 𝟙 (F.E.obj M)) ≫ (π n).app M = 0
  quotient : ∀ (n : ℕ) (M : A.EqMod),
    IsColimit (CokernelCofork.ofπ ((π n).app M) (zero n M))
  transition : ∀ (n : ℕ) (M : A.EqMod),
    (π (n + 1)).app M ≫ (E.obj M).map (homOfLE n.le_succ).op = (π n).app M
  ordinary_unit : ∀ n : ℕ,
    𝟭 A.EqMod ⟶ (E ⋙ (CategoryTheory.evaluation ℕᵒᵖ B.EqMod).obj (op n)) ⋙ f.eqRestrict
  ordinary_unit_eq : ∀ (n : ℕ) (M : A.EqMod),
    (ordinary_unit n).app M =
      F.adj.unit.app M ≫ f.eqRestrict.map ((π n).app M)
  T : DerivedCategory A.EqMod ⥤ DerivedCategory (ℕᵒᵖ ⥤ B.EqMod)
  ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  universal : T.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A.EqMod (.up ℤ))
  pointwise : (E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).HasPointwiseLeftDerivedFunctor
    (HomologicalComplex.quasiIso A.EqMod (.up ℤ))
  computes : ∀ P : CochainComplex A.EqMod ℤ, A.IsKFlat P → IsIso (ε.app P)
  triangulated : ∃ (_ : T.CommShift ℤ), T.IsTriangulated
  level : ∀ _n : ℕ,
    DerivedCategory A.EqMod ⥤ DerivedCategory B.EqMod
  level_counit : ∀ n : ℕ, DerivedCategory.Q ⋙ level n ⟶
    (E ⋙ (CategoryTheory.evaluation ℕᵒᵖ B.EqMod).obj (op n)).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q
  level_universal : ∀ n : ℕ, (level n).IsLeftDerivedFunctor (level_counit n)
    (HomologicalComplex.quasiIso A.EqMod (.up ℤ))
  unit : ∀ n : ℕ, 𝟭 (DerivedCategory A.EqMod) ⟶ level n ⋙ f.eqRestrict.mapDerivedCategory
  unit_normalized : ∀ (n : ℕ) (K : CochainComplex A.EqMod ℤ),
    (unit n).app (DerivedCategory.Q.obj K) ≫
      f.eqRestrict.mapDerivedCategory.map ((level_counit n).app K) ≫
      f.eqRestrict.mapDerivedCategoryFactors.hom.app
        (((E ⋙ (CategoryTheory.evaluation ℕᵒᵖ B.EqMod).obj (op n)).mapHomologicalComplex
          (.up ℤ)).obj K) =
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexIdIso A.EqMod (.up ℤ)).inv.app K ≫
          (NatTrans.mapHomologicalComplex (ordinary_unit n) (.up ℤ)).app K ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl
            ((E ⋙ (CategoryTheory.evaluation ℕᵒᵖ B.EqMod).obj (op n)) ⋙
              f.eqRestrict)) (.up ℤ)).inv.app K)
  evaluation : ∀ n : ℕ,
    T ⋙ ((CategoryTheory.evaluation ℕᵒᵖ B.EqMod).obj (op n)).mapDerivedCategory ≅ level n
  evaluation_normalized : ∀ (n : ℕ) (P : CochainComplex A.EqMod ℤ),
    (evaluation n).hom.app (DerivedCategory.Q.obj P) ≫ (level_counit n).app P =
      (((CategoryTheory.evaluation ℕᵒᵖ B.EqMod).obj (op n)).mapDerivedCategory).map
        (ε.app P) ≫
      ((CategoryTheory.evaluation ℕᵒᵖ B.EqMod).obj (op n)).mapDerivedCategoryFactors.hom.app
        ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl
          (E ⋙ (CategoryTheory.evaluation ℕᵒᵖ B.EqMod).obj (op n))) (.up ℤ)).hom.app P)

attribute [instance] ReductionModel.additive

/-- Simultaneous reduction exists using one actual equivariant K-flat resolution.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: take level n to be the cokernel of l^(n+1) on scalar extension; cokernel
universality supplies every transition and functorial map. Exact evaluation detects
quasi-isomorphisms. Thus this one functor to the whole tower category inverts
quasi-isomorphisms between equivariant K-flat complexes. Resolve and localize to
obtain its pointwise left derivation. Evaluation is exact, so evaluation of the
universal pair is the specified level left derivation. Shifts and cones commute
with the termwise quotient construction, giving its triangulated structure. -/
theorem reductionModel_nonempty {A B : Action σ} {f : Map A B}
    (l : ℕ) [Fact l.Prime] (F : ScalarModel f) :
    Nonempty (ReductionModel l F) := by
  sorry


-- Auto-generated `mk.inj`/`mk.injEq`/`SizeOf` lemmas re-check the huge field types in the kernel.
set_option genInjectivity false in
set_option genSizeOfSpec false in
attribute [local instance] commRingSheafify

/-- Constant ring sheaves retain the ordinary constant-sheaf construction.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
abbrev constantRing (K : CommRingCat.{r}) := (constantSheaf J CommRingCat.{r}).obj K

/-- The actual constant integer-to-p-adic scalar map.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
def integerToPadic (l : ℕ) [Fact l.Prime] :
    constantRing (J := J) (CommRingCat.of (ULift.{r} ℤ)) ⟶
      constantRing (J := J) (CommRingCat.of (ULift.{r} ℤ_[l])) :=
  (constantSheaf J CommRingCat.{r}).map (CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((Int.castRingHom ℤ_[l]).comp ULift.ringEquiv.toRingHom)))

/-- The actual positive-level constant p-adic quotient.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
def padicQuotient (l : ℕ) [Fact l.Prime] (n : ℕ) :
    constantRing (J := J) (CommRingCat.of (ULift.{r} ℤ_[l])) ⟶
      constantRing (J := J) (CommRingCat.of (ULift.{r} (ZMod (l ^ (n + 1))))) :=
  (constantSheaf J CommRingCat.{r}).map (CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((PadicInt.toZModPow (n + 1)).comp ULift.ringEquiv.toRingHom)))

/-- Integral coefficients with their actual constant sheaves and residue maps.
These are presentation isomorphisms, not independently chosen coefficient rings.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
structure IntegralCoefficients (l : ℕ) [Fact l.Prime] where
  Z : Action σ
  C : Action σ
  Q : ℕ → Action σ
  z : Z.ring ≅ constantRing (J := J) (CommRingCat.of (ULift.{r} ℤ))
  c : C.ring ≅ constantRing (J := J) (CommRingCat.of (ULift.{r} ℤ_[l]))
  q : ∀ n : ℕ, (Q n).ring ≅
    constantRing (J := J) (CommRingCat.of (ULift.{r} (ZMod (l ^ (n + 1)))))
  scalar : Map Z C
  scalar_eq : scalar.hom = z.hom ≫ integerToPadic l ≫ c.inv
  quotient : ∀ n : ℕ, Map C (Q n)
  quotient_eq : ∀ n : ℕ, (quotient n).hom = c.hom ≫ padicQuotient l n ≫ (q n).inv
  finite : ∀ n : ℕ, Map Z (Q n)
  finite_eq : ∀ n : ℕ, (finite n).hom = scalar.hom ≫ (quotient n).hom

/-- All constant coefficient rings have their canonical equivariant presentations.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: inverse image commutes with the constant-object functor by its adjunction.
Transport the ring and module operations through that comparison. All residue
maps come from constant ring homomorphisms and therefore commute with this action. -/
theorem integralCoefficients_nonempty (l : ℕ) [Fact l.Prime] :
    Nonempty (IntegralCoefficients (σ := σ) l) := by
  sorry

-- Auto-generated `mk.inj`/`mk.injEq`/`SizeOf` lemmas re-check the huge field types in the kernel.
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The underlying sheaves of sets, retaining the module inverse-image comparison.
Source: Stacks 03D2 (blueprint: lem-pur-equivariant-reduction-calculus). -/
abbrev Action.moduleSets (A : Action σ) : A.Mod ⥤ Sheaf J (Type r) :=
  toSheaf _ ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{r})

-- Auto-generated `mk.inj`/`mk.injEq`/`SizeOf` lemmas re-check the huge field types in the kernel.
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The regular module with its specified semilinear ring action. The section
isomorphism is linear into the ring acting on itself; the last equation fixes the action.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
structure UnitPresentation (A : Action σ) where
  M : A.EqMod
  sections : A.moduleSets.obj M.carrier ≅
    (sheafCompose J (CategoryTheory.forget CommRingCat.{r})).obj A.ring
  linear : ∀ (U : Cᵒᵖ) (a : A.ring.obj.obj U) (m : M.carrier.val.obj U),
    sections.hom.hom.app U (a • m) = a * (@id (A.ring.obj.obj U) (sections.hom.hom.app U m))
  action : A.moduleSets.map M.str.hom ≫ sections.hom =
    A.lift.moduleUnderlying.hom.app M.carrier ≫ σ.functor.map sections.hom ≫
      A.lift.ringUnderlying.hom

/-- The equivariant regular module exists with its canonical normalization.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: use the ring sheaf acting on itself by multiplication. Its algebraic inverse
image is the regular inverse-image ring module, and the given ring identification
is linear. Its multiplication graph gives the displayed linearity and action equation. -/
theorem unitPresentation_nonempty (A : Action σ) : Nonempty (UnitPresentation A) := by
  let U := unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A.ring)
  let e : A.lift.modules.obj U ≅ U :=
    CochainTensorComparison.UnitConstruction.unitIso A.ring A.ring σ.functor A.lift
  refine ⟨{ M := IsoAlgebra.mk U e
            sections := Iso.refl _
            linear := ?_
            action := ?_ }⟩
  · intro W a m
    rfl
  · simp only [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.comp_id]
    ext W x
    rfl

-- Auto-generated `mk.inj`/`mk.injEq`/`SizeOf` lemmas re-check the huge field types in the kernel.
set_option genInjectivity false in
set_option genSizeOfSpec false in
universe t
open AlgebraicGeometry

/-- The sheaf of sets of units used by the recorded Kummer sequence.
Source: Stacks 03PL (blueprint: lem-pur-equivariant-reduction-calculus). -/
abbrev unitsSets (T : Scheme.{t}) :=
  (sheafCompose (Scheme.ProEt.topology T)
    (CategoryTheory.forget AddCommGrpCat.{t + 1})).obj (Scheme.proEtaleUnitsSheaf T)

/-- A scheme automorphism acts on units by the identity on the sections of the
unchanged test scheme. This uniquely specifies the canonical units comparison.
Source: Stacks 03PL (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: postcomposition changes only a test object's structure map to T, not its
underlying scheme or its global units. The identity on these units is natural;
postcomposition with the inverse is its inverse. Sectionwise equality gives uniqueness. -/
theorem unitsAction_existsUnique (T : Scheme.{t}) (g : T ≅ T) :
    ∃! e : (Scheme.isoSectionwiseInverseImage g.hom (Type (t + 1))).obj
        (unitsSets T) ≅ unitsSets T,
      ∀ (V : T.ProEtᵒᵖ) (x : ((Scheme.isoSectionwiseInverseImage g.hom
          (Type (t + 1))).obj (unitsSets T)).obj.obj V),
        HEq (e.hom.hom.app V x) x := by
  let e : (Scheme.isoSectionwiseInverseImage g.hom (Type (t + 1))).obj
      (unitsSets T) ≅ unitsSets T :=
    ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _))
  refine ⟨e, ?_, ?_⟩
  · intro V x
    rfl
  · intro e' he'
    apply Iso.ext
    apply ObjectProperty.hom_ext
    ext V x
    exact eq_of_heq (he' V x)

/-- The canonical comparison characterized in `unitsAction_existsUnique`.
Source: Stacks 03PL (blueprint: lem-pur-equivariant-reduction-calculus). -/
def unitsAction (T : Scheme.{t}) (g : T ≅ T) :=
  (unitsAction_existsUnique T g).exists.choose

-- Auto-generated `mk.inj`/`mk.injEq`/`SizeOf` lemmas re-check the huge field types in the kernel.
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The actual equivariant Kummer sequence, with the existing kernel sheaves and
power transitions. The structure equation specifies the natural scheme action
on units; the monic inclusions then specify the action on roots.
Source: Stacks 03PL, blueprint (3) (blueprint: lem-pur-equivariant-reduction-calculus). -/
structure KummerPresentation (T : Scheme.{t}) (g : T ≅ T)
    (τ : Sheaf (Scheme.ProEt.topology T) (Type (t + 1)) ≌
      Sheaf (Scheme.ProEt.topology T) (Type (t + 1)))
    (s : τ.functor ≅ Scheme.isoSectionwiseInverseImage g.hom (Type (t + 1)))
    (l : ℕ) [Fact l.Prime] (P : IntegralCoefficients (σ := τ) l) where
  G : P.Z.EqMod
  units : P.Z.ab.obj G ≅ Scheme.proEtaleUnitsSheaf T
  action : P.Z.moduleSets.map G.str.hom ≫
      (sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{t + 1})).map units.hom =
    P.Z.lift.moduleUnderlying.hom.app G.carrier ≫
      τ.functor.map
        ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{t + 1})).map units.hom) ≫
      s.hom.app (unitsSets T) ≫ (unitsAction T g).hom
  U : ℕᵒᵖ ⥤ P.C.EqMod
  roots : U ⋙ P.C.ab ≅ Scheme.proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)
  inclusion : ∀ n : ℕ, P.scalar.eqRestrict.obj (U.obj (op n)) ⟶ G
  inclusion_eq : ∀ n : ℕ, P.Z.ab.map (inclusion n) ≫ units.hom =
    roots.hom.app (op n) ≫ Scheme.proEtaleRootsOfUnityInclusion T (l ^ (n + 1))
  zero : ∀ n : ℕ, inclusion n ≫ (l ^ (n + 1) • 𝟙 G) = 0
  exact : ∀ n : ℕ,
    (ShortComplex.mk (inclusion n) (l ^ (n + 1) • 𝟙 G) (zero n)).ShortExact

/-- Kummer exactness lifts to actual semilinear module sheaves.
Source: Stacks 03PL, blueprint (3) (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: units carry their canonical integral action; roots are the recorded kernel
of the power map. Their l-power torsion gives the canonical action of Z_l through
Z/l^(n+1). Postcomposition by the scheme automorphism respects multiplication,
powers and these inclusions. Invertibility of l makes the power map locally
surjective by the finite etale root cover, also a pro-etale cover. Kernels and
cokernels are created by exact fixed-pair forgetting. The recorded power maps
on roots are linear, equivariant and compose to the specified root tower. -/
theorem kummerPresentation_nonempty (T : Scheme.{t}) (g : T ≅ T)
    (τ : Sheaf (Scheme.ProEt.topology T) (Type (t + 1)) ≌
      Sheaf (Scheme.ProEt.topology T) (Type (t + 1)))
    (s : τ.functor ≅ Scheme.isoSectionwiseInverseImage g.hom (Type (t + 1)))
    (l : ℕ) [Fact l.Prime] [∀ x : T, Invertible (l : T.residueField x)]
    (P : IntegralCoefficients (σ := τ) l) :
    Nonempty (KummerPresentation T g τ s l P) := by
  sorry

-- Auto-generated `mk.inj`/`mk.injEq`/`SizeOf` lemmas re-check the huge field types in the kernel.
set_option genInjectivity false in
set_option genSizeOfSpec false in
universe u' v'

-- Auto-generated `mk.inj`/`mk.injEq`/`SizeOf` lemmas re-check the huge field types in the kernel.
set_option genInjectivity false in
set_option genSizeOfSpec false in
attribute [instance] InverseImage.leftExact

section Pullback
variable {D : Type u'} [Category.{v'} D] [EssentiallySmall.{r} D]
  {K : GrothendieckTopology D} {τ : Sheaf K (Type r) ≌ Sheaf K (Type r)}
  {A : Action σ} {B : Action τ}

/-- Geometric inverse image is additive.
Source: Stacks 03D2, blueprint (2)
(blueprint: lem-pur-equivariant-reduction-calculus).
Proof: the underlying module-addition graph transports addition of maps through
inverse image, and the commuting comparison does not change these maps. -/
theorem InverseImage.additive (H : InverseImage A B) : H.eqPullback.Additive := by
  have := algebraicImage_additive H.algebraic
  exact IsoAlgebra.additive_mapOfNatIso _

attribute [instance] InverseImage.additive

end Pullback


section RingedPullback
variable {D : Type u'} [Category.{v'} D] [EssentiallySmall.{r} D]
  {K : GrothendieckTopology D} {τ : Sheaf K (Type r) ≌ Sheaf K (Type r)}
  {A : Action σ} {B V : Action τ}

end RingedPullback

section ScalarPullback
variable {D : Type u'} [Category.{v'} D] [EssentiallySmall.{r} D]
  {K : GrothendieckTopology D} {τ : Sheaf K (Type r) ≌ Sheaf K (Type r)}
  {A B : Action σ} {A' B' : Action τ}

/-- A coefficient square over a geometric inverse image. The equality of the
set-valued functors and commuting comparisons means the same geometric morphism
is used on the two coefficient rings.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
structure CoefficientSquare (f : Map A B) (f' : Map A' B')
    (H : InverseImage A A') (I : InverseImage B B') : Prop where
  functor_eq : H.L = I.L
  comm_eq : HEq H.comm I.comm
  ring_square : HEq
    (H.algebraic.ringUnderlying.hom ≫
      (sheafCompose K (CategoryTheory.forget CommRingCat.{r})).map f'.hom)
    (I.L.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{r})).map f.hom) ≫
      I.algebraic.ringUnderlying.hom)

-- Auto-generated `mk.inj`/`mk.injEq`/`SizeOf` lemmas re-check the huge field types in the kernel.
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Postcomposition with exact inverse image preserves finite colimits of towers.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
instance InverseImage.towerColimits (I : InverseImage B B') :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ B.EqMod B'.EqMod).obj
      I.eqPullback) := ⟨fun _ _ _ ↦ inferInstance⟩

-- Auto-generated `mk.inj`/`mk.injEq`/`SizeOf` lemmas re-check the huge field types in the kernel.
set_option genInjectivity false in
set_option genSizeOfSpec false in
end ScalarPullback


section Forgetting
variable {A B : Action σ} {f : Map A B} (F : ScalarModel f)

/-- Postcomposition with exact fixed-pair forgetting preserves finite colimits.
Source: blueprint (2) (blueprint: lem-pur-equivariant-reduction-calculus). -/
instance Action.towerForget_colimits (A : Action σ) :
    PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A.EqMod A.Mod).obj A.forget) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

-- Auto-generated `mk.inj`/`mk.injEq`/`SizeOf` lemmas re-check the huge field types in the kernel.
set_option genInjectivity false in
set_option genSizeOfSpec false in
end Forgetting

/-- The positive Kummer boundary equation after exact forgetting, including the
canonical single, shift and shift-addition maps. The sequence on the right is the
image of the original short exact sequence under the exact functor.
Source: blueprint (3)-(4), node proof Steps 10--12
(blueprint: lem-pur-equivariant-reduction-calculus). -/
@[irreducible] def IsPositiveBoundaryAfterForgetting
    {A₀ : Type a₀} [Category.{h₀} A₀] [Abelian A₀] [HasDerivedCategory.{w₀} A₀]
    {A₁ : Type a₁} [Category.{h₁} A₁] [Abelian A₁] [HasDerivedCategory.{w₁} A₁]
    (L : A₀ ⥤ A₁) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {S : ShortComplex A₀} (hS : S.ShortExact)
    (b : ((DerivedCategory.singleFunctor A₀ 0).obj S.X₃)⟦(1 : ℤ)⟧ ⟶
      ((DerivedCategory.singleFunctor A₀ 0).obj S.X₁)⟦(2 : ℤ)⟧) : Prop :=
  ((L.mapDerivedCategorySingleFunctor 0).inv.app S.X₃)⟦(1 : ℤ)⟧' ≫
      (L.mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.singleFunctor A₀ 0).obj S.X₃) ≫
      L.mapDerivedCategory.map b ≫
      (L.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
        ((DerivedCategory.singleFunctor A₀ 0).obj S.X₁) ≫
      ((L.mapDerivedCategorySingleFunctor 0).hom.app S.X₁)⟦(2 : ℤ)⟧' =
    (ShortComplex.ShortExact.singleδ (hS.map_of_exact L))⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd' (DerivedCategory A₁) (1 : ℤ) 1 2 rfl).inv.app
        ((DerivedCategory.singleFunctor A₁ 0).obj (L.obj S.X₁))

-- Auto-generated `mk.inj`/`mk.injEq`/`SizeOf` lemmas re-check the huge field types in the kernel.
set_option genInjectivity false in
set_option genSizeOfSpec false in
universe w w'

set_option backward.defeqAttrib.useBackward true in
/-- Shift compatibility carries a shifted degree-one map through shift addition.
Source: Mathlib's `Functor.commShiftIso_add'`; node proof Step 12
(blueprint: lem-pur-equivariant-reduction-calculus). -/
private theorem map_shift_boundary
    {C : Type u} [Category.{v} C] [HasShift C ℤ]
    {D : Type u'} [Category.{v'} D] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] {X Y : C} (f : X ⟶ Y⟦(1 : ℤ)⟧) :
    (F.commShiftIso (1 : ℤ)).inv.app X ≫
      F.map (f⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd' C (1 : ℤ) 1 2 rfl).inv.app Y) ≫
      (F.commShiftIso (2 : ℤ)).hom.app Y =
    (F.map f ≫ (F.commShiftIso (1 : ℤ)).hom.app Y)⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd' D (1 : ℤ) 1 2 rfl).inv.app (F.obj Y) := by
  rw [F.commShiftIso_add' (show (1 : ℤ) + 1 = 2 from rfl)]
  simp only [Functor.CommShift.isoAdd'_hom_app, Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc ((shiftFunctorAdd' C (1 : ℤ) 1 2 rfl).inv.app Y)
    ((shiftFunctorAdd' C (1 : ℤ) 1 2 rfl).hom.app Y)]
  simp only [Iso.inv_hom_id_app, F.map_id, Category.id_comp]
  rw [F.commShiftIso_hom_naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc]

set_option backward.defeqAttrib.useBackward true in
/-- Reassociated form of `map_shift_boundary`, stated directly (the `@[reassoc]` attribute
spent about 19 s generating it). -/
private theorem map_shift_boundary_assoc
    {C : Type u} [Category.{v} C] [HasShift C ℤ]
    {D : Type u'} [Category.{v'} D] [HasShift D ℤ]
    (F : C ⥤ D) [F.CommShift ℤ] {X Y : C} (f : X ⟶ Y⟦(1 : ℤ)⟧)
    {Z : D} (h : (F.obj Y)⟦(2 : ℤ)⟧ ⟶ Z) :
    (F.commShiftIso (1 : ℤ)).inv.app X ≫
      F.map (f⟦(1 : ℤ)⟧' ≫ (shiftFunctorAdd' C (1 : ℤ) 1 2 rfl).inv.app Y) ≫
      (F.commShiftIso (2 : ℤ)).hom.app Y ≫ h =
    (F.map f ≫ (F.commShiftIso (1 : ℤ)).hom.app Y)⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd' D (1 : ℤ) 1 2 rfl).inv.app (F.obj Y) ≫ h := by
  have e := congrArg (fun k ↦ k ≫ h) (map_shift_boundary F f)
  simpa only [Category.assoc] using e

set_option backward.defeqAttrib.useBackward true in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 1000000 in
-- The concrete Kummer square unfolds large derived functor expressions.
set_option backward.defeqAttrib.useBackward true in
/-- Canonical commutation of abelian inverse image with underlying sets, normalized
by the two recorded inverse-image units. The direct images commute with forgetting
by their sectionwise definition.
Source: Stacks 03D2, 03PL (blueprint: lem-pur-equivariant-reduction-calculus).
Proof: inverse image preserves finite limits and colimits, hence the group operation
graphs. The inverse image of the underlying set sheaf therefore carries precisely
the inverse-image abelian group. The adjunction units fix the comparison uniquely;
the analogous construction with the inverse comparison supplies its inverse. -/
theorem abelianSetsComparison_existsUnique {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ∃! e : Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{t + 1} ⋙
        sheafCompose (Scheme.ProEt.topology X)
          (CategoryTheory.forget AddCommGrpCat.{t + 1}) ≅
      sheafCompose (Scheme.ProEt.topology Y)
        (CategoryTheory.forget AddCommGrpCat.{t + 1}) ⋙
          Scheme.proEtaleSheafInverseImage f (Type (t + 1)),
      ∀ M : Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{t + 1},
        (Scheme.proEtaleSheafAdjunction f (Type (t + 1))).unit.app
            ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{t + 1})).obj M) ≫
          (Scheme.proEtaleSheafDirectImage f (Type (t + 1))).map (e.inv.app M) =
        (sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{t + 1})).map
          ((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{t + 1}).unit.app M) := by
  let : RepresentablyFlat (Scheme.proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
  let : PreservesFilteredColimitsOfSize.{t, t + 1}
      (CategoryTheory.forget AddCommGrpCat.{t + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{t + 1, t + 1, t, t + 1} _
  let e := sheafPullbackForgetIso (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (Scheme.proEtaleBaseChange f) (CategoryTheory.forget AddCommGrpCat.{t + 1})
  have he : ∀ M : Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{t + 1},
      (Scheme.proEtaleSheafAdjunction f (Type (t + 1))).unit.app
          ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{t + 1})).obj M) ≫
        (Scheme.proEtaleSheafDirectImage f (Type (t + 1))).map (e.inv.app M) =
      (sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{t + 1})).map
        ((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{t + 1}).unit.app M) := by
    intro M
    have h : (sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{t + 1})).map
          ((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{t + 1}).unit.app M) ≫
        (Scheme.proEtaleSheafDirectImage f (Type (t + 1))).map (e.hom.app M) =
      (Scheme.proEtaleSheafAdjunction f (Type (t + 1))).unit.app
        ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{t + 1})).obj M) :=
      sheafPullbackForgetIso_unit (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
        (Scheme.proEtaleBaseChange f) (CategoryTheory.forget AddCommGrpCat.{t + 1}) M
    clear_value e
    rw [← h, Category.assoc, ← Functor.map_comp, e.hom_inv_id_app,
      CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  clear_value e
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext_inv
  apply NatTrans.ext
  funext M
  apply ((Scheme.proEtaleSheafAdjunction f (Type (t + 1))).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact (he' M).trans (he M).symm


/-- The unit-normalized underlying-set comparison of abelian inverse image.
Source: Stacks 03D2 (blueprint: lem-pur-equivariant-reduction-calculus). -/
def abelianSetsComparison {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (abelianSetsComparison_existsUnique f).exists.choose

-- Auto-generated `mk.inj`/`mk.injEq`/`SizeOf` lemmas re-check the huge field types in the kernel.
set_option genInjectivity false in
set_option genSizeOfSpec false in
end SheafOfModules.EquivariantReduction
