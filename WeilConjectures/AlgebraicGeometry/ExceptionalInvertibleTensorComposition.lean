/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection
public import WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicallySmooth
public import WeilConjectures.SixFunctors.Etale.Derived.Identity
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.CompUnit
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteExceptionalComposition
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekInvertible
public import WeilConjectures.SixFunctors.Etale.Derived.InvertiblePullback

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.SmoothPurity.ExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperOpenInterchange
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitudeProEtaleModule
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportProjectionApplication
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.HomCongr
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapDualizable
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.SixFunctors.Supporting.PullbackTorAmplitude
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientFlatModel
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.AlgebraicGeometry.Finite.FiniteTensorConstructibleCohomology
import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactProjectionFormula
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import WeilConjectures.AlgebraicGeometry.Projection.ProjectionComparisonEtaleProEtale
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSiteCoherence
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.HomCongr
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoprojectionMate
public import WeilConjectures.AlgebraicGeometry.ExceptionalIdentityMate
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorCompositionEquation
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExchangeProjection

/-!
# Exceptional co-projection for invertible tensor factors

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-the-trace-map-in-top-degree/sk-cor-trace/sk-thm-regular/
sk-thm-regular.proof.md, Step 4(iii), with the projection/counit construction of
sk-lem-coprojection and the exceptional compositor of sk-prop-sp-composition.
(blueprint: lem-pur-exceptional-invertible-tensor-composition).

The maps and equations are written in the canonical finite etale-origin coordinates.
The fully faithful comparison, with its tensor, pullback, compact-support and counit
comparisons, transports these equations to the small pro-etale constructible category.
In particular, no right adjoint on the ambient pro-etale derived category is used.
The law predicates below expand to equations of the specified maps, not existence
of unspecified isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X Y Z : Scheme.{u}}
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]

/-- Theta is the specified tensor/counit transpose, in pullback-first order.
Source: sk-thm-regular Step 4(iii), the tensor map of def-pur-co-smoothness.
(blueprint: lem-pur-exceptional-invertible-tensor-composition). -/
def exceptionalTensorTheta
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj (dualizingComplex Λ f) ⟶
        (R(f)^![Λ]).obj K :=
  (((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) X).hom.app
    ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).app (dualizingComplex Λ f)) ≫
    dualizingComplexTensorMap Λ f K

/-- The specified action r_w = theta composed with 1 tensor w.
There is no smoothness assumption and w need not be invertible.
Source: sk-thm-regular, Step 4(iii), projection/counit tensor passage.
(blueprint: lem-pur-exceptional-invertible-tensor-composition). -/
def exceptionalCoefficientAction
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (J : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (w : J ⟶ dualizingComplex Λ f) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj J ⟶ (R(f)^![Λ]).obj K :=
  derivedTensorHom (ModuleCat.{u + 1} Λ)
    (𝟙 ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) w ≫ exceptionalTensorTheta Λ f K

/-- The canonical shuffle chi: pullback-tensor, associators and the signed symmetry.
Source: sk-thm-regular, Step 4(iii), projection/counit tensor passage.
(blueprint: lem-pur-exceptional-invertible-tensor-composition). -/
def exceptionalCoefficientShuffle
    (K L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (J :
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (((L((f)^*[ModuleCat.{u + 1} Λ])).obj
      ((((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj (K)).obj (L)))))).obj (J)) ≅ (((derivedTensor
      (ModuleCat.{u + 1} Λ) X).obj ((((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      (((L((f)^*[ModuleCat.{u + 1} Λ])).obj (K)))).obj (J)))).obj (((L((f)^*[ModuleCat.{u + 1}
      Λ])).obj (L)))) :=
  ((derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj J).mapIso (leftDerivedUpperStarTensorIso
      (ModuleCat.{u + 1} Λ) (f) (K) (L)) ≪≫
    (derivedTensorAssociator (ModuleCat.{u + 1} Λ) X (((L((f)^*[ModuleCat.{u + 1} Λ])).obj (K)))
      (((L((f)^*[ModuleCat.{u + 1} Λ])).obj (L))) (J)) ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (((L((f)^*[ModuleCat.{u + 1} Λ])).obj (K)))).mapIso
      (((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) X).app (((L((f)^*[ModuleCat.{u + 1} Λ])).obj
      (L)))).app J) ≪≫
    (derivedTensorAssociator (ModuleCat.{u + 1} Λ) X (((L((f)^*[ModuleCat.{u + 1} Λ])).obj (K)))
      (J) (((L((f)^*[ModuleCat.{u + 1} Λ])).obj (L)))).symm

private theorem tensorHom_right_id
    {K K' : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)} (a : K ⟶ K')
    (L : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    derivedTensorHom A a (𝟙 L) = a ▷ L := by
  simp only [derivedTensorHom, derivedTensor_map_app, derivedTensor_obj_map,
    whiskerLeft_id]
  exact Category.comp_id _

private theorem tensorHom_left_id
    (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A))
    {L L' : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)} (a : L ⟶ L') :
    derivedTensorHom A (𝟙 K) a = K ◁ a := by
  simp only [derivedTensorHom, derivedTensor_map_app, derivedTensor_obj_map,
    id_whiskerRight]
  exact Category.id_comp _

private theorem tensorHom_left_comp
    (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A))
    {L M N : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)}
    (a : L ⟶ M) (b : M ⟶ N) :
    derivedTensorHom A (𝟙 K) (a ≫ b) =
      derivedTensorHom A (𝟙 K) a ≫ derivedTensorHom A (𝟙 K) b := by
  rw [tensorHom_left_id, tensorHom_left_id, tensorHom_left_id, whiskerLeft_comp]

private noncomputable def tensorIso
    {K K' L L' : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)}
    (e : K ≅ K') (d : L ≅ L') :
    ((derivedTensor A T).obj K).obj L ≅ ((derivedTensor A T).obj K').obj L' where
  hom := derivedTensorHom A e.hom d.hom
  inv := derivedTensorHom A e.inv d.inv
  hom_inv_id := by
    rw [derivedTensorHom_comp, e.hom_inv_id, d.hom_inv_id, derivedTensorHom_id]
  inv_hom_id := by
    rw [derivedTensorHom_comp, e.inv_hom_id, d.inv_hom_id, derivedTensorHom_id]

private theorem isoHom_inv {C : Type*} [Category C] {A B : C} (e : A ≅ B) :
    inv e.hom = e.inv := by
  apply IsIso.inv_eq_of_hom_inv_id
  exact e.hom_inv_id

private theorem inverse_square
    {C : Type*} [Category C] {A A' B B' : C}
    (e : A ≅ B) (e' : A' ≅ B') (u : A ⟶ A') (v : B ⟶ B')
    (h : v ≫ e'.inv = e.inv ≫ u) : u ≫ e'.hom = e.hom ≫ v := by
  apply (cancel_epi e.inv).1
  apply (cancel_mono e'.inv).1
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.inv_hom_id_assoc] using h.symm

private theorem inverse_triangle
    {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (u : A ⟶ D) (v : B ⟶ D) (h : e.inv ≫ u = v) :
    e.hom ≫ v = u := by
  rw [← h, Iso.hom_inv_id_assoc]

private theorem inverse_composite
    {C : Type*} [Category C] {A B C' D E : C}
    (a : A ≅ B) (b : A ≅ C') (c : C' ≅ D) (d : D ≅ E) (e : B ≅ E)
    (h : e.hom ≫ d.inv ≫ c.inv = a.inv ≫ b.hom) :
    a.hom = b.hom ≫ c.hom ≫ d.hom ≫ e.inv := by
  have hi : a = b ≪≫ c ≪≫ d ≪≫ e.symm := by
    apply Iso.ext_inv
    apply (cancel_mono b.hom).1
    simpa only [Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] using h.symm
  simpa only [Iso.trans_hom, Iso.symm_hom] using congrArg Iso.hom hi

private theorem inverse_associativity
    {C : Type*} [Category C] {A B C' D E F : C}
    (e : A ≅ B) (d : B ≅ C') (j : A ≅ D) (e' : D ≅ E)
    (r : E ≅ F) (a : F ≅ C')
    (h : r.inv ≫ e'.inv ≫ j.inv = a.hom ≫ d.inv ≫ e.inv) :
    e.hom ≫ d.hom = j.hom ≫ e'.hom ≫ r.hom ≫ a.hom := by
  have hi : (e ≪≫ d).symm = (j ≪≫ e' ≪≫ r ≪≫ a).symm := by
    apply Iso.ext
    apply (cancel_epi a.hom).1
    simpa only [Iso.symm_hom, Iso.trans_inv, Iso.hom_inv_id_assoc,
      Category.assoc] using h.symm
  simpa only [Iso.symm_inv, Iso.trans_hom, Category.assoc] using
    congrArg Iso.inv hi

private theorem braided_shuffle
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    (A B U J W : C) (δ : U ≅ A ⊗ B) (w : J ⟶ W) :
    δ.hom ▷ J ≫ (α_ A B J).hom ≫ A ◁ (β_ B J).hom ≫
      (α_ A J B).inv ≫ (A ◁ w) ▷ B ≫ (β_ A W).hom ▷ B ≫
      (α_ W A B).hom ≫ W ◁ δ.inv = U ◁ w ≫ (β_ U W).hom := by
  rw [← associator_inv_naturality_middle_assoc,
    ← whiskerLeft_comp_assoc, ← BraidedCategory.braiding_naturality_right]
  rw [whiskerLeft_comp_assoc, ← associator_naturality_right_assoc,
    ← whisker_exchange_assoc, ← BraidedCategory.braiding_tensor_left_hom_assoc,
    BraidedCategory.braiding_naturality_left_assoc,
    ← whiskerLeft_comp, δ.hom_inv_id, whiskerLeft_id, Category.comp_id]

private theorem braided_action_naturality
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [BraidedCategory C]
    (P : D ⥤ C) (G : D ⥤ C) (W : C)
    (θ : ∀ K, W ⊗ P.obj K ⟶ G.obj K)
    (hθ : ∀ {K K'} (a : K ⟶ K'), W ◁ P.map a ≫ θ K' = θ K ≫ G.map a)
    {K K' : D} (a : K ⟶ K') (J : C) (w : J ⟶ W) :
    P.map a ▷ J ≫ P.obj K' ◁ w ≫ (β_ (P.obj K') W).hom ≫ θ K' =
      P.obj K ◁ w ≫ (β_ (P.obj K) W).hom ≫ θ K ≫ G.map a := by
  rw [← whisker_exchange_assoc, BraidedCategory.braiding_naturality_left_assoc,
    hθ]

private theorem braided_action_tensor
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [BraidedCategory C] [MonoidalCategory D]
    (P : D ⥤ C) (G : D ⥤ C) (W : C)
    (θ : ∀ K, W ⊗ P.obj K ⟶ G.obj K)
    (τ : ∀ K L, G.obj K ⊗ P.obj L ⟶ G.obj (K ⊗ L))
    (δ : ∀ K L, P.obj (K ⊗ L) ≅ P.obj K ⊗ P.obj L)
    (hθ : ∀ K L, θ K ▷ P.obj L ≫ τ K L =
      (α_ W (P.obj K) (P.obj L)).hom ≫ W ◁ (δ K L).inv ≫ θ (K ⊗ L))
    (K L : D) (J : C) (w : J ⟶ W) :
    P.obj (K ⊗ L) ◁ w ≫ (β_ (P.obj (K ⊗ L)) W).hom ≫ θ (K ⊗ L) =
      (δ K L).hom ▷ J ≫ (α_ (P.obj K) (P.obj L) J).hom ≫
        P.obj K ◁ (β_ (P.obj L) J).hom ≫ (α_ (P.obj K) J (P.obj L)).inv ≫
        (P.obj K ◁ w ≫ (β_ (P.obj K) W).hom ≫ θ K) ▷ P.obj L ≫ τ K L := by
  simp only [comp_whiskerRight, Category.assoc]
  rw [hθ]
  have hb := braided_shuffle (P.obj K) (P.obj L) (P.obj (K ⊗ L)) J W (δ K L) w
  simpa only [Category.assoc] using (congrArg (fun z ↦ z ≫ θ (K ⊗ L)) hb).symm

private theorem braided_action_unit
    {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C]
    (U J W : C) (η : U ≅ 𝟙_ C) (w : J ⟶ W) :
    U ◁ w ≫ (β_ U W).hom ≫ W ◁ η.hom ≫ (ρ_ W).hom =
      η.hom ▷ J ≫ (λ_ J).hom ≫ w := by
  rw [← BraidedCategory.braiding_naturality_left_assoc,
    braiding_tensorUnit_left, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, whisker_exchange_assoc,
    leftUnitor_naturality]

private theorem projectionTensorMap_unit
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {P : D ⥤ C} {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (π : ∀ A B, F.obj A ⊗ B ⟶ F.obj (A ⊗ P.obj B))
    [∀ A B, IsIso (π A B)] (η : P.obj (𝟙_ D) ≅ 𝟙_ C)
    (hunit : ∀ A, π A (𝟙_ D) ≫ F.map (A ◁ η.hom ≫ (ρ_ A).hom) =
      (ρ_ (F.obj A)).hom) (K : D) :
    adj.projectionTensorMap π K (𝟙_ D) ≫ G.map (ρ_ K).hom =
      G.obj K ◁ η.hom ≫ (ρ_ (G.obj K)).hom := by
  let q (A : C) := (ρ_ A).inv ≫ A ◁ η.inv
  have hπ (A : C) : F.map (q A) ≫ inv (π A (𝟙_ D)) = (ρ_ (F.obj A)).inv := by
    rw [IsIso.comp_inv_eq, Iso.eq_inv_comp, ← hunit A, Category.assoc,
      ← F.map_comp]
    simp only [q, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← whiskerLeft_comp, η.hom_inv_id, whiskerLeft_id, F.map_id, Category.comp_id]
  have ht : q (G.obj K) ≫ adj.projectionTensorMap π K (𝟙_ D) =
      G.map (ρ_ K).inv := by
    apply (adj.homEquiv _ _).symm.injective
    dsimp only [Adjunction.projectionTensorMap]
    rw [← adj.homEquiv_naturality_left, Equiv.symm_apply_apply,
      Adjunction.homEquiv_counit, adj.counit_naturality]
    change F.map (q (G.obj K)) ≫ inv (π (G.obj K) (𝟙_ D)) ≫
      adj.counit.app K ▷ (𝟙_ D) = adj.counit.app K ≫ (ρ_ K).inv
    rw [← Category.assoc, hπ]
    exact (rightUnitor_inv_naturality _).symm
  apply (cancel_epi (q (G.obj K))).1
  calc
    q (G.obj K) ≫ (adj.projectionTensorMap π K (𝟙_ D) ≫ G.map (ρ_ K).hom) =
        G.map (ρ_ K).inv ≫ G.map (ρ_ K).hom := by rw [← Category.assoc, ht]
    _ = 𝟙 _ := by rw [← G.map_comp, Iso.inv_hom_id, G.map_id]
    _ = q (G.obj K) ≫ (G.obj K ◁ η.hom ≫ (ρ_ (G.obj K)).hom) := by
      simp only [q, Category.assoc, ← whiskerLeft_comp_assoc,
        Iso.inv_hom_id, whiskerLeft_id_assoc, Iso.inv_hom_id]

-- Adapted from the source library instance-congruence proof constructor.

private meta def tensorInstanceCongrHEq
    (cache : IO.Ref (Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr))
    (pairs : Array (Lean.Expr × Lean.Expr × Lean.Expr)) :
    Nat → Lean.Expr → Lean.Expr → Lean.MetaM Lean.Expr
  | 0, a, b => do
    throwError "congruence depth exhausted: {a} versus {b}"
  | n + 1, a, b => do
    if let some h := (← cache.get).get? (a, b) then return h
    let compute : Lean.MetaM Lean.Expr := do
      let a := a.consumeMData
      let b := b.consumeMData
      let a ← if a.isMVar then Lean.instantiateMVars a else pure a
      let b ← if b.isMVar then Lean.instantiateMVars b else pure b
      let normalize (e : Lean.Expr) : Lean.Expr :=
        match e.headBeta with
        | .letE _ _ value body _ => body.instantiate1 value
        | e' =>
          if (e'.isAppOfArity ``CategoryTheory.Functor.obj 6 ||
              e'.isAppOfArity ``CategoryTheory.Functor.map 8) &&
              (e'.getArg! 4).isAppOfArity ``CategoryTheory.Functor.id 2 then
            e'.getAppArgs.back!
          else e'
      let a' := normalize a
      let b' := normalize b
      if a != a' || b != b' then
        return ← tensorInstanceCongrHEq cache pairs n a' b'
      for (x, y, h) in pairs do
        if a == x && b == y then return h
        if a == y && b == x then return ← Lean.Meta.mkAppM ``HEq.symm #[h]
      if a == b then
        return ← Lean.Meta.mkHEqRefl a
      if (← Lean.Meta.isProof a) && (← Lean.Meta.isProof b) then
        return ← Lean.Meta.mkAppM ``proof_irrel_heq #[a, b]
      if let .lam name type body info := a then
        if let .lam name' type' body' info' := b then
          let htype ← tensorInstanceCongrHEq cache pairs n type type'
          let htype ← AlgebraicGeometry.ProEtale.instanceCongrToEq htype
          return ← Lean.Meta.withLocalDecl name info type fun x =>
            Lean.Meta.withLocalDecl name' info' type' fun y => do
              let hxy ← Lean.Meta.mkHEq x y
              Lean.Meta.withLocalDeclD `hxy hxy fun hxy => do
                let h ← tensorInstanceCongrHEq cache (pairs.push (x, y, hxy)) n
                  (body.instantiate1 x) (body'.instantiate1 y)
                let h ← Lean.Meta.mkLambdaFVars #[x, y, hxy] h
                Lean.Meta.mkAppM ``Function.hfunext #[htype, h]
      let expandProjection (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
        let fn := e.getAppFn
        let .proj typeName index major := fn | return e
        let info := Lean.getStructureInfo (← Lean.getEnv) typeName
        let p ← Lean.Meta.mkProjection major info.fieldNames[index]!
        return Lean.mkAppN p e.getAppArgs
      -- Restrict definitional fallback to projections of local instance parameters.
      let isLocalProjection (e : Lean.Expr) : Bool :=
        match e.getAppFn with
        | .proj _ _ major => major.isFVar && e.getAppNumArgs == 0
        | _ => false
      if isLocalProjection a || isLocalProjection b then
        if ← Lean.Meta.withTransparency .reducible (Lean.Meta.isDefEq a b) then
          return ← Lean.Meta.mkHEqRefl a
      let a' ← expandProjection a
      let b' ← expandProjection b
      if a != a' || b != b' then
        return ← tensorInstanceCongrHEq cache pairs n a' b'
      let af := a.getAppFn.consumeMData
      let bf := b.getAppFn.consumeMData
      -- The generic coefficient proof can expose the small site as a Comma type.
      -- This test unfolds only those site aliases; the returned term is kernel checked.
      if af.isConstOf ``AlgebraicGeometry.Scheme.Etale ||
          bf.isConstOf ``AlgebraicGeometry.Scheme.Etale ||
          af.isConstOf ``AlgebraicGeometry.Scheme.instCategoryEtale ||
          bf.isConstOf ``AlgebraicGeometry.Scheme.instCategoryEtale then
        if ← Lean.Meta.withTransparency .all (Lean.Meta.isDefEq a b) then
          return ← Lean.Meta.mkHEqRefl a
      let aa := a.getAppArgs
      let ba := b.getAppArgs
      if af.isConstOf ``CategoryTheory.Preadditive.mk &&
          bf.isConstOf ``CategoryTheory.Abelian.toPreadditive then
        return ← Lean.Meta.mkHEqRefl a
      if bf.isConstOf ``CategoryTheory.Preadditive.mk &&
          af.isConstOf ``CategoryTheory.Abelian.toPreadditive then
        return ← Lean.Meta.mkHEqRefl a
      if af.isConstOf ``CategoryTheory.Functor.mk &&
          bf.isConstOf ``CategoryTheory.Functor.ShiftSequence.sequence then
        return ← Lean.Meta.mkHEqRefl a
      if bf.isConstOf ``CategoryTheory.Functor.mk &&
          af.isConstOf ``CategoryTheory.Functor.ShiftSequence.sequence then
        return ← Lean.Meta.mkHEqRefl a
      let sameHead ← if af == bf then pure true else
        if af.isConst && bf.isConst && af.constName! == bf.constName! then
          Lean.Meta.isDefEq af bf
        else pure false
      if sameHead && aa.size ≥ 4 && ba.size ≥ 4 &&
          (af.isConstOf ``CategoryTheory.Functor.obj ||
            af.isConstOf ``CategoryTheory.Functor.map ||
            af.isConstOf ``CategoryTheory.NatTrans.app) then
        let sameDomain ← Lean.Meta.isDefEq aa[0]! ba[0]!
        let sameCodomain ← Lean.Meta.isDefEq aa[2]! ba[2]!
        if !sameDomain || !sameCodomain then
          let reduceComponent (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
            let some e' ← Lean.Meta.withTransparency .instances
                (Lean.Meta.unfoldDefinition? e (ignoreTransparency := true)) | return none
            let some f ← Lean.Meta.withTransparency .all
                (Lean.Meta.reduceProj? e'.getAppFn) | return none
            let e'' := Lean.mkAppN f e'.getAppArgs
            if e'' == e then return none
            return some e''
          if let some a' ← reduceComponent a then
            return ← tensorInstanceCongrHEq cache pairs n a' b
          if let some b' ← reduceComponent b then
            return ← tensorInstanceCongrHEq cache pairs n a b'
      if !sameHead || aa.size != ba.size then
        let isProjection (f : Lean.Expr) : Lean.MetaM Bool := do
          if f.isConst then
            return (← Lean.getProjectionFnInfo? f.constName!).isSome
          return false
        if !(← isProjection af) then
          if let some a' ← Lean.Meta.unfoldDefinition? a (ignoreTransparency := true) then
            return ← tensorInstanceCongrHEq cache pairs n a' b
        if !(← isProjection bf) then
          if let some b' ← Lean.Meta.unfoldDefinition? b (ignoreTransparency := true) then
            return ← tensorInstanceCongrHEq cache pairs n a b'
        let reduceProjection (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
          let some e' ← Lean.Meta.withTransparency .instances
              (Lean.Meta.unfoldDefinition? e (ignoreTransparency := true)) | return none
          let some f ← Lean.Meta.withTransparency .all
              (Lean.Meta.reduceProj? e'.getAppFn) | return none
          let e'' := Lean.mkAppN f e'.getAppArgs
          if e'' == e then return none
          if e''.getAppFn.isProj then
            let .proj typeName index major := e''.getAppFn | return none
            let info := Lean.getStructureInfo (← Lean.getEnv) typeName
            let p ← Lean.Meta.mkProjection major info.fieldNames[index]!
            let e''' := Lean.mkAppN p e''.getAppArgs
            if e''' == e then return none
          return some e''
        if ← isProjection af then
          if let some a' ← reduceProjection a then
            return ← tensorInstanceCongrHEq cache pairs n a' b
        if ← isProjection bf then
          if let some b' ← reduceProjection b then
            return ← tensorInstanceCongrHEq cache pairs n a b'
        throwError "different congruence heads: {a} versus {b}"
      let expandCompositeObj (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
        let args := e.getAppArgs
        if e.isAppOf ``CategoryTheory.Functor.obj && args.size ≥ 2 then
          let functor := args[args.size - 2]!
          if functor.isAppOf ``CategoryTheory.Functor.comp then
            let fs := functor.getAppArgs
            let x ← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj
              #[fs[fs.size - 2]!, args.back!]
            return ← Lean.Meta.mkAppM ``CategoryTheory.Functor.obj #[fs.back!, x]
        return e
      let a' ← expandCompositeObj a
      let b' ← expandCompositeObj b
      if a != a' || b != b' then
        return ← tensorInstanceCongrHEq cache pairs n a' b'
      let build : Lean.MetaM Lean.Expr := do
        let mut first := 0
        while first < aa.size && aa[first]! == ba[first]! do
          first := first + 1
        let f := Lean.mkAppN af (aa.extract 0 first)
        let ct ← Lean.Meta.mkHCongrWithArity f (aa.size - first)
        let mut args := #[]
        for i in [first:aa.size] do
          let h ← tensorInstanceCongrHEq cache pairs n aa[i]! ba[i]!
          let h ← if ct.argKinds[i - first]! == .eq then
            AlgebraicGeometry.ProEtale.instanceCongrToEq h else pure h
          args := args.push aa[i]! |>.push ba[i]! |>.push h
        return Lean.mkAppN ct.proof args
      try build catch err =>
        -- Equal applications can expose their functor parameters differently.
        -- Reduce a component projection before trying to compare those parameters.
        let reduceComponent (e : Lean.Expr) : Lean.MetaM (Option Lean.Expr) := do
          let some e' ← Lean.Meta.withTransparency .instances
              (Lean.Meta.unfoldDefinition? e (ignoreTransparency := true)) | return none
          let some f ← Lean.Meta.withTransparency .all
              (Lean.Meta.reduceProj? e'.getAppFn) | return none
          let e'' := Lean.mkAppN f e'.getAppArgs
          if e'' == e then return none
          return some e''
        if let some a' ← reduceComponent a then
          return ← tensorInstanceCongrHEq cache pairs n a' b
        if let some b' ← reduceComponent b then
          return ← tensorInstanceCongrHEq cache pairs n a b'
        throw err
    let h ← compute
    cache.modify fun m => m.insert (a, b) h
    return h

private meta def exactTensorCongr (proof : Expr) : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let proofType ← instantiateMVars (← inferType proof)
  let cache ← IO.mkRef ({} : Std.HashMap (Expr × Expr) Expr)
  let ds := (← getLCtx).decls.toList.filterMap id
  let coeff ← match target.find? (fun e ↦ e.isAppOf ``ModuleCat) with
    | some e => pure (some e)
    | none => pure ((ds.find? (fun d ↦ d.userName.eraseMacroScopes == `A)).map (·.toExpr))
  if let some coeff := coeff then
    for d in ds do
      if d.type.isAppOf ``AlgebraicGeometry.Scheme then
        let h ← mkAppM ``AlgebraicGeometry.ProEtale.derivedTensorCanonical
          #[coeff, d.toExpr]
        let some (_, lhs, rhs) := (← inferType h).eq? | throwError "expected tensor equality"
        let he ← mkAppM ``heq_of_eq #[h]
        let heSymm ← mkAppM ``HEq.symm #[he]
        cache.modify fun m => (m.insert (lhs, rhs) he).insert (rhs, lhs) heSymm
  for d in ds do
    if d.type.isAppOf ``AlgebraicGeometry.Scheme then
      let e ← mkAppM ``AlgebraicGeometry.Scheme.Etale #[d.toExpr]
      let e' ← withTransparency .all (whnf e)
      let h ← mkHEqRefl e
      cache.modify fun m => (m.insert (e, e') h).insert (e', e) h
      for typ in #[proofType, target] do
        let expanded := typ.find? fun z ↦
          match z.getAppFn with
          | .const n _ => n.toString.endsWith ".Comma" &&
              (z.find? (fun a ↦ a == d.toExpr)).isSome
          | _ => false
        if let some expanded := expanded then
          if ← withTransparency .all (isDefEq e expanded) then
            cache.modify fun m => (m.insert (e, expanded) h).insert (expanded, e) h
  let he ← tensorInstanceCongrHEq cache #[] 200 proofType target
  let e ← mkAppM ``eq_of_heq #[he]
  (← getMainGoal).assign (← mkAppM ``Eq.mp #[e, proof])

private theorem tensorMate_naturality_left
    {K K' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (a : K ⟶ K')
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    derivedTensorHom (ModuleCat.{u + 1} Λ) ((R(f)^![Λ]).map a)
        (𝟙 ((L((f)^*[ModuleCat.{u + 1} Λ])).obj L)) ≫
        rightDerivedUpperShriekTensorMap f K' L =
      rightDerivedUpperShriekTensorMap f K L ≫
        (R(f)^![Λ]).map (derivedTensorHom (ModuleCat.{u + 1} Λ) a (𝟙 L)) := by
  have : ∀ M N, IsIso (((projectionMap (ModuleCat.{u + 1} Λ) f).app M).app N) := fun M N ↦ by
    let : IsIso ((projectionMap (ModuleCat.{u + 1} Λ) f).app M) :=
      NatIso.isIso_app_of_isIso (projectionMap (ModuleCat.{u + 1} Λ) f) M
    exact NatIso.isIso_app_of_isIso ((projectionMap (ModuleCat.{u + 1} Λ) f).app M) N
  simpa only [tensorHom_right_id, tensorHom_left_id] using
    Adjunction.projectionTensorMap_naturality_left
    (rightDerivedUpperShriekAdjunction Λ f) _
    (projectionMap_app_app_naturality_left f) a L

private theorem tensorMate_naturality_right
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {L L' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (a : L ⟶ L') :
    derivedTensorHom (ModuleCat.{u + 1} Λ) (𝟙 ((R(f)^![Λ]).obj K))
        ((L((f)^*[ModuleCat.{u + 1} Λ])).map a) ≫
        rightDerivedUpperShriekTensorMap f K L' =
      rightDerivedUpperShriekTensorMap f K L ≫
        (R(f)^![Λ]).map (derivedTensorHom (ModuleCat.{u + 1} Λ) (𝟙 K) a) := by
  have : ∀ M N, IsIso (((projectionMap (ModuleCat.{u + 1} Λ) f).app M).app N) := fun M N ↦ by
    let : IsIso ((projectionMap (ModuleCat.{u + 1} Λ) f).app M) :=
      NatIso.isIso_app_of_isIso (projectionMap (ModuleCat.{u + 1} Λ) f) M
    exact NatIso.isIso_app_of_isIso ((projectionMap (ModuleCat.{u + 1} Λ) f).app M) N
  simpa only [tensorHom_right_id, tensorHom_left_id] using
    Adjunction.projectionTensorMap_naturality_right
    (rightDerivedUpperShriekAdjunction Λ f) _
    (projectionMap_app_app_naturality_right f) K a

private noncomputable def coefficientActionOfAdjunction
    (adj : rightDerivedLowerShriek A f ⊣ G)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (J : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (w : J ⟶ G.obj (𝟙_ _)) :
    ((derivedTensor A X).obj ((L((f)^*[A])).obj K)).obj J ⟶ G.obj K :=
  derivedTensorHom A (𝟙 _) w ≫
    (((derivedTensorSymmetry A X).hom.app ((L((f)^*[A])).obj K)).app _) ≫
    lowerShriekRightAdjointUnitTensorMap adj K

private noncomputable def coefficientShuffleGeneric
    (K L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) (J :
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (((derivedTensor A X).obj ((L((f)^*[A])).obj (((derivedTensor A Y).obj K).obj L))).obj J) ≅
    (((derivedTensor A X).obj (((derivedTensor A X).obj ((L((f)^*[A])).obj K)).obj J)).obj
        ((L((f)^*[A])).obj L)) :=
  ((derivedTensor A X).flip.obj J).mapIso (leftDerivedUpperStarTensorIso A f K L) ≪≫
    derivedTensorAssociator A X ((L((f)^*[A])).obj K) ((L((f)^*[A])).obj L) J ≪≫
    ((derivedTensor A X).obj ((L((f)^*[A])).obj K)).mapIso
      (((derivedTensorSymmetry A X).app ((L((f)^*[A])).obj L)).app J) ≪≫
    (derivedTensorAssociator A X ((L((f)^*[A])).obj K) J ((L((f)^*[A])).obj L)).symm

private theorem coefficientActionOfAdjunction_naturality
    (adj : rightDerivedLowerShriek A f ⊣ G)
    {K K' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)} (a : K ⟶ K')
    (J : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (w : J ⟶ G.obj (𝟙_ _)) :
    derivedTensorHom A ((L((f)^*[A])).map a) (𝟙 J) ≫
      coefficientActionOfAdjunction f adj K' J w =
    coefficientActionOfAdjunction f adj K J w ≫ G.map a := by
  have : ∀ M N, IsIso (((projectionMap A f).app M).app N) := fun M N ↦ by
    let : IsIso ((projectionMap A f).app M) :=
      NatIso.isIso_app_of_isIso (projectionMap A f) M
    exact NatIso.isIso_app_of_isIso ((projectionMap A f).app M) N
  let := _root_.DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology A)
  simp only [tensorHom_right_id, coefficientActionOfAdjunction, tensorHom_left_id, Category.assoc]
  change _ ▷ J ≫ _ ◁ w ≫ (β_ _ _).hom ≫ _ = _ ◁ w ≫ (β_ _ _).hom ≫ _ ≫ G.map a
  apply braided_action_naturality
  intro B B' b
  exact AlgebraicGeometry.ProEtale.unitTensorNaturality adj _
    (projectionMap_app_app_naturality_right f) b

private theorem coefficientActionOfAdjunction_unit
    (adj : rightDerivedLowerShriek A f ⊣ G)
    (J : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (w : J ⟶ G.obj (𝟙_ _)) :
    coefficientActionOfAdjunction f adj (𝟙_ _) J w =
      derivedTensorHom A (leftDerivedUpperStarUnitIso A f).hom (𝟙 J) ≫
        (derivedTensorLeftUnitor A X J).hom ≫ w := by
  have : ∀ M N, IsIso (((projectionMap A f).app M).app N) := fun M N ↦ by
    let : IsIso ((projectionMap A f).app M) :=
      NatIso.isIso_app_of_isIso (projectionMap A f) M
    exact NatIso.isIso_app_of_isIso ((projectionMap A f).app M) N
  let := _root_.DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology A)
  have hu := projectionTensorMap_unit adj _ (leftDerivedUpperStarUnitIso A f)
    (projectionMap_rightUnitality A f) (𝟙_ _)
  have hunitors : (λ_ (𝟙_ (_root_.DerivedCategory
      (Sheaf Y.smallEtaleTopology A)))).hom = (ρ_ (𝟙_ _)).hom := by monoidal
  simp only [coefficientActionOfAdjunction, lowerShriekRightAdjointUnitTensorMap,
    tensorHom_left_id, tensorHom_right_id, hunitors]
  rw [hu]
  change _ ◁ w ≫ (β_ _ _).hom ≫ _ ◁ _ ≫ (ρ_ _).hom = _ ▷ J ≫ (λ_ J).hom ≫ w
  exact braided_action_unit _ J _ (leftDerivedUpperStarUnitIso A f) w

private theorem coefficientActionOfAdjunction_tensor
    (adj : rightDerivedLowerShriek A f ⊣ G) (hassoc :
      ProjectionMapAssociativity A f)
    (K L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (J : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (w : J ⟶ G.obj (𝟙_ _)) :
    coefficientActionOfAdjunction f adj (((derivedTensor A Y).obj K).obj L) J
      w =
      (coefficientShuffleGeneric f K L J).hom ≫
        derivedTensorHom A (coefficientActionOfAdjunction f adj K J w) (𝟙
      ((L((f)^*[A])).obj L)) ≫
          lowerShriekRightAdjointTensorMap adj K L := by
  have : ∀ M N, IsIso (((projectionMap A f).app M).app N) := fun M N ↦ by
    let : IsIso ((projectionMap A f).app M) :=
      NatIso.isIso_app_of_isIso (projectionMap A f) M
    exact NatIso.isIso_app_of_isIso ((projectionMap A f).app M) N
  let := _root_.DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology A)
  have hθ := fun K L ↦ AlgebraicGeometry.ProEtale.unitTensorAssoc adj _
    (projectionMap_app_app_naturality_left f)
    (fun K L ↦ (leftDerivedUpperStarTensorIso A f K L).hom) hassoc.assoc K L
  simp only [coefficientActionOfAdjunction, tensorHom_left_id, tensorHom_right_id,
    coefficientShuffleGeneric, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    derivedTensorAssociator_eq, derivedTensor_map_app, derivedTensor_obj_map,
    Functor.flip_obj_map]
  have h := braided_action_tensor (L((f)^*[A])) G (G.obj (𝟙_ _))
    (lowerShriekRightAdjointUnitTensorMap adj) (lowerShriekRightAdjointTensorMap adj)
    (leftDerivedUpperStarTensorIso A f)
    (by
      intro B B'
      simpa only [isoHom_inv, lowerShriekRightAdjointUnitTensorMap] using hθ B B')
    K L J w
  simp only [Category.assoc] at h ⊢
  run_tac Lean.Elab.Tactic.withMainContext do
    exactTensorCongr (← Lean.Meta.getLocalDeclFromUserName `h).toExpr

private theorem tensorMate_assoc
    (K L M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    derivedTensorHom (ModuleCat.{u + 1} Λ) (rightDerivedUpperShriekTensorMap f K L)
        (𝟙 ((L((f)^*[ModuleCat.{u + 1} Λ])).obj M)) ≫
      rightDerivedUpperShriekTensorMap f (((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj K).obj L) M ≫
      (R(f)^![Λ]).map (derivedTensorAssociator (ModuleCat.{u + 1} Λ) Y K L M).hom =
    (derivedTensorAssociator (ModuleCat.{u + 1} Λ) X ((R(f)^![Λ]).obj K)
      ((L((f)^*[ModuleCat.{u + 1} Λ])).obj L) ((L((f)^*[ModuleCat.{u + 1} Λ])).obj M)).hom ≫
      derivedTensorHom (ModuleCat.{u + 1} Λ) (𝟙 ((R(f)^![Λ]).obj K))
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) f L M).inv ≫
      rightDerivedUpperShriekTensorMap f K
        (((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj L).obj M) := by
  have : ∀ M N, IsIso (((projectionMap (ModuleCat.{u + 1} Λ) f).app M).app N) := fun M N ↦ by
    let : IsIso ((projectionMap (ModuleCat.{u + 1} Λ) f).app M) :=
      NatIso.isIso_app_of_isIso (projectionMap (ModuleCat.{u + 1} Λ) f) M
    exact NatIso.isIso_app_of_isIso ((projectionMap (ModuleCat.{u + 1} Λ) f).app M) N
  have h := (rightDerivedUpperShriekAdjunction Λ f).projectionTensorMap_assoc
    (fun A B ↦ ((projectionMap (ModuleCat.{u + 1} Λ) f).app A).app B)
    (projectionMap_app_app_naturality_left f)
    (fun A B ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) f A B).hom)
    (projectionMapAssociativity Λ f).assoc K L M
  simp only [isoHom_inv] at h
  simp only [tensorHom_right_id, tensorHom_left_id, derivedTensorAssociator_eq,
]
  run_tac Lean.Elab.Tactic.withMainContext do
    exactTensorCongr (← Lean.Meta.getLocalDeclFromUserName `h).toExpr

private theorem tensorMate_unit
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    rightDerivedUpperShriekTensorMap f K (constantComplex Λ Y) ≫
        (R(f)^![Λ]).map (derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) Y K).hom =
      derivedTensorHom (ModuleCat.{u + 1} Λ) (𝟙 ((R(f)^![Λ]).obj K))
        (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) f).hom ≫
        (derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) X ((R(f)^![Λ]).obj K)).hom := by
  have : ∀ M N, IsIso (((projectionMap (ModuleCat.{u + 1} Λ) f).app M).app N) := fun M N ↦ by
    let : IsIso ((projectionMap (ModuleCat.{u + 1} Λ) f).app M) :=
      NatIso.isIso_app_of_isIso (projectionMap (ModuleCat.{u + 1} Λ) f) M
    exact NatIso.isIso_app_of_isIso ((projectionMap (ModuleCat.{u + 1} Λ) f).app M) N
  simpa only [tensorHom_left_id, derivedTensorRightUnitor_eq, constantComplex] using
    projectionTensorMap_unit (rightDerivedUpperShriekAdjunction Λ f) _
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) f)
      (projectionMap_rightUnitality (ModuleCat.{u + 1} Λ) f) K

private theorem coprojection_tensorMate
    (K L M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (e : ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj M).obj L ≅ constantComplex Λ Y)
    (e' : ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj L).obj M ≅ constantComplex Λ Y) :
    (derivedTensorRightCompRightDerivedUpperShriekIso Λ f L M e e').inv.app K =
      rightDerivedUpperShriekTensorMap f K L :=
  exceptionalCoprojectionMate Λ f K L M e e'

private theorem finite_lower_composition_eq
    [IsNoetherian Y] [IsNoetherian Z] [IsSeparated g] [LocallyOfFiniteType g]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)] :
    unboundedEtaleLowerShriekCompIso Λ f g =
      (ProEtale.smoothCompactSupportCompIso Λ f g).symm := by
  have hc : rightDerivedLowerShriekIso Λ (HasCompactification.compactification g) =
      Iso.refl _ :=
    (unboundedEtaleCompactSupport_comparison_coherence Λ g).1 _
  simp only [ProEtale.smoothCompactSupportCompIso, hc, Functor.isoWhiskerLeft_refl,
    Iso.trans_refl, Iso.trans_symm, Iso.symm_symm_eq, ← Functor.isoWhiskerRight_symm,
    unboundedEtaleLowerShriekCompIso, Iso.trans_assoc]
  apply Iso.ext
  ext K
  simp only [Iso.trans_hom, Iso.symm_hom]
  simp only [rightDerivedLowerShriek]

private theorem rightAdjointUniq_iso
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (e : L ≅ L') :
    Adjunction.rightAdjointUniq (adj.ofNatIsoLeft e) adj' =
      conjugateIsoEquiv adj adj' e.symm := by
  apply Iso.ext
  ext K
  simp only [Adjunction.rightAdjointUniq, conjugateIsoEquiv_apply_hom,
    conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft_counit,
    NatTrans.comp_app, Functor.map_comp, Iso.refl_hom, NatTrans.id_app,
    Functor.whiskerLeft_app, Iso.symm_hom]
  erw [R'.map_id, Category.id_comp]

private theorem finite_exceptional_composition_eq
    [IsNoetherian Y] [IsNoetherian Z] [IsSeparated g] [LocallyOfFiniteType g]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)] :
    WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition Λ f g =
      ProEtale.smoothExceptionalCompIso Λ f g := by
  rw [ProEtale.smoothExceptionalCompIso, rightAdjointUniq_iso,
    ← finite_lower_composition_eq Λ f g]
  rfl

private theorem tensorMate_composition
    [IsNoetherian Y] [IsNoetherian Z] [IsSeparated g] [LocallyOfFiniteType g]
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact (f ≫ g)]
    (K L : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    derivedTensorHom (ModuleCat.{u + 1} Λ)
        ((WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition Λ f g).hom.app K)
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g).hom.app L) ≫
      rightDerivedUpperShriekTensorMap f ((R(g)^![Λ]).obj K)
        ((L((g)^*[ModuleCat.{u + 1} Λ])).obj L) ≫
      (R(f)^![Λ]).map (rightDerivedUpperShriekTensorMap g K L) =
    rightDerivedUpperShriekTensorMap (f ≫ g) K L ≫
      (WeilConjectures.PurityFiniteSetting.finiteExceptionalComposition Λ f g).hom.app
        (((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj K).obj L) := by
  have h := lowerShriekRightAdjointTensorMap_comp (rfl : f ≫ g = f ≫ g)
    (rightDerivedUpperShriekAdjunction Λ f) (rightDerivedUpperShriekAdjunction Λ g)
    (rightDerivedUpperShriekAdjunction Λ (f ≫ g))
    (ProEtale.smoothCompactSupportCompIso Λ f g)
    (ProEtale.smoothProjectionCompCompatible Λ f g) K L
  change _ = _ ≫ _ ≫ _ ≫ _ at h
  have hc := finite_exceptional_composition_eq Λ f g
  dsimp only [ProEtale.smoothExceptionalCompIso] at hc
  rw [← hc] at h
  simp only [derivedTensorHom, derivedTensor_map_app, derivedTensor_obj_map,
    Functor.comp_obj, rightDerivedUpperShriekTensorMap, lowerShriekRightAdjointTensorMap] at h ⊢
  have h' := h.symm
  simp only [Category.assoc] at h' ⊢
  run_tac Lean.Elab.Tactic.withMainContext do
    exactTensorCongr (← Lean.Meta.getLocalDeclFromUserName `h').toExpr

private theorem tensorMate_identity
    (T : Scheme.{u})
    (K L : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    rightDerivedUpperShriekTensorMap (𝟙 T) K L ≫
        (rightDerivedUpperShriekIdIso Λ T).hom.app
          (((derivedTensor (ModuleCat.{u + 1} Λ) T).obj K).obj L) =
      derivedTensorHom (ModuleCat.{u + 1} Λ)
        ((rightDerivedUpperShriekIdIso Λ T).hom.app K)
        ((leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) T).hom.app L) := by
  have h := exceptionalIdentityMate Λ T K L
  simp only [rightDerivedUpperShriekTensorMap, lowerShriekRightAdjointTensorMap] at h ⊢
  run_tac Lean.Elab.Tactic.withMainContext do
    exactTensorCongr (← Lean.Meta.getLocalDeclFromUserName `h).toExpr

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

open Etale

end AlgebraicGeometry.ProEtale
