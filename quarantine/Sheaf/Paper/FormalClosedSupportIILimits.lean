/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FormalClosedSupport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Triangulated.Functor
import Sheaf.Paper.FormalClosedPullbackProducts
import Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# Closed support and sequential derived limits

Source: Stacks Project, Tag 09AA; blueprint
`sec-six-functors-basics/sk-lem-formal-closed-support-ii`, node
`det-formal-closed-support-ii-limits`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w x

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical commutation with shifts of the derived tensor functor
`K ⊗ᴸ_{Λ_X} -` on `D(X_proét, Λ)`, induced from the tensor product of complexes
(`DerivedCategory.commShiftTensorLeft`); this is the shift structure with which
`L[0] ⊗ᴸ -` is a triangulated functor. Source: Stacks Project, Tag 06YU
(definition-derived-tor); blueprint `def-sfb-derived-tensor-modules`,
used by `det-formal-closed-support-ii-limits` (blueprint:
det-formal-closed-support-ii-limits). -/
noncomputable instance derivedTensorObjCommShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) (K : DerivedCategory (FormalSupportModules Λ X)) :
    ((derivedTensor Λ X).obj K).CommShift ℤ :=
  DerivedCategory.commShiftTensorLeft (FormalSupportModules Λ X) K

/--
The properties required of each functor in the closed-support limits statement, for a
functor `F` with its given (canonical) commutation with shifts.
Source: Stacks Project, Tag 09AA; blueprint
`det-formal-closed-support-ii-limits`.
-/
structure ClosedSupportLimitFunctorProperties
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{x} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] : Prop where
  additive : F.Additive
  triangulated : F.IsTriangulated
  products : ∀ (I : Type (max u v w x)),
    PreservesLimitsOfShape (Discrete I) F
  fibers : ∀ (T : Triangle C), T ∈ distTriang C →
    F.mapTriangle.obj T ∈ distTriang D
  sequential_limits :
    ∀ {K : ℕ → C} [HasProduct K]
      (f : ∀ n : ℕ, K (n + 1) ⟶ K n)
      (L : C) (p : L ⟶ ∏ᶜ K)
      (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle f L p δ →
      ∀ [HasProduct (fun n : ℕ => F.obj (K n))],
      ∃ e : F.obj (∏ᶜ K) ≅ ∏ᶜ (fun n : ℕ => F.obj (K n)),
        (∀ n : ℕ, e.hom ≫ Pi.π _ n = F.map (Pi.π K n)) ∧
        IsDerivedLimitTriangle (fun n : ℕ => F.map (f n))
          (F.obj L) (F.map p ≫ e.hom)
          (e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app L)
  comparison_isIso :
    ∀ {K : ℕ → C} [HasProduct K]
      (f : ∀ n : ℕ, K (n + 1) ⟶ K n)
      (L : C) (p : L ⟶ ∏ᶜ K)
      (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle f L p δ →
      ∀ [HasProduct (fun n : ℕ => F.obj (K n))]
      (L' : D) (p' : L' ⟶ ∏ᶜ (fun n : ℕ => F.obj (K n)))
      (δ' : (∏ᶜ (fun n : ℕ => F.obj (K n))) ⟶ L'⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle (fun n : ℕ => F.map (f n)) L' p' δ' →
      (e : F.obj (∏ᶜ K) ≅ ∏ᶜ (fun n : ℕ => F.obj (K n))) →
      (∀ n : ℕ, e.hom ≫ Pi.π _ n = F.map (Pi.π K n)) →
      (ψ : F.obj L ⟶ L') →
      (ψ ≫ p' = F.map p ≫ e.hom) →
      ((e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app L) ≫
        (shiftFunctor D (1 : ℤ)).map ψ = δ') →
      IsIso ψ

private theorem mapTransition
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{x} D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    {K : ℕ → C} [HasProduct K]
    [HasProduct (fun n => F.obj (K n))] (f : ∀ n, K (n + 1) ⟶ K n)
    (e : F.obj (∏ᶜ K) ≅ ∏ᶜ (fun n => F.obj (K n)))
    (he : ∀ n, e.hom ≫ Pi.π _ n = F.map (Pi.π K n)) :
    F.map (towerTransitionEndomorphism f) ≫ e.hom =
      e.hom ≫ towerTransitionEndomorphism (fun n => F.map (f n)) := by
  apply Pi.hom_ext
  intro n
  simp only [towerTransitionEndomorphism, towerProductShift, Functor.map_sub,
    Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc,
    Pi.lift_π, Category.id_comp, he]
  simp only [← F.map_comp, Pi.lift_π, Category.id_comp]
  rw [← Category.assoc, he, ← F.map_comp]

private theorem mapRoos
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{x} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.Additive] [F.IsTriangulated]
    {K : ℕ → C} [HasProduct K]
    [HasProduct (fun n => F.obj (K n))] (f : ∀ n, K (n + 1) ⟶ K n)
    (L : C) (p : L ⟶ ∏ᶜ K) (δ : ∏ᶜ K ⟶ L⟦(1 : ℤ)⟧)
    (h : IsDerivedLimitTriangle f L p δ)
    (e : F.obj (∏ᶜ K) ≅ ∏ᶜ (fun n => F.obj (K n)))
    (he : ∀ n, e.hom ≫ Pi.π _ n = F.map (Pi.π K n)) :
    IsDerivedLimitTriangle (fun n => F.map (f n)) (F.obj L) (F.map p ≫ e.hom)
      (e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app L) := by
  let T := Triangle.mk p (towerTransitionEndomorphism f) δ
  let T' := Triangle.mk (F.map p ≫ e.hom)
    (towerTransitionEndomorphism (fun n => F.map (f n)))
    (e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app L)
  let q : F.mapTriangle.obj T ≅ T' :=
    Triangle.isoMk _ _ (Iso.refl _) e e (by
      change F.map p ≫ e.hom = 𝟙 _ ≫ (F.map p ≫ e.hom)
      simp)
      (mapTransition F f e he) (by
        change (F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app L) ≫
          (shiftFunctor D (1 : ℤ)).map (𝟙 _) =
            e.hom ≫ (e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app L)
        simp)
  exact isomorphic_distinguished _ (F.map_distinguished T h) _ q.symm

private theorem limitProperties
    {C : Type u} {D : Type v} [Category.{w} C] [Category.{x} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.Additive] [F.IsTriangulated]
    (hprod : ∀ I : Type (max u v w x), PreservesLimitsOfShape (Discrete I) F) :
    ClosedSupportLimitFunctorProperties F := by
  have : PreservesLimitsOfShape (Discrete (ULift.{max u v w x} ℕ)) F := hprod _
  have : PreservesLimitsOfShape (Discrete ℕ) F :=
    preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) F
  refine ⟨inferInstance, inferInstance, hprod, F.map_distinguished, ?_, ?_⟩
  · intro K hK f L p δ h hFK
    let e := PreservesProduct.iso F K
    have he (n : ℕ) : e.hom ≫ Pi.π _ n = F.map (Pi.π K n) :=
      piComparison_comp_π F K n
    exact ⟨e, he, mapRoos F f L p δ h e he⟩
  · intro K hK f L p δ h hFK L' p' δ' h' e he ψ hψ hδ
    let T := Triangle.mk (F.map p ≫ e.hom)
      (towerTransitionEndomorphism (fun n => F.map (f n)))
      (e.inv ≫ F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app L)
    let T' := Triangle.mk p' (towerTransitionEndomorphism (fun n => F.map (f n))) δ'
    let q : T ⟶ T' := Triangle.homMk _ _ ψ (𝟙 _) (𝟙 _)
      (by simpa [T, T'] using hψ.symm) (by simp [T, T'])
      (by simpa [T, T'] using hδ)
    exact isIso₁_of_isIso₂₃ q (mapRoos F f L p δ h e he) h'
      (by dsimp [q, Triangle.homMk]; infer_instance) (by dsimp [q, Triangle.homMk]; infer_instance)

private theorem dualizableFinitePower {A : Type*} [Category A] [Preadditive A]
    [HasFiniteBiproducts A] [HasBinaryBiproducts A] [MonoidalCategory A] [MonoidalPreadditive A]
    (M : A) (hM : IsDualizable M) (n : ℕ) :
    IsDualizable (⨁ fun _ : Fin n => M) := by
  classical
  induction n with
  | zero =>
    apply IsZero.isDualizable
    exact (IsZero.iff_id_eq_zero _).2 (by apply biproduct.hom_ext; intro i; exact i.elim0)
  | succ n hn =>
    let e : (⨁ fun _ : Fin (n + 1) => M) ≅ M ⊞ (⨁ fun _ : Fin n => M) := {
      hom := biprod.lift (biproduct.π _ 0)
        (biproduct.lift fun i : Fin n => biproduct.π _ i.succ)
      inv := biproduct.lift (Fin.cases biprod.fst (fun i => biprod.snd ≫ biproduct.π _ i))
      hom_inv_id := by
        apply biproduct.hom_ext
        intro i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      inv_hom_id := by
        apply biprod.hom_ext
        · simp
        · apply biproduct.hom_ext
          intro i
          simp }
    exact (hM.biprod hn).of_iso e.symm

open CategoryTheory.MonoidalCategory in
private theorem finiteFreeSingleDualizable
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) (n : ℕ) :
    IsDualizable ((DerivedCategory.singleFunctor (FormalSupportModules Λ X) 0).obj
      (Mod.finiteFree (condensedRingObj Λ X) n)) := by
  let F := DerivedCategory.singleFunctor (FormalSupportModules Λ X) 0
  let e := F.mapBiproduct (fun _ : Fin n => Mod.regular (condensedRingObj Λ X))
  have h : IsDualizable (F.obj (Mod.regular (condensedRingObj Λ X))) :=
    (show IsDualizable (𝟙_ (DerivedCategory (FormalSupportModules Λ X))) from
      ⟨inferInstance⟩).of_iso
      (DerivedCategory.singleFunctorObjUnitIso (FormalSupportModules Λ X)).symm
  exact (dualizableFinitePower _ h n).of_iso e.symm

open CategoryTheory.MonoidalCategory in
private theorem tensorProducts
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (S : Scheme.{u}) (L : FormalSupportModules Λ S)
    (hL : ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S,
      ∀ c : 𝒰.I₀, ∃ n : ℕ, Nonempty
        ((formalSupportPullback Λ (𝒰.f c)).obj L ≅
          Mod.finiteFree (condensedRingObj Λ (𝒰.X c)) n)) :
    ∀ I : Type (u + 2), PreservesLimitsOfShape (Discrete I)
      ((derivedTensor Λ S).obj
        ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj L)) := by
  obtain ⟨𝒰, h𝒰⟩ := hL
  let Λ' : Profinite.CondensedRing.{u} := ⟨Λ⟩
  have hdual : Nonempty (HasRightDual
      ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj L)) := by
    apply (condensed_dualizable_iff_proetale_cover Λ' S 𝒰 _).2
    intro c
    obtain ⟨n, ⟨e⟩⟩ := h𝒰 c
    let q := (upperStarLowerStarAdjunction Λ (𝒰.f c)).leftAdjointUniq
      (formalSupportPullbackAdjunction Λ (𝒰.f c))
    let e' := ((upperStar Λ (𝒰.f c)).mapDerivedCategorySingleFunctor 0).app L ≪≫
      (DerivedCategory.singleFunctor (FormalSupportModules Λ (𝒰.X c)) 0).mapIso
        (q.app L ≪≫ e)
    exact (finiteFreeSingleDualizable Λ (𝒰.X c) n).of_iso e'.symm
  obtain ⟨hd⟩ := hdual
  let : HasRightDual
      ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj L) := hd
  intro I
  have : PreservesLimitsOfSize.{u + 2, u + 2}
      ((derivedTensor Λ S).obj
        ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj L)) :=
    (tensorLeftAdjunction
      ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj L)
      hd.rightDual).rightAdjoint_preservesLimits
  infer_instance

private theorem openPullbackProducts
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X V : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] :
    ∀ I : Type (u + 2), PreservesLimitsOfShape (Discrete I)
      (formalSupportPullback Λ j).mapDerivedCategory := by
  let e := (upperStarLowerStarAdjunction Λ j).leftAdjointUniq
    (formalSupportPullbackAdjunction Λ j)
  let a := (openImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight e
  let b := a.mapDerivedCategoryRightDerivedAdjunction
  let c := b.ofNatIsoRight (formalSupportPullback Λ j).rightDerivedFunctorIsoMapDerivedCategory
  intro I
  let := c.rightAdjoint_preservesLimits
  infer_instance

/-- Assertions that closed support and finite-free tensoring preserve products,
fibers, and sequential derived limits. Source: Stacks Project, Tag 09AA;
blueprint `det-formal-closed-support-ii-limits`.

Proof: the support kernel is computed sectionwise and commutes with products and
finite limits; the inverse-image and direct-image module functors preserve these
limits and their derived functors are triangulated. K-injective resolutions and
termwise products identify the derived products, and the Roos triangle is carried
to the Roos triangle of the image tower. On a covering trivializing the finite
locally free module, tensor is a finite direct-sum functor, hence exact and
product preserving; the same termwise calculation gives its derived statement.
The product comparison is the one commuting with every projection, and every
Roos-triangle completion with those product comparisons is invertible by TR3.
-/
structure ClosedSupportIILimitsAssertions
    {Z V X S : Scheme.{u}} (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (i : Z ⟶ X) (j : V ⟶ X) (u : S ⟶ Z)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    [IsOpenImmersion u]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : FormalSupportModules Λ S) : Prop where
  j_star : ClosedSupportLimitFunctorProperties
    ((formalSupportPullback Λ j).mapDerivedCategory)
  u_star : ClosedSupportLimitFunctorProperties
    ((formalSupportPullback Λ u).mapDerivedCategory)
  u_star_closed_support : ClosedSupportLimitFunctorProperties
    ((formalClosedSupport Λ i j).rightDerivedFunctor ⋙
      (formalSupportPullback Λ u).mapDerivedCategory)
  i_star : ClosedSupportLimitFunctorProperties
    ((formalSupportPullback Λ i).mapDerivedCategory)
  rj_star : ClosedSupportLimitFunctorProperties
    ((lowerStar Λ j).rightDerivedFunctor)
  closed_support : ClosedSupportLimitFunctorProperties
    ((formalClosedSupport Λ i j).rightDerivedFunctor)
  tensor : ClosedSupportLimitFunctorProperties
    ((derivedTensor Λ S).obj
      ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj L))

/-- Closed support commutes with derived limits of sequences.
Source: Stacks Project, Tag 09AA; blueprint
`sec-six-functors-basics/sk-lem-formal-closed-support-ii`, node
`det-formal-closed-support-ii-limits` (blueprint: det-formal-closed-support-ii-limits).

Proof:
1. Exact open extension by zero is left adjoint to open pullback. Derive the
adjunction and identify the derived exact pullback with its termwise functor.
Thus both open restrictions preserve products. The closed restriction product
clause is `formalClosedPullback_preservesDerivedProducts`.
2. The derived inverse-image/direct-image adjunction makes Rj_* a right adjoint.
The existing closed-support theorem makes RG a right adjoint to the exact i_*.
Hence both preserve products, as does u^* RG by composition. All these functors
are triangulated with their canonical shift structures.
3. Dualizability is local for pro-etale covers. On the trivializing cover, the
single complex L[0] is a finite biproduct of tensor units, hence dualizable.
Descend this pairing; tensoring by L[0] is right adjoint to tensoring by its dual,
so preserves products. The derived tensor triangulated instance uses precisely
the shift structure fixed in this module.
4. For any additive triangulated F preserving products, the projection equations
identify F(1 - s) with 1 - F(s) under the product comparison. The explicit
triangle isomorphism with components id, e, e proves the image Roos triangle.
For any comparison to another such triangle, use its given commuting squares
with components psi, id, id and the two-out-of-three theorem for distinguished
triangles. This proves invertibility of every comparison, without selecting a cone.
-/
theorem formalClosedSupportIILimitsAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    {Z V X S : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : V ⟶ X) (u : S ⟶ Z)
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    [IsOpenImmersion u]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (L : FormalSupportModules Λ S)
    (hL : ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage S,
      ∀ c : 𝒰.I₀, ∃ n : ℕ,
        Nonempty
          ((formalSupportPullback Λ (𝒰.f c)).obj L ≅
            Mod.finiteFree (condensedRingObj Λ (𝒰.X c)) n)) :
    Nonempty (ClosedSupportIILimitsAssertions Λ i j u hij L) := by
  obtain ⟨hc⟩ := formalClosedSupportAssertions Λ ℓ k p hpℓ i j hij
  have hpj := openPullbackProducts Λ j
  have hpu := openPullbackProducts Λ u
  have hpi : ∀ I : Type (u + 2), PreservesLimitsOfShape (Discrete I)
      (formalSupportPullback Λ i).mapDerivedCategory :=
    formalClosedPullback_preservesDerivedProducts Λ k i j hij
  have hpt : ∀ I : Type (u + 2), PreservesLimitsOfShape (Discrete I)
      ((derivedTensor Λ S).obj
        ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj L)) :=
    tensorProducts Λ S L hL
  have hpRj : ∀ I : Type (u + 2), PreservesLimitsOfShape (Discrete I)
      (lowerStar Λ j).rightDerivedFunctor := by
    intro I
    have : PreservesLimitsOfSize.{u + 2, u + 2} (lowerStar Λ j).rightDerivedFunctor :=
      (formalSupportPullbackAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction
        |>.rightAdjoint_preservesLimits
    infer_instance
  have hpG : ∀ I : Type (u + 2), PreservesLimitsOfShape (Discrete I)
      (formalClosedSupport Λ i j).rightDerivedFunctor := by
    intro I
    let := hc.rightAdjoint.rightAdjoint_preservesLimits
    infer_instance
  have hpGu : ∀ I : Type (u + 2), PreservesLimitsOfShape (Discrete I)
      ((formalClosedSupport Λ i j).rightDerivedFunctor ⋙
        (formalSupportPullback Λ u).mapDerivedCategory) := by
    intro I
    have := hpG I
    have := hpu I
    infer_instance
  have : ((derivedTensor Λ S).obj
      ((DerivedCategory.singleFunctor (FormalSupportModules Λ S) 0).obj L)).IsTriangulated :=
    DerivedCategory.isTriangulated_tensorLeft _ _
  exact ⟨{
    j_star := limitProperties _ hpj
    u_star := limitProperties _ hpu
    u_star_closed_support := limitProperties _ hpGu
    i_star := limitProperties _ hpi
    rj_star := limitProperties _ hpRj
    closed_support := limitProperties _ hpG
    tensor := limitProperties _ hpt
  }⟩

end AlgebraicGeometry.ProEtale.CondensedRing
