/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.AmbientIndDerived
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
public import WeilConjectures.CategoryTheory.Triangulated.LocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible

import WeilConjectures.AlgebraicGeometry.ConstructibleCompactnessSheaf
import Mathlib.Algebra.FiveLemma
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Dévissage of compact constructible complexes

Source: `literature/blueprint/latest/blueprint/part-six-operations/
sec-six-functors-basics/sec-compactness/sec-compactness-2/
sk-thm-constructible-compactness/sk-thm-constructible-compactness-devissage.md`,
node `det-constructible-compactness-devissage`, order 2444; the proof follows
Stacks Project, Tags 0149, 05QB and 09QH.
(blueprint: det-constructible-compactness-devissage)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

section FixedFamily

variable {D : Type u} [Category.{v} D] [Preadditive D] {I : Type w}
  (F : I → D) [HasCoproduct F]

open Classical in
private noncomputable abbrev familyComparison (K : D) :=
  DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp K (Sigma.ι F i))

private theorem familyComparison_naturality {K L : D} (f : K ⟶ L) :
    (familyComparison F K).comp
        (DirectSum.map (fun i ↦ Preadditive.leftComp (F i) f)) =
      (Preadditive.leftComp (∐ F) f).comp (familyComparison F L) := by
  classical
  apply DirectSum.addHom_ext
  intro i x
  simp only [AddMonoidHom.comp_apply, DirectSum.map_of, DirectSum.toAddMonoid_of]
  exact Category.assoc f x (Sigma.ι F i)

private theorem familyComparison_retract {K L : D} (r : Retract K L)
    (hL : Function.Bijective (familyComparison F L)) :
    Function.Bijective (familyComparison F K) := by
  classical
  let d := DirectSum.map (fun i ↦ Preadditive.leftComp (F i) r.r)
  let e := DirectSum.map (fun i ↦ Preadditive.leftComp (F i) r.i)
  have hd (x) : familyComparison F L (d x) = r.r ≫ familyComparison F K x :=
    DFunLike.congr_fun (familyComparison_naturality F r.r) x
  have he (x) : familyComparison F K (e x) = r.i ≫ familyComparison F L x :=
    DFunLike.congr_fun (familyComparison_naturality F r.i) x
  have hed (x) : e (d x) = x := by
    ext i
    simp only [e, d, DirectSum.map_apply]
    change r.i ≫ r.r ≫ x i = x i
    rw [← Category.assoc, r.retract, Category.id_comp]
  constructor
  · intro x y hxy
    have h : d x = d y := hL.1 (by rw [hd, hd, hxy])
    exact (hed x).symm.trans ((congrArg e h).trans (hed y))
  · intro f
    obtain ⟨x, hx⟩ := hL.2 (r.r ≫ f)
    refine ⟨e x, ?_⟩
    rw [he, hx, ← Category.assoc, r.retract, Category.id_comp]

private theorem familyComparison_iso {K L : D} (e : K ≅ L)
    (hL : Function.Bijective (familyComparison F L)) :
    Function.Bijective (familyComparison F K) :=
  familyComparison_retract F e.retract hL

private theorem sum_exact
    {A B C : I → Type v} [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, AddCommGroup (C i)] (f : ∀ i, A i →+ B i) (g : ∀ i, B i →+ C i)
    (h : ∀ i, Function.Exact (f i) (g i)) :
    Function.Exact (DirectSum.map f) (DirectSum.map g) := by
  classical
  intro x
  constructor
  · intro hx
    have hx' (i : I) : g i (x i) = 0 := by
      simpa only [DirectSum.map_apply, DFinsupp.zero_apply] using congrArg (fun y ↦ y i) hx
    choose y hy using fun i ↦ (h i (x i)).mp (hx' i)
    refine ⟨∑ i ∈ x.support, DirectSum.of A i (y i), ?_⟩
    simp only [map_sum, DirectSum.map_of, hy]
    exact DirectSum.sum_support_of x
  · rintro ⟨y, rfl⟩
    ext i
    simpa only [DirectSum.map_apply, DFinsupp.zero_apply] using (h i).apply_apply_eq_zero (y i)

variable [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

private theorem hom_triangle_exact (T : Triangle D) (hT : T ∈ distTriang D) (W : D) :
    Function.Exact (Preadditive.leftComp W T.mor₂) (Preadditive.leftComp W T.mor₁) := by
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := T.yoneda_exact₂ hT x hx
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, rfl⟩
    change T.mor₁ ≫ T.mor₂ ≫ y = 0
    rw [← Category.assoc, comp_distTriang_mor_zero₁₂ T hT, zero_comp]

private theorem familyComparison_cone (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : Function.Bijective (familyComparison F T.obj₁))
    (h₂ : Function.Bijective (familyComparison F T.obj₂))
    (h₁' : Function.Bijective (familyComparison F (T.obj₁⟦(1 : ℤ)⟧)))
    (h₂' : Function.Bijective (familyComparison F (T.obj₂⟦(1 : ℤ)⟧))) :
    Function.Bijective (familyComparison F T.obj₃) := by
  classical
  let U := T.rotate
  let V := U.rotate
  have hU : U ∈ distTriang D := rot_of_distTriang T hT
  have hV : V ∈ distTriang D := rot_of_distTriang U hU
  let c := familyComparison F
  let d (s t : D) (f : s ⟶ t) :=
    DirectSum.map (fun i ↦ Preadditive.leftComp (F i) f)
  let p (s t : D) (f : s ⟶ t) := Preadditive.leftComp (∐ F) f
  have hc {s t : D} (f : s ⟶ t) : (p s t f).comp (c t) = (c s).comp (d s t f) :=
    (familyComparison_naturality F f).symm
  exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (d _ _ V.mor₂) (d _ _ T.mor₃) (d _ _ T.mor₂) (d _ _ T.mor₁)
    (p _ _ V.mor₂) (p _ _ T.mor₃) (p _ _ T.mor₂) (p _ _ T.mor₁)
    (c (T.obj₂⟦(1 : ℤ)⟧)) (c (T.obj₁⟦(1 : ℤ)⟧)) (c T.obj₃) (c T.obj₂) (c T.obj₁)
    (hc V.mor₂) (hc T.mor₃) (hc T.mor₂) (hc T.mor₁)
    (sum_exact _ _ (fun i ↦ hom_triangle_exact V hV (F i)))
    (sum_exact _ _ (fun i ↦ hom_triangle_exact U hU (F i)))
    (sum_exact _ _ (fun i ↦ hom_triangle_exact T hT (F i)))
    (hom_triangle_exact V hV (∐ F)) (hom_triangle_exact U hU (∐ F))
    (hom_triangle_exact T hT (∐ F)) h₂'.2 h₁' h₂ h₁.1

open Classical in
private def familyLocus : ObjectProperty D := fun K ↦
  ∀ n : ℤ, Function.Bijective (familyComparison F (K⟦n⟧))

private theorem familyLocus_thick :
    (familyLocus F).IsTriangulated ∧ (familyLocus F).IsClosedUnderIsomorphisms ∧
      (familyLocus F).IsStableUnderRetracts := by
  classical
  let Q := familyLocus F
  let : Q.IsStableUnderRetracts := ⟨fun r hL n ↦
    familyComparison_retract F (r.map (shiftFunctor D n)) (hL n)⟩
  let : Q.ContainsZero := ⟨0, isZero_zero D, fun n ↦ by
    have h0 := (shiftFunctor D n).map_isZero (isZero_zero D)
    have : ∀ i, Subsingleton ((0 : D)⟦n⟧ ⟶ F i) := fun i ↦ ⟨fun _ _ ↦ h0.eq_of_src _ _⟩
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, h0.eq_of_src _ _⟩⟩⟩
  let : Q.IsStableUnderShift ℤ := ⟨fun r ↦
    ObjectProperty.IsStableUnderShiftBy.mk (fun K hK n ↦
      familyComparison_iso F ((shiftFunctorAdd D r n).app K).symm (hK (r + n)))⟩
  let : Q.IsTriangulatedClosed₃ := ObjectProperty.IsTriangulatedClosed₃.mk'
    (fun T hT h₁ h₂ n ↦ familyComparison_cone F
      ((Triangle.shiftFunctor D n).obj T) (Triangle.shift_distinguished T hT n)
      (h₁ n) (h₂ n)
      (familyComparison_iso F ((shiftFunctorAdd D n 1).app T.obj₁).symm (h₁ (n + 1)))
      (familyComparison_iso F ((shiftFunctorAdd D n 1).app T.obj₂).symm (h₂ (n + 1))))
  let : Q.IsTriangulatedClosed₂ := .of_isTriangulatedClosed₃
  exact ⟨{}, inferInstance, inferInstance⟩

end FixedFamily

open Classical in
private theorem comparison_transport
    {J : Type w} {V W : J → Type*} [∀ j, AddCommGroup (V j)]
    [∀ j, AddCommGroup (W j)] {V₀ W₀ : Type*} [AddCommGroup V₀] [AddCommGroup W₀]
    (f : ∀ j, V j →+ V₀) (g : ∀ j, W j →+ W₀)
    (e : ∀ j, V j ≃+ W j) (e₀ : V₀ ≃+ W₀)
    (he : ∀ j x, e₀ (f j x) = g j (e j x))
    (hg : Function.Bijective (DirectSum.toAddMonoid g)) :
    Function.Bijective (DirectSum.toAddMonoid f) := by
  classical
  let m := DirectSum.map (fun j ↦ (e j).toAddMonoidHom)
  have hm : Function.Bijective m :=
    ⟨(DirectSum.map_injective _).2 (fun j ↦ (e j).injective),
      (DirectSum.map_surjective _).2 (fun j ↦ (e j).surjective)⟩
  have hcomp : (DirectSum.toAddMonoid g).comp m =
      e₀.toAddMonoidHom.comp (DirectSum.toAddMonoid f) := by
    apply DirectSum.addHom_ext
    intro j x
    simp only [AddMonoidHom.comp_apply, m, DirectSum.map_of, DirectSum.toAddMonoid_of]
    exact (he j x).symm
  have hb := hg.comp hm
  change Function.Bijective ((DirectSum.toAddMonoid g).comp m) at hb
  rw [hcomp] at hb
  exact ⟨fun x y hxy ↦ hb.1 (congrArg e₀ hxy), fun y ↦ by
    obtain ⟨x, hx⟩ := hb.2 (e₀ y)
    exact ⟨x, e₀.injective hx⟩⟩

open Classical in
private theorem comparison_sourceShift
    {D : Type u} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    {I : Type w} (F : I → D) [HasCoproduct F] (S : D)
    (c : Cofan F) (hc : IsColimit c)
    (h : ∀ m : ℤ, Function.Bijective (DirectSum.toAddMonoid
      (fun i ↦ Preadditive.rightComp S ((shiftFunctor D m).map (c.inj i))))) :
    familyLocus F S := by
  classical
  intro n
  let adj := (shiftEquiv D n).toAdjunction
  let : (shiftEquiv D n).functor.Additive := by
    change (shiftFunctor D n).Additive
    infer_instance
  let e := hc.coconePointUniqueUpToIso (coproductIsCoproduct F)
  let post : (S ⟶ (∐ F)⟦-n⟧) ≃+ (S ⟶ c.pt⟦-n⟧) :=
    { toEquiv := Iso.homCongr (Iso.refl S) ((shiftFunctor D (-n)).mapIso e.symm)
      map_add' := by intro f g; simp [Iso.homCongr, Preadditive.add_comp] }
  apply comparison_transport _ _ (fun i ↦ adj.homAddEquiv S (F i))
    ((adj.homAddEquiv S (∐ F)).trans post) ?_ (h (-n))
  intro i x
  change post (adj.homEquiv S (∐ F) (x ≫ Sigma.ι F i)) =
    adj.homEquiv S (F i) x ≫ (shiftFunctor D (-n)).map (c.inj i)
  rw [adj.homEquiv_naturality_right]
  dsimp [post, Iso.homCongr]
  simp only [Category.id_comp, Category.assoc]
  let y : S ⟶ (F i)⟦-n⟧ := adj.homEquiv S (F i) x
  change y ≫ (shiftFunctor D (-n)).map (Sigma.ι F i) ≫
      (shiftFunctor D (-n)).map e.inv = y ≫ (shiftFunctor D (-n)).map (c.inj i)
  rw [← Functor.map_comp]
  exact congrArg (y ≫ ·)
    (congrArg ((shiftFunctor D (-n)).map)
      (hc.comp_coconePointUniqueUpToIso_inv (coproductIsCoproduct F) ⟨i⟩))

private theorem comparison_in_fullSubcategory
    {D : Type u} [Category.{v} D] [Preadditive D] [HasCoproducts.{v} D]
    (P : ObjectProperty D) [HasCoproducts.{v} P.FullSubcategory]
    [∀ I : Type v, PreservesColimitsOfShape (Discrete I) P.ι]
    (K : P.FullSubcategory)
    (hK : ∀ (I : Type v) (F : I → P.FullSubcategory),
      Function.Bijective (familyComparison (fun i ↦ (F i).obj) K.obj)) :
    IsCompactObject K := by
  classical
  intro I F
  let G := P.ι
  let e (L : P.FullSubcategory) : (K ⟶ L) ≃+ (K.obj ⟶ L.obj) :=
    AddEquiv.ofBijective G.mapAddHom ⟨G.map_injective, G.map_surjective⟩
  let s := sigmaComparison G F
  let post : (K.obj ⟶ G.obj (∐ F)) ≃+ (K.obj ⟶ ∐ fun i ↦ (F i).obj) :=
    { toEquiv := Iso.homCongr (Iso.refl _) (asIso s).symm
      map_add' := by intro f g; simp [Iso.homCongr, Preadditive.add_comp] }
  apply comparison_transport _ _ (fun i ↦ e (F i)) ((e (∐ F)).trans post) ?_ (hK I F)
  intro i f
  change 𝟙 K.obj ≫ G.map (f ≫ Sigma.ι F i) ≫ inv s =
    G.map f ≫ Sigma.ι (fun i ↦ (F i).obj) i
  rw [Category.id_comp, Functor.map_comp, Category.assoc, map_ι_comp_inv_sigmaComparison]
  rfl

/-- Constructibility is unchanged by an isomorphism of module sheaves. -/
private theorem constructible_isoClosed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (IsConstantModelConstructible Λ X) := by
  have hlocal (Y : Scheme.{u})
      {M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
      (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ Y M) :
      HasFiniteConstantLocalModel Λ Y N := by
    obtain ⟨𝒰, h𝒰⟩ := hM
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 i
    exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (𝒰.f i)).mapIso e.symm ≪≫ eP⟩⟩
  have hstrat (Y : Scheme.{u})
      {M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
      (e : M ≅ N) (hM : IsFiniteConstantStratified Λ Y M) :
      IsFiniteConstantStratified Λ Y N := by
    obtain ⟨S, hS⟩ := hM
    exact ⟨S, fun a ↦ hlocal _
      ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩
  exact ⟨fun e hM ↦ by
    unfold IsConstantModelConstructible at hM ⊢
    split_ifs at hM ⊢ with hX
    · exact hstrat _ e hM
    · exact fun U hU ↦ hstrat _ ((CondensedRing.upperStar Λ U.ι).mapIso e) (hM U hU)⟩

/-- Closure under the small coproducts used in the source localizing-closure API. -/
private theorem localizing_of_cofans
    {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (P : ObjectProperty D) [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hsum : ∀ (I : Type v) (F : I → D) (c : Cofan F), IsColimit c →
      (∀ i, P (F i)) → P c.pt) : P.IsLocalizing := by
  refine ⟨fun I ↦ ⟨?_⟩⟩
  rintro K ⟨c⟩
  have hc : IsColimit (Cofan.mk K (fun i ↦ c.ι.app ⟨i⟩)) := by
    have h := (IsColimit.precomposeInvEquiv
      (Discrete.natIsoFunctor (F := c.diag)) c.cocone).symm c.isColimit
    exact h.ofIsoColimit (Cocone.ext (Iso.refl _) (by simp))
  exact hsum I (fun i ↦ c.diag.obj ⟨i⟩) _ hc (fun i ↦ c.prop_diag_obj ⟨i⟩)

-- The original statement binds the index universe through the type of its family.
open Classical in
set_option linter.unusedVariables false in
/-- The fixed-family Hom comparison is thick, and bounded finite-constant constructible
complexes are compact in their localizing closure.

Source: `literature/blueprint/latest/blueprint/part-six-operations/
sec-six-functors-basics/sec-compactness/sec-compactness-2/
sk-thm-constructible-compactness/sk-thm-constructible-compactness-devissage.md`,
node `det-constructible-compactness-devissage`, order 2444; Stacks Project, Tags 0149,
05QB and 09QH.  The comparison locus `Q I F` is formed for one fixed small family
`F` in `Dic`, and each thick-subcategory clause is asserted for that fixed family.
The proof is postponed as follows.  For a fixed small family in `Dic`,
write `Q(C)` for the comparison in every source shift and let `B` be its ambient
coproduct.  The zero object, isomorphisms and all shifts preserve `Q`; the coproduct
exists by the localizing-closure existence theorem.  Applying Hom out of a distinguished
triangle to each family member and to `B` gives a five-term exact ladder.  Direct sums
of the rows remain exact because every element has finite support, and the coprojections
make the ladder commute.  The four outer comparison maps are isomorphisms, so the five
lemma gives the middle one.  A retract argument using the splitting maps proves closure
under direct summands.  The sheaf compactness statement, with target shift `-n`, gives
`Q` for constructible sheaves in degree zero.  Finally, the truncation triangles of a
bounded constructible complex give a finite Postnikov induction, hence `Q` for every
bounded constructible complex.  The ambient ind-constructible theorem identifies every
member of the localizing closure and every small family of such members with `Dic`; its
ambient coproduct therefore computes the coproduct in the localizing subcategory.  The
shift-zero comparison is exactly compactness in the sense of `def-pc-compact-object`.
(blueprint: det-constructible-compactness-devissage). -/
theorem constructibleCompactnessDevissage
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (hk : Finite k ∨ IsAlgClosed k)
    (X : Scheme.{u}) (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ]
    (hΛ : Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj E) ∨
      Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ)) :
    let C := DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))
    let Cons : ObjectProperty
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)) :=
      IsConstantModelConstructible Λ X
    let Dbc : ObjectProperty C := constantModelBoundedConstructible Λ X
    let IndCons : ObjectProperty
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)) := ObjectProperty.ind.{u + 1} Cons
    let Dic : ObjectProperty C := fun K ↦ ∀ r : ℤ,
      IndCons ((DerivedCategory.homologyFunctor _ r).obj K)
    let Loc : ObjectProperty C := Dbc.localizingClosure
    let Q : ∀ (I : Type (u + 1)), (I → C) → ObjectProperty C := fun I F K ↦
      ∀ n : ℤ,
        Function.Bijective
          (DirectSum.toAddMonoid
            (fun i ↦ Preadditive.rightComp (K⟦n⟧) (Sigma.ι F i)))
    (∀ (I : Type (u + 1)) (F : I → C), (∀ i, Dic (F i)) →
      (Q I F).IsTriangulated ∧
        (Q I F).IsClosedUnderIsomorphisms ∧
        (Q I F).IsStableUnderRetracts ∧
        (∀ M, Cons M → Q I F ((DerivedCategory.singleFunctor _ 0).obj M)) ∧
        Dbc ≤ Q I F) ∧
      (∀ (K : C) (hK : Dbc K), IsCompactObject
        (⟨K, ObjectProperty.le_localizingClosure (P := Dbc) K hK⟩ : Loc.FullSubcategory)) := by
  classical
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let C := DerivedCategory A
  let Cons : ObjectProperty A := IsConstantModelConstructible Λ X
  let Dbc : ObjectProperty C := constantModelBoundedConstructible Λ X
  let Dic : ObjectProperty C := fun K ↦ ∀ n : ℤ,
    ObjectProperty.ind.{u + 1} Cons ((DerivedCategory.homologyFunctor A n).obj K)
  let : X.Over (Spec (.of k)) := ⟨aX⟩
  have : IsSeparated (X ↘ Spec (.of k)) := inferInstanceAs (IsSeparated aX)
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType aX)
  have : QuasiCompact (X ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact aX)
  have _ := hk
  have hambient : Dic.IsTriangulated ∧
      (∀ (I : Type (u + 1)) (F : I → C) (c : Cofan F), IsColimit c →
        (∀ i, Dic (F i)) → Dic c.pt) ∧ Dbc ≤ Dic := by
    rcases hΛ with h | h
    · cases h
      have h := (ambientIndConstructibleDerived ℓ E k p hp hpl X).1
      exact ⟨h.1, h.2.1, h.2.2.2.1⟩
    · cases h
      have h := (ambientIndConstructibleDerived ℓ E k p hp hpl X).2
      exact ⟨h.1, h.2.1, h.2.2.2.1⟩
  let : Cons.IsClosedUnderIsomorphisms := constructible_isoClosed Λ X
  let : Dic.IsClosedUnderIsomorphisms := ⟨fun e h n ↦
    (ObjectProperty.ind.{u + 1} Cons).prop_of_iso
      ((DerivedCategory.homologyFunctor A n).mapIso e) (h n)⟩
  let : Dic.IsTriangulated := hambient.1
  let : Dic.IsLocalizing := localizing_of_cofans Dic hambient.2.1
  have hloc : Dbc.localizingClosure ≤ Dic :=
    ObjectProperty.localizingClosure_le hambient.2.2
  have hsingle (I : Type (u + 1)) (F : I → C) (hF : ∀ i, Dic (F i))
      (M : A) (hM : Cons M) :
      familyLocus F ((DerivedCategory.singleFunctor A 0).obj M) := by
    rcases hΛ with h | h
    · cases h
      obtain ⟨c, hc, hm⟩ := constructible_compactness_sheaf
        ℓ E k p hp hpl X M hM I F hF
      exact comparison_sourceShift F _ c hc hm
    · cases h
      obtain ⟨c, hc, hm⟩ := constructible_compactness_sheaf_padicAlgCl
        ℓ k p hp hpl X M hM I F hF
      exact comparison_sourceShift F _ c hc hm
  have hbounded (I : Type (u + 1)) (F : I → C) (hF : ∀ i, Dic (F i)) :
      Dbc ≤ familyLocus F := by
    let := (familyLocus_thick F).1
    let := (familyLocus_thick F).2.1
    intro K hK
    exact DerivedCategory.prop_of_bounded (familyLocus F) Cons
      (hsingle I F hF) K hK.1 hK.2
  refine ⟨fun I F hF ↦ ?_, fun K hK ↦ ?_⟩
  · exact ⟨(familyLocus_thick F).1, (familyLocus_thick F).2.1,
      (familyLocus_thick F).2.2, hsingle I F hF, hbounded I F hF⟩
  · apply comparison_in_fullSubcategory Dbc.localizingClosure ⟨K,
      ObjectProperty.le_localizingClosure Dbc K hK⟩
    intro I F
    have hF : ∀ i, Dic (F i).obj := fun i ↦ hloc _ (F i).property
    exact familyComparison_iso (fun i ↦ (F i).obj)
      ((shiftFunctorZero C ℤ).app K).symm
      (hbounded I (fun i ↦ (F i).obj) hF K hK 0)

end AlgebraicGeometry.ProEtale
