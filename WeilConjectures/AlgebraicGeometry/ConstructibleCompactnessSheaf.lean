/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstructibleCompactnessBounded
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructibleEllAdic
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison

/-!
# Compactness of constructible sheaves against arbitrary families

Source: blueprint latest, `sec-six-functors-basics/sk-thm-constructible-compactness/`,
`sk-thm-constructible-compactness-sheaf.md` and its proof
(blueprint: det-constructible-compactness-sheaf).

Both rational coefficient cases use the ordinary unbounded derived module category.
The base field is finite or algebraically closed, as in the current parent theorem;
this supplies the finite uniform Ext cutoff required by the finite-window argument.
The original unrestricted-base statement omitted this condition.

The adopted constructibility predicate agrees with finite constant local models on X.
Ext continuity extends the uniform bound to ind-constructible targets. The bounded
comparison supplies single-degree compactness, and the existing abstract finite-window
argument gives compactness for arbitrary families. Finally, finite expressions give
surjectivity of the displayed additive comparison and coproduct projections give
injectivity. All shifts use the shifted injections of the same coproduct cofan.
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj DirectSum

namespace AlgebraicGeometry.ProEtale


open Classical in
/-- A direct-sum comparison is bijective when every map has finite support. -/
private theorem comparison_of_compactFor
    {D : Type*} [Category D] [Preadditive D] {I : Type*}
    (S : D) (K : I → D) [HasCoproduct K] (c : Cofan K) (hc : IsColimit c)
    (hK : CompactFor S K) :
    Function.Bijective (DirectSum.toAddMonoid
      (fun i ↦ Preadditive.rightComp S (c.inj i))) := by
  classical
  let α := DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp S (c.inj i))
  let π (j : I) : c.pt ⟶ K j := hc.desc
    (Cofan.mk (K j) (fun i ↦ if h : i = j then eqToHom (congrArg K h) else 0))
  have hπ (i j : I) : c.inj i ≫ π j =
      if h : i = j then eqToHom (congrArg K h) else 0 := hc.fac _ ⟨i⟩
  have hα (x : ⨁ i, (S ⟶ K i)) (j : I) : α x ≫ π j = x j := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i f =>
      by_cases h : i = j
      · subst i
        simp [α, Preadditive.rightComp, Category.assoc, hπ]
      · simp [α, Preadditive.rightComp, Category.assoc, hπ,
          DirectSum.of_eq_of_ne, h, Ne.symm h]
    | add x y hx hy => simp [map_add, Preadditive.add_comp, hx, hy]
  constructor
  · intro x y h
    apply DirectSum.ext
    intro j
    rw [← hα x j, ← hα y j, h]
  · intro f
    obtain ⟨T, g, hg⟩ := hK.of_isColimit hc f
    refine ⟨∑ i ∈ T, DirectSum.of (fun i ↦ S ⟶ K i) i (g i), ?_⟩
    simpa only [map_sum, DirectSum.toAddMonoid_of, Preadditive.rightComp,
      AddMonoidHom.mk'_apply] using hg.symm

/-- Vanishing of maps between single objects is independent of the localization chosen. -/
private theorem single_subsingleton_change
    {A : Type u} [Category.{v} A] [Abelian A]
    (h₁ h₂ : HasDerivedCategory.{v} A) (C B : A) (n : ℤ)
    (h : letI := h₂
      Subsingleton ((DerivedCategory.singleFunctor A 0).obj C ⟶
        (DerivedCategory.singleFunctor A n).obj B)) :
    letI := h₁
    Subsingleton ((DerivedCategory.singleFunctor A 0).obj C ⟶
      (DerivedCategory.singleFunctor A n).obj B) := by
  let Q₁ := letI := h₁; DerivedCategory.Q (C := A)
  let Q₂ := letI := h₂; DerivedCategory.Q (C := A)
  let e₁ := letI := h₁; (DerivedCategory.singleFunctorIsoCompQ A 0).app C
  let e₁' := letI := h₁; (DerivedCategory.singleFunctorIsoCompQ A n).app B
  let e₂ := letI := h₂; (DerivedCategory.singleFunctorIsoCompQ A 0).app C
  let e₂' := letI := h₂; (DerivedCategory.singleFunctorIsoCompQ A n).app B
  let e := (Iso.homCongr e₁ e₁').trans
    ((Localization.homEquiv (HomologicalComplex.quasiIso A (.up ℤ)) Q₁ Q₂).trans
      (Iso.homCongr e₂ e₂').symm)
  exact ⟨fun f g ↦ e.injective (h.elim (e f) (e g))⟩

open Classical in
/-- The all-shift bounded comparison for sheaves implies compactness of single objects. -/
private theorem single_compactFor_of_comparison
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    (C : A) {I : Type t} (B : I → A)
    [HasCoproducts.{t} (DerivedCategory A)]
    (c : Cofan (fun i ↦ (DerivedCategory.singleFunctor A 0).obj (B i)))
    (hc : IsColimit c)
    (h : ∀ m : ℤ, Function.Bijective (constructibleBoundedComparison C _ c m))
    (n : ℤ) :
    CompactFor ((DerivedCategory.singleFunctor A 0).obj C)
      (fun i ↦ (DerivedCategory.singleFunctor A n).obj (B i)) := by
  classical
  let Y := fun i ↦ (DerivedCategory.singleFunctor A 0).obj (B i)
  let L := fun i ↦ (Y i)⟦-n⟧
  let d : Cofan L := Cofan.mk (c.pt⟦-n⟧)
    (fun i ↦ (shiftFunctor _ (-n)).map (c.inj i))
  have hd : IsColimit d := isColimitCofanMkObjOfIsColimit (shiftFunctor _ (-n)) Y _ hc
  have hL : CompactFor ((DerivedCategory.singleFunctor A 0).obj C) L := by
    intro f
    let e := hd.coconePointUniqueUpToIso (coproductIsCoproduct L)
    obtain ⟨x, hx⟩ := (h (-n)).2 (f ≫ e.inv)
    refine ⟨x.support, fun i ↦ x i, ?_⟩
    have hsum : constructibleBoundedComparison C Y c (-n) x =
        ∑ i ∈ x.support, x i ≫ d.inj i := by
      have hgen (i : I) (g : (DerivedCategory.singleFunctor A 0).obj C ⟶ L i) :
          constructibleBoundedComparison C Y c (-n)
            (DirectSum.of (fun i ↦ (DerivedCategory.singleFunctor A 0).obj C ⟶ L i) i g) =
              g ≫ d.inj i := by
        change (DirectSum.toAddMonoid
          (fun j ↦ Preadditive.rightComp ((DerivedCategory.singleFunctor A 0).obj C)
            (d.inj j))) (DirectSum.of _ i g) = _
        exact DirectSum.toAddMonoid_of
          (fun j ↦ Preadditive.rightComp ((DerivedCategory.singleFunctor A 0).obj C)
            (d.inj j)) i g
      calc
        _ = constructibleBoundedComparison C Y c (-n)
            (∑ i ∈ x.support, DirectSum.of _ i (x i)) :=
          congrArg (constructibleBoundedComparison C Y c (-n))
            (DirectSum.sum_support_of x).symm
        _ = _ := by
          simp only [map_sum]
          apply Finset.sum_congr rfl
          intro i _
          exact hgen i (x i)
    rw [← cancel_mono e.inv, Preadditive.sum_comp, ← hx, hsum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Category.assoc]
    exact congrArg (x i ≫ ·) ((coproductIsCoproduct L).comp_coconePointUniqueUpToIso_hom
      hd ⟨i⟩).symm
  exact CompactFor.of_iso
    (fun i ↦ (((DerivedCategory.singleFunctors A).shiftIso (-n) n 0 (by omega)).app
      (B i)).symm) hL

open Classical in
/-- The finite-window argument gives the actual comparison in any chosen localization. -/
private theorem comparison_of_heart_bound
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{v} A]
    [IsGrothendieckAbelian.{t} A] [HasLimitsOfShape (Discrete ℕ) A]
    [HasExactLimitsOfShape (Discrete ℕ) A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    (C : A) (I : Type t) [P.IsClosedUnderColimitsOfShape (Discrete I)]
    (N : ℤ)
    (hvan : ∀ B, P B → ∀ n ≤ N,
      ∀ f : (DerivedCategory.singleFunctor A 0).obj C ⟶
        (DerivedCategory.singleFunctor A n).obj B, f = 0)
    (hsum : ∀ (n : ℤ) (B : I → A), (∀ i, P (B i)) →
      CompactFor ((DerivedCategory.singleFunctor A 0).obj C)
        (fun i ↦ (DerivedCategory.singleFunctor A n).obj (B i)))
    (K : I → DerivedCategory A) (hK : ∀ i, DerivedCategory.homologyProperty P (K i)) :
    ∃ (c : Cofan K) (_ : IsColimit c), ∀ m : ℤ,
      Function.Bijective (constructibleBoundedComparison C K c m) := by
  classical
  let : Abelian.HasKInjectiveResolutions A :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{t}
  let : HasColimitsOfSize.{t, t} A := IsGrothendieckAbelian.hasColimits A
  let : HasCoproducts.{t} A := fun J ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  let c : Cofan K := Cofan.mk (∐ K) (Sigma.ι K)
  refine ⟨c, coproductIsCoproduct K, fun m ↦ ?_⟩
  let L := fun i ↦ (K i)⟦m⟧
  have hL : CompactFor ((DerivedCategory.singleFunctor A 0).obj C) L :=
    DerivedCategory.compactFor_of_homologyProperty 0 N hvan hsum L
      (fun i ↦ (DerivedCategory.homologyProperty P).le_shift m (K i) (hK i))
  let d : Cofan L := Cofan.mk (c.pt⟦m⟧)
    (fun i ↦ (shiftFunctor _ m).map (c.inj i))
  have hd : IsColimit d := isColimitCofanMkObjOfIsColimit (shiftFunctor _ m) K _
    (coproductIsCoproduct K)
  exact comparison_of_compactFor _ L d hd hL

set_option maxHeartbeats 1500000 in
-- The geometric module-object categories require a large instance-normalization budget.
/-- Compactness against arbitrary ind-constructible families for a finite coefficient
subextension over a finite or algebraically closed base field.

Source: blueprint latest, `sec-six-functors-basics/sk-thm-constructible-compactness/`,
`sk-thm-constructible-compactness-sheaf.md` and its proof
(blueprint: det-constructible-compactness-sheaf).

Proof: identify finite constant-model constructibility with the adopted source-library
predicate on the Noetherian scheme X. Ext continuity and the uniform constructible Ext
bound give one cutoff N for all ind-constructible target sheaves. The canonical
localization Hom equivalence transports this vanishing to the explicit chosen derived
category. Apply the bounded comparison with a=b=0 to sheaves in degree zero and use
single-functor shift isomorphisms to get compactness in every single degree. The proved
abstract finite-window theorem then gives CompactFor for each family K_i[m]: it cuts
all objects to a common bounded window, kills the lower tail by left completeness,
and the upper tail by t-structure orthogonality. Shifts preserve the coproduct cofan.
Finite-support expressions yield surjectivity of the direct-sum comparison; composition
with its coordinate projections recovers every input coordinate, yielding injectivity.
This also handles an empty family and a zero source. -/
-- STATEMENT-DISPUTED: the original arbitrary-base-field version omitted the uniform
-- finite Ext bound. The corrected statement has the field scope of its parent theorem.
theorem constructible_compactness_sheaf
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (hk : Finite k ∨ IsAlgClosed k)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [HasDerivedCategory.{u + 1} (CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))]
    (C : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hC : IsConstantModelConstructible (Profinite.continuousMapRingObj E) X C)
    (I : Type (u + 1))
    (K : I → DerivedCategory (CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)))
    (hK : ∀ (i : I) (n : ℤ), ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
      ((DerivedCategory.homologyFunctor _ n).obj (K i))) :
    ∃ (c : Cofan K) (_ : IsColimit c), ∀ m : ℤ,
      Function.Bijective (constructibleBoundedComparison C K c m) := by
  classical
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : Fact (ringChar k ≠ ℓ) := ⟨by simpa only [ringChar.eq k p] using hpl⟩
  have hk' : Finite k ∨ IsSepClosed k := hk.imp id (fun h ↦ by
    let := h
    infer_instance)
  let Λ := (Profinite.continuousMapRingObj E)
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let : Abelian.HasKInjectiveResolutions A :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{u + 1}
  let : HasCoproducts.{u + 1} A := fun J ↦
    IsGrothendieckAbelian.hasColimitsOfShape_discrete A J
  let : HasCoproducts.{u + 1} (DerivedCategory A) :=
    fun J ↦ DerivedCategory.hasColimitsOfShape_discrete J
  let P : ObjectProperty A := IsIndConstructibleModuleObject (condensedRingObj Λ X)
  have hcomp : IsConstructibleModuleObject (condensedRingObj Λ X) =
      IsConstantModelConstructible Λ X := by
    funext M
    exact propext ((adicConstructibilityPredicateComparison ℓ X Λ (.continuous E)).1 M)
  have hC' : IsConstructibleModuleObject (condensedRingObj Λ X) C := by
    rw [hcomp]
    exact hC
  have hheart := CondensedRing.isIndConstructibleHeart_continuousMapRingObj ℓ E
    (X ↘ Spec (.of k))
  let : P.IsClosedUnderColimitsOfShape (Discrete I) :=
    hheart.isClosedUnderColimitsOfShape_discrete I
  have hind := HasIndConstructibleExtBound.of_continuity
    (CondensedRing.hasConstructibleExtContinuity_continuousMapRingObj ℓ E
      (X ↘ Spec (.of k))) (CondensedRing.hasUniformConstructibleExtBound_continuousMapRingObj ℓ E
      (X ↘ Spec (.of k)) hk')
  obtain ⟨N, hN⟩ := hind.exists_eq_zero C hC'
  refine comparison_of_heart_bound P C I N ?_ ?_ K ?_
  · intro B hB n hn f
    have hz : letI := HasDerivedCategory.ofIsGrothendieckAbelian (C := A)
        Subsingleton ((DerivedCategory.singleFunctor A 0).obj C ⟶
          (DerivedCategory.singleFunctor A n).obj B) := ⟨fun f g ↦
            (hN B hB n hn f).trans (hN B hB n hn g).symm⟩
    have hs := single_subsingleton_change (inferInstance : HasDerivedCategory.{u + 1} A)
      (HasDerivedCategory.ofIsGrothendieckAbelian (C := A)) C B n hz
    exact hs.elim f 0
  · intro n B hB
    have hB' : ∀ i, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible Λ X) (B i) := by
      simpa only [P, IsIndConstructibleModuleObject, hcomp] using hB
    have : (ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible Λ X)).ContainsZero := by
      simpa only [P, IsIndConstructibleModuleObject, hcomp] using
        (inferInstance : P.ContainsZero)
    let Y := fun i ↦ (DerivedCategory.singleFunctor A 0).obj (B i)
    have hY (i : I) (q : ℤ) : ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible Λ X) ((DerivedCategory.homologyFunctor A q).obj
          (Y i)) := by
      by_cases hq : q = 0
      · subst q
        exact (ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)).prop_of_iso
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app (B i)).symm (hB' i)
      · apply (ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)).prop_of_isZero
        rcases lt_or_gt_of_ne hq with hq | hq
        · exact DerivedCategory.isZero_of_isGE (Y i) 0 q hq
        · exact DerivedCategory.isZero_of_isLE (Y i) 0 q hq
    obtain ⟨c, hc, hm⟩ := constructible_compactness_bounded ℓ E k p hp hpl X C hC
      0 0 le_rfl I Y hY (fun i q hq ↦ by
        rcases hq with hq | hq
        · exact DerivedCategory.isZero_of_isGE (Y i) 0 q hq
        · exact DerivedCategory.isZero_of_isLE (Y i) 0 q hq)
    exact single_compactFor_of_comparison C B c hc hm n
  · simpa only [DerivedCategory.homologyProperty, P,
      IsIndConstructibleModuleObject, hcomp] using hK

set_option maxHeartbeats 1500000 in
-- The geometric module-object categories require a large instance-normalization budget.
/-- Compactness against arbitrary ind-constructible families for the condensed algebraic
closure over a finite or algebraically closed base field.

Source: blueprint latest, `sec-six-functors-basics/sk-thm-constructible-compactness/`,
`sk-thm-constructible-compactness-sheaf.md` and its proof, coefficient Lambda = Qlb
(blueprint: det-constructible-compactness-sheaf).

Proof: use the algebraic-closure clauses of the constructibility comparison, heart
closure, Ext continuity and uniform Ext bound. Transport vanishing between the chosen
localizations, use the bounded comparison for degree-zero sheaves, and apply the same
abstract finite-window theorem to K_i[m]. Finite expressions give surjectivity and
coordinate projections give injectivity for the shifted coproduct cofan. The finite
window, cutoff and bounded-family induction are identical to the finite-extension case;
no bound is imposed on the cohomology of the original family. -/
-- STATEMENT-DISPUTED: the original arbitrary-base-field version omitted the uniform
-- finite Ext bound. The corrected statement has the field scope of its parent theorem.
theorem constructible_compactness_sheaf_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (hk : Finite k ∨ IsAlgClosed k)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [HasDerivedCategory.{u + 1} (CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))]
    (C : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hC : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X C)
    (I : Type (u + 1))
    (K : I → DerivedCategory (CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (hK : ∀ (i : I) (n : ℤ), ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
      ((DerivedCategory.homologyFunctor _ n).obj (K i))) :
    ∃ (c : Cofan K) (_ : IsColimit c), ∀ m : ℤ,
      Function.Bijective (constructibleBoundedComparison C K c m) := by
  classical
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : Fact (ringChar k ≠ ℓ) := ⟨by simpa only [ringChar.eq k p] using hpl⟩
  have hk' : Finite k ∨ IsSepClosed k := hk.imp id (fun h ↦ by
    let := h
    infer_instance)
  let Λ := (Profinite.padicAlgClRingObj ℓ)
  let A := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)
  let : Abelian.HasKInjectiveResolutions A :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{u + 1}
  let : HasCoproducts.{u + 1} A := fun J ↦
    IsGrothendieckAbelian.hasColimitsOfShape_discrete A J
  let : HasCoproducts.{u + 1} (DerivedCategory A) :=
    fun J ↦ DerivedCategory.hasColimitsOfShape_discrete J
  let P : ObjectProperty A := IsIndConstructibleModuleObject (condensedRingObj Λ X)
  have hcomp : IsConstructibleModuleObject (condensedRingObj Λ X) =
      IsConstantModelConstructible Λ X := by
    funext M
    exact propext ((adicConstructibilityPredicateComparison ℓ X Λ (.algebraicClosure)).1 M)
  have hC' : IsConstructibleModuleObject (condensedRingObj Λ X) C := by
    rw [hcomp]
    exact hC
  have hheart := CondensedRing.isIndConstructibleHeart_padicAlgClRingObj ℓ
    (X ↘ Spec (.of k))
  let : P.IsClosedUnderColimitsOfShape (Discrete I) :=
    hheart.isClosedUnderColimitsOfShape_discrete I
  have hind := HasIndConstructibleExtBound.of_continuity
    (CondensedRing.hasConstructibleExtContinuity_padicAlgClRingObj ℓ
      (X ↘ Spec (.of k))) (CondensedRing.hasUniformConstructibleExtBound_padicAlgClRingObj ℓ
      (X ↘ Spec (.of k)) hk')
  obtain ⟨N, hN⟩ := hind.exists_eq_zero C hC'
  refine comparison_of_heart_bound P C I N ?_ ?_ K ?_
  · intro B hB n hn f
    have hz : letI := HasDerivedCategory.ofIsGrothendieckAbelian (C := A)
        Subsingleton ((DerivedCategory.singleFunctor A 0).obj C ⟶
          (DerivedCategory.singleFunctor A n).obj B) := ⟨fun f g ↦
            (hN B hB n hn f).trans (hN B hB n hn g).symm⟩
    have hs := single_subsingleton_change (inferInstance : HasDerivedCategory.{u + 1} A)
      (HasDerivedCategory.ofIsGrothendieckAbelian (C := A)) C B n hz
    exact hs.elim f 0
  · intro n B hB
    have hB' : ∀ i, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible Λ X) (B i) := by
      simpa only [P, IsIndConstructibleModuleObject, hcomp] using hB
    have : (ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible Λ X)).ContainsZero := by
      simpa only [P, IsIndConstructibleModuleObject, hcomp] using
        (inferInstance : P.ContainsZero)
    let Y := fun i ↦ (DerivedCategory.singleFunctor A 0).obj (B i)
    have hY (i : I) (q : ℤ) : ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible Λ X) ((DerivedCategory.homologyFunctor A q).obj
          (Y i)) := by
      by_cases hq : q = 0
      · subst q
        exact (ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)).prop_of_iso
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app (B i)).symm (hB' i)
      · apply (ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)).prop_of_isZero
        rcases lt_or_gt_of_ne hq with hq | hq
        · exact DerivedCategory.isZero_of_isGE (Y i) 0 q hq
        · exact DerivedCategory.isZero_of_isLE (Y i) 0 q hq
    obtain ⟨c, hc, hm⟩ := constructible_compactness_bounded_padicAlgCl ℓ  k p hp hpl X C hC
      0 0 le_rfl I Y hY (fun i q hq ↦ by
        rcases hq with hq | hq
        · exact DerivedCategory.isZero_of_isGE (Y i) 0 q hq
        · exact DerivedCategory.isZero_of_isLE (Y i) 0 q hq)
    exact single_compactFor_of_comparison C B c hc hm n
  · simpa only [DerivedCategory.homologyProperty, P,
      IsIndConstructibleModuleObject, hcomp] using hK

end AlgebraicGeometry.ProEtale
