/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.DerivedCategory.CompactOfBoundedExt
import WeilConjectures.AlgebraicGeometry.SixFunctors.IndConstructibleFilteredColimits
import WeilConjectures.AlgebraicGeometry.DetIndHeartIISums
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Constructible compactness for uniformly bounded ind-constructible families

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-constructible-compactness/sk-thm-constructible-compactness-bounded.md
(blueprint: det-constructible-compactness-bounded).

IndCons is `ObjectProperty.ind` of finite constant-model constructibility; membership in
Dic is imposed on every cohomology sheaf. All complexes, morphisms and coproducts are in
the ordinary unbounded derived category. A sum is specified by a colimit cofan, whose
injections define the comparison. Existence of this cofan is included in the conclusion;
any other coproduct gives the same assertion by the unique compatible isomorphism.

The signatures use only the coefficient objects and ordinary derived module categories
reexported by CondensedConstantConstructibility. They do not require the six-functor
restriction framework; omitting that unrelated import keeps this interface within the
60-second single-file compilation budget. The chosen localization is bound explicitly
at the fixed coefficient universe, avoiding repeated normalization of its construction.
This is only a choice of derived-category presentation, supplied by the existing
Grothendieck abelian instance, not an additional mathematical hypothesis.
-/

@[expose] public section

set_option autoImplicit false

universe t w v u

open CategoryTheory CategoryTheory.Limits DirectSum
open scoped ZeroObject

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Classical in
/-- The coproduct projections recover the coordinates of a finite sum. -/
private theorem comparison_injective
    {D : Type*} [Category D] [Preadditive D] {J : Type*}
    (S : D) (Y : J → D) (c : Cofan Y) (hc : IsColimit c) :
    Function.Injective (DirectSum.toAddMonoid
      (fun j ↦ Preadditive.rightComp S (c.inj j))) := by
  classical
  let p (j : J) : c.pt ⟶ Y j := hc.desc
    (Cofan.mk (Y j) (fun i ↦ if h : i = j then eqToHom (congrArg Y h) else 0))
  let α := DirectSum.toAddMonoid (fun j ↦ Preadditive.rightComp S (c.inj j))
  have hp (i j : J) : c.inj i ≫ p j =
      if h : i = j then eqToHom (congrArg Y h) else 0 := hc.fac _ ⟨i⟩
  have hα (x : ⨁ j, (S ⟶ Y j)) (j : J) : α x ≫ p j = x j := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i f =>
      by_cases h : i = j
      · subst i
        simp [α, Preadditive.rightComp, Category.assoc, hp]
      · simp [α, Preadditive.rightComp, Category.assoc, hp,
          DirectSum.of_eq_of_ne, h, Ne.symm h]
    | add x y hx hy => simp [map_add, Preadditive.add_comp, hx, hy]
  intro x y hxy
  apply DirectSum.ext
  intro j
  rw [← hα x j, ← hα y j, hxy]

open Classical in
/-- Finite-support factorization is equivalent to surjectivity of the sum comparison. -/
private theorem comparison_surjective_iff
    {D : Type*} [Category D] [Preadditive D] {J : Type*}
    (S : D) (Y : J → D) [HasCoproduct Y] (c : Cofan Y) (hc : IsColimit c) :
    Function.Surjective (DirectSum.toAddMonoid
      (fun j ↦ Preadditive.rightComp S (c.inj j))) ↔ CompactFor S Y := by
  classical
  let α := DirectSum.toAddMonoid (fun j ↦ Preadditive.rightComp S (c.inj j))
  constructor
  · intro h f
    let e := hc.coconePointUniqueUpToIso (coproductIsCoproduct Y)
    obtain ⟨x, hx⟩ := h (f ≫ e.inv)
    refine ⟨x.support, fun j ↦ x j, ?_⟩
    have hsum : α x = ∑ j ∈ x.support, x j ≫ c.inj j := by
      conv_lhs => rw [← DirectSum.sum_support_of x]
      simp only [map_sum, α, DirectSum.toAddMonoid_of, Preadditive.rightComp]
      rfl
    rw [← cancel_mono e.inv, Preadditive.sum_comp, ← hx, hsum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Category.assoc]
    exact congrArg (x j ≫ ·) ((coproductIsCoproduct Y).comp_coconePointUniqueUpToIso_hom
      hc ⟨j⟩).symm
  · intro h f
    obtain ⟨T, g, hg⟩ := h.of_isColimit hc f
    refine ⟨∑ j ∈ T, DirectSum.of (fun j ↦ S ⟶ Y j) j (g j), ?_⟩
    simpa only [map_sum, DirectSum.toAddMonoid_of, Preadditive.rightComp,
      AddMonoidHom.mk'_apply] using hg.symm

open Classical in
/-- Transport a direct-sum comparison through additive equivalences on all its groups. -/
private theorem sum_bijective_transport
    {J : Type*} {V W : J → Type*} [∀ j, AddCommGroup (V j)]
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
private noncomputable def singleComparison
    {A : Type u} [Category.{v} A] [Abelian A] (hD : HasDerivedCategory.{w} A)
    (C : A) (q : ℤ) {J : Type t} (B : J → A) (c : Cofan B) :=
  letI := hD
  DirectSum.toAddMonoid (fun j ↦
    Preadditive.rightComp ((DerivedCategory.singleFunctor A 0).obj C)
      ((shiftFunctor _ q).map ((DerivedCategory.singleFunctor A 0).map (c.inj j))))

/-- Ext identifies the comparison independently of the chosen derived localization.
Negative shifts give zero groups; nonnegative shifts use the same Ext groups. -/
private theorem single_comparison_change
    {A : Type u} [Category.{v} A] [Abelian A]
    (h₁ : HasDerivedCategory.{w} A) (h₂ : HasDerivedCategory.{v} A)
    (C : A) (q : ℤ) {J : Type t} (B : J → A) (c : Cofan B)
    (h : Function.Bijective (singleComparison h₂ C q B c)) :
    Function.Bijective (singleComparison h₁ C q B c) := by
  classical
  by_cases hq : 0 ≤ q
  · lift q to ℕ using hq
    let : HasExt.{max u v} A := HasExt.standard A
    let e₁ (N : A) := letI := h₁;
      Abelian.Ext.homAddEquiv (X := C) (Y := N) (n := q)
    let e₂ (N : A) := letI := h₂;
      Abelian.Ext.homAddEquiv (X := C) (Y := N) (n := q)
    have hnat₁ {N M : A} (f : N ⟶ M) (x : Abelian.Ext C N q) :
        e₁ M (x.comp (Abelian.Ext.mk₀ f) (Nat.add_zero q)) =
          (letI := h₁
           e₁ N x ≫ (shiftFunctor _ (q : ℤ)).map
             ((DerivedCategory.singleFunctor A 0).map f)) := by
      let := h₁
      simp only [e₁, Abelian.Ext.homAddEquiv_apply, Abelian.Ext.comp_hom,
        Abelian.Ext.mk₀_hom, ShiftedHom.comp_mk₀]
    have hnat₂ {N M : A} (f : N ⟶ M) (x : Abelian.Ext C N q) :
        e₂ M (x.comp (Abelian.Ext.mk₀ f) (Nat.add_zero q)) =
          (letI := h₂
           e₂ N x ≫ (shiftFunctor _ (q : ℤ)).map
             ((DerivedCategory.singleFunctor A 0).map f)) := by
      let := h₂
      simp only [e₂, Abelian.Ext.homAddEquiv_apply, Abelian.Ext.comp_hom,
        Abelian.Ext.mk₀_hom, ShiftedHom.comp_mk₀]
    apply sum_bijective_transport _ _
      (fun j ↦ (e₁ (B j)).symm.trans (e₂ (B j))) ((e₁ c.pt).symm.trans (e₂ c.pt)) ?_ h
    intro j x
    obtain ⟨y, rfl⟩ := (e₁ (B j)).surjective x
    dsimp only [AddEquiv.trans_apply, Preadditive.rightComp, AddMonoidHom.coe_mk,
      AddHom.coe_mk]
    simp only [AddMonoidHom.mk'_apply]
    rw [← hnat₁, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, hnat₂]
  · let := h₁
    have hzero (N : A) : Subsingleton
        ((DerivedCategory.singleFunctor A 0).obj C ⟶
          ((DerivedCategory.singleFunctor A 0).obj N)⟦q⟧) := by
      have : (((DerivedCategory.singleFunctor A 0).obj N)⟦q⟧).IsGE (-q) :=
        DerivedCategory.TStructure.t.isGE_shift _ 0 q (-q) (by omega)
      apply subsingleton_of_forall_eq 0
      intro f
      exact DerivedCategory.TStructure.t.zero_of_isLE_of_isGE f 0 (-q) (by omega)
        inferInstance inferInstance
    have := hzero c.pt
    have (j : J) := hzero (B j)
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- Closure under empty coproducts supplies the zero member needed for truncations. -/
private theorem containsZero_of_sums
    {A : Type*} [Category A] [HasZeroObject A] [HasZeroMorphisms A]
    (P : ObjectProperty A)
    (hsum : ∀ (J : Type t) (B : J → A) (c : Cofan B), IsColimit c →
      (∀ j, P (B j)) → P c.pt) : P.ContainsZero := by
  let B : PEmpty.{t + 1} → A := fun j ↦ j.elim
  let c : Cofan B := Cofan.mk 0 (fun j ↦ j.elim)
  have hc : IsColimit c := Cofan.IsColimit.mk c (fun _ ↦ 0)
    (fun _ j ↦ j.elim) (fun _ _ _ ↦ (isZero_zero A).eq_of_src _ _)
  exact ⟨0, isZero_zero A, hsum _ B c hc (fun j ↦ j.elim)⟩

open Classical in
/-- The source-library bounded dévissage, expressed with the actual additive comparison. -/
private theorem bounded_comparison
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [IsGrothendieckAbelian.{t} A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    (C : A) (I : Type t)
    (hsum : ∀ (q : ℤ) (B : I → A), (∀ i, P (B i)) →
      ∀ (c : Cofan B), IsColimit c → Function.Bijective
        (DirectSum.toAddMonoid (fun i ↦
          Preadditive.rightComp ((DerivedCategory.singleFunctor A 0).obj C)
            ((shiftFunctor _ q).map ((DerivedCategory.singleFunctor A 0).map (c.inj i))))))
    (a b : ℤ) (hab : a ≤ b) (K : I → DerivedCategory A)
    (hK : ∀ i, DerivedCategory.homologyProperty P (K i))
    (hbound : ∀ i n, n < a ∨ b < n →
      IsZero ((DerivedCategory.homologyFunctor A n).obj (K i))) :
    ∃ (c : Cofan K) (_ : IsColimit c), ∀ s : ℤ,
      Function.Bijective (DirectSum.toAddMonoid (fun i ↦
        Preadditive.rightComp ((DerivedCategory.singleFunctor A 0).obj C)
          ((shiftFunctor _ s).map (c.inj i)))) := by
  classical
  let : Abelian.HasKInjectiveResolutions A :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{t}
  let : HasColimitsOfSize.{t, t} A := IsGrothendieckAbelian.hasColimits A
  let : HasCoproducts.{t} A := fun J ↦
    HasColimitsOfSize.has_colimits_of_shape (Discrete J)
  have hsingle (n : ℤ) (B : I → A) (hB : ∀ i, P (B i)) :
      CompactFor ((DerivedCategory.singleFunctor A 0).obj C)
        (fun i ↦ (DerivedCategory.singleFunctor A n).obj (B i)) := by
    let F := DerivedCategory.singleFunctor A 0 ⋙ shiftFunctor _ (-n)
    let c : Cofan (fun i ↦ F.obj (B i)) :=
      Cofan.mk (F.obj (∐ B)) (fun i ↦ F.map (Sigma.ι B i))
    have hc : IsColimit c := isColimitCofanMkObjOfIsColimit F B _
      (coproductIsCoproduct B)
    have h : CompactFor ((DerivedCategory.singleFunctor A 0).obj C)
        (fun i ↦ F.obj (B i)) :=
      (comparison_surjective_iff _ _ c hc).mp
        (hsum (-n) B hB (Cofan.mk (∐ B) (Sigma.ι B)) (coproductIsCoproduct B)).2
    exact CompactFor.of_iso
      (fun i ↦ (((DerivedCategory.singleFunctors A).shiftIso (-n) n 0 (by omega)).app
        (B i)).symm) h
  let c : Cofan K := Cofan.mk (∐ K) (Sigma.ι K)
  refine ⟨c, coproductIsCoproduct K, fun s ↦ ?_⟩
  let L : I → DerivedCategory A := fun i ↦ (K i)⟦s⟧
  have (i : I) : (K i).IsGE a := (DerivedCategory.isGE_iff _ _).mpr
    (fun n hn ↦ hbound i n (Or.inl hn))
  have (i : I) : (K i).IsLE b := (DerivedCategory.isLE_iff _ _).mpr
    (fun n hn ↦ hbound i n (Or.inr hn))
  have (i : I) : (L i).IsGE (a - s) :=
    DerivedCategory.TStructure.t.isGE_shift (K i) a s (a - s) (by omega)
  have (i : I) : (L i).IsLE (a - s + ((b - a).toNat : ℕ)) :=
    DerivedCategory.TStructure.t.isLE_shift (K i) b s _ (by omega)
  have hL : CompactFor ((DerivedCategory.singleFunctor A 0).obj C) L :=
    DerivedCategory.compactFor_of_isGE_of_isLE hsingle (b - a).toNat (a - s) L
      (fun i ↦ (DerivedCategory.homologyProperty P).le_shift s (K i) (hK i))
  let d : Cofan L := Cofan.mk (c.pt⟦s⟧)
    (fun i ↦ (shiftFunctor _ s).map (c.inj i))
  have hd : IsColimit d := isColimitCofanMkObjOfIsColimit (shiftFunctor _ s) K _
    (coproductIsCoproduct K)
  exact ⟨comparison_injective _ L d hd, (comparison_surjective_iff _ L d hd).mpr hL⟩


open Classical in
/-- The additive comparison induced by the shifted coprojections of a cofan in an
ordinary derived category, with the source sheaf in degree zero. On a finitely supported
tuple it is the sum of composites with these shifted coprojections. The convention is
`(K[s])^n = K^(n+s)`. Source: blueprint main-20261015,
sk-thm-constructible-compactness-bounded, displayed alpha_s
(blueprint: det-constructible-compactness-bounded). -/
noncomputable def constructibleBoundedComparison
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    {I : Type t} (C : A) (K : I → DerivedCategory A) (c : Cofan K) (s : ℤ) :
    (⨁ i : I, ((DerivedCategory.singleFunctor A 0).obj C ⟶ (K i)⟦s⟧)) →+
      ((DerivedCategory.singleFunctor A 0).obj C ⟶ c.pt⟦s⟧) :=
  DirectSum.toAddMonoid fun i ↦
    Preadditive.rightComp _ ((shiftFunctor (DerivedCategory A) s).map (c.inj i))

open Classical in
/-- A constructible sheaf over a finite coefficient subextension commutes with coproducts
of ind-constructible complexes in a common cohomological interval, in every shift.
Source: blueprint main-20261015, sk-thm-constructible-compactness-bounded, statement
(blueprint: det-constructible-compactness-bounded).

Proof: The empty-coproduct case of det-ind-heart-filtered-colimits shows that
IndCons contains zero. The Ext-sum comparison det-ind-heart-ii-sums gives compactness
for every family of sheaves placed in a single degree. This is independent of the
chosen derived localization: for nonnegative shifts use Ext.homAddEquiv and its
compatibility with postcomposition, and for negative shifts all Hom groups vanish.
The source-library theorem DerivedCategory.compactFor_of_isGE_of_isLE implements
the blueprint induction on the common width: its base case identifies a complex
supported in one degree with its cohomology sheaf; its successor step uses the
standard truncation triangle and CompactFor.of_distTriang. The latter lifts a finite
expression from the third coproduct along the component triangles, subtracts it,
and lifts the difference from the first coproduct by Hom exactness. Apply this
induction to K_i[s], with bounds [a-s,b-s] and width (b-a).toNat. The resulting
finite expression proves surjectivity of the displayed comparison. Coordinate
projections from the coproduct recover each component of a finite tuple, proving
injectivity. Shift functors preserve the chosen coproduct, so its shifted injections
are exactly those in constructibleBoundedComparison. Empty families are included. -/
theorem constructible_compactness_bounded
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [HasDerivedCategory.{u + 1} (CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))]
    (C : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hC : IsConstantModelConstructible (Profinite.continuousMapRingObj E) X C)
    (a b : ℤ) (hab : a ≤ b) (I : Type (u + 1))
    (K : I → DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)))
    (hK : ∀ (i : I) (n : ℤ), ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
      ((DerivedCategory.homologyFunctor _ n).obj (K i)))
    (hbound : ∀ (i : I) (n : ℤ), n < a ∨ b < n →
      IsZero ((DerivedCategory.homologyFunctor _ n).obj (K i))) :
    ∃ (c : Cofan K) (_ : IsColimit c), ∀ s : ℤ,
      Function.Bijective (constructibleBoundedComparison C K c s) := by
  classical
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let P := ObjectProperty.ind.{u + 1}
    (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
  have : P.ContainsZero := containsZero_of_sums P
    (indConstructible_filteredColimits_and_sums ℓ E k p hp hpl X).2
  exact bounded_comparison P C I
    (fun q B hB c hc ↦ single_comparison_change (inferInstance) _ C q B c
      (det_ind_heart_ii_sums ℓ E X (Profinite.padicSubfieldCondensedRing ℓ E)
        (Or.inl rfl) C hC q I B hB c hc))
    a b hab K hK hbound

open Classical in
/-- The same bounded-family comparison for the condensed algebraic closure, whose sections
have values in a finite subextension. Source: blueprint main-20261015,
sk-thm-constructible-compactness-bounded, statement, Lambda = Qlb
(blueprint: det-constructible-compactness-bounded).

Proof: Apply the same categorical bounded-width argument as for the finite
subextension coefficient. The algebraic-closure clauses of
indConstructible_filteredColimits_and_sums and det_ind_heart_ii_sums supply zero
membership of IndCons and the single-degree comparisons, respectively. The auxiliary
finite coefficient field needed to invoke the latter is the explicit bottom
intermediate field, finite over the base field. Ext identifies these comparisons in
the explicitly chosen localization; negative shifts vanish by the standard
t-structure. Apply DerivedCategory.compactFor_of_isGE_of_isLE to the shifted family
with bounds [a-s,b-s]. Finite-support factorization gives surjectivity, and composing
with coordinate projections gives injectivity. The same argument includes empty
families and the zero sheaf. -/
theorem constructible_compactness_bounded_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [HasDerivedCategory.{u + 1} (CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))]
    (C : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hC : IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X C)
    (a b : ℤ) (hab : a ≤ b) (I : Type (u + 1))
    (K : I → DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)))
    (hK : ∀ (i : I) (n : ℤ), ObjectProperty.ind.{u + 1}
      (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
      ((DerivedCategory.homologyFunctor _ n).obj (K i)))
    (hbound : ∀ (i : I) (n : ℤ), n < a ∨ b < n →
      IsZero ((DerivedCategory.homologyFunctor _ n).obj (K i))) :
    ∃ (c : Cofan K) (_ : IsColimit c), ∀ s : ℤ,
      Function.Bijective (constructibleBoundedComparison C K c s) := by
  classical
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let E : PadicAlgCl.FiniteIntermediateField ℓ := ⟨⊥, inferInstance⟩
  let P := ObjectProperty.ind.{u + 1}
    (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
  have : P.ContainsZero := containsZero_of_sums P
    (indConstructible_filteredColimits_and_sums_padicAlgCl ℓ k p hp hpl X).2
  exact bounded_comparison P C I
    (fun q B hB c hc ↦ single_comparison_change (inferInstance) _ C q B c
      (det_ind_heart_ii_sums ℓ E X (Profinite.padicAlgClCondensedRing ℓ)
        (Or.inr rfl) C hC q I B hB c hc))
    a b hab K hK hbound

end AlgebraicGeometry.ProEtale
