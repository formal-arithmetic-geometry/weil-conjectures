/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstructibleCompactness
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import WeilConjectures.AlgebraicGeometry.AmbientIndDerived
import WeilConjectures.AlgebraicGeometry.ConstructibleCompactnessDevissage

/-!
# Rational constructible compactness over finite or algebraically closed fields

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-compactness/sec-compactness-2/sk-thm-constructible-compactness/_section.md and
sk-thm-constructible-compactness.proof.md, unit statement and proof, with the standing
det-def-sfb-dc-setting preamble (blueprint: sk-thm-constructible-compactness).

The existing `HasConstructibleCompactness` expands both assertions: compactness in
`Loc(Dbc)` and the canonical ambient Hom comparison for every small family in Dic.
Its constructibility predicate uses finite constant scalar models. The two coefficients
are the continuous-function condensed finite extension and the finite-subextension-valued
condensed algebraic closure, pulled back along the pro-etale morphism to the point.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

open AlgebraicGeometry Scheme

namespace AlgebraicGeometry.ProEtale

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

private theorem comparison_of_source_iso
    {D : Type v} [Category.{w} D] [Preadditive D] {I : Type u}
    (F : I → D) [HasCoproduct F] {C C' : D} (e : C ≅ C')
    (c : Cofan F) (hc : IsColimit c)
    (h : Function.Bijective (constructibleCompactnessComparison C' F
      (Cofan.mk (∐ F) (Sigma.ι F)))) :
    Function.Bijective (constructibleCompactnessComparison C F c) := by
  classical
  let s := hc.coconePointUniqueUpToIso (coproductIsCoproduct F)
  let a (i : I) : (C ⟶ F i) ≃+ (C' ⟶ F i) :=
    { toEquiv := Iso.homCongr e (Iso.refl _)
      map_add' := by intro f g; simp [Iso.homCongr, Preadditive.comp_add] }
  let b : (C ⟶ c.pt) ≃+ (C' ⟶ ∐ F) :=
    { toEquiv := Iso.homCongr e s
      map_add' := by
        intro f g
        simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp] }
  apply comparison_transport _ _ a b ?_ h
  intro i f
  change e.inv ≫ (f ≫ c.inj i) ≫ s.hom = (e.inv ≫ f ≫ 𝟙 _) ≫ Sigma.ι F i
  simp only [Category.comp_id, Category.assoc]
  have hs : c.inj i ≫ s.hom = Sigma.ι F i :=
    hc.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct F) ⟨i⟩
  rw [hs]

private theorem compact_in_fullSubcategory
    {D : Type v} [Category.{w} D] [Preadditive D]
    (P : ObjectProperty D) [HasCoproducts.{u} P.FullSubcategory]
    [∀ I : Type u, PreservesColimitsOfShape (Discrete I) P.ι]
    (C : P.FullSubcategory)
    (h : ∀ (I : Type u) (F : I → P.FullSubcategory) (c : Cofan (fun i ↦ (F i).obj)),
      IsColimit c → Function.Bijective
        (constructibleCompactnessComparison C.obj (fun i ↦ (F i).obj) c)) :
    IsCompactObject C := by
  classical
  intro I F
  let G := P.ι
  let c : Cofan (fun i ↦ (F i).obj) :=
    Cofan.mk (G.obj (∐ F)) (fun i ↦ G.map (Sigma.ι F i))
  have hc : IsColimit c :=
    isColimitCofanMkObjOfIsColimit G F _ (coproductIsCoproduct F)
  let e (L : P.FullSubcategory) : (C ⟶ L) ≃+ (C.obj ⟶ L.obj) :=
    AddEquiv.ofBijective G.mapAddHom ⟨G.map_injective, G.map_surjective⟩
  apply comparison_transport _ _ (fun i ↦ e (F i)) (e (∐ F)) ?_ (h I F c hc)
  intro i f
  change G.map (f ≫ Sigma.ι F i) = G.map f ≫ G.map (Sigma.ι F i)
  exact G.map_comp _ _

/-- Every bounded constructible complex is compact in its localizing closure, and its
canonical ambient Hom comparison is bijective for every small family of complexes with
ind-constructible cohomology. This holds for either rational condensed coefficient over
any finite or algebraically closed field of positive characteristic different from `ℓ`.

`HasConstructibleCompactness` uses `Type (u + 1)`-indexed families, all integer cohomology
objects, the ordinary unbounded derived category of internal modules over `Λ_X`, and
`constantModelBoundedConstructible`. It imposes no common cohomological bound on a family.
The existential coproduct structure in its first clause is a conclusion. Its second
clause quantifies over all colimit cofans and uses the actual coprojections to define
`constructibleCompactnessComparison`.

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-six-functors-basics/
sec-compactness/sec-compactness-2/sk-thm-constructible-compactness/, entire unit statement
(_section.md) and proof (sk-thm-constructible-compactness.proof.md); standing
det-def-sfb-dc-setting (blueprint: sk-thm-constructible-compactness).

Proof plan, following the three steps of the node:
1. By sk-cor-ambient-ind-derived, Loc(Dbc) lies in Dic. The arbitrary-class construction
   det-def-localizing-closure-existence gives ambient coproducts and closure under them.
   Since Loc(Dbc) is full, its coproducts and Hom groups are the ambient ones. Thus the
   every-family comparison implies compactness there, as in def-pc-compact-object.
2. For a constructible sheaf in degree zero, apply det-constructible-compactness-sheaf
   with target shift zero to the arbitrary Dic family. Its proof first handles a common
   bounded interval by induction using the ind-heart comparison and then applies the
   common finite-window truncation. Its all-target-shifts clause supplies the sheaf
   comparisons needed for the next step.
3. For this fixed family, det-constructible-compactness-devissage states that the
   objects whose comparisons are isomorphisms for all source shifts form a thick
   triangulated subcategory containing Cons and Dbc. The five lemma, retracts and
   finite Postnikov triangles give this assertion. Evaluate at source shift zero.
   This gives the second clause for every family; step 1 gives the first clause. -/
theorem constructible_compactness_of_finite_or_isAlgClosed
    (k : Type u) [Field k] (hfield : Finite k ∨ IsAlgClosed k)
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (ℓ : ℕ) [Fact ℓ.Prime] (hpl : p ≠ ℓ)
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    HasConstructibleCompactness (Profinite.continuousMapRingObj E) X ∧
      HasConstructibleCompactness (Profinite.padicAlgClRingObj ℓ) X := by
  classical
  have hcoeff (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj Λ] [IsCommMonObj Λ]
      (hΛ : Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj E) ∨
        Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ)) :
      HasConstructibleCompactness Λ X := by
    let A := pulledBackModuleObjects Λ X
    let B : ObjectProperty (DerivedCategory A) := constantModelBoundedConstructible Λ X
    let L := localizingClosure B
    have hex := localizingClosure_exists Λ X B
    let : HasCoproducts.{u + 1} (DerivedCategory A) := hex.1
    have hd := constructibleCompactnessDevissage ℓ k p hp hpl hfield X
      (X ↘ Spec (.of k)) E Λ hΛ
    have hcomp (C : DerivedCategory A) (hC : B C)
        (I : Type (u + 1)) (K : I → DerivedCategory A)
        (hK : ∀ i n, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
          ((DerivedCategory.homologyFunctor A n).obj (K i)))
        (c : Cofan K) (hc : IsColimit c) :
        Function.Bijective (constructibleCompactnessComparison C K c) := by
      have hzero := (hd.1 I K hK).2.2.2.2 C hC 0
      exact comparison_of_source_iso K ((shiftFunctorZero (DerivedCategory A) ℤ).app C).symm
        c hc hzero
    have hlocal : IsLocalizingSubcategory L := hex.2.2.2.1
    let := hlocal.2.1
    let (I : Type (u + 2)) : L.IsClosedUnderColimitsOfShape (Discrete I) := by
      apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
      rintro _ ⟨F, hF⟩
      exact hlocal.2.2 F inferInstance (fun i ↦ hF ⟨i⟩)
    let (I : Type (u + 1)) : L.IsClosedUnderColimitsOfShape (Discrete I) :=
      ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
        (Discrete.equivalence (Equiv.ulift : ULift.{u + 2} I ≃ I))
    let hc : HasCoproducts.{u + 1} L.FullSubcategory := fun I ↦
      hasColimitsOfShape_of_closedUnderColimits (Discrete I) L
    have hLDic : L ≤ fun K ↦ ∀ n, ObjectProperty.ind.{u + 1}
        (IsConstantModelConstructible Λ X)
          ((DerivedCategory.homologyFunctor A n).obj K) := by
      rcases hΛ with h | h
      · cases h
        exact (ambientIndConstructibleDerived ℓ E k p hp hpl X).1.2.2.2.2
      · cases h
        exact (ambientIndConstructibleDerived ℓ E k p hp hpl X).2.2.2.2.2
    refine ⟨⟨hc, ?_⟩, hcomp⟩
    intro C hC
    apply compact_in_fullSubcategory L C
    intro I F c hc
    exact hcomp C.obj hC I (fun i ↦ (F i).obj)
      (fun i ↦ hLDic _ (F i).property) c hc
  exact ⟨hcoeff _ (Or.inl rfl), hcoeff _ (Or.inr rfl)⟩

end AlgebraicGeometry.ProEtale
