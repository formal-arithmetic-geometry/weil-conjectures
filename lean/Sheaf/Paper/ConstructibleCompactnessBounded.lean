/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Sheaf.Paper.LocalizingClosureExistence
import Sheaf.Paper.ConstructibleSingleDegreeComparison
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.Algebra.FiveLemma
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

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

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

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

private lemma directSum_exact {J : Type*} {M N P : J → Type*}
    [∀ j, AddCommGroup (M j)] [∀ j, AddCommGroup (N j)] [∀ j, AddCommGroup (P j)]
    (f : ∀ j, M j →+ N j) (g : ∀ j, N j →+ P j)
    (h : ∀ j, Function.Exact (f j) (g j)) :
    Function.Exact (DirectSum.map f) (DirectSum.map g) := by
  classical
  intro x
  constructor
  · intro hx
    let lift (j : J) (y : N j) : M j :=
      if hy : y = 0 then 0 else if hg : g j y = 0 then ((h j y).1 hg).choose else 0
    have hzero (j : J) : lift j 0 = 0 := by simp [lift]
    refine ⟨DFinsupp.mapRange lift hzero x, ?_⟩
    ext j
    have hj : g j (x j) = 0 := by
      simpa only [DirectSum.map_apply, DFinsupp.zero_apply] using congrArg (fun z ↦ z j) hx
    change f j (lift j (x j)) = x j
    by_cases hz : x j = 0
    · simp [lift, hz]
    · simp only [lift, dif_neg hz, dif_pos hj]
      exact ((h j (x j)).1 hj).choose_spec
  · rintro ⟨y, rfl⟩
    ext j
    simpa only [DirectSum.map_apply, DFinsupp.zero_apply] using (h j).apply_apply_eq_zero (y j)

private abbrev mapCofan {D D' : Type*} [Category* D] [Category* D']
    (F : D ⥤ D') {J : Type*} {K : J → D} (c : Cofan K) :
    Cofan (fun j ↦ F.obj (K j)) :=
  Cofan.mk (F.obj c.pt) (fun j ↦ F.map (c.inj j))

private noncomputable def functorSumComparison
    {D : Type*} [Category* D] (F : D ⥤ AddCommGrpCat.{w})
    {J : Type*} {K : J → D} (c : Cofan K) :
    (⨁ j, F.obj (K j)) →+ F.obj c.pt := by
  classical
  exact DirectSum.toAddMonoid fun j ↦ (F.map (c.inj j)).hom

private lemma functorSumComparison_naturality
    {D : Type*} [Category* D] (F : D ⥤ AddCommGrpCat.{w})
    {J : Type*} {K L : J → D} (c : Cofan K) (d : Cofan L)
    (f : ∀ j, K j ⟶ L j) (g : c.pt ⟶ d.pt)
    (h : ∀ j, c.inj j ≫ g = f j ≫ d.inj j) :
    (F.map g).hom.comp (functorSumComparison F c) =
      (functorSumComparison F d).comp (DirectSum.map fun j ↦ (F.map (f j)).hom) := by
  classical
  apply DirectSum.addHom_ext
  intro j x
  simp only [AddMonoidHom.comp_apply, functorSumComparison, DirectSum.toAddMonoid_of,
    DirectSum.map_of]
  change F.map g (F.map (c.inj j) x) = F.map (d.inj j) (F.map (f j) x)
  simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using
    congrArg (fun z ↦ z x) (congrArg F.map (h j))

private lemma functorSumComparison_iso
    {D : Type*} [Category* D] (F : D ⥤ AddCommGrpCat.{w})
    {J : Type*} {K L : J → D} (c : Cofan K) (d : Cofan L)
    (e : ∀ j, K j ≅ L j) (e' : c.pt ≅ d.pt)
    (h : ∀ j, c.inj j ≫ e'.hom = (e j).hom ≫ d.inj j)
    (hd : Function.Bijective (functorSumComparison F d)) :
    Function.Bijective (functorSumComparison F c) := by
  classical
  have he : ∀ j, Function.Bijective ((F.map (e j).hom).hom) := fun j ↦
    ⟨fun x y hxy ↦ by
      have := congrArg (fun z ↦ F.map (e j).inv z) hxy
      simpa only [← ConcreteCategory.comp_apply, ← F.map_comp, Iso.hom_inv_id,
        F.map_id, ConcreteCategory.id_apply] using this,
      fun y ↦ ⟨F.map (e j).inv y, by
        simp only [← ConcreteCategory.comp_apply, ← F.map_comp, Iso.inv_hom_id,
          F.map_id, ConcreteCategory.id_apply]⟩⟩
  have hi : Function.Injective ((F.map e'.hom).hom) := by
    intro x y hxy
    have := congrArg (fun z ↦ F.map e'.inv z) hxy
    simpa only [← ConcreteCategory.comp_apply, ← F.map_comp, Iso.hom_inv_id,
      F.map_id, ConcreteCategory.id_apply] using this
  have hb := hd.comp (show Function.Bijective
      (DirectSum.map fun j ↦ (F.map (e j).hom).hom) from
    ⟨(DirectSum.map_injective _).2 (fun j ↦ (he j).1),
      (DirectSum.map_surjective _).2 (fun j ↦ (he j).2)⟩)
  change Function.Bijective ((functorSumComparison F d).comp
    (DirectSum.map fun j ↦ (F.map (e j).hom).hom)) at hb
  rw [← show (F.map e'.hom).hom.comp (functorSumComparison F c) =
    (functorSumComparison F d).comp (DirectSum.map fun j ↦ (F.map (e j).hom).hom) from
      functorSumComparison_naturality F c d (fun j ↦ (e j).hom) e'.hom h] at hb
  change Function.Bijective ((F.map e'.hom).hom ∘ functorSumComparison F c) at hb
  exact hb.of_comp_left hi

private lemma functorSumComparison_triangle
    {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : D ⥤ AddCommGrpCat.{w}) [F.IsHomological] [F.ShiftSequence ℤ]
    {J : Type*} (T : J → Pretriangulated.Triangle D)
    (hT : ∀ j, T j ∈ Pretriangulated.distinguishedTriangles (C := D))
    (c : Cofan T) (hc : c.pt ∈ Pretriangulated.distinguishedTriangles (C := D))
    (h₁ : ∀ n : ℤ, Function.Bijective
      (functorSumComparison (F.shift n) (mapCofan Pretriangulated.Triangle.π₁ c)))
    (h₃ : ∀ n : ℤ, Function.Bijective
      (functorSumComparison (F.shift n) (mapCofan Pretriangulated.Triangle.π₃ c))) (n : ℤ) :
    Function.Bijective
      (functorSumComparison (F.shift n) (mapCofan Pretriangulated.Triangle.π₂ c)) := by
  classical
  let f₁ := DirectSum.map fun j ↦ (F.homologySequenceδ (T j) (n - 1) n (by omega)).hom
  let f₂ := DirectSum.map fun j ↦ ((F.shift n).map (T j).mor₁).hom
  let f₃ := DirectSum.map fun j ↦ ((F.shift n).map (T j).mor₂).hom
  let f₄ := DirectSum.map fun j ↦ (F.homologySequenceδ (T j) n (n + 1) rfl).hom
  let g₁ := (F.homologySequenceδ c.pt (n - 1) n (by omega)).hom
  let g₂ := ((F.shift n).map c.pt.mor₁).hom
  let g₃ := ((F.shift n).map c.pt.mor₂).hom
  let g₄ := (F.homologySequenceδ c.pt n (n + 1) rfl).hom
  let i₁ := functorSumComparison (F.shift (n - 1)) (mapCofan Pretriangulated.Triangle.π₃ c)
  let i₂ := functorSumComparison (F.shift n) (mapCofan Pretriangulated.Triangle.π₁ c)
  let i₃ := functorSumComparison (F.shift n) (mapCofan Pretriangulated.Triangle.π₂ c)
  let i₄ := functorSumComparison (F.shift n) (mapCofan Pretriangulated.Triangle.π₃ c)
  let i₅ := functorSumComparison (F.shift (n + 1)) (mapCofan Pretriangulated.Triangle.π₁ c)
  have exact₁ (U : Pretriangulated.Triangle D) 
      (hU : U ∈ Pretriangulated.distinguishedTriangles (C := D)) (a b : ℤ) (hab : a + 1 = b) :=
    (ShortComplex.ab_exact_iff_function_exact _).1 (F.homologySequence_exact₁ U hU a b hab)
  have exact₂ (U : Pretriangulated.Triangle D) 
      (hU : U ∈ Pretriangulated.distinguishedTriangles (C := D)) (a : ℤ) :=
    (ShortComplex.ab_exact_iff_function_exact _).1 (F.homologySequence_exact₂ U hU a)
  have exact₃ (U : Pretriangulated.Triangle D) 
      (hU : U ∈ Pretriangulated.distinguishedTriangles (C := D)) (a b : ℤ) (hab : a + 1 = b) :=
    (ShortComplex.ab_exact_iff_function_exact _).1 (F.homologySequence_exact₃ U hU a b hab)
  refine AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    f₁ f₂ f₃ f₄ g₁ g₂ g₃ g₄ i₁ i₂ i₃ i₄ i₅ ?_ ?_ ?_ ?_
    (directSum_exact _ _ fun j ↦ exact₁ (T j) (hT j) _ _ (by omega))
    (directSum_exact _ _ fun j ↦ exact₂ (T j) (hT j) n)
    (directSum_exact _ _ fun j ↦ exact₃ (T j) (hT j) _ _ rfl)
    (exact₁ c.pt hc _ _ (by omega)) (exact₂ c.pt hc n) (exact₃ c.pt hc _ _ rfl)
    (h₃ (n - 1)).2 (h₁ n) (h₃ n) (h₁ (n + 1)).1
  · apply DirectSum.addHom_ext
    intro j x
    dsimp [g₁, i₁, i₂, f₁, functorSumComparison, mapCofan,
      Pretriangulated.Triangle.π₁, Pretriangulated.Triangle.π₃]
    simp only [DirectSum.toAddMonoid_of, DirectSum.map_of]
    simpa only [ConcreteCategory.comp_apply] using
      congrArg (fun z ↦ z x) (F.homologySequenceδ_naturality (T j) c.pt
        (c.inj j) (n - 1) n (by omega))
  · exact functorSumComparison_naturality (F.shift n)
      (mapCofan Pretriangulated.Triangle.π₁ c) (mapCofan Pretriangulated.Triangle.π₂ c)
      (fun j ↦ (T j).mor₁) c.pt.mor₁ (fun j ↦ (c.inj j).comm₁.symm)
  · exact functorSumComparison_naturality (F.shift n)
      (mapCofan Pretriangulated.Triangle.π₂ c) (mapCofan Pretriangulated.Triangle.π₃ c)
      (fun j ↦ (T j).mor₂) c.pt.mor₂ (fun j ↦ (c.inj j).comm₂.symm)
  · apply DirectSum.addHom_ext
    intro j x
    dsimp [g₄, i₄, i₅, f₄, functorSumComparison, mapCofan,
      Pretriangulated.Triangle.π₁, Pretriangulated.Triangle.π₃]
    simp only [DirectSum.toAddMonoid_of, DirectSum.map_of]
    simpa only [ConcreteCategory.comp_apply] using
      congrArg (fun z ↦ z x) (F.homologySequenceδ_naturality (T j) c.pt
        (c.inj j) n (n + 1) rfl)

private lemma bounded_functor_comparison
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms]
    (F : DerivedCategory A ⥤ AddCommGrpCat.{w}) [F.IsHomological] [F.ShiftSequence ℤ]
    (hbase : ∀ (a : ℤ) (J : Type t) (K : J → DerivedCategory A)
      (c : Cofan K), IsColimit c →
      (∀ j, (K j).IsGE a) → (∀ j, (K j).IsLE a) →
      (∀ j, P ((DerivedCategory.homologyFunctor A a).obj (K j))) →
      ∀ s : ℤ, Function.Bijective (functorSumComparison (F.shift s) c))
    (htri : ∀ (J : Type t) (T : J → Pretriangulated.Triangle (DerivedCategory A)),
      (∀ j, T j ∈ Pretriangulated.distinguishedTriangles) → ∃ c : Cofan T,
      Nonempty (IsColimit (Pretriangulated.Triangle.π₁.mapCocone c)) ∧
      Nonempty (IsColimit (Pretriangulated.Triangle.π₂.mapCocone c)) ∧
      Nonempty (IsColimit (Pretriangulated.Triangle.π₃.mapCocone c)) ∧
      c.pt ∈ Pretriangulated.distinguishedTriangles)
    (N : ℕ) :
    ∀ (a b : ℤ), b - a = N → a ≤ b → ∀ (J : Type t)
      (K : J → DerivedCategory A) (c : Cofan K), IsColimit c →
      (∀ j, (K j).IsGE a) → (∀ j, (K j).IsLE b) →
      (∀ j q, a ≤ q → q ≤ b → P ((DerivedCategory.homologyFunctor A q).obj (K j))) →
      ∀ s : ℤ, Function.Bijective (functorSumComparison (F.shift s) c) := by
  classical
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro a b hN hab J K c hc hge hle hP
    by_cases heq : a = b
    · subst b
      exact hbase a J K c hc hge hle (fun j ↦ hP j a le_rfl le_rfl)
    have hlt : a < b := lt_of_le_of_ne hab heq
    let T : J → Pretriangulated.Triangle (DerivedCategory A) :=
      fun j ↦ (DerivedCategory.TStructure.t.triangleLTGE b).obj (K j)
    have hT (j : J) : T j ∈ Pretriangulated.distinguishedTriangles :=
      DerivedCategory.TStructure.t.triangleLTGE_distinguished b (K j)
    have hAge (j : J) : (T j).obj₁.IsGE a := by
      let := hge j
      exact inferInstanceAs
        (DerivedCategory.TStructure.t.IsGE
          ((DerivedCategory.TStructure.t.truncLT b).obj (K j)) a)
    have hAle (j : J) : (T j).obj₁.IsLE (b - 1) := by
      exact DerivedCategory.TStructure.t.isLE_truncLT_obj _ _ _ (by omega)
    have hBge (j : J) : (T j).obj₃.IsGE b := by
      exact inferInstanceAs
        (DerivedCategory.TStructure.t.IsGE
          ((DerivedCategory.TStructure.t.truncGE b).obj (K j)) b)
    have hBle (j : J) : (T j).obj₃.IsLE b := by
      let := hle j
      exact inferInstanceAs
        (DerivedCategory.TStructure.t.IsLE
          ((DerivedCategory.TStructure.t.truncGE b).obj (K j)) b)
    have hAP (j : J) (q : ℤ) (haq : a ≤ q) (hqb : q ≤ b - 1) :
        P ((DerivedCategory.homologyFunctor A q).obj (T j).obj₁) := by
      let := hBge j
      have := DerivedCategory.isIso_homologyMap_mor₁ (T j) (hT j) (q - 1) q
        (by omega) (DerivedCategory.isZero_of_isGE _ b _ (by omega))
        (DerivedCategory.isZero_of_isGE _ b _ (by omega))
      exact P.prop_of_iso
        (asIso ((DerivedCategory.homologyFunctor A q).map (T j).mor₁)).symm
        (hP j q haq (by omega))
    have hBP (j : J) : P ((DerivedCategory.homologyFunctor A b).obj (T j).obj₃) := by
      let := hAle j
      have := DerivedCategory.isIso_homologyMap_mor₂ (T j) (hT j) b (b + 1) rfl
        (DerivedCategory.isZero_of_isLE _ (b - 1) _ (by omega))
        (DerivedCategory.isZero_of_isLE _ (b - 1) _ (by omega))
      exact P.prop_of_iso (asIso ((DerivedCategory.homologyFunctor A b).map (T j).mor₂))
        (hP j b hab le_rfl)
    obtain ⟨d, hd₁, hd₂, hd₃, hd⟩ := htri J T hT
    have hd₁' : IsColimit (mapCofan Pretriangulated.Triangle.π₁ d) :=
      (Cofan.isColimitMapCoconeEquiv _ _ _).toFun hd₁.some
    have hd₂' : IsColimit (mapCofan Pretriangulated.Triangle.π₂ d) :=
      (Cofan.isColimitMapCoconeEquiv _ _ _).toFun hd₂.some
    have hd₃' : IsColimit (mapCofan Pretriangulated.Triangle.π₃ d) :=
      (Cofan.isColimitMapCoconeEquiv _ _ _).toFun hd₃.some
    have h₁ := ih (b - 1 - a).toNat (by omega) a (b - 1) (by omega) (by omega)
      J (fun j ↦ (T j).obj₁) (mapCofan Pretriangulated.Triangle.π₁ d) hd₁' hAge hAle hAP
    have h₃ := hbase b J (fun j ↦ (T j).obj₃)
      (mapCofan Pretriangulated.Triangle.π₃ d) hd₃' hBge hBle hBP
    intro s
    exact functorSumComparison_iso (F.shift s) c (mapCofan Pretriangulated.Triangle.π₂ d)
      (fun _ ↦ Iso.refl _) (hc.coconePointUniqueUpToIso hd₂')
      (fun j ↦ by
        rw [Iso.refl_hom, Category.id_comp]
        exact hc.comp_coconePointUniqueUpToIso_hom hd₂' ⟨j⟩)
      (functorSumComparison_triangle F T hT d hd h₁ h₃ s)

open Classical in
/-- A constructible sheaf over a finite coefficient subextension commutes with coproducts
of ind-constructible complexes in a common cohomological interval, in every shift.
Source: blueprint main-20261015, sk-thm-constructible-compactness-bounded, statement
(blueprint: det-constructible-compactness-bounded).

Proof: Induct on the nonnegative width b-a, simultaneously for every integer shift.
For width zero, constructible_single_degree_comparison identifies each K with its
single degree-a homology complex and applies det_ind_heart_ii_sums after shifting.
For positive width, the standard t-structure supplies the distinguished triangle
truncLT(b) K -> K -> truncGE(b) K. The outer vertices have bounds [a,b-1] and [b,b].
The cohomology exact sequence identifies their relevant cohomology with that of K;
transport ind-constructibility along these isomorphisms. Apply
localizingClosure_exists to form a distinguished coproduct triangle with specified
vertex coproducts. The shifted preadditive coyoneda gives five-term exact sequences
with terms B[s-1], A[s], K[s], B[s], A[s+1]. Their direct sum is exact: choose a
zero-preserving preimage map on each component kernel, which carries finite support
to finite support. Naturality of the four sequence maps, including the connecting
maps, gives the comparison ladder. Induction and the base case identify its four
outer vertical maps; the additive five lemma makes the middle comparison bijective.
Finally use the unique compatible coproduct isomorphism to transport the assertion
to the chosen cofan. This includes the empty family and every integer shift. -/
theorem constructible_compactness_bounded
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [HasDerivedCategory.{u + 1}
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
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
  have _ := hp
  have _ := hpl
  classical
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let Λ := Profinite.continuousMapRingObj E
  have hex := localizingClosure_exists Λ X ⊥
  let : HasCoproducts.{u + 1} (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) := hex.1
  let F := preadditiveCoyoneda.obj (Opposite.op ((DerivedCategory.singleFunctor _ 0).obj C))
  let c : Cofan K := Cofan.mk (∐ K) (Sigma.ι K)
  have hc : IsColimit c := coproductIsCoproduct K
  refine ⟨c, hc, ?_⟩
  change ∀ s, Function.Bijective (functorSumComparison (F.shift s) c)
  apply bounded_functor_comparison (ObjectProperty.ind.{u + 1}
    (IsConstantModelConstructible Λ X)) F ?_ hex.2.2.1 (b - a).toNat
    a b (by omega) hab I K c hc
    (fun i ↦ (DerivedCategory.isGE_iff _ a).2 (fun n hn ↦ hbound i n (Or.inl hn)))
    (fun i ↦ (DerivedCategory.isLE_iff _ b).2 (fun n hn ↦ hbound i n (Or.inr hn)))
    (fun i q _ _ ↦ hK i q)
  intro a J L d hd hge hle hP s
  exact constructible_single_degree_comparison ℓ E X Λ (Or.inl rfl) C hC
    a J L d hd hge hle hP s

open Classical in
/-- The same bounded-family comparison for the condensed algebraic closure, whose sections
have values in a finite subextension. Source: blueprint main-20261015,
sk-thm-constructible-compactness-bounded, statement, Lambda = Qlb
(blueprint: det-constructible-compactness-bounded).

Proof: Apply the same width induction as for constructible_compactness_bounded.
The single-degree comparison applies to the algebraic-closure coefficient ring by
the second alternative of its coefficient hypothesis. Use the standard truncation
triangle, transport the relevant ind-constructible cohomology across its cohomology
isomorphisms, and form its distinguished coproduct triangle using
localizingClosure_exists. The shifted preadditive coyoneda sequences give the
five-term comparison ladder. Direct sums preserve their exactness by the explicit
zero-preserving component lifts, and all squares commute by naturality, including
those of the connecting maps. The additive five lemma and the compatible coproduct
isomorphism finish the comparison in every shift, also for the empty family. -/
theorem constructible_compactness_bounded_padicAlgCl
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [HasDerivedCategory.{u + 1}
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
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
  have _ := hp
  have _ := hpl
  classical
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let Λ := Profinite.padicAlgClRingObj ℓ
  have hex := localizingClosure_exists Λ X ⊥
  let : HasCoproducts.{u + 1} (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) := hex.1
  let F := preadditiveCoyoneda.obj (Opposite.op ((DerivedCategory.singleFunctor _ 0).obj C))
  let c : Cofan K := Cofan.mk (∐ K) (Sigma.ι K)
  have hc : IsColimit c := coproductIsCoproduct K
  refine ⟨c, hc, ?_⟩
  change ∀ s, Function.Bijective (functorSumComparison (F.shift s) c)
  apply bounded_functor_comparison (ObjectProperty.ind.{u + 1}
    (IsConstantModelConstructible Λ X)) F ?_ hex.2.2.1 (b - a).toNat
    a b (by omega) hab I K c hc
    (fun i ↦ (DerivedCategory.isGE_iff _ a).2 (fun n hn ↦ hbound i n (Or.inl hn)))
    (fun i ↦ (DerivedCategory.isLE_iff _ b).2 (fun n hn ↦ hbound i n (Or.inr hn)))
    (fun i q _ _ ↦ hK i q)
  intro a J L d hd hge hle hP s
  exact constructible_single_degree_comparison ℓ ⟨⊥, inferInstance⟩ X Λ (Or.inr rfl) C hC
    a J L d hd hge hle hP s

end AlgebraicGeometry.ProEtale
