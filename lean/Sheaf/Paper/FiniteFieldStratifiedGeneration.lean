/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Sheaf.SixFunctors.FlatModelGeneration
public import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ConstantFieldFlat
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Field.ULift
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all Sheaf.Paper.ProEtaleConstantModuleConstructibility
import all Sheaf.Paper.ConstructibleCoefficientSerre

/-!
# Finite stratified generation over a finite field

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemmas 6.3.3 and 6.3.9,
and the devissage in Lemma 6.7.13 (blueprint: lem-sfb-finite-field-stratified-generation).

The construction is recorded as a finite list. Its first object is zero, its last object
is isomorphic to the input, and each intervening object is either an allowed generator,
a shift of an earlier object, or a middle-term extension of two earlier objects.
Thus the formula explicitly records both finiteness and the permitted operations.
The coefficient and module categories are ordinary, uncompleted constant-ring modules.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme

-- Fix the coefficient universe before typeclass search tries to invert a `max`.
private local instance finiteFieldAbLocallyBijective (X : AlgebraicGeometry.Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u + 1} X

namespace FiniteStratifiedConstruction

variable {C : Type v} [Category.{w} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ m : ℤ, (shiftFunctor C m).Additive] [Pretriangulated C]

private def Step (G : ObjectProperty C) (K : ℕ → C) (i : ℕ) : Prop :=
  G (K (i + 1)) ∨
    (∃ (k : ℕ) (m : ℤ), k ≤ i ∧ Nonempty (K (i + 1) ≅ (K k)⟦m⟧)) ∨
    (∃ k l, k ≤ i ∧ l ≤ i ∧
      ∃ (f : K k ⟶ K (i + 1)) (g : K (i + 1) ⟶ K l)
        (h : K l ⟶ (K k)⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang C)

private def Built (G : ObjectProperty C) : ObjectProperty C := fun P ↦
  ∃ (n : ℕ) (K : ℕ → C), IsZero (K 0) ∧ Nonempty (K n ≅ P) ∧
    ∀ i < n, Step G K i

private theorem built_iso (G : ObjectProperty C) {P Q : C} (e : P ≅ Q)
    (hP : Built G P) : Built G Q := by
  obtain ⟨n, K, h0, ⟨eP⟩, hs⟩ := hP
  exact ⟨n, K, h0, ⟨eP ≪≫ e⟩, hs⟩

private theorem built_zero (G : ObjectProperty C) {P : C} (hP : IsZero P) : Built G P :=
  ⟨0, fun _ ↦ P, hP, ⟨Iso.refl _⟩, by omega⟩

private theorem built_append (G : ObjectProperty C) {n : ℕ} {K : ℕ → C}
    (h0 : IsZero (K 0)) (hs : ∀ i < n, Step G K i) (P : C)
    (hp : Step G (fun i ↦ if i ≤ n then K i else P) n) : Built G P := by
  let L : ℕ → C := fun i ↦ if i ≤ n then K i else P
  refine ⟨n + 1, L, ?_, ⟨?_⟩, ?_⟩
  · simpa [L] using h0
  · simpa [L] using Iso.refl P
  · intro i hi
    by_cases hin : i < n
    · have he : ∀ j ≤ i + 1, L j = K j := fun j hj ↦ if_pos (by omega)
      rcases hs i hin with h | ⟨k, m, hk, ⟨e⟩⟩ | ⟨k, l, hk, hl, f, g, h, ht⟩
      · exact Or.inl (by simpa only [he (i + 1) le_rfl] using h)
      · exact Or.inr (Or.inl ⟨k, m, hk, ⟨by
          simpa only [he (i + 1) le_rfl, he k (by omega)] using e⟩⟩)
      · apply Or.inr ∘ Or.inr
        refine ⟨k, l, hk, hl, ?_⟩
        rw [he (i + 1) le_rfl, he k (by omega), he l (by omega)]
        exact ⟨f, g, h, ht⟩
    · have : i = n := by omega
      subst i
      exact hp

private theorem built_generator (G : ObjectProperty C) {P : C} (hP : G P) : Built G P := by
  let : Zero C := HasZeroObject.zero' C
  apply built_append G (n := 0) (K := fun _ ↦ 0) (isZero_zero _) (by omega) P
  exact Or.inl (by simpa using hP)

private theorem built_shift (G : ObjectProperty C) {P : C} (hP : Built G P) (m : ℤ) :
    Built G (P⟦m⟧) := by
  obtain ⟨n, K, h0, ⟨e⟩, hs⟩ := hP
  apply built_append G h0 hs (P⟦m⟧)
  refine Or.inr (Or.inl ⟨n, m, le_rfl, ⟨?_⟩⟩)
  simpa using (shiftFunctor C m).mapIso e.symm

private theorem built_join (G : ObjectProperty C) {P Q : C}
    (hP : Built G P) (hQ : Built G Q) :
    ∃ (n : ℕ) (K : ℕ → C) (k l : ℕ), k ≤ n ∧ l ≤ n ∧
      IsZero (K 0) ∧ Nonempty (K k ≅ P) ∧ Nonempty (K l ≅ Q) ∧
      (∀ i < n, Step G K i) := by
  classical
  obtain ⟨a, A, hA, eA, hsA⟩ := hP
  obtain ⟨b, B, hB, eB, hsB⟩ := hQ
  let K : ℕ → C := fun i ↦ if i ≤ a then A i else B (i - (a + 1))
  have hleft (i : ℕ) (hi : i ≤ a) : K i = A i := if_pos hi
  have hright (i : ℕ) : K (a + 1 + i) = B i := by
    simp [K, show ¬a + 1 + i ≤ a from by omega]
  refine ⟨a + 1 + b, K, a, a + 1 + b, by omega, le_rfl, ?_, ?_, ?_, ?_⟩
  · simpa only [hleft 0 (by omega)] using hA
  · simpa only [hleft a le_rfl] using eA
  · simpa only [hright b] using eB
  · intro i hi
    by_cases hia : i < a
    · rcases hsA i hia with h | ⟨k, m, hk, ⟨e⟩⟩ | ⟨k, l, hk, hl, f, g, h, ht⟩
      · exact Or.inl (by simpa only [hleft (i + 1) (by omega)] using h)
      · refine Or.inr (Or.inl ⟨k, m, hk, ⟨?_⟩⟩)
        simpa only [hleft (i + 1) (by omega), hleft k (by omega)] using e
      · apply Or.inr ∘ Or.inr
        refine ⟨k, l, hk, hl, ?_⟩
        rw [hleft (i + 1) (by omega), hleft k (by omega), hleft l (by omega)]
        exact ⟨f, g, h, ht⟩
    · by_cases hie : i = a
      · subst i
        refine Or.inr (Or.inl ⟨0, 0, by omega, ⟨?_⟩⟩)
        rw [show a + 1 = a + 1 + 0 from by omega, hright, hleft 0 (by omega)]
        exact hB.iso hA ≪≫ (shiftFunctorZero C ℤ).symm.app _
      · let j := i - (a + 1)
        have hij : i = a + 1 + j := by omega
        have hj : j < b := by omega
        rcases hsB j hj with h | ⟨k, m, hk, ⟨e⟩⟩ | ⟨k, l, hk, hl, f, g, h, ht⟩
        · exact Or.inl (by simpa only [hij,
            show a + 1 + j + 1 = a + 1 + (j + 1) from by omega, hright] using h)
        · refine Or.inr (Or.inl ⟨a + 1 + k, m, by omega, ⟨?_⟩⟩)
          simpa only [hij, show a + 1 + j + 1 = a + 1 + (j + 1) from by omega,
            hright] using e
        · apply Or.inr ∘ Or.inr
          refine ⟨a + 1 + k, a + 1 + l, by omega, by omega, ?_⟩
          rw [hij, show a + 1 + j + 1 = a + 1 + (j + 1) from by omega,
            hright, hright, hright]
          exact ⟨f, g, h, ht⟩

private theorem built_extension (G : ObjectProperty C) (T : Triangle C)
    (ht : T ∈ distTriang C) (h1 : Built G T.obj₁) (h3 : Built G T.obj₃) :
    Built G T.obj₂ := by
  obtain ⟨n, K, k, l, hk, hl, h0, ⟨e1⟩, ⟨e3⟩, hs⟩ := built_join G h1 h3
  apply built_append G h0 hs T.obj₂
  apply Or.inr ∘ Or.inr
  refine ⟨k, l, hk, hl, ?_⟩
  dsimp only
  rw [if_neg (show ¬n + 1 ≤ n from by omega), if_pos hk, if_pos hl]
  refine ⟨e1.hom ≫ T.mor₁, T.mor₂ ≫ e3.inv,
    e3.hom ≫ T.mor₃ ≫ e1.inv⟦(1 : ℤ)⟧', ?_⟩
  apply isomorphic_distinguished _ ht
  exact Triangle.isoMk _ _ e1 (Iso.refl _) e3
    (by simp) (by simp) (by simp)

private instance built_replete (G : ObjectProperty C) :
    (Built G).IsClosedUnderIsomorphisms := ⟨fun e h ↦ built_iso G e h⟩

private instance built_triangulated (G : ObjectProperty C) : (Built G).IsTriangulated where
  exists_zero := by
    let : Zero C := HasZeroObject.zero' C
    exact ⟨0, isZero_zero _, built_zero G (isZero_zero _)⟩
  isStableUnderShiftBy m := ⟨fun _ h ↦ built_shift G h m⟩
  toIsTriangulatedClosed₂ := .mk' (fun T ht h1 h3 ↦ built_extension G T ht h1 h3)

end FiniteStratifiedConstruction

namespace AlgebraicGeometry

private theorem finiteField_module_flat
    (X : Scheme.{u}) (A : Type u) [Field A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A)) :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := ProEt.topology X) (R := proEtaleConstantRing X A) F := by
  exact SheafOfModules.isFlat_constantFieldModule.{u + 1, u, u + 1, u + 1}
    (ProEt.topology X) (ULift.{u + 1, u} A) F

private theorem finiteField_lisse_models
    (S : Scheme.{u}) (A : Type u) [Field A] [Finite A]
    (L : proEtaleRingModules S (proEtaleConstantRing S A))
    (hL : FlatModelProEtaleLisseProjective S A L) :
    IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses S A
      (fun M ↦ Module.Finite (ULift.{u + 1, u} A) M) L := by
  have hfin : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S),
      Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing S A) L) :=
    fun Ω _ _ x ↦ (hL.2 Ω x).1
  have hc := (finiteLocal_iff S A L).mpr ⟨hL.1, hfin⟩
  obtain ⟨I, U, f, hf, hm⟩ := ProEtale.finiteModels_over (ULift.{u + 1, u} A) _ hc
  refine ⟨I, U, f, hf, fun t ↦ ?_⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := hm t
  have : Finite M := hM
  let a := Functor.whiskerLeft (Over.forget (U t)).op (proEtaleModuleScalarUnit S A)
  have : Presheaf.IsLocallyInjective ((ProEt.topology S).over (U t)) a :=
    (proEtaleConstantRingUnit_over_locallyBijective S A (U t)).1
  have : Presheaf.IsLocallySurjective ((ProEt.topology S).over (U t)) a :=
    (proEtaleConstantRingUnit_over_locallyBijective S A (U t)).2
  let R := ((sheafCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (proEtaleConstantRing S A)).over (U t)
  have := ConstantScalarComparison.constantComparisonHom_isIso
    ((ProEt.topology S).over (U t)) (ULift.{u + 1, u} A) R a M
  refine ⟨M, inferInstance, ⟨?_⟩⟩
  exact (ConstantScalarComparison.restrictionFullyFaithful
    ((ProEt.topology S).over (U t)) (ULift.{u + 1, u} A) R a).preimageIso
      (e ≪≫ asIso (ConstantScalarComparison.constantComparisonHom
        ((ProEt.topology S).over (U t)) (ULift.{u + 1, u} A) R a M))

/-- A bounded constructible complex over a finite field admits a finite construction from
locally closed extensions of locally constant finite-dimensional module sheaves. The
indices in each shift or triangle step refer only to earlier entries of the finite list.
The generator uses the canonical open immersion into the scheme-theoretic image followed
by the closed immersion, as in `flatModelProEtaleExtension`. Local finite-dimensionality
is expressed by the recorded local-model predicate with `Module.Finite` over the lifted
field; this is precisely finite-dimensionality, with no extra stalk or origin assumption.

Source: Bhatt--Scholze, Lemmas 6.3.3 and 6.3.9, finite devissage in Lemma 6.7.13
(blueprint: lem-sfb-finite-field-stratified-generation).

Proof plan. On the small-site skeleton apply `SheafOfModules.isFlat_constantFieldModule`
to each cohomology sheaf. Ordinary abelian sheafification and the locally bijective
criterion supply its site hypotheses. The coefficient ring is exactly the sheafification
of the constant field, so every such module sheaf is flat.

Apply clauses (1) and (2) of `det-sf-flat-model-generation` to a constructible sheaf F.
They give a finite ordered locally closed stratification with locally constant finite
projective restrictions and a finite filtration of F by the canonical g_* j_! extensions.
The strata are constructible because X is Noetherian; finite projective modules over A
are finite-dimensional. Each short exact sequence of this filtration gives the
single-object distinguished triangle by `ShortComplex.ShortExact.singleTriangle_distinguished`.
Beginning with zero and concatenating these middle-term extensions constructs F[0].

Choose the bounds a and b of P. Good truncation gives an acyclic truncation below a,
which is zero in the derived category, and identifies the truncation at b with P.
For each q from a to b the truncation triangle has first term tau_le(q-1) P,
middle term tau_le(q) P and third term H^q(P)[-q]. Construct H^q(P)[0] by the previous
paragraph and shift by -q. Append the corresponding middle-term extension. Finite
induction through this interval constructs P. Concatenating the finite lists for its
finitely many cohomology sheaves gives the displayed list; transport the endpoints
along the truncation isomorphisms. For acyclic P, including the empty scheme, take the
list consisting solely of a zero object. -/
theorem finiteField_stratifiedGeneration
    (X : Scheme.{u}) [IsNoetherian X] (A : Type u) [Field A] [Finite A]
    (P : proEtaleDerivedCategory X A)
    (_hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((@_root_.DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2}
        (proEtaleRingModules X (proEtaleConstantRing X A)) _
        (@SheafOfModules.instAbelian _ _ _ _
          (WeilConjectures.integralCoefficientAbSheafify.{u, u + 1} X)
          (WeilConjectures.integralCoefficientAbLocallyBijective.{u, u + 1} X)) _ q).obj P))
    (_hconstructible : ∀ q : ℤ, IsConstructibleProEtaleModuleSheaf X A
      ((@_root_.DerivedCategory.homologyFunctor.{u + 2, u + 1, u + 2}
        (proEtaleRingModules X (proEtaleConstantRing X A)) _
        (@SheafOfModules.instAbelian _ _ _ _
          (WeilConjectures.integralCoefficientAbSheafify.{u, u + 1} X)
          (WeilConjectures.integralCoefficientAbLocallyBijective.{u, u + 1} X)) _ q).obj P)) :
    ∃ (n : ℕ) (K : Fin (n + 1) → proEtaleDerivedCategory X A),
      IsZero (K 0) ∧ Nonempty (K (Fin.last n) ≅ P) ∧
      ∀ i : Fin n,
        (∃ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
          (L : proEtaleRingModules S (proEtaleConstantRing S A)),
          Topology.IsConstructible (Set.range a.base) ∧
          IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses S A
            (fun M ↦ Module.Finite (ULift.{u + 1, u} A) M) L ∧
          Nonempty (K i.succ ≅ (@_root_.DerivedCategory.singleFunctor.{u + 2, u + 1, u + 2}
            (proEtaleRingModules X (proEtaleConstantRing X A)) _
            (@SheafOfModules.instAbelian _ _ _ _
              (WeilConjectures.integralCoefficientAbSheafify.{u, u + 1} X)
              (WeilConjectures.integralCoefficientAbLocallyBijective.{u, u + 1} X)) _ 0).obj
            ((flatModelProEtaleExtension A a ha).obj L))) ∨
        (∃ (k : Fin (n + 1)) (m : ℤ), k.val ≤ i.val ∧
          Nonempty (K i.succ ≅ (K k)⟦m⟧)) ∨
        (∃ k l : Fin (n + 1), k.val ≤ i.val ∧ l.val ≤ i.val ∧
          ∃ (f : K k ⟶ K i.succ) (g : K i.succ ⟶ K l)
            (h : K l ⟶ (K k)⟦(1 : ℤ)⟧),
            Triangle.mk f g h ∈ distTriang (proEtaleDerivedCategory X A)) := by
  classical
  let C := proEtaleRingModules X (proEtaleConstantRing X A)
  let : Abelian C := @SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} _ _ _ _
    (WeilConjectures.integralCoefficientAbSheafify.{u, u + 1} X)
    (WeilConjectures.integralCoefficientAbLocallyBijective.{u, u + 1} X)
  let : HasDerivedCategory.{u + 2} C := HasDerivedCategory.standard C
  let G : ObjectProperty (proEtaleDerivedCategory X A) := fun Q ↦
    ∃ (S : Scheme.{u}) (a : S ⟶ X) (ha : IsImmersion a)
      (L : proEtaleRingModules S (proEtaleConstantRing S A)),
      Topology.IsConstructible (Set.range a.base) ∧
      IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses S A
        (fun M ↦ Module.Finite (ULift.{u + 1, u} A) M) L ∧
      Nonempty (Q ≅ (_root_.DerivedCategory.singleFunctor.{u + 2, u + 1, u + 2} C 0).obj
        ((flatModelProEtaleExtension A a ha).obj L))
  let Q := FiniteStratifiedConstruction.Built G
  have hsingle (F : C) (hc : IsConstructibleProEtaleModuleSheaf X A F) :
      Q ((_root_.DerivedCategory.singleFunctor.{u + 2, u + 1, u + 2} C 0).obj F) := by
    have hflat := finiteField_module_flat X A F
    have hc' : IsConstructibleProEtaleCoefficientModuleSheaf X (ULift.{u + 1, u} A) F :=
      (CoefficientSerre.coefficient_constructible_iff X (ULift.{u + 1, u} A) F).mpr
        ((proEtaleModuleRestriction_constructible_iff X A F).mp hc)
    obtain ⟨str, ho, hp⟩ := proEtale_flatConstructible_orderedStratification X A F hc' hflat
    obtain ⟨⟨M, h0, ⟨e⟩, hs⟩, _⟩ :=
      proEtale_flatConstructible_extensionFiltration X A F hc' hflat str ho hp
    have hgen (k : Fin str.n) :
        Q ((_root_.DerivedCategory.singleFunctor.{u + 2, u + 1, u + 2} C 0).obj
        ((flatModelProEtaleExtension A (str.immersion k) (str.isImmersion k)).obj
          (proEtaleConstantModulePullback (str.immersion k) A F))) := by
      apply FiniteStratifiedConstruction.built_generator
      exact ⟨str.domain k, str.immersion k, str.isImmersion k, _,
        (by simpa only [str.range_immersion k] using str.isConstructible_stratum k),
        finiteField_lisse_models _ A _ (hp k), ⟨Iso.refl _⟩⟩
    have h (k : Fin (str.n + 1)) :
        Q ((_root_.DerivedCategory.singleFunctor.{u + 2, u + 1, u + 2} C 0).obj (M k)) := by
      induction k using Fin.induction with
      | zero =>
        exact Q.prop_of_isZero
          (Functor.map_isZero
            (_root_.DerivedCategory.singleFunctor.{u + 2, u + 1, u + 2} C 0) h0)
      | succ k ih =>
        obtain ⟨f, g, hfg, hses⟩ := hs k
        exact Q.ext_of_isTriangulatedClosed₂
          (ShortComplex.ShortExact.singleTriangle.{u + 2, u + 1, u + 2} hses)
          (ShortComplex.ShortExact.singleTriangle_distinguished.{u + 2, u + 1, u + 2} hses)
          ih (hgen k)
    exact Q.prop_of_iso
      ((_root_.DerivedCategory.singleFunctor.{u + 2, u + 1, u + 2} C 0).mapIso e) (h _)
  let R : ObjectProperty C := ObjectProperty.isoClosure (IsConstructibleProEtaleModuleSheaf X A)
  have hsingleq (q : ℤ) (F : C) (hF : R F) :
      Q ((_root_.DerivedCategory.singleFunctor.{u + 2, u + 1, u + 2} C q).obj F) := by
    obtain ⟨F', hc, ⟨e⟩⟩ := hF
    have h0 := Q.prop_of_iso
      ((_root_.DerivedCategory.singleFunctor.{u + 2, u + 1, u + 2} C 0).mapIso e.symm)
      (hsingle F' hc)
    exact Q.prop_of_iso
      (((_root_.DerivedCategory.singleFunctors C).shiftIso (-q) q 0 (by omega)).app F)
      (Q.le_shift (-q) _ h0)
  obtain ⟨a, b, hab, hv⟩ := _hbounded
  have ha : P.IsGE a := (_root_.DerivedCategory.isGE_iff P a).mpr
    (fun i hi ↦ hv i (Or.inl hi))
  have hb : P.IsLE (a + (b - a + 1).toNat - 1) := by
    have he : a + (b - a + 1).toNat - 1 = b := by omega
    rw [he]
    exact (_root_.DerivedCategory.isLE_iff P b).mpr (fun i hi ↦ hv i (Or.inr hi))
  have hP : Q P := _root_.DerivedCategory.prop_of_isGE_of_isLE_of_degreewise Q
    (fun _ hz ↦ Q.prop_of_isZero hz)
    (fun T ht h1 h3 ↦ Q.ext_of_isTriangulatedClosed₂ T ht h1 h3)
    (fun _ ↦ R) hsingleq (b - a + 1).toNat a P ha hb
    (fun q _ _ ↦ ⟨_, _hconstructible q, ⟨Iso.refl _⟩⟩)
  obtain ⟨n, K, h0, e, hs⟩ := hP
  refine ⟨n, fun i ↦ K i.val, h0, e, fun i ↦ ?_⟩
  rcases hs i.val i.isLt with h | ⟨k, m, hk, e⟩ | ⟨k, l, hk, hl, f, g, h, ht⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨⟨k, by omega⟩, m, hk, e⟩)
  · exact Or.inr (Or.inr ⟨⟨k, by omega⟩, ⟨l, by omega⟩, hk, hl, f, g, h, ht⟩)

end AlgebraicGeometry
