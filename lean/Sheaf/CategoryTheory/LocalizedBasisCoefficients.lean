/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import Sheaf.CategoryTheory.LocalizationLinearDescent

/-!
# Localization of a specified internal finite basis

Source: Stacks, sites-modules.tex, Tags 0EMC (lemma-simple-invert) and 0EMD
(lemma-simple-invert-module), and the inverting-ell sentence in blueprint
`det-prop-sfb-cartesian-coefficients-finite-free`.
(blueprint: lem-sfb-localized-basis-coefficients)

Global sections are maps from the tensor unit. Invertibility of a section is expressed
by invertibility of its multiplication endomorphism. The finite-sum map in the square
is the componentwise localization map, written using the module biproduct projections
and inclusions. No assertion about objectwise localization of section rings is made.
-/

@[expose] public section

set_option autoImplicit false

universe u v uI uC vC w

open CategoryTheory Limits MonoidalCategory MonObj

namespace CategoryTheory.Mod

/-- The precise finite-basis localization assertion in a given tensor category.
The predicate packages the assertion rather than asserting it for arbitrary categories.
The first conjunct supplies tensor additivity; the remaining assertion is independent
of the choice of that proof. A global section is invertible exactly when multiplication
by it is an isomorphism: applying the inverse to the unit gives its inverse section.
The summand formulas specify the finite-sum formulas on every local tuple.

Source: Stacks Tags 0EMC/0EMD and the blueprint parent's inverting-ell sentence.
(blueprint: lem-sfb-localized-basis-coefficients)
-/
def LocalizedBasisCoefficients
    {H : Type u} [Category.{v} H] [MonoidalCategory H] [BraidedCategory H]
    [Abelian H] : Prop :=
  Nonempty (MonoidalPreadditive H) ∧
  ∀ [MonoidalPreadditive H]
    (R T A B : H) [MonObj R] [MonObj T] [MonObj A] [MonObj B]
    [IsCommMonObj R] [IsCommMonObj T] [IsCommMonObj A] [IsCommMonObj B]
    (φ : Mon.mk R ⟶ Mon.mk T) (t : 𝟙_ H ⟶ R)
    (I : Type uI) [Fintype I] (b : I → (𝟙_ H ⟶ T))
    (q : (⨁ fun _ : I ↦ regular R) ≅ (comap φ.hom).obj (regular T)),
    (∀ i : I,
      (biproduct.ι (fun _ : I ↦ regular R) i).hom ≫ q.hom.hom =
        φ.hom ≫ (ρ_ T).inv ≫ T ◁ b i ≫ μ[T]) →
    ∀ (jR : Mon.mk R ⟶ Mon.mk A) (jT : Mon.mk T ⟶ Mon.mk B),
      IsIso ((λ_ A).inv ≫ (t ≫ jR.hom) ▷ A ≫ μ[A]) →
      (∀ (D : H) [MonObj D] [IsCommMonObj D] (f : Mon.mk R ⟶ Mon.mk D),
        IsIso ((λ_ D).inv ≫ (t ≫ f.hom) ▷ D ≫ μ[D]) →
        ∃! g : Mon.mk A ⟶ Mon.mk D, jR ≫ g = f) →
      IsIso ((λ_ B).inv ≫ (t ≫ φ.hom ≫ jT.hom) ▷ B ≫ μ[B]) →
      (∀ (D : H) [MonObj D] [IsCommMonObj D] (f : Mon.mk T ⟶ Mon.mk D),
        IsIso ((λ_ D).inv ≫ (t ≫ φ.hom ≫ f.hom) ▷ D ≫ μ[D]) →
        ∃! g : Mon.mk B ⟶ Mon.mk D, jT ≫ g = f) →
      ∃ ψ : Mon.mk A ⟶ Mon.mk B,
        jR ≫ ψ = φ ≫ jT ∧
        (∀ ψ' : Mon.mk A ⟶ Mon.mk B, jR ≫ ψ' = φ ≫ jT → ψ' = ψ) ∧
        ∃ qt : (⨁ fun _ : I ↦ regular A) ≅ (comap ψ.hom).obj (regular B),
          (∀ i : I,
            (biproduct.ι (fun _ : I ↦ regular A) i).hom ≫ qt.hom.hom =
              ψ.hom ≫ (ρ_ B).inv ≫ B ◁ (b i ≫ jT.hom) ≫ μ[B]) ∧
          ((∑ i : I,
            (biproduct.π (fun _ : I ↦ regular R) i).hom ≫ jR.hom ≫
              (biproduct.ι (fun _ : I ↦ regular A) i).hom) ≫ qt.hom.hom =
            q.hom.hom ≫ jT.hom) ∧
          (∀ f : (⨁ fun _ : I ↦ regular A) ⟶ (comap ψ.hom).obj (regular B),
            (∑ i : I,
              (biproduct.π (fun _ : I ↦ regular R) i).hom ≫ jR.hom ≫
                (biproduct.ι (fun _ : I ↦ regular A) i).hom) ≫ f.hom =
              q.hom.hom ≫ jT.hom → f = qt.hom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem regularLift_scalar_formula
    {H : Type u} [Category.{v} H] [MonoidalCategory H]
    {A B : H} [MonObj A] [MonObj B]
    (ψ : Mon.mk A ⟶ Mon.mk B) (x : 𝟙_ H ⟶ B) :
    (regularLift ((comap ψ.hom).obj (regular B)) x).hom =
      ψ.hom ≫ (ρ_ B).inv ≫ B ◁ x ≫ μ[B] := by
  change (ρ_ A).inv ≫ A ◁ x ≫ ψ.hom ▷ B ≫ μ[B] = _
  rw [whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem underlying_biproduct_ext
    {H : Type u} [Category.{v} H] [MonoidalCategory H]
    [Abelian H] [MonoidalPreadditive H]
    {R : H} [MonObj R] {I : Type uI} [Finite I]
    {Y : H} (f g : (⨁ fun _ : I ↦ regular R).X ⟶ Y)
    (h : ∀ i, (biproduct.ι (fun _ : I ↦ regular R) i).hom ≫ f =
      (biproduct.ι (fun _ : I ↦ regular R) i).hom ≫ g) : f = g := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have total : (∑ i : I, biproduct.π (fun _ : I ↦ regular R) i ≫
      biproduct.ι (fun _ : I ↦ regular R) i) = 𝟙 _ := by
    apply biproduct.hom_ext'
    intro i
    rw [Preadditive.comp_sum, Finset.sum_eq_single i]
    · rw [← Category.assoc, biproduct.ι_π_self, Category.id_comp, Category.comp_id]
    · intro j _ hji
      rw [← Category.assoc, biproduct.ι_π_ne _ hji.symm, zero_comp]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have ht := congrArg ((forget R).map) total
  simp only [Functor.map_sum, Functor.map_comp, Functor.map_id] at ht
  change (∑ i : I, (biproduct.π (fun _ : I ↦ regular R) i).hom ≫
    (biproduct.ι (fun _ : I ↦ regular R) i).hom) = 𝟙 _ at ht
  calc
    f = (𝟙 _) ≫ f := (Category.id_comp f).symm
    _ = ∑ i : I, (biproduct.π (fun _ : I ↦ regular R) i).hom ≫
        (biproduct.ι (fun _ : I ↦ regular R) i).hom ≫ f := by
      rw [← ht, Preadditive.sum_comp]
      simp only [Category.assoc]
    _ = ∑ i : I, (biproduct.π (fun _ : I ↦ regular R) i).hom ≫
        (biproduct.ι (fun _ : I ↦ regular R) i).hom ≫ g := by
      apply Finset.sum_congr rfl
      intro i _
      rw [h i]
    _ = g := by
      simp only [← Category.assoc]
      rw [← Preadditive.sum_comp, ht, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem regular_multiply_natural
    {H : Type u} [Category.{v} H] [MonoidalCategory H]
    {T B : H} [MonObj T] [MonObj B]
    (j : Mon.mk T ⟶ Mon.mk B) (x : 𝟙_ H ⟶ T) :
    (ρ_ T).inv ≫ T ◁ x ≫ μ[T] ≫ j.hom =
      j.hom ≫ (ρ_ B).inv ≫ B ◁ (x ≫ j.hom) ≫ μ[B] := by
  rw [IsMonHom.mul_hom, tensorHom_def]
  simp only [Category.assoc, whiskerLeft_comp]
  rw [whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem underlying_ι_π
    {H : Type u} [Category.{v} H] [MonoidalCategory H]
    [Abelian H] [MonoidalPreadditive H]
    {R : H} [MonObj R] {I : Type uI} [Finite I] [DecidableEq I] (i j : I) :
    (biproduct.ι (fun _ : I ↦ regular R) i).hom ≫
      (biproduct.π (fun _ : I ↦ regular R) j).hom =
        if i = j then 𝟙 R else 0 := by
  classical
  let : Fintype I := Fintype.ofFinite I
  by_cases h : i = j
  · subst j
    rw [if_pos rfl]
    change (biproduct.ι (fun _ : I ↦ regular R) i).hom ≫
      (biproduct.π (fun _ : I ↦ regular R) i).hom = 𝟙 R
    exact congrArg (fun f : regular R ⟶ regular R ↦ f.hom)
      (biproduct.ι_π_self (fun _ : I ↦ regular R) i)
  · simp only [if_neg h]
    exact congrArg (fun f : regular R ⟶ regular R ↦ f.hom)
      (biproduct.ι_π_ne (fun _ : I ↦ regular R) h)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem componentwise_ι
    {H : Type u} [Category.{v} H] [MonoidalCategory H]
    [Abelian H] [MonoidalPreadditive H]
    {R A : H} [MonObj R] [MonObj A] {I : Type uI} [Fintype I]
    (r : R ⟶ A) (i : I) :
    (biproduct.ι (fun _ : I ↦ regular R) i).hom ≫
      (∑ j : I, (biproduct.π (fun _ : I ↦ regular R) j).hom ≫ r ≫
        (biproduct.ι (fun _ : I ↦ regular A) j).hom) =
      r ≫ (biproduct.ι (fun _ : I ↦ regular A) i).hom := by
  classical
  simp only [Preadditive.comp_sum, ← Category.assoc, underlying_ι_π]
  simp only [ite_comp, zero_comp, Finset.sum_ite_eq, Finset.mem_univ, if_pos]
  change (𝟙 R ≫ r) ≫ (biproduct.ι (fun _ : I ↦ regular A) i).hom = _
  rw [Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def regularScalarMap
    {H : Type u} [Category.{v} H] [MonoidalCategory H]
    {R A : H} [MonObj R] [MonObj A] (j : Mon.mk R ⟶ Mon.mk A) :
    regular R ⟶ (comap j.hom).obj (regular A) :=
  homMk j.hom (by
    change μ[R] ≫ j.hom = R ◁ j.hom ≫ j.hom ▷ A ≫ μ[A]
    rw [IsMonHom.mul_hom, tensorHom_def', Category.assoc])

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finite_regular_hom_ext
    {H : Type u} [Category.{v} H] [MonoidalCategory H]
    [Abelian H] [MonoidalPreadditive H]
    {R A : H} [MonObj R] [MonObj A] {I : Type uI} [Fintype I]
    (j : Mon.mk R ⟶ Mon.mk A) {N : Mod H A}
    (f g : (⨁ fun _ : I ↦ regular A) ⟶ N)
    (h : (∑ i : I, (biproduct.π (fun _ : I ↦ regular R) i).hom ≫ j.hom ≫
      (biproduct.ι (fun _ : I ↦ regular A) i).hom) ≫ f.hom =
      (∑ i : I, (biproduct.π (fun _ : I ↦ regular R) i).hom ≫ j.hom ≫
        (biproduct.ι (fun _ : I ↦ regular A) i).hom) ≫ g.hom) : f = g := by
  apply biproduct.hom_ext'
  intro i
  apply regular_hom_ext
  have hi := congrArg
    (fun k ↦ (η[R] ≫ (biproduct.ι (fun _ : I ↦ regular R) i).hom) ≫ k) h
  simp only [Category.assoc] at hi
  rw [← Category.assoc (biproduct.ι (fun _ : I ↦ regular R) i).hom,
    componentwise_ι j.hom,
    ← Category.assoc (biproduct.ι (fun _ : I ↦ regular R) i).hom,
    componentwise_ι j.hom] at hi
  simpa only [Mod.comp_hom', ← Category.assoc, IsMonHom.one_hom] using hi

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Localization preserves the specified finite basis, with the unique scalar map,
its explicit summand formula, its integral-to-localized square, and linear uniqueness.

Source: Stacks, sites-modules.tex, Tags 0EMC (lemma-simple-invert) and 0EMD
(lemma-simple-invert-module); blueprint parent
`det-prop-sfb-cartesian-coefficients-finite-free`, inverting-ell sentence.
(blueprint: lem-sfb-localized-basis-coefficients)

Proof:
1. The universal property of jR gives the unique scalar map psi:A→B.
2. Define Q on the i-th summand by the regular-module lift of jT(b_i).
Naturality of multiplication and the prescribed summand formulas for q give
Q jR^I = jT q. These equalities are checked using biproduct injections.
3. Apply the module localization universal property
lem-sfb-localization-linear-descent to q⁻¹ followed by jR^I. This constructs an
A-linear map g:B→A^I with g jT = jR^I q⁻¹.
4. The square shows g Q is the identity after jR^I. An A-linear map from A^I
is determined by the images of its standard generators; each generator is the
image under jR^I of the corresponding R-generator since jR preserves one.
Thus g Q = 1. For Q g = 1 use uniqueness in the same localization universal
property: both maps restrict along jT to jT.
5. Package Q and g as the required isomorphism. The summand formulas and square
were proved in step 2. Standard-generator extensionality also gives the stipulated
uniqueness. Empty index types use empty biproduct sums throughout.
-/
theorem sheaf_localizedBasisCoefficients
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) :
    @LocalizedBasisCoefficients.{_, _, uI} (Sheaf J Ab.{w}) _
      (sfbSheafTensorStructure (A := Ab.{w}) J).monoidal
      (sfbSheafTensorStructure (A := Ab.{w}) J).symmetric.toBraidedCategory
      (@sheafIsAbelian C _ Ab.{w} _ _ J
        (hasSheafifyEssentiallySmallSite J Ab.{w})) := by
  let tensor := sfbSheafTensorStructure (A := Ab.{w}) J
  let : MonoidalCategory (Sheaf J Ab.{w}) := tensor.monoidal
  let : SymmetricCategory (Sheaf J Ab.{w}) := tensor.symmetric
  let : Abelian (Sheaf J Ab.{w}) :=
    @sheafIsAbelian C _ Ab.{w} _ _ J
      (hasSheafifyEssentiallySmallSite J Ab.{w})
  let hc := sfbSheafTensor_properties.{uC, vC, _, _, 0, 0} (A := Ab.{w}) J
  let : MonoidalClosed (Sheaf J Ab.{w}) := hc.2.1.some
  refine ⟨⟨sfbSheafTensor_monoidalPreadditive⟩, ?_⟩
  intro mp R T A B _ _ _ _ _ _ _ _ φ t I _ b q hq jR jT hA uA hB uB
  obtain ⟨ψ, hψ, hψunique⟩ := uA B (φ ≫ jT) hB
  refine ⟨ψ, hψ, fun ψ' hψ' ↦ hψunique ψ' hψ', ?_⟩
  let Q : (⨁ fun _ : I ↦ regular A) ⟶ (comap ψ.hom).obj (regular B) :=
    biproduct.desc fun i ↦ regularLift _ (b i ≫ jT.hom)
  have hQ (i : I) :
      (biproduct.ι (fun _ : I ↦ regular A) i).hom ≫ Q.hom =
        ψ.hom ≫ (ρ_ B).inv ≫ B ◁ (b i ≫ jT.hom) ≫ μ[B] := by
    rw [← Mod.comp_hom', biproduct.ι_desc]
    exact regularLift_scalar_formula _ _
  let P : (⨁ fun _ : I ↦ regular R).X ⟶ (⨁ fun _ : I ↦ regular A).X :=
    ∑ i : I, (biproduct.π (fun _ : I ↦ regular R) i).hom ≫ jR.hom ≫
      (biproduct.ι (fun _ : I ↦ regular A) i).hom
  have hSquare : P ≫ Q.hom = q.hom.hom ≫ jT.hom := by
    apply underlying_biproduct_ext
    intro i
    change _ ≫ (P ≫ Q.hom) = _
    dsimp only [P]
    rw [← Category.assoc, componentwise_ι jR.hom, Category.assoc, hQ]
    rw [← Category.assoc (biproduct.ι (fun _ : I ↦ regular R) i).hom, hq]
    have hψhom := congrArg Mon.Hom.hom hψ
    change jR.hom ≫ ψ.hom = φ.hom ≫ jT.hom at hψhom
    rw [← Category.assoc jR.hom ψ.hom, hψhom]
    simpa only [Category.assoc] using
      congrArg (fun k ↦ φ.hom ≫ k)
        (regular_multiply_natural jT (b i)).symm
  have descent := sheaf_localization_linearDescent J R T A B φ t jR jT ψ
    hψ hA uA hB uB
  let p : (⨁ fun _ : I ↦ regular R) ⟶
      (comap jR.hom).obj (⨁ fun _ : I ↦ regular A) :=
    biproduct.desc fun i ↦ regularScalarMap jR ≫
      (comap jR.hom).map (biproduct.ι (fun _ : I ↦ regular A) i)
  have hp : p.hom = P := by
    apply underlying_biproduct_ext
    intro i
    rw [← Mod.comp_hom', biproduct.ι_desc]
    exact (componentwise_ι jR.hom i).symm
  obtain ⟨g, hg, _⟩ := descent _ (q.inv ≫ p)
  have hQg : Q ≫ g = 𝟙 _ := by
    apply finite_regular_hom_ext jR
    change P ≫ (Q.hom ≫ g.hom) = P ≫ 𝟙 _
    rw [← Category.assoc, hSquare, Category.assoc, hg]
    change q.hom.hom ≫ (q.inv.hom ≫ p.hom) = P ≫ 𝟙 _
    rw [← Category.assoc, ← Mod.comp_hom', q.hom_inv_id, Mod.id_hom',
      Category.id_comp, hp, Category.comp_id]
  let f : (comap φ.hom).obj (regular T) ⟶
      (comap jR.hom).obj ((comap ψ.hom).obj (regular B)) :=
    q.inv ≫ p ≫ (comap jR.hom).map Q
  have hf : f.hom = jT.hom := by
    change q.inv.hom ≫ (p.hom ≫ Q.hom) = jT.hom
    rw [hp, hSquare, ← Category.assoc, ← Mod.comp_hom', q.inv_hom_id,
      Mod.id_hom', Category.id_comp]
  have hgQ : g ≫ Q = 𝟙 _ := by
    obtain ⟨z, _, hz⟩ := descent _ f
    apply (hz (g ≫ Q) ?_).trans (hz (𝟙 _) ?_).symm
    · change jT.hom ≫ (g.hom ≫ Q.hom) = f.hom
      rw [← Category.assoc, hg]
      rfl
    · change jT.hom ≫ 𝟙 B = f.hom
      simpa only [Category.comp_id] using hf.symm
  have : IsIso Q := ⟨⟨g, hQg, hgQ⟩⟩
  refine ⟨asIso Q, hQ, hSquare, ?_⟩
  intro f hf
  exact finite_regular_hom_ext jR f Q (hf.trans hSquare.symm)

end CategoryTheory.Mod
