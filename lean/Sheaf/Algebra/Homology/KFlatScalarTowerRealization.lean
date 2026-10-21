/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.CategoryTheory.Functor.OfSequence
import Sheaf.Paper.KFlatRingedToposPullback

/-! # K-flat realization of the augmented scalar-extension tower

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0D6D and 07A6
(blueprint: lem-pe-kflat-scalar-tower-realization).

Indices are shifted by one: Lean index zero denotes the paper's first coefficient.
`localize` is the standard localization through the homotopy quotient. Its canonical
comparison with `DerivedCategory.Q` is `DerivedCategory.quotientCompQhIso`.
All constructions use the dependency's fixed ordinary and derived presentations.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w uA vA
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules.KFlatScalarTower
open SuccessiveDerivedQuotient

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules R)]
  (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a)
  (N : Normalization p)

/-- The ordinary extension followed by restriction, using the existing tensor.
Source: Stacks 06YY (blueprint: lem-pe-kflat-scalar-tower-realization). -/
noncomputable abbrev ordinaryEnd {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :=
  (p a).ordinary ⋙ restriction a

/-- The derived extension followed by exact restriction.
Source: Stacks 06YY, 07A6 (blueprint: lem-pe-kflat-scalar-tower-realization). -/
noncomputable abbrev derivedEnd {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :=
  (p a).derived ⋙ N.right a

/-- Localization of actual cochain complexes through the homotopy quotient.
Source: Stacks 05RR (blueprint: lem-pe-kflat-scalar-tower-realization). -/
noncomputable abbrev localize (R : Sheaf J CommRingCat.{r}) :=
  HomotopyCategory.quotient (Modules R) (.up ℤ) ⋙ DerivedCategory.Qh

/-- The strict coefficient transition: the ordinary adjoint of scalar composition,
followed by restriction and the identity-on-sections restriction comparison.
Source: Stacks 03EK, 07A6, 0D6D
(blueprint: lem-pe-kflat-scalar-tower-realization). -/
noncomputable def ordinaryStep {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (a' : R ⟶ T) (h : a ≫ b = a') :
    ordinaryEnd p a ⟶ ordinaryEnd p a' :=
  Functor.whiskerRight
    (Functor.whiskerLeft (p a).ordinary (N.ordinaryAdjunction b).unit ≫
      Functor.whiskerRight ((N.ordinary a b).hom ≫
        eqToHom (congrArg (fun f ↦ (p f).ordinary) h)) (restriction b))
    (restriction a) ≫
  Functor.whiskerLeft (p a').ordinary ((N.restrictionComp a b).hom ≫
    eqToHom (congrArg (fun f ↦ restriction f) h))

/-- The derived transition is the adjoint of the specified scalar-composition map,
then restricted and identified by the underlying-sheaf comparison.
Source: Stacks 07A6, 0D6D (blueprint: lem-pe-kflat-scalar-tower-realization). -/
noncomputable def derivedStep {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (a' : R ⟶ T) (h : a ≫ b = a') :
    derivedEnd p N a ⟶ derivedEnd p N a' :=
  Functor.whiskerRight
    (Functor.whiskerLeft (p a).derived (N.adjunction b).unit ≫
      Functor.whiskerRight ((N.derived a b).hom ≫
        eqToHom (congrArg (fun f ↦ (p f).derived) h)) (N.right b))
    (N.right a) ≫
  Functor.whiskerLeft (p a').derived ((N.rightComp a b).hom ≫
    eqToHom (congrArg (fun f ↦ N.right f) h))

/-- The canonical K-flat computation morphism after restriction. No arbitrary
isomorphism is chosen: this is the universal derived counit and its factorization.
Source: Stacks 06YY, 07A6 (blueprint: lem-pe-kflat-scalar-tower-realization). -/
noncomputable def computation {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : CochainComplex (Modules R) ℤ) :
    (derivedEnd p N a).obj ((localize R).obj P) ⟶
      (localize R).obj (((ordinaryEnd p a).mapHomologicalComplex (.up ℤ)).obj P) :=
  (N.right a).map ((p a).counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
    (N.right_factors a).hom.app
      (((p a).ordinary.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj P)) ≫
    DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (ordinaryEnd p a)) (.up ℤ)).hom.app
        ((HomotopyCategory.quotient _ _).obj P))

/-- Transport of the canonical computation along the inverse representative isomorphism.
Source: Stacks 06YY (blueprint: lem-pe-kflat-scalar-tower-realization). -/
noncomputable def epsilon {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : CochainComplex (Modules R) ℤ) (K : DerivedCategory (Modules R))
    (e : (localize R).obj P ≅ K) :
    (derivedEnd p N a).obj K ⟶
      (localize R).obj (((ordinaryEnd p a).mapHomologicalComplex (.up ℤ)).obj P) :=
  (derivedEnd p N a).map e.inv ≫ computation p N a P

/-- Finite composites in any inverse sequence, including the empty composite.
This is Mathlib's inverse-sequence functor, with its order morphism evaluated.
Source: Stacks 00D3 (blueprint: lem-pe-kflat-scalar-tower-realization). -/
def composite {A : Type uA} [Category.{vA} A] {X : ℕ → A}
    (f : ∀ n : ℕ, X (n + 1) ⟶ X n) (n m : ℕ) (h : n ≤ m) : X m ⟶ X n :=
  (Functor.ofOpSequence f).map (homOfLE h).op

/-- The augmented K-flat realization, including its prescribed computation maps,
strict tensor formulas, naturality and compatibility with all finite transitions.
There is no flatness/surjectivity assumption on coefficient maps and no boundedness.

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0D6D, 0G7E and 07A6
(blueprint: lem-pe-kflat-scalar-tower-realization).

Proof:
1. The ordinary mate defining ordinaryStep sends a pure tensor s tensor x to
b(s) tensor x. Balancing uses a followed by b equals a'; restriction is the identity
on underlying sheaves. Sectionwise maps descend through sheafification and commute
with differentials. The ordinary adjunction unit is x mapped to 1 tensor x.
2. Apply lem-pur-derived-change-of-rings to a flat-term K-flat P. The canonical
counit is invertible. Exact restriction and its localization factorization give
computation. Transport by the inverse of e gives epsilon, also invertible.
3. The normalized unit clause of lem-pur-sheaf-ring-derived-coefficient-adjunction
identifies the unit on P with its strict ordinary unit. Naturality at e gives the
augmentation equation below.
4. By lem-weil-pbc-ringed-topos-kflat-pullback, extension along a preserves flat-term
K-flatness. The representative clause of
lem-sfb-successive-derived-quotient-normalization identifies scalar composition
with t tensor (s tensor x) mapped to b(s)t tensor x, in scalar-first notation.
5. The adjoint is restriction of that comparison after the normalized unit for b;
it therefore sends s tensor x to b(s) tensor x. Restricting gives the adjacent
transition equation, and naturality transports it along e.
6. Naturality of the universal counit and all factorization comparisons gives the
square for every chain map f, and hence for transported representatives and g.
Compose adjacent equalities to obtain the finite-transition equation, including
identities. The coherent iterated comparisons of the normalization dependency
identify these composites with the direct mate for the composite ring map.
This also proves compatibility of the augmentations and the ring-map composites. -/
theorem kflat_scalar_tower_realization
    {R : Sheaf J CommRingCat.{r}} (B : ℕ → Sheaf J CommRingCat.{r})
    (a : ∀ n : ℕ, R ⟶ B n) (b : ∀ n : ℕ, B (n + 1) ⟶ B n)
    (h : ∀ n : ℕ, a (n + 1) ≫ b n = a n)
    (P : CochainComplex (Modules R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hf : ∀ i : ℤ, IsFlatOnSite (R := R) (P.X i))
    (K : DerivedCategory (Modules R)) (e : (localize R).obj P ≅ K) :
    (∀ n : ℕ, IsIso (epsilon p N (a n) P K e)) ∧
    (∀ n : ℕ, e.hom ≫ (N.adjunction (a n)).unit.app K ≫
      epsilon p N (a n) P K e =
      (localize R).map
        ((NatTrans.mapHomologicalComplex (N.ordinaryAdjunction (a n)).unit (.up ℤ)).app P)) ∧
    (∀ n : ℕ, (derivedStep p N (a (n + 1)) (b n) (a n) (h n)).app K ≫
      epsilon p N (a n) P K e = epsilon p N (a (n + 1)) P K e ≫
        (localize R).map ((NatTrans.mapHomologicalComplex
          (ordinaryStep p N (a (n + 1)) (b n) (a n) (h n)) (.up ℤ)).app P)) ∧
    (∀ (n : ℕ) (i : ℤ) (U : Cᵒᵖ) (s : (B (n + 1)).obj.obj U)
      (x : (P.X i).val.obj U),
      ((ordinaryStep p N (a (n + 1)) (b n) (a n) (h n)).app (P.X i)).val.app U
        (sectionTensor (p (a (n + 1))) (P.X i) U s x) =
      sectionTensor (p (a n)) (P.X i) U (((b n).hom.app U).hom s) x) ∧
    (∀ n : ℕ,
      (NatTrans.mapHomologicalComplex (N.ordinaryAdjunction (a (n + 1))).unit
        (.up ℤ)).app P ≫
      (NatTrans.mapHomologicalComplex
        (ordinaryStep p N (a (n + 1)) (b n) (a n) (h n)) (.up ℤ)).app P =
      (NatTrans.mapHomologicalComplex (N.ordinaryAdjunction (a n)).unit (.up ℤ)).app P) ∧
    (∀ (P' : CochainComplex (Modules R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (R := R) P' →
      (∀ i : ℤ, IsFlatOnSite (R := R) (P'.X i)) →
      ∀ (K' : DerivedCategory (Modules R)) (e' : (localize R).obj P' ≅ K')
        (f : P ⟶ P') (g : K ⟶ K'), (localize R).map f ≫ e'.hom = e.hom ≫ g →
      ∀ n : ℕ, (derivedEnd p N (a n)).map g ≫ epsilon p N (a n) P' K' e' =
        epsilon p N (a n) P K e ≫ (localize R).map
          (((ordinaryEnd p (a n)).mapHomologicalComplex (.up ℤ)).map f)) ∧
    (∀ (n m : ℕ) (hnm : n ≤ m),
      composite (X := fun i ↦ (derivedEnd p N (a i)).obj K)
        (fun i ↦ (derivedStep p N (a (i + 1)) (b i) (a i) (h i)).app K)
        n m hnm ≫ epsilon p N (a n) P K e =
      epsilon p N (a m) P K e ≫ (localize R).map
        (composite (X := fun i ↦
          ((ordinaryEnd p (a i)).mapHomologicalComplex (.up ℤ)).obj P)
          (fun i ↦ (NatTrans.mapHomologicalComplex
            (ordinaryStep p N (a (i + 1)) (b i) (a i) (h i)) (.up ℤ)).app P) n m hnm)) ∧
    (∀ (n m : ℕ) (hnm : n ≤ m),
      ∃ hc : a m ≫ composite (X := B) b n m hnm = a n,
        ((derivedStep p N (a m) (composite (X := B) b n m hnm) (a n) hc).app K =
          composite (X := fun i ↦ (derivedEnd p N (a i)).obj K)
            (fun i ↦ (derivedStep p N (a (i + 1)) (b i) (a i) (h i)).app K)
            n m hnm) ∧
        ((NatTrans.mapHomologicalComplex
          (ordinaryStep p N (a m) (composite (X := B) b n m hnm) (a n) hc)
          (.up ℤ)).app P =
          composite (X := fun i ↦
            ((ordinaryEnd p (a i)).mapHomologicalComplex (.up ℤ)).obj P)
            (fun i ↦ (NatTrans.mapHomologicalComplex
              (ordinaryStep p N (a (i + 1)) (b i) (a i) (h i)) (.up ℤ)).app P)
            n m hnm)) := by
  sorry

end SheafOfModules.KFlatScalarTower
