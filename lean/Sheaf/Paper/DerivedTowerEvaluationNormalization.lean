/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.Algebra.Homology.DiagramKFlatReplacements
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.Paper.ResolvingRepresentativeWhiskering
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # Counit normalization of derived strict-tower evaluation

Source: Stacks Project, Derived Categories, Tag 06XN (dual),
`lemma-find-existence-computes`; the completed-pullback evaluation subargument
(blueprint: lem-cbc-derived-tower-evaluation-normalization).

The index `n : ℕ` denotes positive level `n + 1`. The comparison is unique at each
level by its value on strict objectwise K-flat complexes with flat terms. The final
identity includes every transition `b ≥ a`, including identity transitions.
-/

@[expose] public section

set_option autoImplicit false

universe u uA vA uB vB wA wB wTA wTB

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.DerivedTowerPullback

/-- The dependency's module category, with the standard commutative-ring forgetful map.
This transparent abbreviation shares the existing construction and its universe instances.
Source: Stacks Modules on Sites, Section 03DA
(blueprint: lem-cbc-derived-tower-evaluation-normalization). -/
abbrev Modules {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :=
  ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

section Evaluation

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]

/-- The degreewise identity commuting levelwise pullback and evaluation of complexes.
Source: Stacks Tag 06XN, evaluation calculation before localization
(blueprint: lem-cbc-derived-tower-evaluation-normalization). -/
def evaluationComplexIso (F : A ⥤ B) [F.Additive] (n : ℕ) :
    (((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)) ⋙
        (((evaluation ℕᵒᵖ B).obj (op n)).mapHomologicalComplex (.up ℤ)) ≅
      (((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex (.up ℤ)) ⋙
        F.mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex
    (Iso.refl _ : (Functor.whiskeringRight ℕᵒᵖ A B).obj F ⋙
      (evaluation ℕᵒᵖ B).obj (op n) ≅ (evaluation ℕᵒᵖ A).obj (op n) ⋙ F) (.up ℤ)

variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]

/-- Canonical localization of any composite tower transition, with no chosen derived map.
Source: Stacks Tags 05RU and 06XN; exact evaluation of strict towers
(blueprint: lem-cbc-derived-tower-evaluation-normalization). -/
noncomputable def derivedTransition (a b : ℕ) (h : a ≤ b) :
    ((evaluation ℕᵒᵖ A).obj (op b)).mapDerivedCategory ⟶
      ((evaluation ℕᵒᵖ A).obj (op a)).mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) _ _ _ _
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex
        ((evaluation ℕᵒᵖ A).map (homOfLE h).op) (.up ℤ)) DerivedCategory.Q)

end Evaluation

section Normalization

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ B)]

/-- The type of the stated comparison at a fixed level.
Source: Stacks Tag 06XN, evaluation subargument
(blueprint: lem-cbc-derived-tower-evaluation-normalization). -/
abbrev Comparison (L : DerivedCategory A ⥤ DerivedCategory B)
    (Lt : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory (ℕᵒᵖ ⥤ B)) (n : ℕ) :=
  Lt ⋙ ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory ≅
    ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory ⋙ L

/-- The counit equation on a specified class of strict tower representatives.
Source: Stacks Tag 06XN (dual), counits on computing representatives
(blueprint: lem-cbc-derived-tower-evaluation-normalization).

The main theorem supplies exactly the objectwise K-flat flat-term class. This equation
is `v ≫ ε = evaluation(τ)` with the canonical exact-localization factors displayed. -/
def IsNormalizedOn (F : A ⥤ B) [F.Additive]
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (Lt : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory (ℕᵒᵖ ⥤ B))
    (ε : (DerivedCategory.Q (C := A)) ⋙ L ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ (DerivedCategory.Q (C := B)))
    (τ : (DerivedCategory.Q (C := ℕᵒᵖ ⥤ A)) ⋙ Lt ⟶
      ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ) ⋙
        (DerivedCategory.Q (C := ℕᵒᵖ ⥤ B)))
    (good : CochainComplex (ℕᵒᵖ ⥤ A) ℤ → Prop) (n : ℕ)
    (v : Comparison (A := A) (B := B) L Lt n) : Prop :=
  ∀ P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, good P →
    v.hom.app ((DerivedCategory.Q (C := ℕᵒᵖ ⥤ A)).obj P) ≫
        L.map (((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.hom.app P) ≫
        ε.app (P.asFunctor.obj (op n)) =
      ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map (τ.app P) ≫
        ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategoryFactors.hom.app
          ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (DerivedCategory.Q (C := B)).map ((evaluationComplexIso F n).hom.app P)

end Normalization

/-- The existing objectwise K-flat flat-term class, as a predicate on strict tower complexes.
Source: Stacks Tag 06XN applied with the diagram replacements of Tags 077J and 06YY
(blueprint: lem-cbc-derived-tower-evaluation-normalization). -/
def IsGoodTower {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (P : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ) : Prop :=
  (∀ k : ℕ, CochainComplex.IsAcyclicTensorKFlat (R := R) (P.asFunctor.obj (op k))) ∧
    ∀ (k : ℕ) (q : ℤ), SheafOfModules.IsFlat (R := R) ((P.X q).obj (op k))

section RingedTopoi

variable {C D : Type u}

variable [SmallCategory C]

variable [SmallCategory D]

variable (J : GrothendieckTopology C)

variable (K : GrothendieckTopology D)

variable (R : Sheaf J CommRingCat.{u})

variable (S : Sheaf K CommRingCat.{u})

variable (f : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

variable (F : Modules R ⥤
        Modules S)

variable [F.Additive]

variable (adj : F ⊣ f.modules)

variable [HasDerivedCategory.{wA} (Modules R)]

variable [HasDerivedCategory.{wB} (Modules S)]

variable [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ Modules R)]

variable [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ Modules S)]

variable (L : DerivedCategory (Modules R) ⥤
        DerivedCategory (Modules S))

variable (Lt : DerivedCategory (ℕᵒᵖ ⥤ Modules R) ⥤
        DerivedCategory (ℕᵒᵖ ⥤ Modules S))

variable (ε : (DerivedCategory.Q (C := (Modules R))) ⋙ L ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ (DerivedCategory.Q (C := (Modules S))))

variable (τ : (DerivedCategory.Q (C := ℕᵒᵖ ⥤ (Modules R))) ⋙ Lt ⟶
      ((Functor.whiskeringRight ℕᵒᵖ (Modules R) (Modules S)).obj F).mapHomologicalComplex
        (.up ℤ) ⋙
        (DerivedCategory.Q (C := ℕᵒᵖ ⥤ (Modules S))))

variable [hL : L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso (Modules R) (.up ℤ))]

variable [hLt : Lt.IsLeftDerivedFunctor τ
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ (Modules R)) (.up ℤ))]

include adj hL hLt

/-- Unique representative normalization of derived tower evaluation and all transitions.
Source: Stacks Tag 06XN, `lemma-find-existence-computes` (dual), completed-pullback
invocation, evaluation subargument Step 4
(blueprint: lem-cbc-derived-tower-evaluation-normalization).

Here `F ⊣ f.modules` specifies the usual module pullback, namely inverse image followed
by extension of scalars, as in `diagram_pullback_quasiIso`. The two universal pairs are
arbitrary; no particular choice of derived pullback or counit is imposed.

Proof:
1. Exact evaluation has the displayed canonical localization factorization. On
complexes, evaluation commutes with levelwise `F` by the degreewise identity, including
all composite transition maps (lem-weil-tower-category-levelwise-abelian,
lem-weil-pbc-exact-functor-derived-factorization, def-weil-inverse-system).
2. Resolve strict towers by objectwise K-flat flat-term complexes using
lem-weil-pbc-diagram-kflat-replacements. Its one-object case supplies the corresponding
class for single complexes. Evaluation sends the tower class into the single class.
3. Apply lem-pur-left-derived-from-kflat-class. The two counits are invertible on
these classes. Uniqueness of universal pairs transfers this computation to the chosen
pairs `L, ε` and `Lt, τ` (equivalently use the homotopy-category localization).
4. On good representatives set `v = evaluation(τ) ≫ ε⁻¹`, with the displayed factors.
Naturality of both counits makes this a natural isomorphism on the full good class.
5. Use lem-weil-pbc-resolving-representative-whiskering with `p = id` and `q = Qh`.
Quasi-isomorphisms admit a right calculus by
lem-pc-quasi-isomorphisms-multiplicative-system. Its unary consequence follows by
pullback along the first projection and restriction along the diagonal. Thus restriction
to good representatives is fully faithful. The quotient from complexes to the homotopy
category is full and surjective on objects, so the same calculation applies to `Q`.
6. Extend the comparison and its inverse by fullness. Faithfulness proves the inverse
identities. Cancel the invertible single-level counit to get uniqueness at each level.
7. For every `b ≥ a`, compute on a good strict tower: counit naturality for its transition
and naturality of the target evaluation transition at `τ` give
`v_b ≫ L(d) ≫ ε_a = d' ≫ v_a ≫ ε_a`. Cancel `ε_a`.
8. Faithfulness extends this equality to every derived strict tower. When `a = b`
the identity transitions give the same equality, so no boundary case is omitted. -/
theorem exists_unique_normalized_evaluation :
    ∃ v : ∀ n : ℕ, Comparison (A := (Modules R))
        (B := (Modules S)) L Lt n,
      (∀ n : ℕ, IsNormalizedOn F L Lt ε τ (IsGoodTower R) n (v n)) ∧
      (∀ (n : ℕ) (v' : Comparison (A := (Modules R))
        (B := (Modules S)) L Lt n),
        IsNormalizedOn F L Lt ε τ (IsGoodTower R) n v' → v' = v n) ∧
      ∀ (a b : ℕ) (h : a ≤ b)
        (M : DerivedCategory (ℕᵒᵖ ⥤ (Modules R))),
        (v b).hom.app M ≫ L.map ((derivedTransition (A := (Modules R)) a b h).app M) =
          (derivedTransition (A := (Modules S)) a b h).app (Lt.obj M) ≫
            (v a).hom.app M := by
  sorry

end RingedTopoi

end CategoryTheory.DerivedTowerPullback
