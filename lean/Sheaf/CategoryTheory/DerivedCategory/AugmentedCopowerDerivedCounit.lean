/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.RepresentableSumShriekAcyclic
public import Sheaf.CategoryTheory.ContinuousCocontinuousDerivedShriek
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.Algebra.Homology.Single

/-! # Augmented copower resolutions and the normalized derived counit

Source: Stacks Project, Cohomology on Sites, Tag 08PH (example-morphism-categories),
and Derived Categories, Tag 0DVC (lemma-pre-derived-adjoint-functors)
(blueprint: lem-trf-augmented-copower-derived-counit).

Identity coverings impose no sheaf condition: the module categories here are exactly
presheaves. Copowers, Kan extension, their adjunction, complexes and localization are
Mathlib constructions. Opposite arrows encode restriction. The normalization below is
the one in `ContinuousCocontinuousDerivedShriekData.normalization`, expressed in the
presheaf presentation of the identity-cover sites. Thus the derived adjunction is fixed
relative to its comparison, including its counit, without an arbitrary automorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u wE wD wR

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {E D : Type u} [SmallCategory E] [SmallCategory D]
variable {R : Type u} [CommRing R] (u : E ⥤ D)

/-- The ordinary transpose and its canonical Kan-coordinate formula.
Source: Stacks Project, Tag 08PH
(blueprint: lem-trf-augmented-copower-derived-counit).

Proof, steps 1--2: the evaluation adjunction identifies each summand map with its
identity coefficient `f j`; naturality gives the restriction formula. The Kan adjunction
and preservation of coproducts give the displayed normalized isomorphism `e`. Both
representing bijections send an adjunct to the same coefficient, giving its formula.
Transposing the incoming differential gives `α⁰ d⁻¹ = 0`; injectivity of transposition
makes the corresponding differential composite zero. All other components vanish
because the target is concentrated in degree zero. This needs no projectivity of M.
Step 4: naturality of the adjunct gives restriction in each degree. -/
theorem augmentedCopower_transpose_formula
    (K : Dᵒᵖ ⥤ ModuleCat.{u} R) (C : CochainComplex (Eᵒᵖ ⥤ ModuleCat.{u} R) ℤ)
    (hC : ∀ r : ℤ, 0 < r → IsZero (C.X r))
    (α : C ⟶ (((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{u} R)).obj u.op).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up
      ℤ) 0).obj K))
    [QuasiIso α]
    (J : Type u) (U : J → E) (M : J → ModuleCat.{u} R)
    (d : C.X 0 ≅ (∐ fun j : J ↦ (evaluationLeftAdjoint (ModuleCat.{u} R) (op (U j))).obj (M j)))
    (f : ∀ j : J, M j ⟶ K.obj (op (u.obj (U j))))
    (hf : ∀ j : J, f j =
      Sigma.ι (fun _ : op (U j) ⟶ op (U j) ↦ M j) (𝟙 (op (U j))) ≫
        (Sigma.ι (fun j : J ↦
          (evaluationLeftAdjoint (ModuleCat.{u} R) (op (U j))).obj (M j)) j).app
            (op (U j)) ≫ d.inv.app (op (U j)) ≫
        (α.f 0).app (op (U j)) ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 K).hom.app
          (op (u.obj (U j))))
    (c : ((u.op.lan : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (Dᵒᵖ ⥤ ModuleCat.{u} R)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C ⟶ (HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u} R)
      (ComplexShape.up ℤ) 0).obj K)
    (hc : ((u.op.lanAdjunction (ModuleCat.{u} R)).mapHomologicalComplex (ComplexShape.up
      ℤ)).homEquiv C ((HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
      K) c = α) :
    (∀ (j : J) (W : Eᵒᵖ) (t : op (U j) ⟶ W),
      Sigma.ι (fun _ : op (U j) ⟶ W ↦ M j) t ≫
          (Sigma.ι (fun j : J ↦
            (evaluationLeftAdjoint (ModuleCat.{u} R) (op (U j))).obj (M j)) j).app W ≫
          d.inv.app W ≫ (α.f 0).app W ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            K).hom.app (u.op.obj W) =
        f j ≫ K.map (u.op.map t)) ∧
    (∃ e : (u.op.lan : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (Dᵒᵖ ⥤ ModuleCat.{u} R)).obj (C.X 0) ≅ (∐ fun j : J
      ↦ (evaluationLeftAdjoint (ModuleCat.{u} R) (op (u.obj (U j)))).obj (M j)),
      (∀ (j : J) (W : Eᵒᵖ) (t : op (U j) ⟶ W),
        Sigma.ι (fun _ : op (U j) ⟶ W ↦ M j) t ≫
            (Sigma.ι (fun j : J ↦
              (evaluationLeftAdjoint (ModuleCat.{u} R) (op (U j))).obj (M j)) j).app W ≫
            d.inv.app W ≫
            ((u.op.lanAdjunction (ModuleCat.{u} R)).unit.app (C.X 0)).app W ≫
            e.hom.app (u.op.obj W) =
          Sigma.ι (fun _ : op (u.obj (U j)) ⟶ u.op.obj W ↦ M j) (u.op.map t) ≫
            (Sigma.ι (fun j : J ↦
              (evaluationLeftAdjoint (ModuleCat.{u} R) (op (u.obj (U j)))).obj (M j))
                j).app (u.op.obj W)) ∧
      (∀ (j : J) (V : Dᵒᵖ) (t : op (u.obj (U j)) ⟶ V),
        Sigma.ι (fun _ : op (u.obj (U j)) ⟶ V ↦ M j) t ≫
            (Sigma.ι (fun j : J ↦
              (evaluationLeftAdjoint (ModuleCat.{u} R) (op (u.obj (U j)))).obj (M j))
                j).app V ≫ e.inv.app V ≫ (c.f 0).app V ≫ (HomologicalComplex.singleObjXSelf
                  (ComplexShape.up ℤ) 0 K).hom.app V =
          f j ≫ K.map t)) ∧
    (∀ r : ℤ, r ≠ 0 → c.f r = 0) ∧
    ((u.op.lan : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (Dᵒᵖ ⥤ ModuleCat.{u} R)).map (C.d (-1) 0) ≫ c.f 0 = 0) ∧
    (∀ (V V' : Dᵒᵖ) (s : V ⟶ V') (r : ℤ),
      ((((u.op.lan : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (Dᵒᵖ ⥤ ModuleCat.{u} R)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C).X r).map s ≫ (c.f r).app V' =
        (c.f r).app V ≫ (((HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ)
          0).obj K).X r).map s) := by
  sorry

variable [HasDerivedCategory.{wE} (Eᵒᵖ ⥤ ModuleCat.{u} R)]
variable [HasDerivedCategory.{wD} (Dᵒᵖ ⥤ ModuleCat.{u} R)]

/-- The two identities for the actual normalized derived counit.
Source: Stacks Project, Tag 0DVC and Tag 08PH
(blueprint: lem-trf-augmented-copower-derived-counit).

Proof, step 3: normalization sends `ε_C ≫ Q(c)` to `Q(α)`, using the canonical
factorization of exact precomposition. The counit, precomposed with `LQ(α)`, has
that same transpose by naturality of the derived adjunction. Injectivity gives
the first equality. Localization inverts α; the factorization is an isomorphism,
and L preserves these inverses. Compose with that inverse for the second equality.
The normalized Hom bijection precludes any extra automorphism. -/
theorem augmentedCopower_derived_counit
    (L : DerivedCategory (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ DerivedCategory (Dᵒᵖ ⥤ ModuleCat.{u} R))
    (ε : DerivedCategory.Q ⋙ L ⟶ (u.op.lan : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (Dᵒᵖ ⥤ ModuleCat.{u}
      R)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (hL : L.IsLeftDerivedFunctor ε
      (HomologicalComplex.quasiIso (Eᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (a : L ⊣ ((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{u} R)).obj u.op).mapDerivedCategory)
    (hnorm : ∀ (X : CochainComplex (Eᵒᵖ ⥤ ModuleCat.{u} R) ℤ)
      (N : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{u} R) ℤ) (b : ((u.op.lan : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤
        (Dᵒᵖ ⥤ ModuleCat.{u} R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj X ⟶ N),
      a.homEquiv (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj N)
          (ε.app X ≫ DerivedCategory.Q.map b) =
        DerivedCategory.Q.map (((u.op.lanAdjunction (ModuleCat.{u} R)).mapHomologicalComplex
          (ComplexShape.up ℤ)).homEquiv X N b) ≫
          ((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{u} R)).obj
            u.op).mapDerivedCategoryFactors.inv.app N)
    (K : Dᵒᵖ ⥤ ModuleCat.{u} R) (C : CochainComplex (Eᵒᵖ ⥤ ModuleCat.{u} R) ℤ)
    (α : C ⟶ (((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{u} R)).obj u.op).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up
      ℤ) 0).obj K))
    [QuasiIso α] [IsIso (ε.app C)]
    (c : ((u.op.lan : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (Dᵒᵖ ⥤ ModuleCat.{u} R)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C ⟶ (HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u} R)
      (ComplexShape.up ℤ) 0).obj K)
    (hc : ((u.op.lanAdjunction (ModuleCat.{u} R)).mapHomologicalComplex (ComplexShape.up
      ℤ)).homEquiv C ((HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
      K) c = α) :
    (L.map (DerivedCategory.Q.map α ≫
        ((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{u} R)).obj
          u.op).mapDerivedCategoryFactors.inv.app ((HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u}
          R) (ComplexShape.up ℤ) 0).obj K)) ≫
        a.counit.app (DerivedCategory.Q.obj ((HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u} R)
          (ComplexShape.up ℤ) 0).obj K)) =
      ε.app C ≫ DerivedCategory.Q.map c) ∧
    (a.counit.app (DerivedCategory.Q.obj ((HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u} R)
      (ComplexShape.up ℤ) 0).obj K)) =
      inv (L.map (DerivedCategory.Q.map α ≫
        ((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{u} R)).obj
          u.op).mapDerivedCategoryFactors.inv.app ((HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u}
          R) (ComplexShape.up ℤ) 0).obj K))) ≫
        ε.app C ≫ DerivedCategory.Q.map c) := by
  sorry

/-- Evaluation of the representative is the localization of the displayed chain map.
Source: Stacks Project, Tag 08PH and Tag 0DVC
(blueprint: lem-trf-augmented-copower-derived-counit).

Proof, step 4: evaluation is exact because kernels and cokernels of presheaves are
pointwise. It therefore descends to localization. Apply this descended functor to
the second counit identity, and then use its canonical factorization on the map c.
The result is precisely the localized chain map at V, under the indicated source
comparison and the target factorization isomorphism. -/
theorem augmentedCopower_evaluated_counit
    (L : DerivedCategory (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ DerivedCategory (Dᵒᵖ ⥤ ModuleCat.{u} R))
    (ε : DerivedCategory.Q ⋙ L ⟶ (u.op.lan : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (Dᵒᵖ ⥤ ModuleCat.{u}
      R)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (hL : L.IsLeftDerivedFunctor ε
      (HomologicalComplex.quasiIso (Eᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (a : L ⊣ ((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{u} R)).obj u.op).mapDerivedCategory)
    (hnorm : ∀ (X : CochainComplex (Eᵒᵖ ⥤ ModuleCat.{u} R) ℤ)
      (N : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{u} R) ℤ) (b : ((u.op.lan : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤
        (Dᵒᵖ ⥤ ModuleCat.{u} R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj X ⟶ N),
      a.homEquiv (DerivedCategory.Q.obj X) (DerivedCategory.Q.obj N)
          (ε.app X ≫ DerivedCategory.Q.map b) =
        DerivedCategory.Q.map (((u.op.lanAdjunction (ModuleCat.{u} R)).mapHomologicalComplex
          (ComplexShape.up ℤ)).homEquiv X N b) ≫
          ((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{u} R)).obj
            u.op).mapDerivedCategoryFactors.inv.app N)
    (K : Dᵒᵖ ⥤ ModuleCat.{u} R) (C : CochainComplex (Eᵒᵖ ⥤ ModuleCat.{u} R) ℤ)
    (α : C ⟶ (((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{u} R)).obj u.op).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up
      ℤ) 0).obj K))
    [QuasiIso α] [IsIso (ε.app C)]
    (c : ((u.op.lan : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (Dᵒᵖ ⥤ ModuleCat.{u} R)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C ⟶ (HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u} R)
      (ComplexShape.up ℤ) 0).obj K)
    (hc : ((u.op.lanAdjunction (ModuleCat.{u} R)).mapHomologicalComplex (ComplexShape.up
      ℤ)).homEquiv C ((HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
      K) c = α)
    [HasDerivedCategory.{wR} (ModuleCat.{u} R)] (V : Dᵒᵖ) :
    (((evaluation Dᵒᵖ (ModuleCat.{u} R)).obj V).mapDerivedCategory).map
        (a.counit.app (DerivedCategory.Q.obj ((HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u} R)
          (ComplexShape.up ℤ) 0).obj K))) =
      (((evaluation Dᵒᵖ (ModuleCat.{u} R)).obj V).mapDerivedCategory).map
          (inv (L.map (DerivedCategory.Q.map α ≫
            ((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{u} R)).obj
              u.op).mapDerivedCategoryFactors.inv.app ((HomologicalComplex.single (Dᵒᵖ ⥤
              ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj K))) ≫ ε.app C) ≫
        ((evaluation Dᵒᵖ (ModuleCat.{u} R)).obj V).mapDerivedCategoryFactors.hom.app
          (((u.op.lan : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (Dᵒᵖ ⥤ ModuleCat.{u} R)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C) ≫
        DerivedCategory.Q.map
          ((((evaluation Dᵒᵖ (ModuleCat.{u} R)).obj V).mapHomologicalComplex
            (ComplexShape.up ℤ)).map c) ≫
        ((evaluation Dᵒᵖ (ModuleCat.{u} R)).obj V).mapDerivedCategoryFactors.inv.app
          ((HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj K) := by
  sorry

/-- Naturality of ordinary and derived representatives, including generator formulas.
Source: Stacks Project, Tag 08PH and Tag 0DVC
(blueprint: lem-trf-augmented-copower-derived-counit).

Proof, steps 4--5: the transpose of either side of the ordinary naturality equation
is the assumed augmentation square, by naturality of the ordinary adjunction.
Localize that equality and use naturality of ε to obtain the derived equality.
The restriction formula on generators is the functor composition law of K;
the coefficient formula is the naturality square of q at t. No preservation of
the decompositions by v is required, and no quasi-isomorphism condition on α' is
needed for these uninverted representative equalities. -/
theorem augmentedCopower_transpose_naturality
    (L : DerivedCategory (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ DerivedCategory (Dᵒᵖ ⥤ ModuleCat.{u} R))
    (ε : DerivedCategory.Q ⋙ L ⟶ (u.op.lan : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (Dᵒᵖ ⥤ ModuleCat.{u}
      R)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (K K' : Dᵒᵖ ⥤ ModuleCat.{u} R) (C C' : CochainComplex (Eᵒᵖ ⥤ ModuleCat.{u} R) ℤ)
    (α : C ⟶ (((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{u} R)).obj u.op).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up
      ℤ) 0).obj K))
    (α' : C' ⟶ (((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{u} R)).obj u.op).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up
      ℤ) 0).obj K'))
    (q : K ⟶ K') (v : C ⟶ C')
    (h : v ≫ α' = α ≫ (((Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{u} R)).obj
      u.op).mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map q))
    (c : ((u.op.lan : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (Dᵒᵖ ⥤ ModuleCat.{u} R)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C ⟶ (HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u} R)
      (ComplexShape.up ℤ) 0).obj K)
    (c' : ((u.op.lan : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (Dᵒᵖ ⥤ ModuleCat.{u} R)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj C' ⟶ (HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u} R)
      (ComplexShape.up ℤ) 0).obj K')
    (hc : ((u.op.lanAdjunction (ModuleCat.{u} R)).mapHomologicalComplex (ComplexShape.up
      ℤ)).homEquiv C ((HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
      K) c = α)
    (hc' : ((u.op.lanAdjunction (ModuleCat.{u} R)).mapHomologicalComplex (ComplexShape.up
      ℤ)).homEquiv C' ((HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
      K') c' = α') :
    (c ≫ (HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map q =
      ((u.op.lan : (Eᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (Dᵒᵖ ⥤ ModuleCat.{u} R)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map v ≫ c') ∧
    (ε.app C ≫ DerivedCategory.Q.map c ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.single (Dᵒᵖ ⥤ ModuleCat.{u} R) (ComplexShape.up ℤ) 0).map q) =
      L.map (DerivedCategory.Q.map v) ≫ ε.app C' ≫ DerivedCategory.Q.map c') ∧
    (∀ (J : Type u) (U : J → E) (M : J → ModuleCat.{u} R)
      (f : ∀ j : J, M j ⟶ K.obj (op (u.obj (U j))))
      (j : J) (V V' : Dᵒᵖ) (t : op (u.obj (U j)) ⟶ V) (s : V ⟶ V'),
      f j ≫ K.map (t ≫ s) = f j ≫ K.map t ≫ K.map s) ∧
    (∀ (J : Type u) (U : J → E) (M : J → ModuleCat.{u} R)
      (f : ∀ j : J, M j ⟶ K.obj (op (u.obj (U j))))
      (j : J) (V : Dᵒᵖ) (t : op (u.obj (U j)) ⟶ V),
      f j ≫ K.map t ≫ q.app V = f j ≫ q.app (op (u.obj (U j))) ≫ K'.map t) := by
  sorry

end CategoryTheory
