/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FieldShriekCompositionNormalization
public import Sheaf.Paper.FiniteFieldFiber

/-! # Normalized components of the integral field shriek compositor

Source: Stacks Project, Tag 0F7J, and Bhatt--Scholze Definition 6.7.6
(blueprint: lem-zl-field-shriek-integral-component).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))

/-- The proper/open normalization at one input. Its equation is exactly the
component equation of `SfIntegralCompositionSpec`; it asserts no naturality in the input.
Source: Stacks 0F7J (blueprint: lem-zl-field-shriek-integral-component). -/
def SfIntegralCompositionComponentSpec
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (K : sfIntegralConstructibleCategory l E X)
    (a : (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cg E).obj
        ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cf E).obj K)
      ⟶ (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cfg E).obj K)
    : Prop :=
  ∀ (d : Compactification g) (e : Compactification (f ≫ d.i))
    (rf : e.restrict.Refinement cf) (rg : d.Refinement cg)
    (rfg : (d.comp e).Refinement cfg),
  ∃ hη : IsIso ((openDerivedAdjunction (completed l E) (pullback.fst e.g d.i)).unit.app
      ((openExtension (completed l E) e.restrict.i).mapDerivedCategory.obj K.obj)),
  ∃ hLambda : IsIso (sfCompositionLambda l E (pullback.fst e.g d.i) e.restrict.g e.g d.i
      e.isPullback_restrict.w.symm
        ((openExtension (completed l E) e.restrict.i).mapDerivedCategory.obj K.obj) hη),
  ∃ (ρf : (image (completed l E) e.restrict).obj K.obj ≅
      (image (completed l E) cf).obj K.obj)
    (ρg : (image (completed l E) d).obj
        ((image (completed l E) e.restrict).obj K.obj) ≅
      (image (completed l E) cg).obj ((image (completed l E) e.restrict).obj K.obj))
    (ρfg : (image (completed l E) (d.comp e)).obj K.obj ≅
      (image (completed l E) cfg).obj K.obj),
    SfCompletedRefinementSpec l E rf K.obj ρf ∧
    SfCompletedRefinementSpec l E rg ((image (completed l E) e.restrict).obj K.obj) ρg ∧
    SfCompletedRefinementSpec l E rfg K.obj ρfg ∧
    a.hom =
      (sfQcqsCompactSupportRealization l E D.k (coefficientPrimeUnit l D hl) cg).inv.app
          ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cf E).obj K) ≫
        (image (completed l E) cg).map
          ((sfQcqsCompactSupportRealization l E D.k (coefficientPrimeUnit l D hl) cf).inv.app K) ≫
        (image (completed l E) cg).map ρf.inv ≫ ρg.inv ≫
        sfCompletedCompositionOnTower l E d e K.obj hη hLambda ≫ ρfg.hom ≫
        (sfQcqsCompactSupportRealization l E D.k (coefficientPrimeUnit l D hl) cfg).hom.app K


/-- There is a uniquely normalized isomorphism at each integral constructible input.
Source: Stacks 0F7J, compatible compactifications and independence of choices;
Bhatt--Scholze Definition 6.7.6 and Lemmas 6.7.7, 6.1.13
(blueprint: lem-zl-field-shriek-integral-component).

Proof: choose a compatible tower refining the supplied compactifications. On its
proper/open square construct Lambda from restriction exchange and the inverse open unit.
Its inverse open adjunct Gamma is invertible: its finite reductions are the finite
proper/open isomorphisms, and its cone is complete with zero reductions. Whisker Gamma
by the outer proper and open functors, insert their compositors, and conjugate by the
normalized refinement and Roos isomorphisms. All these factors are actual isomorphisms.
For any second tower, take a common refining tower and equalize its parallel refinement
arrows. Proper/open mate pasting and refinement coherence identify the two conjugates.
This proves the displayed normalization on every tower. Conversely that equation on
one such refining tower fixes the component, since the normalized refinements are
unique by the open adjunction and all conjugating factors are invertible. Faithfulness
of the full-subcategory inclusion and Iso.ext give uniqueness. This statement concerns
one input only and does not assert the naturality needed to assemble a functor iso. -/
theorem sfFieldShriekCompositionIntegral_component
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (K : sfIntegralConstructibleCategory l E X) :
    ∃! a : (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cg E).obj
        ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cf E).obj K)
      ≅ (sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cfg E).obj K,
      SfIntegralCompositionComponentSpec D l hl cf cg cfg E K a.hom := by
  sorry

end WeilConjectures
