/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.Paper.QcqsCompactSupportRealization
public import WeilConjectures.Compactification.Comp
public import WeilConjectures.Compactification.Refinement

/-! # Proper/open normalization for the compact-support compositor

The completed-ring arrows and the integral normalization predicate from Stacks 0F7J.
These definitions are shared by construction and coefficient compatibility.
(blueprint: def-zl-field-shriek-composition-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

section Completed
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The pullback square comparison made from the canonical completed compositors.
Source: Stacks 0F7J, proper/open square
(blueprint: lem-zl-field-shriek-composition-qcqs). -/
def sfCompositionPullSquare {V T Y S : Scheme.{u}}
    (b : V ⟶ T) (r : V ⟶ Y) (p : T ⟶ S) (i : Y ⟶ S)
    (w : b ≫ p = r ≫ i) :
    pull (completed l E) i ⋙ pull (completed l E) r ≅
      pull (completed l E) p ⋙ pull (completed l E) b :=
  (geometricPullComposition (completed l E) r i (completedPull_comp l E r i)).symm ≪≫
    eqToIso (congrArg (fun h ↦ pull (completed l E) h) w.symm) ≪≫
    geometricPullComposition (completed l E) b p (completedPull_comp l E b p)

/-- The open restriction comparison: geometric exchange, then the inverse open unit.
The unit proof is supplied by the statement, rather than assumed as a geometric
hypothesis. Source: Stacks 0F7J, proper/open comparison
(blueprint: lem-zl-field-shriek-composition-qcqs). -/
def sfCompositionLambda {V T Y S : Scheme.{u}}
    (b : V ⟶ T) (r : V ⟶ Y) (p : T ⟶ S) (i : Y ⟶ S)
    [IsOpenImmersion b] (w : b ≫ p = r ≫ i)
    (N : DerivedCategory (scalarReductionSource l E V))
    (hη : IsIso ((openDerivedAdjunction (completed l E) b).unit.app N)) :
    (pull (completed l E) i).obj
        ((push (completed l E) p).obj
          ((openExtension (completed l E) b).mapDerivedCategory.obj N)) ⟶
      (push (completed l E) r).obj N :=
  (proEtaleRingDerivedAdjunction r ((completed l E).ring Y)
    ((completed l E).ring V) ((completed l E).pull r)).unit.app _ ≫
    (push (completed l E) r).map
      ((sfCompositionPullSquare l E b r p i w).hom.app _ ≫
        (pull (completed l E) b).map
          ((proEtaleRingDerivedAdjunction p ((completed l E).ring S)
            ((completed l E).ring T) ((completed l E).pull p)).counit.app _) ≫
        @inv _ _ _ _ ((openDerivedAdjunction (completed l E) b).unit.app N) hη)

/-- The proper/open map is the specified open adjunct of inverse restriction.
Source: Stacks 0F7J and 0F7B (blueprint: lem-zl-field-shriek-composition-qcqs). -/
def sfCompositionGamma {V T Y S : Scheme.{u}}
    (b : V ⟶ T) (r : V ⟶ Y) (p : T ⟶ S) (i : Y ⟶ S)
    [IsOpenImmersion b] [IsOpenImmersion i] (w : b ≫ p = r ≫ i)
    (N : DerivedCategory (scalarReductionSource l E V))
    (hη : IsIso ((openDerivedAdjunction (completed l E) b).unit.app N))
    (hLambda : IsIso (sfCompositionLambda l E b r p i w N hη)) :
    (openExtension (completed l E) i).mapDerivedCategory.obj
        ((push (completed l E) r).obj N) ⟶
      (push (completed l E) p).obj
        ((openExtension (completed l E) b).mapDerivedCategory.obj N) :=
  ((openDerivedAdjunction (completed l E) i).homEquiv _ _).symm
    (@inv _ _ _ _ (sfCompositionLambda l E b r p i w N hη) hLambda)

/-- The normalized open compositor, conjugate to composition of open restriction.
Source: Stacks 0F7J (blueprint: lem-zl-field-shriek-composition-qcqs). -/
def sfCompositionOpenComp {X V T : Scheme.{u}} (c : X ⟶ V) (b : V ⟶ T)
    [IsOpenImmersion c] [IsOpenImmersion b] :
    (openExtension (completed l E) c).mapDerivedCategory ⋙
        (openExtension (completed l E) b).mapDerivedCategory ≅
      (openExtension (completed l E) (c ≫ b)).mapDerivedCategory :=
  Adjunction.leftAdjointCompIso (openDerivedAdjunction (completed l E) c)
    (openDerivedAdjunction (completed l E) b)
    (openDerivedAdjunction (completed l E) (c ≫ b))
    (geometricPullComposition (completed l E) c b (completedPull_comp l E c b)).symm

/-- Equality transport for exact completed open extension.
Source: Stacks 0F7J, a=bc (blueprint: lem-zl-field-shriek-composition-qcqs). -/
def sfCompositionOpenCongr {X T : Scheme.{u}} {a b : X ⟶ T}
    [IsOpenImmersion a] [IsOpenImmersion b] (w : a = b) :
    (openExtension (completed l E) a).mapDerivedCategory ≅
      (openExtension (completed l E) b).mapDerivedCategory := by
  subst b
  exact Iso.refl _

/-- The actual compatible-tower composition, before rationalizing any Hom group.
The factors are Rq_* Gamma c_!, proper composition, and open composition a=bc.
Source: Stacks 0F7J, the displayed four equalities
(blueprint: lem-zl-field-shriek-composition-qcqs). -/
def sfCompletedCompositionOnTower {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (d : Compactification g) (e : Compactification (f ≫ d.i))
    (K : DerivedCategory (scalarReductionSource l E X))
    (hη : IsIso ((openDerivedAdjunction (completed l E) (pullback.fst e.g d.i)).unit.app
      ((openExtension (completed l E) e.restrict.i).mapDerivedCategory.obj K)))
    (hLambda : IsIso (sfCompositionLambda l E (pullback.fst e.g d.i) e.restrict.g e.g d.i
      e.isPullback_restrict.w.symm
        ((openExtension (completed l E) e.restrict.i).mapDerivedCategory.obj K) hη)) :
    (image (completed l E) d).obj ((image (completed l E) e.restrict).obj K) ⟶
      (image (completed l E) (d.comp e)).obj K :=
  (push (completed l E) d.g).map
      (sfCompositionGamma l E (pullback.fst e.g d.i) e.restrict.g e.g d.i
        e.isPullback_restrict.w.symm
        ((openExtension (completed l E) e.restrict.i).mapDerivedCategory.obj K) hη hLambda) ≫
    (geometricPushComposition (completed l E) e.g d.g
      (completedPull_comp l E e.g d.g)).hom.app _ ≫
    (push (completed l E) (e.g ≫ d.g)).map
      ((sfCompositionOpenComp l E e.restrict.i (pullback.fst e.g d.i)).hom.app K ≫
        (sfCompositionOpenCongr l E e.restrict_i_fst).hom.app K)

/-- Normalization of a compactification-refinement comparison. The open adjunct is
fixed by the proper counit and the open unit, and its inverse is pushed forward
using the canonical proper compositor. Source: Stacks 0F7J, independence of choices
(blueprint: lem-zl-field-shriek-composition-qcqs). -/
def SfCompletedRefinementSpec {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : DerivedCategory (scalarReductionSource l E X))
    (ρ : (image (completed l E) c).obj K ≅ (image (completed l E) d).obj K) : Prop :=
  ∃ ε : (openExtension (completed l E) d.i).mapDerivedCategory.obj K ≅
      (push (completed l E) r.hom).obj
        ((openExtension (completed l E) c.i).mapDerivedCategory.obj K),
    (openDerivedAdjunction (completed l E) d.i).homEquiv _ _ ε.hom ≫
        refinementRestriction (completed l E) r (completedPull_comp l E c.i r.hom) K =
      (openDerivedAdjunction (completed l E) c.i).unit.app K ∧
    ρ.hom =
      ((geometricPushComposition (completed l E) r.hom d.g
        (completedPull_comp l E r.hom d.g) ≪≫
          eqToIso (congrArg (fun h ↦ push (completed l E) h) r.hom_g)).symm.app _).hom ≫
        (push (completed l E) d.g).map ε.inv

end Completed

section Integral
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))] [Z.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Z ↘ Spec (.of K₀))] [QuasiCompact (Z ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [g.IsOver (Spec (.of K₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))

/-- The canonical integral compactification composition, including arbitrary choices
of the three compactifications. On any compatible tower refining those choices it
is the actual completed proper/open map, conjugated by the specified refinement and
Roos comparisons. The refinements are constrained by their adjunction normalization.
Source: Stacks 0F7J, compatible tower and independence of choices
(blueprint: lem-zl-field-shriek-composition-qcqs). -/
def SfIntegralCompositionSpec
    (α : sfCompactSupportFiniteIntegralFunctor l K₀ hl cf E ⋙
        sfCompactSupportFiniteIntegralFunctor l K₀ hl cg E ≅
      sfCompactSupportFiniteIntegralFunctor l K₀ hl cfg E) : Prop :=
  ∀ (d : Compactification g) (e : Compactification (f ≫ d.i))
    (rf : e.restrict.Refinement cf) (rg : d.Refinement cg)
    (rfg : (d.comp e).Refinement cfg) (K : sfIntegralConstructibleCategory l E X),
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
    (α.hom.app K).hom =
      (sfQcqsCompactSupportRealization l E K₀ hl cg).inv.app
          ((sfCompactSupportFiniteIntegralFunctor l K₀ hl cf E).obj K) ≫
        (image (completed l E) cg).map
          ((sfQcqsCompactSupportRealization l E K₀ hl cf).inv.app K) ≫
        (image (completed l E) cg).map ρf.inv ≫ ρg.inv ≫
        sfCompletedCompositionOnTower l E d e K.obj hη hLambda ≫ ρfg.hom ≫
        (sfQcqsCompactSupportRealization l E K₀ hl cfg).hom.app K

end Integral

end WeilConjectures
