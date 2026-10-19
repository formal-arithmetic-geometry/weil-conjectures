/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.CompactSupportFiniteFieldIndependence
public import WeilConjectures.Compactification.Comp
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.Compactification.NagataCompactification
import Sheaf.AlgebraicGeometry.CompatibleCompactificationTriangle
import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.IntegralResidueTor
import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Paper.FiniteTorAmplitude
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.SfDerivedComplete
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import WeilConjectures.Compactification.CategoryBaseChange
import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
import Sheaf.Paper.PbcRationalTransport
import Sheaf.Paper.SfScalarExtensionComposition
import Sheaf.CategoryTheory.StageSystemFunctorDescent
import Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars
import Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
import Sheaf.AlgebraicGeometry.CompactificationRefinementCoherence
import Sheaf.Paper.BasicOperationsCoefficientReduction
import Sheaf.Paper.SfIntegralCompactSupportConstructible
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
import Sheaf.SixFunctors.IntegralCompactificationSystemRealization

/-! # Canonical compact-support composition with field coefficients on qcqs schemes

Source: Stacks Project, Tag 0F7J, lemma-shriek-composition; Bhatt--Scholze,
Definition 6.7.6 and Lemmas 6.7.7 and 6.1.13, followed by raw rationalization
and common finite-stage descent (blueprint: lem-zl-field-shriek-composition-qcqs).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport
open GeneralAlgebraicallyClosedCoefficients

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

section Field
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

/-- Existence and canonicity of the actual integral compactification compositor.
Source: Stacks 0F7J; Bhatt--Scholze, Definition 6.7.6 and Lemmas 6.7.7, 6.1.13
(blueprint: lem-zl-field-shriek-composition-qcqs).

Proof (steps 1--5 of the DAG, before field-coefficient passage):
1. Finite-type schemes over the field are Noetherian and qcqs. Apply Nagata and
compatible-compactification-triangle to obtain d,e,V and the proper/open square.
Properness, quasi-compact opens and finite-type composition keep every ambient
scheme finite type and qcqs, without imposing separated structure morphisms.
2. Take strict derived reductions of each integral input. Constructible-origin
supplies finite-level etale origins; integral-residue-tor supplies uniform finite
Tor bounds. Integral compact-support constructibility and operation-reduction give
the same bounds and normalization for all intermediate proper/open expressions.
3. Construct the proper/open adjunction mate on actual semilinear systems, with its
unit normalization. Strict-tower-proper-open-calculus identifies its finite maps
and proves them invertible on these inputs. Conservativity tests invertibility of
this constructed system map; it does not lift a family of finite derived arrows.
4. Whisker by q and c and insert the canonical proper and open compositors. Apply
the total-limit functor and the natural Roos realization comparisons. The result
is the displayed completed-coefficient composite and the actual recorded nested
integral functor, on maps as well as objects.
5. Proper/open pasting and compactification-refinement-coherence commute with all
common refinements and compatible towers. Their normalized open adjoints give the
refinement isomorphisms in the predicate. Common refining towers and equalizers
make the map independent of choices and uniquely determine it. This argument takes
place before total limit; it never infers equality of system maps from evaluations. -/
theorem sfFieldShriekCompositionIntegral_existsUnique
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    ∃! α : sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cf E ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cg E ≅
      sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cfg E,
      SfIntegralCompositionSpec l E D.k (coefficientPrimeUnit l D hl) cf cg cfg α := by
  sorry

/-- The canonical integral compositor, selected only from its uniquely determining
proper/open and common-refinement normalization. Source: Stacks 0F7J
(blueprint: lem-zl-field-shriek-composition-qcqs). -/
def sfFieldShriekCompositionIntegral
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cf E ⋙
        sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cg E ≅
      sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) cfg E :=
  (sfFieldShriekCompositionIntegral_existsUnique D l hl cf cg cfg E).exists.choose

/-- Raw rationalization gives exactly the field-coefficient composition comparison.
Its component is the localization of the actual integral component, so the
proper/open and common-refinement normalization is retained.
Source: Stacks 0F7J, with the Bhatt--Scholze integral construction and raw localization
(blueprint: lem-zl-field-shriek-composition-qcqs).

Proof (step 6 of the DAG): the recorded integral functors are exact and integral
linear. Rational-transport extends them uniquely on localized Hom groups, with
component alpha tensor one. The localized inverse is its inverse. The fixed
finite functors use precisely this pure-tensor extension. Uniqueness transports
the integral proper/open formula and all its common-refinement equalities.
No Karoubi completion and no change of integral representative is used. -/
theorem sfFieldShriekCompositionRational_existsUnique
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    ∃! β : sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) cf E ⋙
        sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) cg E ≅
      sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) cfg E,
      ∀ K : sfRationalConstructibleCategory l E X,
        HEq (β.hom.app K)
          ((sfRationalConstructibleLocalization l E Z).map
            ((sfFieldShriekCompositionIntegral D l hl cf cg cfg E).hom.app K.obj)) := by
  sorry

/-- The canonical composition isomorphism at a finite coefficient field.
Source: Stacks 0F7J and raw rational passage
(blueprint: lem-zl-field-shriek-composition-qcqs). -/
def sfFieldShriekCompositionRational
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) cf E ⋙
        sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) cg E ≅
      sfCompactSupportFiniteFunctor l D.k (coefficientPrimeUnit l D hl) cfg E :=
  (sfFieldShriekCompositionRational_existsUnique D l hl cf cg cfg E).exists.choose

/-- On the common finite-stage category the component at (E,K) is the class of the
finite-field compositor. The three actions have the fixed finite functors and
normalized coefficient mates of the dependency definition. They are arbitrary
choices of that normalized construction; no geometric or coefficient hypothesis
is imposed on an input object.
Source: Stacks 0F7J with common finite-stage descent
(blueprint: lem-zl-field-shriek-composition-qcqs).

Proof (steps 7--8 of the DAG): coefficient extension preserves the actual units,
counits and tensor associators in the normalized proper/open mate. Operation-
reduction and scalar-extension-composition therefore identify the E compositor
with the F compositor after the canonical coefficient comparisons; tensor
associativity gives the identity and tower equations. Coherent-pair-functor-descent
then descends these transformations to arbitrary common-stage representatives.
The component is [E,alpha_E]; [E,alpha_E inverse] is its inverse. Equality after
further extension gives independence of representatives and of the common field.
The descent preserves composition and equations, hence also the compactification
formula and its common-refinement independence. This proves both field cases. -/
theorem sfFieldShriekCompositionQbar_existsUnique
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (Sf : SfCompactSupportCoefficientAction l D.k (coefficientPrimeUnit l D hl) Ω cf)
    (Sg : SfCompactSupportCoefficientAction l D.k (coefficientPrimeUnit l D hl) Ω cg)
    (Sfg : SfCompactSupportCoefficientAction l D.k (coefficientPrimeUnit l D hl) Ω cfg) :
    ∃! γ : Sf.system.functor ⋙ Sg.system.functor ≅ Sfg.system.functor,
      ∀ (E₀ : Padic.FiniteCoefficientFields l Ω) (K : Stage l Ω X E₀),
        HEq (γ.hom.app ⟨E₀, K⟩)
          ((inclusion (l := l) (Ω := Ω) (Y := Z) E₀).map
            ((sfFieldShriekCompositionRational D l hl cf cg cfg
              (AlgebraicallyClosedCoefficients.Coefficient l Ω E₀)).hom.app K)) := by
  sorry

end Field
end WeilConjectures
