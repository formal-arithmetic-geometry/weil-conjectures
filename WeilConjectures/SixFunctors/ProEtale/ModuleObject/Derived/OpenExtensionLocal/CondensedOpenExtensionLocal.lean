/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedModule.NativeCondensedModuleLocalFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedIsomorphismSquareExchange
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
import WeilConjectures.CategoryTheory.Exact.ExactDerivedCohomologyCoherence
import WeilConjectures.AlgebraicGeometry.Exact.ExactDerivedTransformation
import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import WeilConjectures.CategoryTheory.Triangulated.TStructure.CohomologyComparisonPasting
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor
import Mathlib.CategoryTheory.Limits.Creates
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf

/-! # Condensed open extension, cohomology and local Frobenius

Source: latest blueprint, part-weights-riemann-hypothesis/sec-deligne-laumon-general/
sec-reduction-to-the-relative-affine-line/sk-prop-wgen-relative-line/
lem-zl-morphism-open-closed-reduction.proof.md, Part 2
(blueprint: lem-zl-condensed-open-extension-local).

The comparison uses the chosen compactification and the normalized trivial-open comparison.
Weil cohomology is transported by the normalized exact-derived homology comparison.
All module and derived categories are the ordinary condensed-coefficient categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u vC vD uC uD wC wD uV vV

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.OpenExtensionLocal

/-- Localize an exact commutation isomorphism termwise, using the canonical compositors.
Source: Part 2, exact extension by zero and its Frobenius square
(blueprint: lem-zl-condensed-open-extension-local). -/
def derivedExchange {C : Type uC} {E : Type uD} [Category.{vC} C] [Category.{vD} E]
    [Abelian C] [Abelian E] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} E]
    (J : C ⥤ E) (P : C ⥤ C) (Q : E ⥤ E)
    [J.Additive] [P.Additive] [Q.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (β : J ⋙ Q ≅ P ⋙ J) :
    J.mapDerivedCategory ⋙ Q.mapDerivedCategory ≅
      P.mapDerivedCategory ⋙ J.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso J Q).symm ≪≫
    Functor.mapDerivedCategoryNatIso β ≪≫ Functor.mapDerivedCategoryCompIso P J

section AbstractCohomology

variable {C : Type uC} {E : Type uD} [Category.{vC} C] [Category.{vD} E]
  [Abelian C] [Abelian E] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} E]
  (J : C ⥤ E) (P : C ⥤ C) (Q : E ⥤ E)
  [J.Additive] [P.Additive] [Q.Additive]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]

/-- Cohomology of a strict pair, through the normalized exact-derived comparison.
Source: Part 2, Weil cohomology of exact extension
(blueprint: lem-zl-condensed-open-extension-local). -/
def pairCohomology (r : ℤ) :=
  IsoAlgebra.mapOfNatIso (P.mapDerivedCategoryHomologyFunctorIso r)

/-- Transport the induced Weil structure across the specified derived comparison.
Source: Part 2, the Weil structure on the compactification functor
(blueprint: lem-zl-condensed-open-extension-local). -/
def transportDerivedPair (β : J ⋙ Q ≅ P ⋙ J)
    (K : IsoAlgebra P.mapDerivedCategory) (L : DerivedCategory E)
    (c : L ≅ J.mapDerivedCategory.obj K.carrier) :=
  IsoAlgebra.mk L
    (Q.mapDerivedCategory.mapIso c ≪≫
      ((IsoAlgebra.mapOfNatIso (derivedExchange J P Q β)).obj K).str ≪≫ c.symm)

/-- The compact-support cohomology comparison, with its canonical carrier formula.
The arbitrary-looking L is accompanied by the specified comparison c; no map or Weil
structure is assumed as free data in the specialization to compact support.
Source: Part 2, cohomology after the compactification comparison
(blueprint: lem-zl-condensed-open-extension-local). -/
def CompactWeilCohomology (β : J ⋙ Q ≅ P ⋙ J)
    (K : IsoAlgebra P.mapDerivedCategory) (L : DerivedCategory E)
    (c : L ≅ J.mapDerivedCategory.obj K.carrier) (r : ℤ) : Prop :=
  ∃ e : (pairCohomology Q r).obj (transportDerivedPair J P Q β K L c) ≅
      (IsoAlgebra.mapOfNatIso β).obj ((pairCohomology P r).obj K),
    e.hom.hom.f = (DerivedCategory.homologyFunctor E r).map c.hom ≫
      (J.mapDerivedCategoryHomologyFunctorIso r).inv.app K.carrier

end AbstractCohomology

variable (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  (U₀ X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom] [IsSeparated U₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀.left]

/-- Finite type is stable under the specified geometric base change.
Source: the separated finite-type setting of Part 2
(blueprint: lem-zl-condensed-open-extension-local). -/
instance geometricFiniteType (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] :
    LocallyOfFiniteType ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj T₀).hom :=
  inferInstanceAs (LocallyOfFiniteType
    (pullback.snd T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Quasi-compactness is stable under the specified geometric base change.
Source: the finite-type setting of Part 2
(blueprint: lem-zl-condensed-open-extension-local). -/
instance geometricQuasiCompact (T₀ : Over (Spec (.of D.k₀)))
    [QuasiCompact T₀.hom] :
    QuasiCompact ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).obj T₀).hom :=
  inferInstanceAs (QuasiCompact
    (pullback.snd T₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Evaluate the actual adjunction unit through a specified inverse-image compositor.
Source: Part 2, the on-open fiber unit
(blueprint: lem-zl-condensed-open-extension-local). -/
def evaluatedUnit {C : Type uC} {E : Type uD} {V : Type uV}
    [Category.{vC} C] [Category.{vD} E] [Category.{vV} V]
    {J : C ⥤ E} {R : E ⥤ C} (a : J ⊣ R)
    (A : C ⥤ V) (B : E ⥤ V) (c : B ≅ R ⋙ A) (F : C) :
    A.obj F ⟶ B.obj (J.obj F) :=
  A.map (a.unit.app F) ≫ c.inv.app (J.obj F)

/-- Evaluate the canonical open unit at a geometric point before specializing the open.
This has the specified inverse-image compositor and ordinary unit, with an abstract immersion j.
Source: Part 2, on-open fiber identification
(blueprint: lem-zl-condensed-open-extension-local). -/
def moduleFibreUnit (k : Type u) [Field k] [IsSepClosed k]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : WeilConjectures.NativeCondensedModule.Modules ℓ U) (z : Spec (.of k) ⟶ U) :=
  evaluatedUnit
    (openImmersionLowerShriekUpperStarAdjunction (Profinite.padicAlgClRingObj ℓ) j)
    (upperStar (Profinite.padicAlgClRingObj ℓ) z ⋙
      WeilConjectures.NativeCondensedModule.pointSections ℓ k)
    (upperStar (Profinite.padicAlgClRingObj ℓ) (z ≫ j) ⋙
      WeilConjectures.NativeCondensedModule.pointSections ℓ k)
    (Functor.isoWhiskerRight (upperStarComp (Profinite.padicAlgClRingObj ℓ) z j)
      (WeilConjectures.NativeCondensedModule.pointSections ℓ k) ≪≫ Functor.associator _ _ _) F

/-- Canonical on-open fiber identification and intertwining of the actual local operators.
The equality hx only changes from the composite point to the specified equal point y.
All maps in this predicate are the ordinary unit and the existing local-return operators.
Source: Part 2, same fibers and local geometric Frobenius
(blueprint: lem-zl-condensed-open-extension-local). -/
def PointwiseOpenComparison {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (a : U ⟶ U) (b : X ⟶ X)
    (β : openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j ⋙
        upperStar (Profinite.padicAlgClRingObj ℓ) b ≅
      upperStar (Profinite.padicAlgClRingObj ℓ) a ⋙
        openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j)
    (F : WeilConjectures.condensedWeilModules (Profinite.padicAlgClRingObj ℓ) a)
    (z : Spec (.of D.k) ⟶ U) (y : Spec (.of D.k) ⟶ X) (hx : z ≫ j = y)
    (n : ℕ)
    (hy : y ≫ WeilConjectures.NativeCondensedModule.localPositivePower b n =
      WeilConjectures.NativeCondensedModule.localPositivePower
        (WeilConjectures.NativeCondensedModule.frobeniusPointIso D).hom n ≫ y) :
    Prop :=
  ∃ hret : z ≫ WeilConjectures.NativeCondensedModule.localPositivePower a n =
      WeilConjectures.NativeCondensedModule.localPositivePower
        (WeilConjectures.NativeCondensedModule.frobeniusPointIso D).hom n ≫ z,
    ∃ e : WeilConjectures.NativeCondensedModule.fibre ℓ D F.carrier z ≅
        WeilConjectures.NativeCondensedModule.fibre ℓ D
          ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j).obj F.carrier) y,
      e.hom = moduleFibreUnit ℓ D.k j F.carrier z ≫ eqToHom
        (congrArg (WeilConjectures.NativeCondensedModule.fibre ℓ D
          ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j).obj F.carrier)) hx) ∧
      WeilConjectures.NativeCondensedModule.operator ℓ D a F.carrier F.str z n hret ≫ e.hom =
        e.hom ≫ WeilConjectures.NativeCondensedModule.operator ℓ D b
          ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) j).obj F.carrier)
          ((IsoAlgebra.mapOfNatIso β).obj F).str y n hy

/-- Restriction and transport of the specified open adjunction. The equations specify
both underlying maps, including the orientation of the compact-support comparison.
Source: Part 2, normalized open unit and counit
(blueprint: lem-zl-condensed-open-extension-local). -/
def RestrictedAdjunctionComparison {C : Type uC} {E : Type uD}
    [Category.{vC} C] [Category.{vD} E]
    {J : C ⥤ E} {S : E ⥤ C} (a : J ⊣ S)
    (P : ObjectProperty C) (Q : ObjectProperty E)
    (R : P.FullSubcategory ⥤ E) (c : R ≅ P.ι ⋙ J) : Prop :=
  ∃ hR : ∀ K, Q (R.obj K),
    ∃ hS : ∀ M : Q.FullSubcategory, P (S.obj M.obj),
      ∃ b : Q.lift R hR ⊣ P.lift (Q.ι ⋙ S) hS,
        (∀ K, (b.unit.app K).hom =
          a.unit.app K.obj ≫ S.map (c.inv.app K)) ∧
        (∀ M, (b.counit.app M).hom =
          c.hom.app ⟨S.obj M.obj, hS M⟩ ≫ a.counit.app M.obj)

end AlgebraicGeometry.ProEtale.CondensedRing.OpenExtensionLocal
