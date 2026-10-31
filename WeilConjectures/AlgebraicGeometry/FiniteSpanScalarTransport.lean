/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSpanModuleComparisonData
import WeilConjectures.AlgebraicGeometry.FiniteSpanScalarTransportOrdinary
import WeilConjectures.AlgebraicGeometry.FiniteSpanScalarTransportCoherence
import WeilConjectures.AlgebraicGeometry.FiniteSpanScalarTransportSections
import WeilConjectures.AlgebraicGeometry.FiniteSpanScalarTransportDerived

/-! # Scalar transport from a supplied natural coefficient-ring isomorphism

The coefficient isomorphism is input, and its finite-field chart normalization and
exchange compatibility are separate arguments in FiniteSpanModuleDerivedComparison.
Source: Stacks Project, Modules on Sites, Tags 03D6 and 03D7; Derived Categories,
Tags 070I, 070Y and 09T5; Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-sf-finite-span-scalar-transport).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteSpanComparison

/-- A natural ring isomorphism extends to normalized ordinary and derived module transport.
Source: Stacks Project, Modules on Sites, Tags 03D6 and 03D7; Derived Categories,
Tags 070I, 070Y and 09T5; Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-sf-finite-span-scalar-transport).

Proof: assembly of four steps, each with its own node.
1. lem-sf-finite-span-scalar-ordinary gives Data with exactly this theta, the native
   precomposition coefficient map, a pushComparison that is the identity on sections, and the
   ordinary mate equation for pullComparison.
2. lem-sf-finite-span-scalar-coherence, applied to these three normalizations, gives the
   geometric push compositor, its left-adjoint mate as pull compositor, the rho composition
   law and the ordinary composition equation; replace the two compositor fields by them.
   The other fields, hence the clauses of step 1, are unchanged.
3. lem-sf-finite-span-scalar-derived, applied to the retained ordinary mate equation, gives
   the right-derived lift of pushComparison with its unit normalization and
   DerivedNormalization for every scheme morphism; replace only derivedPushComparison.
4. lem-sf-finite-span-scalar-sections gives, for the resulting Data, the underlying sheaf
   equality, the basis correspondence (also in rank zero) and K-injective preservation in
   both directions. The last clause is DerivedNormalization specialized to morphisms of
   schemes separated of finite type over the field. -/
theorem finiteSpanScalarTransport (l : ℕ) [Fact l.Prime]
    (theta : ∀ X : Scheme.{u},
      condensedRingObj (Profinite.padicAlgClRingObj l) X ≅ nativeAb l X)
    [∀ X : Scheme.{u}, IsMonHom (theta X).hom]
    (hcoeff : ∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
      condensedPushforwardHom (Profinite.padicAlgClRingObj l) f ≫
        (lowerStar Ab.{u + 1} f).map (theta X).hom =
      (theta Y).hom ≫ (weilCoefficientsForgetAb l Y).map (adicConstantSheafToLowerStar l f)) :
    ∃ d : Data.{u} l, letI := d; d.theta = theta ∧
  -- coefficient_sections
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.ProEtᵒᵖ)
    (r : (ring l Y).obj.obj V) (x : ((InternalModuleOperations.siteMap f).obj V.unop).left),
    (((d.coefficientMap f).hom.app V r).down.1 x) =
      r.down.1 ((Limits.pullback.fst V.unop.hom f).base x)) ∧
  -- rho_composition
  (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    rho l (f ≫ g) = (upperStarComp Ab.{u + 1} f g).hom.app (nativeAb l Z) ≫
      (upperStar Ab.{u + 1} f).map (rho l g) ≫ rho l f) ∧
  -- ordinary_mate
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (mateEquiv (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
      (adjunction l f (d.coefficientMap f)) (d.pullComparison f).inv).natTrans =
        (d.pushComparison f).hom) ∧
  -- push_identity
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : internal l X)
    (V : Y.ProEtᵒᵖ) (m : ((CondensedRing.lowerStar
      (Profinite.padicAlgClRingObj l) f).obj M).X.obj.obj V),
    (((d.pushComparison f).hom.app M).val.app V) m = m) ∧
  -- underlying
  (∀ X : Scheme.{u},
    (equivalence l X (d.theta X)).functor ⋙ SheafOfModules.toSheaf (ring l X) =
      Mod.forget (condensedRingObj (Profinite.padicAlgClRingObj l) X)) ∧
  -- finiteFree_sections
  (∀ (X : Scheme.{u}) (V : X.ProEtᵒᵖ) (M : internal l X) (n : ℕ)
    (b : Module.Basis (Fin n)
      ((InternalModuleOperations.ring (Profinite.padicAlgClRingObj l) X).obj.obj V)
      (((InternalModuleOperations.equivalence
        (Profinite.padicAlgClRingObj l) X).functor.obj M).val.obj V)),
    ∃ b' : Module.Basis (Fin n) ((ring l X).obj.obj V)
      (((equivalence l X (d.theta X)).functor.obj M).val.obj V),
      ∀ i : Fin n, b' i = b i) ∧
  -- pushComposition_sections
  (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : modules l X) (V : Z.ProEtᵒᵖ)
    (m : ((direct l g (d.coefficientMap g)).obj
      ((direct l f (d.coefficientMap f)).obj M)).val.obj V),
    (((d.pushComposition f g).hom.app M).val.app V).hom m =
      (((ProEtale.lowerStarComp Ab.{u + 1} f g).hom.app
        ((SheafOfModules.toSheaf (ring l X)).obj M)).hom.app V).hom m) ∧
  -- pullComposition_mate
  (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    d.pullComposition f g = (Adjunction.leftAdjointCompIso
      (adjunction l g (d.coefficientMap g)) (adjunction l f (d.coefficientMap f))
      (adjunction l (f ≫ g) (d.coefficientMap (f ≫ g))) (d.pushComposition f g)).symm) ∧
  -- ordinary_composition
  (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : internal l Z),
    (d.pullComparison (f ≫ g)).hom.app M ≫
      (d.pullComposition f g).hom.app ((equivalence l Z (d.theta Z)).functor.obj M) =
    (equivalence l X (d.theta X)).functor.map
      ((CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) f g).hom.app M) ≫
      (d.pullComparison f).hom.app
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g).obj M) ≫
      (inverse l f (d.coefficientMap f)).map ((d.pullComparison g).hom.app M)) ∧
  -- kinjective_forward
  (∀ (X : Scheme.{u}) (I : CochainComplex (internal l X) ℤ),
    I.IsKInjective → CochainComplex.IsKInjective
      (((equivalence l X (d.theta X)).functor.mapHomologicalComplex (.up ℤ)).obj I)) ∧
  -- kinjective_inverse
  (∀ (X : Scheme.{u}) (I : CochainComplex (modules l X) ℤ),
    I.IsKInjective → CochainComplex.IsKInjective
      (((equivalence l X (d.theta X)).inverse.mapHomologicalComplex (.up ℤ)).obj I)) ∧
  -- derived_push_normalization
  (∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (internal l X) ℤ),
    (equivalence l Y (d.theta Y)).functor.mapDerivedCategory.map
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).rightDerivedFunctorUnitQ P) ≫
      (d.derivedPushComparison f).hom.app (DerivedCategory.Q.obj P) ≫
      (direct l f (d.coefficientMap f)).rightDerivedFunctor.map
        ((equivalence l X (d.theta X)).functor.mapDerivedCategoryFactors.hom.app P) =
    (equivalence l Y (d.theta Y)).functor.mapDerivedCategoryFactors.hom.app
      (((CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).mapHomologicalComplex
        (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (d.pushComparison f) (.up ℤ)).hom.app P) ≫
      (direct l f (d.coefficientMap f)).rightDerivedFunctorUnitQ
        (((equivalence l X (d.theta X)).functor.mapHomologicalComplex (.up ℤ)).obj P)) ∧
  -- field_normalization
  (∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p],
    p ≠ l → ∀ (X Y : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y),
    DerivedNormalization l f.left) := by
  obtain ⟨d, htheta, hcoeff', hmate, hpush⟩ :=
    finiteSpanScalarTransportOrdinary l theta hcoeff
  let := d
  obtain ⟨pc, qc, hrho, hpc, hqc, hcomp⟩ :=
    finiteSpanScalarTransportCoherence l hcoeff' hmate hpush
  let d₁ : Data.{u} l := { d with pushComposition := pc, pullComposition := qc }
  obtain ⟨β, hunit, hderived⟩ := finiteSpanScalarTransportDerived l (d := d₁) hmate
  let d₂ : Data.{u} l := { d₁ with derivedPushComparison := β }
  obtain ⟨hunderlying, hbases, hforward, hinverse⟩ :=
    finiteSpanScalarTransportSections l (d := d₂)
  refine ⟨d₂, htheta, hcoeff', hrho, hmate, hpush, hunderlying, hbases,
    hpc, hqc, hcomp, hforward, hinverse, hunit, ?_⟩
  intro k _ p _ _ hpl X Y _ _ _ _ _ _ f
  exact hderived f.left

end AlgebraicGeometry.ProEtale.FiniteSpanComparison
