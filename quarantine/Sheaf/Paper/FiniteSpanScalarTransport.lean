/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Sheaf.Paper.FiniteSpanModuleComparisonData

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

Proof:
1. Reconstruct the native coefficient map from precomposition of locally finite functions.
   It preserves addition, multiplication, one and restrictions pointwise. Taking adjuncts
   of the input coefficient square gives the inverse coefficient square. Invertibility of
   theta and the condensed coefficient pullback makes rho invertible; precomposition twice
   proves its composition law, including identities and empty schemes.
2. Restrict internal module actions along theta inverse and apply sectionModuleEquivalence.
   The inverse restricts along theta. The composites agree on actions, maps and restrictions;
   hence the equivalence preserves finite limits and colimits. It keeps underlying abelian
   sheaves. Restricting a finite basis along a ring isomorphism keeps its vectors, also in
   rank zero. This is the explicit equivalence already defined in the data module.
3. Apply internal_module_operations_transport before relabelling the reconstructed scalars.
   The input square identifies the two direct-image actions, so pushComparison is identity
   on sections. The inverse coefficient square identifies pullback actions, using the tensor
   maps r tensor m to rho inverse(r)m and m to 1 tensor m. These give exact pullback and
   additive direct image. The tensor-formula presheaf adjoint is constructed on small models
   of the sites, as in the existing internal-module transport proof.
4. Tensor transposition evaluates at 1 tensor m, which the comparisons preserve, proving the
   ordinary mate equation. Use the geometric direct-image compositor on sections and its
   unique adjoint mate for pullComposition. The coefficient composition law and naturality
   give ordinary_composition by pasting the two ordinary comparison squares.
5. The equivalence and its inverse are exact, so their termwise functors preserve acyclic
   complexes. The homotopy Hom into E(I) is Hom from E inverse(N) into I, proving preservation
   of K-injectives both ways. Apply small-ringed-site K-injective resolutions to the native
   section rings, with section universe u+1. These supply hasResolutions and hasDerived.
6. On a K-injective resolution P to I compare the ordinary pushforwards of I and E(I).
   The canonical transition maps and kInjectiveDerivedMapComputation make this comparison
   natural and resolution-independent. Its defining right-derived-unit equation is exactly
   derived_push_normalization, for every unbounded complex P.
7. Apply sectionDerivedPushpullNormalization for the condensed coefficient before scalar
   relabelling. Exact pullback has K-injective-preserving right adjoint. The bijectivity of
   Qh on Hom into a K-injective identifies the derived transpose with ordinary chain
   transposition; Adjunction.derived and its counit compatibility give the displayed chain
   equation. Relabelling preserves this transpose by step 4, so transposing identities
   identifies the derived mate with the normalized right-derived comparison. This proves
   the field normalization, without an exchange or a properness assumption. -/
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
    DerivedNormalization l f.left) := by sorry

end AlgebraicGeometry.ProEtale.FiniteSpanComparison
