/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F9
-/
module

public import Sheaf.Paper.ConstantAdicQuotientScalarComparison
public import Sheaf.Paper.ConstantAdicRestrictedTower
public import Sheaf.Paper.SourceIsomorphismNormalizedPresheafEvaluation
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves

/-! # Descent of the finite levels before constructing Isom sheaves

Source: Stacks Tags 099Z, 09B1, 099Y, 09BV and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard

/-- Completion quotient coefficients, indexed by positive exponents.
Source: Stacks Tag 031C (blueprint: lem-weil-pbc-lisse-tower-etale-descent). -/
abbrev lisseTowerEtaleRing {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :=
  AdicCompletion d.ideal A ⧸
    (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)

/-- The consecutive quotient homomorphism.
Source: Stacks Tag 031C (blueprint: lem-weil-pbc-lisse-tower-etale-descent). -/
def lisseTowerEtaleQuotient {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :
    lisseTowerEtaleRing d (n + 1) →+* lisseTowerEtaleRing d n :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right
    (I := d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) (Nat.le_succ (n + 1)))

/-- Forget quotient coefficients to the completion.
Source: Stacks Tag 06YY (blueprint: lem-weil-pbc-lisse-tower-etale-descent). -/
abbrev lisseTowerAlgebraForget {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :=
  (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
    (Ideal.Quotient.mk ((d.ideal.map
      (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)))).mapDerivedCategory

/-- The algebraic arrow after forgetting scalars, with the specified compositors.
Source: Stacks Tag 06YY (blueprint: lem-weil-pbc-lisse-tower-etale-descent). -/
def lisseTowerAlgebraArrow {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ)
    {E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1)))}
    {E' : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))}
    (k : E ⟶ (normalizationModuleRestrict (lisseTowerEtaleQuotient d n)).obj E') :
    (lisseTowerAlgebraForget d (n + 1)).obj E ⟶
      (lisseTowerAlgebraForget d n).obj E' :=
  (lisseTowerAlgebraForget d (n + 1)).map k ≫
    (Functor.mapDerivedCategoryCompIso
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (lisseTowerEtaleQuotient d n))
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
        (Ideal.Quotient.mk ((d.ideal.map
          (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 2))))).inv.app E' ≫
    (Functor.mapDerivedCategoryNatIso (ModuleCat.restrictScalarsComp'.{u + 1}
      (Ideal.Quotient.mk ((d.ideal.map
        (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 2)))
      (lisseTowerEtaleQuotient d n)
      (Ideal.Quotient.mk ((d.ideal.map
        (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1)))
      (Ideal.Quotient.factor_comp_mk _).symm)).inv.app E'

attribute [local irreducible] pbcDerivedRestrict
  constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow etaleIsomorphismNormalizationArrow
  lisseTowerAlgebraArrow

/-- Raw etale descent data. The source arrows are not supplied: the model comparison
respects *every* algebraic arrow. There are no Isom-sheaf reduction maps or evaluations.
Source: Stacks Tags 099Z, 09B1, 099Y and 06YY
(blueprint: lem-weil-pbc-lisse-tower-etale-descent). -/
structure LisseTowerEtaleDescent
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (M : AdicTower X d) (U : Y.ProEt)
    (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))) where
  D : ∀ n : ℕ, DerivedCategory
    (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
  boundedD : ∀ n : ℕ, ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q → IsZero
    ((DerivedCategory.homologyFunctor _ q).obj (D n))
  lisseD : ∀ (n : ℕ) (q : ℤ), IsFiniteLocallyConstantSheaf
    ((DerivedCategory.homologyFunctor _ q).obj (D n))
  stalk : ∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ U.left), Nonempty ((pointSmallEtale x).sheafFiber.obj
      (derivedLocalIsomorphismSheaf
        ((normalizationConstant U.left.smallEtaleTopology).obj (K n)) (D n)))
  delta : ∀ n : ℕ, D (n + 1) ⟶
    (normalizationRestrict U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)).obj (D n)
  local_delta_universal : ∀ (n : ℕ) (V : U.left.Etale),
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk
      (etaleIsomorphismNormalizationArrow U.left (lisseTowerEtaleQuotient d n) (delta n) V)))
  local_constant_universal : ∀ (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))))
    (E' : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (k : E ⟶ (normalizationModuleRestrict (lisseTowerEtaleQuotient d n)).obj E'),
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk k)) →
    ∀ V : U.left.Etale, Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk
      (etaleIsomorphismNormalizationArrow U.left (lisseTowerEtaleQuotient d n)
        (normalizationConstantArrow U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)
          k) V)))
  restriction_square : ∀ (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))))
    (E' : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (k : E ⟶ (normalizationModuleRestrict (lisseTowerEtaleQuotient d n)).obj E')
    (V Z : U.left.Etale) (f : V ⟶ Z)
    (e : (localIsomorphismRestriction U.left (lisseTowerEtaleRing d (n + 1)) Z).obj
        ((normalizationConstant U.left.smallEtaleTopology).obj E) ≅
      (localIsomorphismRestriction U.left (lisseTowerEtaleRing d (n + 1)) Z).obj (D (n + 1)))
    (e' : (localIsomorphismRestriction U.left (lisseTowerEtaleRing d n) Z).obj
        ((normalizationConstant U.left.smallEtaleTopology).obj E') ≅
      (localIsomorphismRestriction U.left (lisseTowerEtaleRing d n) Z).obj (D n)),
    e.hom ≫ etaleIsomorphismNormalizationArrow U.left (lisseTowerEtaleQuotient d n)
        (delta n) Z =
      etaleIsomorphismNormalizationArrow U.left (lisseTowerEtaleQuotient d n)
        (normalizationConstantArrow U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)
          k) Z ≫ (normalizationRestrict Z.left.smallEtaleTopology
            (lisseTowerEtaleQuotient d n)).map e'.hom →
    (localIsomorphismMap ((normalizationConstant U.left.smallEtaleTopology).obj E)
      (D (n + 1)) f e).hom ≫ etaleIsomorphismNormalizationArrow U.left
        (lisseTowerEtaleQuotient d n) (delta n) V =
      etaleIsomorphismNormalizationArrow U.left (lisseTowerEtaleQuotient d n)
        (normalizationConstantArrow U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)
          k) V ≫ (normalizationRestrict V.left.smallEtaleTopology
            (lisseTowerEtaleQuotient d n)).map
              (localIsomorphismMap ((normalizationConstant U.left.smallEtaleTopology).obj E')
                (D n) f e').hom
  realization : ∀ (V : U.left.ProEt) (W : Y.ProEt),
    (W ⟶ ProEt.mk (V.hom ≫ U.hom)) → ∀ n : ℕ,
    DerivedCategory (Sheaf (ProEt.topology V.left)
      (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))) ⥤
      DerivedCategory (pbcModules W.left
        ((adicTowerInverseImage (W.hom ≫ g)).obj ((pbcAdicRings X d).obj (op n))))
  model : ∀ (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))),
    (realization V W f n).obj ((localProEtaleComparison V.hom
      (lisseTowerEtaleRing d n)).obj
        ((normalizationConstant U.left.smallEtaleTopology).obj E)) ≅
      (constantAdicQuotientRealization (W.hom ≫ g) d n).obj E
  actual : ∀ (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) (n : ℕ),
    (realization V W f n).obj
      ((localProEtaleComparison V.hom (lisseTowerEtaleRing d n)).obj (D n)) ≅
      (adicTowerPullback (W.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj (M.level n)
  scalar : ∀ (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) (n : ℕ),
    normalizationRestrict (ProEt.topology V.left) (lisseTowerEtaleQuotient d n) ⋙
        realization V W f (n + 1) ⋙
          pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d (n + 1)) ≅
      realization V W f n ⋙ pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d n)
  actual_normalized : ∀ (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) (n : ℕ),
    let H (k : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d k)
    (H (n + 1)).map ((realization V W f (n + 1)).map
      (localProEtaleNormalization V.hom (lisseTowerEtaleQuotient d n) (delta n))) ≫
      (scalar V W f n).hom.app
        ((localProEtaleComparison V.hom (lisseTowerEtaleRing d n)).obj (D n)) ≫
      (H n).map (actual V W f n).hom =
    (H (n + 1)).map (actual V W f (n + 1)).hom ≫
      constantAdicRestrictedStep (W.hom ≫ g) d M n
  model_normalized : ∀ (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom)) (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))))
    (E' : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (k : E ⟶ (normalizationModuleRestrict (lisseTowerEtaleQuotient d n)).obj E'),
    let H (j : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d j)
    let c (j : ℕ) (N : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d j))) :=
      (H j).mapIso (model V W f j N) ≪≫
        ((constantAdicQuotientRightIso (W.hom ≫ g) d j).app N).symm
    (H (n + 1)).map ((realization V W f (n + 1)).map
      (localProEtaleNormalization V.hom (lisseTowerEtaleQuotient d n)
        (normalizationConstantArrow U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)
          k))) ≫
      (scalar V W f n).hom.app ((localProEtaleComparison V.hom
        (lisseTowerEtaleRing d n)).obj
          ((normalizationConstant U.left.smallEtaleTopology).obj E')) ≫ (c n E').hom =
      (c (n + 1) E).hom ≫
        (constantAdicFiniteRealization (W.hom ≫ g) d).map (lisseTowerAlgebraArrow d n k)

/-- Separately locally algebraic finite levels descend, together with the actual
normalization arrows. The constant comparison is natural for every algebraic source
arrow; this theorem has no supplied source normalization, no reduction on Isom sheaves,
and no evaluation of sheaf sections.

Source: Stacks Tags 099Z and 09B1 (bounded-below classical comparison), 099Y
(finite locally constant descent), 09BV (Isom torsors), and 06YY (derived base change).
(blueprint: lem-weil-pbc-lisse-tower-etale-descent).

Proof: localize the pro-etale site at U. Identify each completion quotient with A/I^(n+1)
using completeness for the finitely generated ideal; in particular it is finite. The
canonical constant-module comparison identifies the supplied local models with exact
constant fixed-ring realizations. Their cohomology is bounded and finite locally
constant. Classical bounded-below comparison descends the actual level to an etale
complex D_n, and full faithfulness descends its normalization arrow. The canonical
coefficient interchange is the mate of sectionwise scalar restriction. Its scalar
extension mate is invertible, so the descended arrow is universal, as M.normalization
is invertible. Exact restriction to each etale object preserves these scalar
extension universal arrows. For constants use exact constant realization on that object.
Naturality of the coefficient mate and associativity of inverse image show that
restriction takes every supplied generator square to the displayed restricted square.
Nonempty local marking torsors give nonempty geometric Isom stalks, since finite
locally constant sheaves descend through comparison. Realization on V followed by
restriction along W gives the displayed functors and level comparisons. Paste their
coefficient mates. For the actual level, the resulting identity is the definition of
adicTowerRestrictedTransition. For constants, sectionwise restriction fixes every
constant section. Thus the pasted identity holds for every algebraic arrow k and
localizes to precisely the displayed scalar compositors. No section is evaluated and
no compatible markings, Isom reduction maps, or inverse limits are selected. Empty
bases and zero complexes use these same exact functors and the empty covering. -/
theorem lisse_tower_etale_descent
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (U : Y.ProEt)
    (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{u + 1}
      (AdicCompletion d.ideal A ⧸
        (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
    (hbounded : ∀ n : ℕ, ∃ a b : ℤ, ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (K n)))
    (hfinite : ∀ (n : ℕ) (q : ℤ), Module.Finite
      (AdicCompletion d.ideal A ⧸
          (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
          (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))) q).obj (K n)))
    (hmodels : ∀ n : ℕ, ∃ T : Sieve U, T ∈ ProEt.topology Y U ∧
      ∀ (W : Y.ProEt) (w : W ⟶ U), T w →
        Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj (K n) ≅
          (adicTowerPullback (W.hom ≫ g)
            ((pbcAdicRings X d).obj (op n))).obj (M.level n))) :
    Nonempty (LisseTowerEtaleDescent X Y g d M U K) := by sorry

end AlgebraicGeometry.Scheme
