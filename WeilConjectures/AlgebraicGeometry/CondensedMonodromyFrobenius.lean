/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedLisseMonodromy
public import WeilConjectures.AlgebraicGeometry.CondensedModuleLocalFrobenius
public import WeilConjectures.AlgebraicGeometry.EtaleWeilFundamentalRepresentation
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ArithmeticLiftFibrePath
public import Mathlib.RepresentationTheory.Invariants
import WeilConjectures.AlgebraicGeometry.LinearAlgebraicGroup.Monodromy

/-! # Condensed geometric sections and local Frobenius

Source: latest blueprint, sec-purity-real-sheaves/sk-lem-wrp-hc2/p-real-sections.md,
its residual-Frobenius paragraph, and sk-lem-wrp-hc2.proof.md, final paragraph
(blueprint: lem-a1-condensed-monodromy-frobenius).

The auxiliary declarations spell out the arrows in the assertion. `FibreAssertions`
records the representation, sections, naturality, tensor and dual clauses;
`ArithmeticAssertions` fixes the arithmetic normalization and the actual local-return
operator. The theorem asserts their existence over the given finite-field scheme.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped TensorProduct CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedLisseMonodromy

/-- Geometric sections after forgetting the Weil structure.
Source: p-real-sections.md, displayed H⁰ formula
(blueprint: lem-a1-condensed-monodromy-frobenius). -/
abbrev Sections (l : ℕ) [Fact l.Prime] {X : Scheme.{u}} (L : Lisse l X) :=
  Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) X) ⟶ L.obj

/-- Constant coefficient multiplication on the source of a section.
Source: p-real-sections.md, linearity of evaluation
(blueprint: lem-a1-condensed-monodromy-frobenius). -/
def sectionScalar (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) (c : Coeff.{u} l) :
    End (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) X)) :=
  Mod.regularEndRingHom
    (MonObj.Γ.mapFunctor (upperStarFromPoint X)
      (Profinite.PadicAlgCl.constRingHom l c.down))

/-- Evaluation of a module map from the coefficient unit at its unit vector.
Source: p-real-sections.md, evaluation at the chosen geometric point
(blueprint: lem-a1-condensed-monodromy-frobenius). -/
def sectionEvaluation (l : ℕ) [Fact l.Prime] {k : Type u} [Field k]
    (C : Context l k) (S : CompatibleSystem l k)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ C.X)
    (L : Lisse l C.X) (b : Sections l L) : (fibre l t).obj L :=
  (fibre l t).map
    (ObjectProperty.homMk (eqToHom (S.tensorDual C).unit_object ≫ b) :
      (S.tensorDual C).unit ⟶ L)
      (((S.tensorDual C).unitFibre Ω t).symm 1)

/-- Pullback transport followed by theta, using the canonical coefficient-unit comparison.
Source: p-real-sections.md, definition of geometric Frobenius on geometric sections
(blueprint: lem-a1-condensed-monodromy-frobenius). -/
def sectionFrobenius (l : ℕ) [Fact l.Prime] {k : Type u} [Field k]
    (C : Context l k) (S : CompatibleSystem l k) (h : C.X ≅ C.X)
    (L : Lisse l C.X) (θ : (S.toSystem.pullback l h.hom).obj L ≅ L)
    (b : Sections l L) : Sections l L :=
  (CondensedRing.upperStarObjRegularIso (Profinite.padicAlgClRingObj l) h.hom).inv ≫
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) h.hom).map b ≫ θ.hom.hom

/-- The degree-one map theta L_s⁻¹ on the original condensed fibre.
Source: def-wf-fundamental-representation.md, specified degree-one operator
(blueprint: lem-a1-condensed-monodromy-frobenius). -/
def degreeOne (l : ℕ) [Fact l.Prime] {k : Type u} [Field k]
    (C : Context l k) (S : CompatibleSystem l k) (h : C.X ≅ C.X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ C.X)
    (τ : FiniteEtale.fiber t ≅ FiniteEtale.fiber (t ≫ h.hom))
    (L : Lisse l C.X) (θ : (S.toSystem.pullback l h.hom).obj L ≅ L) :
    (fibre l t).obj L ≃ₗ[Coeff.{u} l] (fibre l t).obj L :=
  ((S.comparison C).path l τ L).trans
    (((S.toSystem.pullbackFibre l h.hom t).symm.app L).toLinearEquiv.trans
      (((fibre l t).mapIso θ).toLinearEquiv))

/-- The underlying ordinary condensed-module Weil isomorphism, without a lattice.
Source: the degree-zero clause of def-weil-weil-sheaf-complex
(blueprint: lem-a1-condensed-monodromy-frobenius). -/
def underlyingWeil (l : ℕ) [Fact l.Prime] {k : Type u} [Field k]
    (C : Context l k) (S : CompatibleSystem l k) (h : C.X ≅ C.X)
    (L : Lisse l C.X) (θ : (S.toSystem.pullback l h.hom).obj L ≅ L) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) h.hom).obj L.obj ≅ L.obj :=
  (ObjectProperty.ι _).mapIso θ

/-- The ordinary local-return construction evaluated on the displayed geometric fibre.
This uses the same internal return arrow and iterate as CondensedModule.operator;
only the published terminal-section scalar transport is applied here.
Source: def-weil-local-frobenius-trace, ordinary module local-return formula
(blueprint: lem-a1-condensed-monodromy-frobenius). -/
def localReturn (l : ℕ) [Fact l.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
    (C : Context l D.k) (S : CompatibleSystem l D.k) (h : C.X ≅ C.X)
    (L : Lisse l C.X) (θ : (S.toSystem.pullback l h.hom).obj L ≅ L)
    (z : Spec (.of D.k) ⟶ C.X) (n : ℕ)
    (hz : z ≫ WeilConjectures.localPositivePower h.hom n =
      WeilConjectures.localPositivePower (WeilConjectures.frobeniusPointIso D).hom n ≫ z) :
    End ((fibre l z).obj L) :=
  ((geometricEvaluation l D.k).mapIso
    ((CondensedRing.pointComparison (Profinite.padicAlgClRingObj l)
      (CondensedRing.upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj l)
        (WeilConjectures.localPositivePower (WeilConjectures.frobeniusPointIso D).hom n))
      (WeilConjectures.localPositivePower h.hom n) hz).app L.obj ≪≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).mapIso
        (WeilConjectures.CondensedModule.iterate l h.hom L.obj
          (underlyingWeil l C S h L θ) n))).hom

/-- All fibre and geometric-section conclusions, simultaneously for all Weil modules.
The section isomorphisms are additive equivalences with their scalar law written out,
so their source is literally Hom_Mod(Λ_X,L), with no auxiliary scalar instance.
Source: p-real-sections.md and sk-lem-wrp-hc2.proof.md
(blueprint: lem-a1-condensed-monodromy-frobenius). -/
structure FibreAssertions (l : ℕ) [Fact l.Prime] {k : Type u} [Field k]
    (C : Context l k) (S : CompatibleSystem l k) (h : C.X ≅ C.X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ C.X)
    (W : Type v) [Group W] (d : Monodromy.DegreeDatum W)
    (E : EtaleWeilDegreeData h t W d) where
  representation : ∀ (L : Lisse l C.X)
    (_θ : (S.toSystem.pullback l h.hom).obj L ≅ L),
    Representation (Coeff.{u} l) W ((fibre l t).obj L)
  geometric : ∀ (L : Lisse l C.X) (θ : (S.toSystem.pullback l h.hom).obj L ≅ L)
    (g : Aut (FiniteEtale.fiber t)) (v : (fibre l t).obj L),
    representation L θ (E.geom g) v = (S.comparison C).path l g L v
  frobenius : ∀ (L : Lisse l C.X) (θ : (S.toSystem.pullback l h.hom).obj L ≅ L),
    representation L θ d.degreeOneElement = (degreeOne l C S h t E.path L θ).toLinearMap
  extension : ∀ (L : Lisse l C.X) (θ : (S.toSystem.pullback l h.hom).obj L ≅ L)
    (g : Aut (FiniteEtale.fiber t)) (n : ℤ) (v : (fibre l t).obj L),
    representation L θ ((E.geom g : W) * d.degreeOneElement ^ n) v =
      (S.comparison C).path l g L ((degreeOne l C S h t E.path L θ ^ n) v)
  agreement : ∀ (L : Lisse l C.X) (θ : (S.toSystem.pullback l h.hom).obj L ≅ L)
    (w : W) (v : (fibre l t).obj L),
    (S.comparison C).beta l t L (representation L θ w v) =
      etaleFundamentalRep l (Coeff.{u} l) h t d E (S.weil l C h L θ) w
        ((S.comparison C).beta l t L v)
  sections : ∀ (L : Lisse l C.X) (θ : (S.toSystem.pullback l h.hom).obj L ≅ L),
    ∃ e : Sections l L ≃+
        Representation.invariants ((representation L θ).comp d.deg.ker.subtype),
      (∀ b : Sections l L, (e b).val = sectionEvaluation l C S t L b) ∧
      (∀ (c : Coeff.{u} l) (b : Sections l L),
        (e (sectionScalar l C.X c ≫ b)).val = c • (e b).val) ∧
      (∀ b : Sections l L,
        (e (sectionFrobenius l C S h L θ b)).val =
          degreeOne l C S h t E.path L θ (e b).val)
  morphisms : ∀ (L M : Lisse l C.X)
    (θL : (S.toSystem.pullback l h.hom).obj L ≅ L)
    (θM : (S.toSystem.pullback l h.hom).obj M ≅ M) (f : L ⟶ M),
    (S.toSystem.pullback l h.hom).map f ≫ θM.hom = θL.hom ≫ f →
    ∀ (w : W) (v : (fibre l t).obj L),
      (fibre l t).map f (representation L θL w v) =
        representation M θM w ((fibre l t).map f v)
  evaluation_natural : ∀ (L M : Lisse l C.X) (f : L ⟶ M) (b : Sections l L),
    sectionEvaluation l C S t M (b ≫ f.hom) =
      (fibre l t).map f (sectionEvaluation l C S t L b)
  duals : ∀ (L : Lisse l C.X) (θ : (S.toSystem.pullback l h.hom).obj L ≅ L),
    ∃ θdual : (S.toSystem.pullback l h.hom).obj ((S.tensorDual C).dual L) ≅
        (S.tensorDual C).dual L,
      ∀ (w : W) (φ : (fibre l t).obj ((S.tensorDual C).dual L))
        (v : (fibre l t).obj L),
        (S.tensorDual C).dualFibre Ω t L
          (representation ((S.tensorDual C).dual L) θdual w φ)
            (representation L θ w v) = (S.tensorDual C).dualFibre Ω t L φ v
  tensors : ∀ (L M : Lisse l C.X)
    (θL : (S.toSystem.pullback l h.hom).obj L ≅ L)
    (θM : (S.toSystem.pullback l h.hom).obj M ≅ M),
    ∃ θtensor : (S.toSystem.pullback l h.hom).obj ((S.tensorDual C).tensor L M) ≅
        (S.tensorDual C).tensor L M,
      ∀ (w : W) (v : (fibre l t).obj L) (v' : (fibre l t).obj M),
        (S.tensorDual C).tensorFibre Ω t L M
          (representation ((S.tensorDual C).tensor L M) θtensor w
            (((S.tensorDual C).tensorFibre Ω t L M).symm (v ⊗ₜ v'))) =
              representation L θL w v ⊗ₜ representation M θM w v'

/-- The projection to the finite-field model in geometric coordinates.
Source: def-wf-weil-group, base-change convention
(blueprint: lem-a1-condensed-monodromy-frobenius). -/
def modelProjection (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    {X : Scheme.{u}} (j : X ≅ (D.geometricFiber X₀).left) : X ⟶ X₀.left :=
  j.hom ≫ pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))

/-- Geometric Frobenius in the same coordinates as the condensed monodromy context.
Source: def-wf-fundamental-representation.md, g_X = 1 × Spec(gamma)
(blueprint: lem-a1-condensed-monodromy-frobenius). -/
def modelFrobenius (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    {X : Scheme.{u}} (j : X ≅ (D.geometricFiber X₀).left) : X ≅ X :=
  j ≪≫ D.geometricFrobenius X₀ ≪≫ j.symm

/-- The existing Weil group, using the arithmetic image of the geometric base point.
Source: def-wf-weil-group
(blueprint: lem-a1-condensed-monodromy-frobenius). -/
abbrev ModelWeilGroup (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [GeometricallyConnected X₀.hom] {X : Scheme.{u}}
    (j : X ≅ (D.geometricFiber X₀).left)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X) :=
  FiniteEtale.weilGroup X₀.hom (t ≫ modelProjection D X₀ j)
    (Aut (FiniteEtale.fiber (t ≫ modelProjection D X₀ j)))

/-- The existing degree homomorphism, without rescaling its integer grading.
Source: lem-wf-weil-group-exact-sequence
(blueprint: lem-a1-condensed-monodromy-frobenius). -/
abbrev modelDegree (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [GeometricallyConnected X₀.hom] {X : Scheme.{u}}
    (j : X ≅ (D.geometricFiber X₀).left)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X) :=
  FiniteEtale.weilGroupDeg X₀.hom (t ≫ modelProjection D X₀ j)
    (Aut (FiniteEtale.fiber (t ≫ modelProjection D X₀ j)))

/-- Arithmetic normalization and the local-return conjugacy on the original fibres.
Source: arithmetic finite-path normalization and sk-lem-wrp-hc2.proof.md, final paragraph
(blueprint: lem-a1-condensed-monodromy-frobenius). -/
structure ArithmeticAssertions (l : ℕ) [Fact l.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [GeometricallyConnected X₀.hom] (C : Context l D.k)
    (j : C.X ≅ (D.geometricFiber X₀).left) (S : CompatibleSystem l D.k)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ C.X)
    (d : Monodromy.DegreeDatum (ModelWeilGroup D X₀ j t))
    (E : EtaleWeilDegreeData (modelFrobenius D X₀ j) t _ d)
    (A : FibreAssertions l C S (modelFrobenius D X₀ j) t _ d E) where
  degree_eq : d.deg = modelDegree D X₀ j t
  geometric_inclusion : ∀ g : Aut (FiniteEtale.fiber t),
    ((E.geom g).val.val).1 =
      FiniteEtale.fiberAutBaseChange (modelProjection D X₀ j) t g
  basepoint_eq : (t ≫ (modelFrobenius D X₀ j).hom) ≫ modelProjection D X₀ j =
    t ≫ modelProjection D X₀ j
  path_normalization :
    FiniteEtale.pullbackPathIso (modelProjection D X₀ j) E.path ≪≫
      eqToIso (congrArg FiniteEtale.fiber basepoint_eq) = d.degreeOneElement.val.1
  local_frobenius : ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (ι : X₀.left.residueField x.val →+* D.k)
    (hι : ι.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (z : Spec (.of D.k) ⟶ C.X),
    z ≫ j.hom = WeilConjectures.localClosedPoint D X₀ x ι hι →
    ∀ τ : FiniteEtale.fiber z ≅ FiniteEtale.fiber t,
    ∃ hz : z ≫ WeilConjectures.localPositivePower (modelFrobenius D X₀ j).hom
        (WeilConjectures.localClosedPointDegree D X₀ x - 1) =
      WeilConjectures.localPositivePower (WeilConjectures.frobeniusPointIso D).hom
        (WeilConjectures.localClosedPointDegree D X₀ x - 1) ≫ z,
    ∃ w : ModelWeilGroup D X₀ j t,
      modelDegree D X₀ j t w =
        Multiplicative.ofAdd (WeilConjectures.localClosedPointDegree D X₀ x : ℤ) ∧
      ∀ (L : Lisse l C.X)
        (θ : (S.toSystem.pullback l (modelFrobenius D X₀ j).hom).obj L ≅ L)
        (v : (fibre l t).obj L),
        (S.comparison C).path l τ L
          ((localReturn l D C S (modelFrobenius D X₀ j) L θ z
            (WeilConjectures.localClosedPointDegree D X₀ x - 1) hz).hom
              ((S.comparison C).path l τ.symm L v)) = A.representation L θ w v

/-- Geometric sections, dual sections, and local Frobenius under condensed monodromy.

Source: p-real-sections.md, displayed geometric-sections and residual-Frobenius formulas;
sk-lem-wrp-hc2.proof.md, dual and degree-d local assertions
(blueprint: lem-a1-condensed-monodromy-frobenius).

Proof: Obtain the normalized actual-fibre tensor comparison from
lem-a1-condensed-lisse-monodromy. Arithmetic finite paths give the conjugation identity
for theta L_s⁻¹ (lem-wf-arithmetic-lift-fibre-path), on finite reductions first; only L,
not theta, is reduced integrally. Identify the geometric group with the degree kernel
using lem-wf-weil-group-exact-sequence and extend by new-t2-degree-kernel-extension.
The normalized comparison gives agreement with def-wf-fundamental-representation.
Full faithfulness sends Hom(Λ_X,L) to Hom_P(Λ,V); evaluation at 1 identifies this with
V^P. Naturality of the unit path gives e F_Gamma = T e. Apply tensor duality to obtain
the inverse transpose operator on the dual and its invariant sections. For a local
return of length d, reparametrization on each finite cover gives the arithmetic
Frobenius of degree d. Conjugate it by the chosen geometric path. Iteration of theta
and finite-path normalization identify the resulting action with the actual local
return arrow of def-weil-local-frobenius-trace. These equalities are natural in
morphisms and preserve tensor pairings, hence also duals. The local clause uses the
actual positive residue degree, with localPositivePower indexed by degree minus one.
Coordinates j merely identify the dependency's geometric
context with the stated fibre product; they impose no restriction on the input scheme.
-/
theorem condensed_monodromy_frobenius
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [Smooth X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] [GeometricallyConnected X₀.hom] :
    ∃ (C : Context l D.k) (j : C.X ≅ (D.geometricFiber X₀).left)
      (S : CompatibleSystem l D.k), WeilCompatibility l S ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ C.X)
        (s : ModelWeilGroup D X₀ j t),
        modelDegree D X₀ j t s = Multiplicative.ofAdd 1 →
        ∃ (d : Monodromy.DegreeDatum (ModelWeilGroup D X₀ j t))
          (E : EtaleWeilDegreeData (modelFrobenius D X₀ j) t _ d)
          (A : FibreAssertions l C S (modelFrobenius D X₀ j) t _ d E),
          d.degreeOneElement = s ∧ Nonempty (ArithmeticAssertions l D X₀ C j S t d E A) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedLisseMonodromy
