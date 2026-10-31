/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistsOfUniverses
public import WeilConjectures.AlgebraicGeometry.CondensedRationalAdjunction
public import WeilConjectures.AlgebraicGeometry.NativeRationalFieldAdjunctionTransport
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientDescentTwoColimit
public import WeilConjectures.AlgebraicGeometry.ExceptionalInverseImageExistence
public import WeilConjectures.SecSmoothPurity.TransportFamily
public import WeilConjectures.SecSmoothPurity.TransportScalarLines
public import Mathlib.CategoryTheory.Adjunction.Unique

import WeilConjectures.Algebra.Homology.OrdinaryLineDerivedScalarComparison
import WeilConjectures.AlgebraicGeometry.RationalLocalizedHom
import WeilConjectures.SixFunctors.ScalarSixCtf
public import WeilConjectures.SixFunctors.ScalarSixCompactSupport
public import WeilConjectures.SixFunctors.ScalarSixPullback
public import WeilConjectures.AlgebraicGeometry.CartesianCoefficients

/-! # Condensed algebraic-closure purity adjunction

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-sp-qbar/
  sk-thm-sp-qbar-adjunction.md (blueprint: prop-pur-condensed-qbar-adjunction).

The rational adjunctions are universally supplied with their rationalization and
integral normalization; the conclusion retains their actual units and counits.
The Hom-colimit composite is specified on every finite representative and every
choice of model isomorphisms. Together with the recorded Hom-descent theorem, this
is its universal representative description, including independence of models.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedQbarPurityAdjunction

/-- The finite-field inclusion as a bundled condensed ring map.
Source: coefficient transitions (blueprint: prop-pur-condensed-qbar-adjunction). -/
def fieldMap (ell : ℕ) [Fact ell.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F) :
    (Coefficient.rational E).bundled.{u} ell ⟶ (Coefficient.rational F).bundled ell :=
  CommMon.homMk (Mon.Hom.mk (Profinite.padicSubfieldRingObjMap ell h))

/-- The inclusion into the finite-subextension-valued algebraic-closure sheaf.
Source: coefficient transitions (blueprint: prop-pur-condensed-qbar-adjunction). -/
def closureMap (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) :
    (Coefficient.rational E).bundled.{u} ell ⟶ Coefficient.closure.bundled ell :=
  CommMon.homMk (Mon.Hom.mk (Profinite.padicSubfieldRingObjToPadicAlgCl ell E))

/-- Restriction of the actual derived scalar extension; only membership is supplied.
Source: scalar endpoints (blueprint: prop-pur-condensed-qbar-adjunction). -/
def extend (ell : ℕ) [Fact ell.Prime] {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell) (T : Scheme.{u})
    (h : ∀ K, property ell c T K → property ell c' T ((scalarSixChange a T).obj K)) :
    c.ctf ell T ⥤ c'.ctf ell T :=
  (property ell c' T).lift ((property ell c T).ι ⋙ scalarSixChange a T)
    (fun K ↦ h K.obj K.property)

/-- The two native scalar endpoints, normalized by the actual compact-support mate
and the native pullback/Tate-line comparison.
Source: displayed Hom composite (blueprint: prop-pur-condensed-qbar-adjunction). -/
structure Comparisons (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (s : SmoothDatum D)
    {c c' : Coefficient ell} (a : c.bundled ell ⟶ c'.bundled ell)
    (A : ExplicitAdjunction ell D c s) (B : ExplicitAdjunction ell D c' s) where
  hX : ∀ K, property ell c s.X.left K → property ell c' s.X.left
    ((scalarSixChange a s.X.left).obj K)
  hY : ∀ K, property ell c s.Y.left K → property ell c' s.Y.left
    ((scalarSixChange a s.Y.left).obj K)
  coefficient_normalization : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell
  line : ScalarLineCoordinates ell a coefficient_normalization s.X.left
  b : support ell c s.compactification A.support_closed ⋙ extend ell a s.Y.left hY ≅
    extend ell a s.X.left hX ⋙ support ell c' s.compactification B.support_closed
  j : source ell c s.map s.dim A.source_closed ⋙ extend ell a s.X.left hX ≅
    extend ell a s.Y.left hY ⋙ source ell c' s.map s.dim B.source_closed
  b_normalized : ∀ M : c.ctf ell s.X.left,
    (b.hom.app M).hom = (scalarSupportMap a s.compactification).app M.obj
  j_normalized : ∀ K : c.ctf ell s.Y.left,
    (j.hom.app K).hom =
      sourceScalar ell a s.map s.dim coefficient_normalization line K.obj

/-- The actual unit, counit, and Hom transition equations, retaining native maps.
Source: scalar-change equations (blueprint: prop-pur-condensed-qbar-adjunction). -/
structure TransitionLaws (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (s : SmoothDatum D)
    {c c' : Coefficient ell} (a : c.bundled ell ⟶ c'.bundled ell)
    (A : ExplicitAdjunction ell D c s) (B : ExplicitAdjunction ell D c' s)
    (q : Comparisons ell D s a A B) : Prop where
  unit : ∀ M : c.ctf ell s.X.left,
    B.adjunction.unit.app ((extend ell a s.X.left q.hX).obj M) =
      (extend ell a s.X.left q.hX).map (A.adjunction.unit.app M) ≫
        q.j.hom.app _ ≫ (source ell c' s.map s.dim B.source_closed).map (q.b.hom.app M)
  counit : ∀ K : c.ctf ell s.Y.left,
    q.b.hom.app _ ≫ (support ell c' s.compactification B.support_closed).map
        (q.j.hom.app K) ≫
      B.adjunction.counit.app ((extend ell a s.Y.left q.hY).obj K) =
        (extend ell a s.Y.left q.hY).map (A.adjunction.counit.app K)
  hom : ∀ (M : c.ctf ell s.X.left) (K : c.ctf ell s.Y.left)
    (z : (support ell c s.compactification A.support_closed).obj M ⟶ K),
    B.adjunction.homEquiv ((extend ell a s.X.left q.hX).obj M)
        ((extend ell a s.Y.left q.hY).obj K)
        (q.b.inv.app M ≫ (extend ell a s.Y.left q.hY).map z) =
      (extend ell a s.X.left q.hX).map (A.adjunction.homEquiv M K z) ≫ q.j.hom.app K

set_option maxHeartbeats 1600000 in
-- Native scalar functor endpoints contain large derived-category expressions.
/-- Ordinary derived tensor associativity, with its actual coefficient-composite equality.
Source: coefficient cocycles (blueprint: prop-pur-condensed-qbar-adjunction). -/
@[irreducible]
def tower (ell : ℕ) [Fact ell.Prime]
    {c₁ c₂ c₃ : Coefficient ell}
    (a₁₂ : c₁.bundled.{u} ell ⟶ c₂.bundled ell)
    (a₂₃ : c₂.bundled.{u} ell ⟶ c₃.bundled ell)
    (a₁₃ : c₁.bundled.{u} ell ⟶ c₃.bundled ell)
    (h : a₁₂ ≫ a₂₃ = a₁₃) (T : Scheme.{u}) :
    scalarSixChange a₁₂ T ⋙ scalarSixChange a₂₃ T ≅ scalarSixChange a₁₃ T :=
  scalarSixTower a₁₂ a₂₃ T ≪≫ eqToIso (congrArg (fun a ↦ scalarSixChange a T) h)

/-- The endpoint cocycles in the ambient derived categories. Full-subcategory
inclusions preserve and reflect these equations, and the associators are exactly
ordinary derived tensor transitivity, rather than additional isomorphism data.
Source: field-transition transitivity (blueprint: prop-pur-condensed-qbar-adjunction). -/
def Cocycle (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (s : SmoothDatum D)
    {c₁ c₂ c₃ : Coefficient ell}
    (a₁₂ : c₁.bundled ell ⟶ c₂.bundled ell)
    (a₂₃ : c₂.bundled ell ⟶ c₃.bundled ell)
    (a₁₃ : c₁.bundled ell ⟶ c₃.bundled ell)
    (A : ExplicitAdjunction ell D c₁ s) (B : ExplicitAdjunction ell D c₂ s)
    (C : ExplicitAdjunction ell D c₃ s)
    (q₁₂ : Comparisons ell D s a₁₂ A B)
    (q₂₃ : Comparisons ell D s a₂₃ B C)
    (q₁₃ : Comparisons ell D s a₁₃ A C) : Prop :=
  ∃ map_comp : a₁₂ ≫ a₂₃ = a₁₃,
    (∀ M : c₁.ctf ell s.X.left,
      (scalarSixChange a₂₃ s.Y.left).map (q₁₂.b.hom.app M).hom ≫
          (q₂₃.b.hom.app ((extend ell a₁₂ s.X.left q₁₂.hX).obj M)).hom ≫
          (CondensedRing.rightDerivedLowerShriekOfCompactification
            (c₃.obj ell) s.compactification).map
            ((tower ell a₁₂ a₂₃ a₁₃ map_comp s.X.left).hom.app M.obj) =
        (tower ell a₁₂ a₂₃ a₁₃ map_comp s.Y.left).hom.app
            ((support ell c₁ s.compactification A.support_closed).obj M).obj ≫
          (q₁₃.b.hom.app M).hom) ∧
    (∀ K : c₁.ctf ell s.Y.left,
      (scalarSixChange a₂₃ s.X.left).map (q₁₂.j.hom.app K).hom ≫
          (q₂₃.j.hom.app ((extend ell a₁₂ s.Y.left q₁₂.hY).obj K)).hom ≫
          (c₃.smoothSource ell s.map s.dim).map
            ((tower ell a₁₂ a₂₃ a₁₃ map_comp s.Y.left).hom.app K.obj) =
        (tower ell a₁₂ a₂₃ a₁₃ map_comp s.X.left).hom.app
            ((source ell c₁ s.map s.dim A.source_closed).obj K).obj ≫
          (q₁₃.j.hom.app K).hom)

/-- The model-independent representative formula for the Hom-colimit bijection.
It quantifies over every finite field and every chosen model identification.
Source: displayed Hom composite (blueprint: prop-pur-condensed-qbar-adjunction). -/
def ModelFormula (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (s : SmoothDatum D)
    (A : ∀ E : PadicAlgCl.FiniteIntermediateField ell,
      ExplicitAdjunction ell D (.rational E) s)
    (B : ExplicitAdjunction ell D (.closure) s)
    (q : ∀ E : PadicAlgCl.FiniteIntermediateField ell,
      Comparisons ell D s (closureMap ell E) (A E) B) : Prop :=
  ∀ (E : PadicAlgCl.FiniteIntermediateField ell)
    (M₀ : (Coefficient.rational E).ctf ell s.X.left)
    (K₀ : (Coefficient.rational E).ctf ell s.Y.left)
    (M : Coefficient.closure.ctf ell s.X.left)
    (K : Coefficient.closure.ctf ell s.Y.left)
    (i : (extend ell (closureMap ell E) s.X.left (q E).hX).obj M₀ ≅ M)
    (j : (extend ell (closureMap ell E) s.Y.left (q E).hY).obj K₀ ≅ K)
    (z : (support ell (.rational E) s.compactification (A E).support_closed).obj M₀ ⟶ K₀),
    B.adjunction.homEquiv M K
      ((support ell (.closure) s.compactification B.support_closed).map i.inv ≫
        (q E).b.inv.app M₀ ≫
        (extend ell (closureMap ell E) s.Y.left (q E).hY).map z ≫ j.hom) =
      i.inv ≫ (extend ell (closureMap ell E) s.X.left (q E).hX).map
        ((A E).adjunction.homEquiv M₀ K₀ z) ≫
        (q E).j.hom.app K₀ ≫ (source ell (.closure) s.map s.dim B.source_closed).map j.hom

set_option maxHeartbeats 1600000 in
-- Native scalar functor endpoints contain large derived-category expressions.
/-- The finite-field Hom construction gives the native qbar purity adjunction.
Source: qbar adjunction (blueprint: prop-pur-condensed-qbar-adjunction).

Proof. 1. Use scalar-six-ctf for scalar restrictions. Combine compact-support and
pullback scalar comparisons with native Tate-line tensor and shift comparisons;
ordinary-line-derived-scalar-comparison includes dimension zero. These are the
normalized endpoints b and j.
2. Apply native-rational-field-adjunction-transport to the rational adjunctions
retained by the supplied G and Rationalization G. IntegralNormalization G fixes
its integral scalar transport, including the trace-counit family. Its unit and
counit equations give the
Hom transition equation, and its endpoint cocycles give transitivity.
3. Finite coefficient descent supplies a common finite model for M and K and the
outer Hom-colimit identifications. Send each finite representative z to its rational
adjunction transpose, and inversely use its inverse transpose. The transition
equation shows that these maps descend and are mutually inverse.
4. Descend two model identifications, their inverses, and inverse equations to one
finite field. Rational naturality identifies the two constructions, including
changing a fixed model identification by an automorphism. Descend arbitrary arrows
to obtain naturality in both arguments.
5. Construct the adjunction from this natural Hom bijection. Evaluating at identity
arrows gives the stated scalar unit/counit equations. The same endpoint cocycles
prove transitivity under further finite extension and extension to qbar.
6. Restrict the Brown adjunction supplied by existence. Unique-right-adjoint gives
the unique gamma with F(gamma) followed by its counit equal to this same counit. -/
theorem condensed_qbar_purity_adjunction (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (_hEll : ell ≠ D.p)
    (s : SmoothDatum D) (G : NativeRationalFieldTransport.Functors ell D s)
    (_rationalization : NativeRationalFieldTransport.Rationalization G)
    (_integral : NativeRationalFieldTransport.IntegralNormalization G) :
    ∃ (B : ExplicitAdjunction ell D (.closure) s)
      (q : ∀ E : PadicAlgCl.FiniteIntermediateField ell,
        Comparisons ell D s (closureMap ell E) (G.finiteAdjunction E) B)
      (r : ∀ (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F),
        Comparisons ell D s (fieldMap ell h) (G.finiteAdjunction E) (G.finiteAdjunction F)),
      (∀ (M : Coefficient.closure.ctf ell s.X.left)
        (K : Coefficient.closure.ctf ell s.Y.left),
        ∃ (E : PadicAlgCl.FiniteIntermediateField ell)
          (M₀ : (Coefficient.rational E).ctf ell s.X.left)
          (K₀ : (Coefficient.rational E).ctf ell s.Y.left),
          Nonempty ((extend ell (closureMap ell E) s.X.left (q E).hX).obj M₀ ≅ M) ∧
          Nonempty ((extend ell (closureMap ell E) s.Y.left (q E).hY).obj K₀ ≅ K)) ∧
      ModelFormula ell D s G.finiteAdjunction B q ∧
      (∀ E : PadicAlgCl.FiniteIntermediateField ell,
        TransitionLaws ell D s (closureMap ell E) (G.finiteAdjunction E) B (q E)) ∧
      (∀ (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F),
        TransitionLaws ell D s (fieldMap ell h)
          (G.finiteAdjunction E) (G.finiteAdjunction F) (r E F h)) ∧
      (∀ (E F L : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F) (h' : F ≤ L),
        Cocycle ell D s (fieldMap ell h) (fieldMap ell h')
          (fieldMap ell (h.trans h'))
          (G.finiteAdjunction E) (G.finiteAdjunction F) (G.finiteAdjunction L)
          (r E F h) (r F L h') (r E L (h.trans h'))) ∧
      (∀ (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F),
        Cocycle ell D s (fieldMap ell h) (closureMap ell F)
          (closureMap ell E) (G.finiteAdjunction E) (G.finiteAdjunction F) B
          (r E F h) (q F) (q E)) ∧
      (∀ (H : Coefficient.closure.ctf ell s.Y.left ⥤
          Coefficient.closure.ctf ell s.X.left)
        (brown : support ell (.closure) s.compactification B.support_closed ⊣ H),
        ∃! gamma : source ell (.closure) s.map s.dim B.source_closed ≅ H,
          ∀ K : Coefficient.closure.ctf ell s.Y.left,
            (support ell (.closure) s.compactification B.support_closed).map
              (gamma.hom.app K) ≫ brown.counit.app K = B.adjunction.counit.app K) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedQbarPurityAdjunction
