/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.ExceptionalAdjointAdmissibility
public import Sheaf.Paper.VerdierExchange
public import Sheaf.Paper.DirectImagesConstructible
import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
import Sheaf.Paper.BasicOperationsCoefficientReduction
import Sheaf.Paper.CanonicalOriginCompactSupportComposition

/-! # Verdier exchange under exceptional-adjoint admissibility

Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
fix-cor-verdier-exchange.md (blueprint: fix-cor-verdier-exchange).

The existing all-coefficient exchange construction is reused. Its assertion is
restricted to the coefficient stages at which the three morphisms are admissible.
In particular no ambient admissibility of an arbitrary smooth proper scheme is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures
namespace AdmissibleVerdierExchange
open ConstructibleExceptionalCoefficients
open VerdierExchange

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

set_option linter.defProp false in
/-- The base-field unit mapped into the local ring by the structure map.
The explicit ring-homomorphism formula supplies the proof required by the
admissibility predicates; it is not a postponed theorem.
Source: standing coefficient setting (blueprint: fix-cor-verdier-exchange). -/
def baseUnit (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (x : Spec (.of D.k)) : IsUnit (l : (Spec (.of D.k)).presheaf.stalk x) :=
  (map_natCast
    (((Spec (.of D.k)).presheaf.germ ⊤ x trivial).hom.comp
      (Scheme.ΓSpecIso (.of D.k)).inv.hom) l) ▸
    (finiteFieldDatumPrimeUnit D l hl).map
      (((Spec (.of D.k)).presheaf.germ ⊤ x trivial).hom.comp
        (Scheme.ΓSpecIso (.of D.k)).inv.hom)

/-- Admissibility at exactly the selected coefficient stage, using the dependency's
finite, integral, rational and algebraically closed predicates without changing FullCD.
Source: hypothesis of fix-cor-verdier-exchange and definition of exceptional-adjoint
admissibility (blueprint: fix-cor-verdier-exchange). -/
def atStage (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (s : Stage.{u} l) : Prop :=
  match s with
  | .finite E n => IsExceptionalAdjointAdmissibleAtFiniteStage l E.carrier n n.pos
      (Spec (.of D.k)) X Y (baseUnit l D hl) f c
  | .integral E => IsExceptionalAdjointAdmissibleAtIntegral l E.carrier
      (Spec (.of D.k)) X Y (baseUnit l D hl) f c
  | .rational E => IsExceptionalAdjointAdmissibleAtRational l E.carrier
      (Spec (.of D.k)) X Y (baseUnit l D hl) f c
  | .closed => IsExceptionalAdjointAdmissibleAtAlgebraicallyClosed l Ω
      (Spec (.of D.k)) X Y (baseUnit l D hl) f c

section Geometry
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} (f : X ⟶ Y)
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The three hypotheses are imposed at the selected stage, never simultaneously at
all stages. The base-over-base instance is fixed to its identity structure morphism.
Source: hypotheses f, a_Y and a_X (blueprint: fix-cor-verdier-exchange). -/
def admissible (cf : Compactification f) (cY : Compactification (Y ↘ Spec (.of D.k)))
    (cX : Compactification (f ≫ (Y ↘ Spec (.of D.k)))) (s : Stage.{u} l) : Prop :=
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  atStage l Ω D hl f cf s ∧
    atStage l Ω D hl (Y ↘ Spec (.of D.k)) cY s ∧
    atStage l Ω D hl (f ≫ (Y ↘ Spec (.of D.k))) cX s

end Geometry

section Geometry
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (Sf : System l Ω D hl (f := f)) (Sg : System l Ω D hl (f := g))
  (Sfg : System l Ω D hl (f := f ≫ g))
  (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))

/-- The existing normalized exchange construction, with its isomorphism and shift
conclusions asserted only at stages satisfying P. All operation, Hom, projection,
composition and coefficient interfaces are the published ones. Coefficient squares
are required on the two admissible endpoints, including identity scalar extensions.
Source: statement and proof steps 1--5 (blueprint: fix-cor-verdier-exchange). -/
structure Package (P : Stage.{u} l → Prop) where
  unit (s : Stage.{u} l) : C l Ω Z s
  stage (s : Stage.{u} l) : StageData l Ω s
    (Sf.ring.operation cf s) (Sg.ring.operation cg s) (Sfg.ring.operation cfg s) (unit s)
  ring (s : RingStage.{u} l) : RingRealization l Ω f s (stage (s.stage l))
  projection (s : RingStage.{u} l) :
    RingProjection l Ω cf s (ring s) (Sf.ring.left cf s)
  conclusion (s : Stage.{u} l) (_hs : P s) : StageConclusion l Ω (stage s)
  ringShifts (s : RingStage.{u} l) (hs : P (s.stage l)) :
    RingShiftRealization l Ω (ring s) (conclusion (s.stage l) hs)
  exchangeNaturality {s t : Stage.{u} l}
      {TX : C l Ω X s ⥤ C l Ω X t} {TY : C l Ω Y s ⥤ C l Ω Y t}
      {TZ : C l Ω Z s ⥤ C l Ω Z t}
      (b : StageScalar l Ω (stage s) (stage t) TX TY TZ)
      (_hc : TX.map (stage s).dualizing.hom ≫ (b.kappaX l Ω).hom =
        (b.exceptional.b l Ω).hom.app ((Sg.ring.operation cg s).G.obj (unit s)) ≫
          (Sf.ring.operation cf t).G.map (b.kappaY l Ω).hom ≫ (stage t).dualizing.hom)
      (M : C l Ω X s) :
    TY.map ((stage s).epsilon l Ω M) ≫
        b.star l Ω (((stage s).dualX l Ω).obj (op M)) ≫
        (stage t).star.map (b.dualX l Ω M) =
      b.dualY l Ω ((Sf.ring.operation cf s).F.obj M) ≫
        ((stage t).dualY l Ω).map ((b.exceptional.q l Ω).inv.app M).op ≫
        (stage t).epsilon l Ω (TX.obj M)
  integralAlpha (E : FieldStage.{u} l) :
    (Sf.ring.operation cf (.integral E)).F ⋙ (Sg.ring.operation cg (.integral E)).F ≅
      (Sfg.ring.operation cfg (.integral E)).F
  integralAlpha_normalized (E : FieldStage.{u} l) :
    Functor.isoWhiskerRight (integralAlpha E)
        (PurCompactSupport.finiteTorIntegralInclusion l E.carrier Z) =
      integralAlphaRealization l Ω D hl f g Sf Sg Sfg cf cg cfg E
  integralDualizing (E : FieldStage.{u} l) :
    (stage (.integral E)).dualizing =
      (composition (Sf.ring.operation cf (.integral E)).adjunction
        (Sg.ring.operation cg (.integral E)).adjunction
        (Sfg.ring.operation cfg (.integral E)).adjunction (integralAlpha E)).app
          (unit (.integral E))
  ringScalar {s t : RingStage.{u} l}
      (a : PurCompactSupport.Change (s.coefficients l) (t.coefficients l)) (ha : Allowed l a)
      (hs : P (s.stage l)) (ht : P (t.stage l)) :
    ∃ (SX : Scalar l Ω a X) (SY : Scalar l Ω a Y) (SZ : Scalar l Ω a Z),
      ∃ b : StageScalar l Ω (stage (s.stage l)) (stage (t.stage l))
          SX.functor SY.functor SZ.functor,
        ScalarConclusion l Ω b ∧
        Nonempty (ScalarShifts l Ω (conclusion (s.stage l) hs)
          (conclusion (t.stage l) ht) b) ∧
        (∀ K : C l Ω X (s.stage l),
          (t.inclusion l Ω Y).map ((b.exceptional.q l Ω).hom.app K) ≫
              (Sf.ring.left cf t).hom.app (SX.functor.obj K) ≫
              (PurCompactSupport.image (t.coefficients l) cf).map
                (SX.realization.hom.app K) =
            SY.realization.hom.app ((Sf.ring.operation cf (s.stage l)).F.obj K) ≫
              (pbcDerivedExtend (a.map Y)).map ((Sf.ring.left cf s).hom.app K) ≫
              (PurCompactSupport.comparison a cf).app ((s.inclusion l Ω X).obj K)) ∧
        (∀ K : C l Ω Y (s.stage l),
          (t.inclusion l Ω Z).map ((b.structureY.q l Ω).hom.app K) ≫
              (Sg.ring.left cg t).hom.app (SY.functor.obj K) ≫
              (PurCompactSupport.image (t.coefficients l) cg).map
                (SY.realization.hom.app K) =
            SZ.realization.hom.app ((Sg.ring.operation cg (s.stage l)).F.obj K) ≫
              (pbcDerivedExtend (a.map Z)).map ((Sg.ring.left cg s).hom.app K) ≫
              (PurCompactSupport.comparison a cg).app ((s.inclusion l Ω Y).obj K)) ∧
        (∀ K : C l Ω X (s.stage l),
          (t.inclusion l Ω Z).map ((b.structureX.q l Ω).hom.app K) ≫
              (Sfg.ring.left cfg t).hom.app (SX.functor.obj K) ≫
              (PurCompactSupport.image (t.coefficients l) cfg).map
                (SX.realization.hom.app K) =
            SZ.realization.hom.app ((Sfg.ring.operation cfg (s.stage l)).F.obj K) ≫
              (pbcDerivedExtend (a.map Z)).map ((Sfg.ring.left cfg s).hom.app K) ≫
              (PurCompactSupport.comparison a cfg).app ((s.inclusion l Ω X).obj K)) ∧
        (t.inclusion l Ω Z).map b.unit.hom ≫ (ring t).unitIso.hom =
          SZ.realization.hom.app (unit (s.stage l)) ≫
            (pbcDerivedExtend (a.map Z)).map (ring s).unitIso.hom ≫ ringUnitScalar l a Z
  rationalization (E : FieldStage.{u} l)
      (hs : P (.integral E)) (ht : P (.rational E)) :
    ∃ b : StageScalar l Ω (stage (.integral E)) (stage (.rational E))
        (ConstructibleExceptionalCoefficients.rationalization l Ω E X)
        (ConstructibleExceptionalCoefficients.rationalization l Ω E Y)
        (ConstructibleExceptionalCoefficients.rationalization l Ω E Z),
      ScalarConclusion l Ω b ∧
      Nonempty (ScalarShifts l Ω (conclusion (.integral E) hs)
        (conclusion (.rational E) ht) b) ∧
      b.exceptional = Sf.fields.rationalizationComparison cf E ∧
      b.structureY = Sg.fields.rationalizationComparison cg E ∧
      b.structureX = Sfg.fields.rationalizationComparison cfg E
  rationalScalar (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (hs : P (.rational E)) (ht : P (.rational L)) :
    ∃ b : StageScalar l Ω (stage (.rational E)) (stage (.rational L))
        (ConstructibleExceptionalCoefficients.rationalScalar l Ω E L i X)
        (ConstructibleExceptionalCoefficients.rationalScalar l Ω E L i Y)
        (ConstructibleExceptionalCoefficients.rationalScalar l Ω E L i Z),
      ScalarConclusion l Ω b ∧
      Nonempty (ScalarShifts l Ω (conclusion (.rational E) hs)
        (conclusion (.rational L) ht) b) ∧
      b.exceptional = Sf.fields.rationalComparison cf E L i ∧
      b.structureY = Sg.fields.rationalComparison cg E L i ∧
      b.structureX = Sfg.fields.rationalComparison cfg E L i
  common (i : AlgebraicallyClosedCoefficients.Index l Ω)
      (hs : P (.rational (commonField l Ω i))) (ht : P .closed) :
    ∃ b : StageScalar l Ω (stage (.rational (commonField l Ω i))) (stage .closed)
        (commonInclusion l Ω X i) (commonInclusion l Ω Y i) (commonInclusion l Ω Z i),
      ScalarConclusion l Ω b ∧
      Nonempty (ScalarShifts l Ω (conclusion (.rational (commonField l Ω i)) hs)
        (conclusion .closed ht) b) ∧
      b.exceptional = Sf.common.commonComparison cf i ∧
      b.structureY = Sg.common.commonComparison cg i ∧
      b.structureX = Sfg.common.commonComparison cfg i

end Geometry

/-- The original node's stagewise assertion. The operation systems are universally
quantified choices of the normalized canonical operations, not new hypotheses.
Source: complete statement of fix-cor-verdier-exchange
(blueprint: fix-cor-verdier-exchange). -/
def Assertion (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] : Prop :=
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  ∀ (Sf : System l Ω D hl (f := f))
    (SY : System l Ω D hl (f := Y ↘ Spec (.of D.k)))
    (SX : System l Ω D hl (f := f ≫ (Y ↘ Spec (.of D.k))))
    (cf : Compactification f) (cY : Compactification (Y ↘ Spec (.of D.k)))
    (cX : Compactification (f ≫ (Y ↘ Spec (.of D.k)))),
    Nonempty (Package l Ω D hl f (Y ↘ Spec (.of D.k)) Sf SY SX cf cY cX
      (admissible l Ω D hl f cf cY cX))

/-- Verdier-duality exchange on the finite-Tor constructible domain, at each of the
four coefficient kinds subject to precisely its three admissibility hypotheses.
The dualizing objects are the exceptional images of the coefficient unit; their
Hom duals, canonical exchange, naturality, signed shifts and coefficient squares
are the published VerdierExchange constructions, restricted by admissible.

Source: main-20261015, sec-six-functors/sk-thm-sf-package,
fix-cor-verdier-exchange.md (blueprint: fix-cor-verdier-exchange).

Proof plan:
1. Use the support composition law of def-fix-six-functor-datum and the adjunctions
   fix-prop-adjunctions for f, a_Y and a_X. Conjugate the inverse support compositor
   under their pasted adjunctions, as in VerdierExchange.composition; evaluation
   at the coefficient unit gives c: Rf^! omega_Y ≅ omega_X.
2. The unit has Tor interval [0,0]. Exceptional finite-Tor preservation from
   def-weil-exceptional-inverse-image and fix-prop-adjunctions puts omega_Y and
   Rf_! M in the tensor-Hom domain. Invert fix-lem-tensor-adjunction at omega_Y,
   then apply Rf_* RHom(M,c). Transposition of projection and evaluation identifies
   that composite with the actual StageData.epsilon, without choosing an iso.
3. Naturality of tensor-Hom exchange and bifunctoriality of RHom give the
   contravariant naturality square. It is encoded by StageConclusion.epsilon.
4. For finite reduction or scalar extension, transpose both sides of the c square
   through the pasted adjunctions. Both transposes use the f counit followed by the
   a_Y counit and the compact-support comparison. The unit/counit preservation of
   lem-fix-operation-reduction and exceptional-adjoint-admissibility identifies
   them. Injectivity of the adjunction Hom bijections gives the c square.
   Transpose extended evaluation for the Hom comparison and use the direct-image
   mate for Rf_*. Pasting these squares gives ScalarConclusion.exchange.
   At integral coefficients use the normalized completed support compositor and
   its finite projections; pass to rational and common finite stages on maps.
5. Derived adjunctions commute with shifts. The actual signed Hom-complex shift
   sends M[r] to D(M)[-r]. HomShift's signed comparison and functoriality of RHom
   in c identify the two shifted exchange arrows. RingShiftRealization and
   ScalarShifts retain this normalization under reduction and scalar extension.
-/
theorem verdier_exchange
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (_S : SixFunctorOperationDatum D C E n hn)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Assertion C.l C.Qbar D C.different f := by
  sorry

end AdmissibleVerdierExchange
end WeilConjectures
