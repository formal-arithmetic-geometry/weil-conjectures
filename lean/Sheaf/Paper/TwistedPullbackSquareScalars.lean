/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module
public import Sheaf.Paper.TwistedPullbackSquareCoordinates
public import Sheaf.Paper.TwistedPullbackSquareShiftEquations
public import Sheaf.Paper.TwistedPullbackAdicAgreement
public import Sheaf.Paper.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.FiniteSmoothPullbackExchange
public import Sheaf.Paper.AdicPurityScalarNaturality

import Sheaf.Paper.TwistedPullbackScalarPrimitives
import Sheaf.Paper.TwistedPullbackCoefficientCoherence
import Sheaf.Paper.TwistedPullbackAdicIdentification
import Sheaf.Paper.AdicOperationDomainsSourceComparison
import Sheaf.Paper.FrameworkPbcPullbackScalarBridge
import Sheaf.Paper.SfIntegralConstructibleTriangulated

/-! # Scalar squares for the twisted pullback of a Cartesian square

Source: current blueprint sec-smooth-purity/sk-thm-purity-transport,
base-change and coefficient compatibility
(blueprint: lem-pur-twisted-pullback-square-scalars).

The formulas use framework coordinates for the raw PBC categories. The conclusion
also supplies their normalized PBC presentation, pullback, scalar and twist maps.
No exceptional inverse-image or exceptional exchange map enters the square.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.TwistedPullbackScalars
section Pasting
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L)
  {X X' Y Y' : Scheme.{u}}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ x : X', Invertible (l : X'.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ y : Y', Invertible (l : Y'.residueField y)]
  (u : X' ⟶ X) (f : X ⟶ Y) (f' : X' ⟶ Y') (v : Y' ⟶ Y)
  (sq : u ≫ f = f' ≫ v) (d : ℕ)

attribute [local irreducible] rationalDerivedPullback
attribute [local implicit_reducible] D H U V

private theorem scalarSquarePasting :
    SquareEquations l E L i u f f' v sq d ∧ Naturality l E L i u f f' v sq d := by
  obtain ⟨hZ, hC, hN⟩ := twistedPullbackScalarPrimitives l E L i u f f' v sq d
  have hq := hN.2.1
  have hz := hN.2.2.2.2.2.2.2.2.2.1
  dsimp only [Natural, Functor.comp_map] at hq hz
  have hA (K : sfRationalConstructibleCategory l E Y) :
      (rA l E L i u f d K).hom ≫
          (z l L u d ((rationalDerivedPullback l L f).obj ((T l E L i Y).obj K))).hom =
        (T l E L i X').map
            (z l E u d ((rationalDerivedPullback l E f).obj K)).hom ≫
          (q l E L i X' d ((U l E u f).obj K)).hom ≫
          (D l L X' d).map (PU l E L i u f K).hom := by
    dsimp only [rA, a, H, U, Functor.comp_obj, Iso.trans_hom, Functor.mapIso_hom]
    simp only [Functor.map_comp, Category.assoc]
    have hn := congrArg
      (fun b ↦ (p l E L i u ((D l E X d).obj
          ((rationalDerivedPullback l E f).obj K))).hom ≫
        (rationalDerivedPullback l L u).map
          (q l E L i X d ((rationalDerivedPullback l E f).obj K)).hom ≫ b)
      (hz _ _ (p l E L i f K).hom)
    simp only [Functor.comp_obj] at hn
    rw [hn]
    simpa only [H, U, Functor.comp_obj, PU, Iso.trans_hom, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc] using
      congrArg (fun b ↦ b ≫ (D l L X' d).map
        ((rationalDerivedPullback l L u).map (p l E L i f K).hom))
        (hZ ((rationalDerivedPullback l E f).obj K))
  have hB (K : sfRationalConstructibleCategory l E Y) :
      (rB l E L i f' v d K).hom =
        (q l E L i X' d ((V l E f' v).obj K)).hom ≫
          (D l L X' d).map (PV l E L i f' v K).hom := by
    simp only [rB, a, PV, PU, H, V, Functor.comp_obj, Functor.comp_map, Iso.trans_hom,
      Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  refine ⟨⟨hZ, hC, hA, hB, ?_⟩, hN⟩
  intro K
  have hn := congrArg
    (fun b ↦ (T l E L i X').map
        (z l E u d ((rationalDerivedPullback l E f).obj K)).hom ≫
      b ≫ (D l L X' d).map (PV l E L i f' v K).hom)
    (hq _ _ ((t l E u f f' v sq).hom.app K))
  have hc := congrArg (fun b ↦
      (T l E L i X').map (z l E u d ((rationalDerivedPullback l E f).obj K)).hom ≫
        (q l E L i X' d ((U l E u f).obj K)).hom ≫ (D l L X' d).map b) (hC K)
  have ha := congrArg (fun b ↦ b ≫ (D l L X' d).map
    ((t l L u f f' v sq).hom.app ((T l E L i Y).obj K))) (hA K)
  dsimp only [m, Iso.trans_hom, Functor.mapIso_hom]
  rw [Functor.map_comp, hB K]
  simp only [Functor.map_comp, Functor.comp_obj, Category.assoc] at hn hc ha ⊢
  exact hn.trans (hc.trans ha.symm)

private theorem finiteTor_of_iso (W : Scheme.{u})
    {K N : DerivedCategory (integralTowerModules l E W)} (e : K ≅ N)
    (hK : finiteTorConstructibleIntegral l E W K) :
    finiteTorConstructibleIntegral l E W N := by
  refine ⟨ObjectProperty.prop_of_iso (sfIntegralConstructible l E W) e hK.1, ?_⟩
  obtain ⟨a, b, hab, h⟩ := hK.2
  refine ⟨a, b, hab, fun n ↦ ?_⟩
  let en := (scalarReductionDerivedExtension l E W n).mapIso e
  refine ⟨(h n).1, ?_⟩
  rintro Q P ⟨q⟩ f hf hP M j hj
  exact (h n).2 Q P ⟨q ≪≫ en.symm⟩ f hf hP M j hj

end Pasting

variable (B : FiniteFieldDatum.{u}) (C : B.CoefficientDatum)

/-- The residue inverse follows from ell different from p and the structure map to k.
This supplies the framework's instance without imposing a geometric hypothesis.
Source: purity conventions, coefficient prime invertible over k
(blueprint: lem-pur-twisted-pullback-square-scalars). -/
@[instance_reducible] def finiteResidueInverse (W : Scheme.{u})
    [W.Over (Spec (.of B.k))] (x : W) : Invertible (C.l : W.residueField x) :=
  let P : PurityFiniteSetting :=
    { field := B, coefficients := C, extension := ⊥, level := 1, level_pos := le_rfl }
  (Eq.mp (congrArg IsUnit (map_natCast (W.residue x).hom C.l))
    ((P.coefficientPrime_isUnit_stalk W (W ↘ Spec (.of B.k)) x).map
      (W.residue x).hom)).invertible

/-- Geometric consequences of the hypotheses, collected as conclusions so that no
extra Noetherian, dimension, finiteness or smoothness assumption is imposed.
Source: purity transport, domains and smooth base change
(blueprint: lem-pur-twisted-pullback-square-scalars). -/
structure Geometry {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y') (d : ℕ) where
  noethX : IsNoetherian X
  noethX' : IsNoetherian X'
  noethY : IsNoetherian Y
  noethY' : IsNoetherian Y'
  dimX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)
  dimX' : Fact (∃ n : ℕ, topologicalKrullDim X' ≤ n)
  dimY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)
  dimY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ n)
  invX : Fact (∀ x : X, IsUnit (C.l : X.presheaf.stalk x))
  invX' : Fact (∀ x : X', IsUnit (C.l : X'.presheaf.stalk x))
  invY : Fact (∀ y : Y, IsUnit (C.l : Y.presheaf.stalk y))
  invY' : Fact (∀ y : Y', IsUnit (C.l : Y'.presheaf.stalk y))
  finiteF : LocallyOfFiniteType f
  compactF : QuasiCompact f
  separatedF' : IsSeparated f'
  finiteF' : LocallyOfFiniteType f'
  compactF' : QuasiCompact f'
  smoothF' : SmoothOfRelativeDimension d f'

variable {X X' Y Y' : Scheme.{u}}
  [X.Over (Spec (.of B.k))] [X'.Over (Spec (.of B.k))]
  [Y.Over (Spec (.of B.k))] [Y'.Over (Spec (.of B.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of B.k))] [QuasiCompact (X ↘ Spec (.of B.k))]
  [IsSeparated (X ↘ Spec (.of B.k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of B.k))] [QuasiCompact (X' ↘ Spec (.of B.k))]
  [IsSeparated (X' ↘ Spec (.of B.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of B.k))] [QuasiCompact (Y ↘ Spec (.of B.k))]
  [IsSeparated (Y ↘ Spec (.of B.k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of B.k))] [QuasiCompact (Y' ↘ Spec (.of B.k))]
  [IsSeparated (Y' ↘ Spec (.of B.k))]
  (u : X' ⟶ X) (f : X ⟶ Y) (f' : X' ⟶ Y') (v : Y' ⟶ Y)
  [u.IsOver (Spec (.of B.k))] [f.IsOver (Spec (.of B.k))]
  [f'.IsOver (Spec (.of B.k))] [v.IsOver (Spec (.of B.k))]
  [IsSeparated f] (d : ℕ) [SmoothOfRelativeDimension d f]

/-- All five specified equations, naturality, all seven unit/tower/shift families,
the canonical raw PBC coordinate identifications, and agreement with the integral
adic a at both smooth arrows. The equal-field and d=0 cases remain included.
Source: purity transport, scalar squares and their full coherence
(blueprint: lem-pur-twisted-pullback-square-scalars). -/
def Conclusion (sq : u ≫ f = f' ≫ v) (g : Geometry B C f f' d) : Prop :=
  letI := g.noethX
  letI := g.noethX'
  letI := g.noethY
  letI := g.noethY'
  letI := g.dimX
  letI := g.dimX'
  letI := g.dimY
  letI := g.dimY'
  letI := g.invX
  letI := g.invX'
  letI := g.invY
  letI := g.invY'
  letI : ∀ x : X, Invertible (C.l : X.residueField x) := finiteResidueInverse B C X
  letI : ∀ x : X', Invertible (C.l : X'.residueField x) := finiteResidueInverse B C X'
  letI : ∀ y : Y, Invertible (C.l : Y.residueField y) := finiteResidueInverse B C Y
  letI : ∀ y : Y', Invertible (C.l : Y'.residueField y) := finiteResidueInverse B C Y'
  letI := g.finiteF
  letI := g.compactF
  letI := g.separatedF'
  letI := g.finiteF'
  letI := g.compactF'
  letI := g.smoothF'
  ∃ s : ShiftCoherence C.l C.Qbar u f f' v d,
    Nonempty (SquareCoordinates C.l C.Qbar u f f' v d s) ∧
    (∀ (E L : Fields C.l C.Qbar) (h : E ≤ L),
      SquareEquations C.l E.val L.val (IntermediateField.inclusion h) u f f' v sq d ∧
      Naturality C.l E.val L.val (IntermediateField.inclusion h) u f f' v sq d) ∧
    TowerCoherence C.l C.Qbar u f f' v d ∧
    SquareShiftEquations C.l C.Qbar u f f' v sq d s ∧
    (∃ hC : AdicPurityScalarNaturality.ScalarClosed B C X Y,
      AdicAgreement B C f d hC s.atX) ∧
    (∃ hC : AdicPurityScalarNaturality.ScalarClosed B C X' Y',
      AdicAgreement B C f' d hC s.atX')

set_option linter.unusedSectionVars false in
/-- The scalar squares of the specified twisted-pullback comparison.
Source: blueprint sec-smooth-purity/sk-thm-purity-transport, base-change coherence,
and its coefficient-change proof; Stacks 07A4 and 099N
(blueprint: lem-pur-twisted-pullback-square-scalars).

Proof: The four finite-type k-schemes are Noetherian of finite dimension and ell
is invertible on them. Smooth base change supplies the asserted properties of f'.
Use the coefficient-presentation equivalences on the common integral objects.
Their pullback comparisons are fixed by the actual quotient-unit maps of the
whole strict tower, with zero shifted coordinate. The scalar comparison is fixed
by ordinary tensor balancing and completion chi. Thus conjugation identifies the
specified PBC p with the framework p, in the displayed inverse direction. Exact
coefficient relabeling identifies the degree-zero Tate line and the PBC twist.
On roots the two line routes send (zeta tensor e) tensor l to pull(zeta) tensor el;
powers commute with pullback and transitions, and the empty tensor is the unit.
The scalar/pullback/tensor balancing equation on a common good representative,
followed by normalized realization, the line equation and localization, gives Z.
The composition equation for p gives C by cancellation of the two compositors
and the Cartesian commutativity equality. Expand a in rA, use naturality of z and
Z to obtain the first intermediate identity; functoriality gives the second for
rB. Naturality of q at t and C then paste these identities to give M. All maps
are natural on integral representatives and on localized pure tensors, hence on
all raw rational arrows. Tensor multiplication and reassociation give the unit
and tower equations for p and q, including the coefficient unit at d=0. Expanding
the composites gives those equations for PU, PV, a, rA and rB. On complexes the
line is in degree zero and the common shift is 2d, so no extra sign is introduced;
the canonical signed shift comparisons commute with balancing and every tower
projection. Descend and localize these comparisons to obtain all shift equations.
Finally remove completed tensor by the normalized tensor/termwise comparison
and conjugate by the two actual chi maps. The resulting integral composite is
exactly sourceScalarComponent in adic purity scalar naturality. Its localization
is the displayed a, at both f and f'. This proves every asserted compatibility. -/
theorem twistedPullbackSquareScalars (cartesian : IsPullback u f' f v) :
    ∃ g : Geometry B C f f' d, Conclusion B C u f f' v d cartesian.w g := by
  have hlocX : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of B.k))
  have hlocX' : IsLocallyNoetherian X' :=
    LocallyOfFiniteType.isLocallyNoetherian (X' ↘ Spec (.of B.k))
  have hlocY : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of B.k))
  have hlocY' : IsLocallyNoetherian Y' :=
    LocallyOfFiniteType.isLocallyNoetherian (Y' ↘ Spec (.of B.k))
  have hcompX : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of B.k))
  have hcompX' : CompactSpace X' :=
    QuasiCompact.compactSpace_of_compactSpace (X' ↘ Spec (.of B.k))
  have hcompY : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of B.k))
  have hcompY' : CompactSpace Y' :=
    QuasiCompact.compactSpace_of_compactSpace (Y' ↘ Spec (.of B.k))
  let : IsNoetherian X := { toIsLocallyNoetherian := hlocX, toCompactSpace := hcompX }
  let : IsNoetherian X' := { toIsLocallyNoetherian := hlocX', toCompactSpace := hcompX' }
  let : IsNoetherian Y := { toIsLocallyNoetherian := hlocY, toCompactSpace := hcompY }
  let : IsNoetherian Y' := { toIsLocallyNoetherian := hlocY', toCompactSpace := hcompY' }
  have hdimX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ n) :=
    ⟨AlgebraicGeometry.exists_topologicalKrullDim_le (X ↘ Spec (.of B.k))⟩
  have hdimX' : Fact (∃ n : ℕ, topologicalKrullDim X' ≤ n) :=
    ⟨AlgebraicGeometry.exists_topologicalKrullDim_le (X' ↘ Spec (.of B.k))⟩
  have hdimY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n) :=
    ⟨AlgebraicGeometry.exists_topologicalKrullDim_le (Y ↘ Spec (.of B.k))⟩
  have hdimY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ n) :=
    ⟨AlgebraicGeometry.exists_topologicalKrullDim_le (Y' ↘ Spec (.of B.k))⟩
  let := hdimX
  let := hdimX'
  let := hdimY
  let := hdimY'
  let P : PurityFiniteSetting :=
    { field := B, coefficients := C, extension := ⊥, level := 1, level_pos := le_rfl }
  have hinvX := P.coefficientPrime_isUnit_stalk X (X ↘ Spec (.of B.k))
  have hinvX' := P.coefficientPrime_isUnit_stalk X' (X' ↘ Spec (.of B.k))
  have hinvY := P.coefficientPrime_isUnit_stalk Y (Y ↘ Spec (.of B.k))
  have hinvY' := P.coefficientPrime_isUnit_stalk Y' (Y' ↘ Spec (.of B.k))
  have hfiniteF : LocallyOfFiniteType f := by
    have hc : LocallyOfFiniteType (f ≫ Y ↘ Spec (.of B.k)) := by
      rw [CategoryTheory.comp_over]
      infer_instance
    exact locallyOfFiniteType_of_comp f (Y ↘ Spec (.of B.k))
  have hseparatedF' : IsSeparated f' :=
    IsSeparated.isStableUnderBaseChange.of_isPullback cartesian inferInstance
  have hfiniteF' : LocallyOfFiniteType f' :=
    locallyOfFiniteType_isStableUnderBaseChange.of_isPullback cartesian hfiniteF
  let : ∀ x : X, Invertible (C.l : X.residueField x) := finiteResidueInverse B C X
  let : ∀ x : X', Invertible (C.l : X'.residueField x) := finiteResidueInverse B C X'
  let : ∀ y : Y, Invertible (C.l : Y.residueField y) := finiteResidueInverse B C Y
  let : ∀ y : Y', Invertible (C.l : Y'.residueField y) := finiteResidueInverse B C Y'
  have hgeom : Geometry B C f f' d :=
    { noethX := inferInstance
      noethX' := inferInstance
      noethY := inferInstance
      noethY' := inferInstance
      dimX := hdimX
      dimX' := hdimX'
      dimY := hdimY
      dimY' := hdimY'
      invX := ⟨hinvX⟩
      invX' := ⟨hinvX'⟩
      invY := ⟨hinvY⟩
      invY' := ⟨hinvY'⟩
      finiteF := hfiniteF
      compactF := inferInstance
      separatedF' := hseparatedF'
      finiteF' := hfiniteF'
      compactF' := inferInstance
      smoothF' := (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback
        cartesian inferInstance
    }
  refine ⟨hgeom, ?_⟩
  let := hgeom.finiteF
  let := hgeom.compactF
  let := hgeom.separatedF'
  let := hgeom.finiteF'
  let := hgeom.compactF'
  let := hgeom.smoothF'
  let : Fact (∀ x : X, IsUnit (C.l : X.presheaf.stalk x)) := hgeom.invX
  let : Fact (∀ x : X', IsUnit (C.l : X'.presheaf.stalk x)) := hgeom.invX'
  let : Fact (∀ y : Y, IsUnit (C.l : Y.presheaf.stalk y)) := hgeom.invY
  let : Fact (∀ y : Y', IsUnit (C.l : Y'.presheaf.stalk y)) := hgeom.invY'
  obtain ⟨s, hcoords, htower, hshift⟩ :=
    twistedPullbackCoefficientCoherence C.l C.Qbar u f f' v cartesian.w d
  obtain ⟨bridge, _⟩ := FrameworkPbc.frameworkPbcPullbackScalarBridge C.l
  have hclosed : AdicPurityScalarNaturality.ScalarClosed B C X Y := by
    intro R S h side K
    cases side
    · exact finiteTor_of_iso C.l S.val Y
        ((bridge.scalar R.val S.val (IntermediateField.inclusion h) Y).ordinary.app K.obj)
        ((AdicOperationSource.scalar_preserves P R.val S.val
          (IntermediateField.inclusion h) Y).2.1 K)
    · exact finiteTor_of_iso C.l S.val X
        ((bridge.scalar R.val S.val (IntermediateField.inclusion h) X).ordinary.app K.obj)
        ((AdicOperationSource.scalar_preserves P R.val S.val
          (IntermediateField.inclusion h) X).2.1 K)
  have hclosed' : AdicPurityScalarNaturality.ScalarClosed B C X' Y' := by
    intro R S h side K
    cases side
    · exact finiteTor_of_iso C.l S.val Y'
        ((bridge.scalar R.val S.val (IntermediateField.inclusion h) Y').ordinary.app K.obj)
        ((AdicOperationSource.scalar_preserves P R.val S.val
          (IntermediateField.inclusion h) Y').2.1 K)
    · exact finiteTor_of_iso C.l S.val X'
        ((bridge.scalar R.val S.val (IntermediateField.inclusion h) X').ordinary.app K.obj)
        ((AdicOperationSource.scalar_preserves P R.val S.val
          (IntermediateField.inclusion h) X').2.1 K)
  exact ⟨s, hcoords, fun R S h ↦ scalarSquarePasting C.l R.val S.val
      (IntermediateField.inclusion h) u f f' v cartesian.w d, htower, hshift,
    ⟨hclosed, twistedPullbackAdicIdentification B C f d hclosed s.atX⟩,
    ⟨hclosed', twistedPullbackAdicIdentification B C f' d hclosed' s.atX'⟩⟩

end WeilConjectures.TwistedPullbackScalars
