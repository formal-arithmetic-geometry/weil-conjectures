/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientFamilyPullback
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalPullbackSquares
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarPullbackComparison
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Quotient.DiagonalQuotientLinePullbackNormalization
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarUnitPullbackNormalization
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarExchangeCube
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalPullNormalizationExistence
import all WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization

/-! # Scalar pasting of the three trace squares

Source: diagonal tower coefficient changes, paragraph (3), scalar base change.
(blueprint: lem-diagonal-quotient-trace-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] quotientLine quotientLineMap derivedUpper derivedLower
  derivedScalars modelExchange singlePullback PullEndpoint.shift Endpoint.shift

set_option allowUnsafeReducibility true in
attribute [local reducible] derivedLower derivedUpper derivedScalars
  QuotientChange.L QuotientChange.D
  CondensedRing.moduleObjectDerivedPullback

private instance sectionGrothendieck
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (ModuleRingedComparison.modules R X) :=
  IsGrothendieckAbelian.of_equivalence (ModuleRingedComparison.equivalence R X)

private theorem scalar_pullback_isIso
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S) :
    IsIso (scalarPullbackComparison a f) := by
  let : ∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules R Z) := fun Z ↦
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let : ∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules T Z) := fun Z ↦
    HasDerivedCategory.ofIsGrothendieckAbelian _
  obtain ⟨b, hb⟩ := QuotientChange.internal_pull_normalization_exists a f
  have h := QuotientChange.normalized_inverse a f b hb
  have he : scalarPullbackComparison a f = b.inv := by
    simpa only [scalarPullbackComparison, Adjunction.pushHomOfComapIso,
      scalarRestrictionPullbackIso, QuotientChange.normalizationRestrictionPull,
      QuotientChange.scalarAdj, QuotientChange.V, QuotientChange.V₀, QuotientChange.L,
      QuotientChange.D, QuotientChange.extension, id_eq,
      CondensedRing.moduleObjectDerivedPullback, derivedUpper, derivedScalars] using h.symm
  rw [he]
  infer_instance

private theorem trace_scalar_paste
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (U : A ⥤ B) (V : C ⥤ D) (T : A ⥤ C) (S : B ⥤ D)
    (χ : U ⋙ S ⟶ T ⋙ V)
    {A₀ A₁ : A} {B₀ B₁ : B} {C₀ C₁ : C} {D₀ D₁ : D}
    (t₀ : A₀ ⟶ A₁) (t₀' : B₀ ⟶ B₁) (t : C₀ ⟶ C₁) (t' : D₀ ⟶ D₁)
    (i : U.obj A₀ ≅ B₀) (p : U.obj A₁ ≅ B₁)
    (e : T.obj A₀ ≅ C₀) (c : T.obj A₁ ≅ C₁)
    (e' : S.obj B₀ ≅ D₀) (c' : S.obj B₁ ≅ D₁)
    (j : V.obj C₀ ⟶ D₀) (q : V.obj C₁ ≅ D₁)
    [IsIso (χ.app A₀)]
    (hi : U.map t₀ ≫ p.hom = i.hom ≫ t₀')
    (he : T.map t₀ ≫ c.hom = e.hom ≫ t)
    (he' : S.map t₀' ≫ c'.hom = e'.hom ≫ t')
    (hpush : χ.app A₀ ≫ V.map e.hom ≫ j = S.map i.hom ≫ e'.hom)
    (hunit : χ.app A₁ ≫ V.map c.hom ≫ q.hom = S.map p.hom ≫ c'.hom) :
    IsIso j ∧ V.map t ≫ q.hom = j ≫ t' := by
  have hj : IsIso (χ.app A₀ ≫ V.map e.hom ≫ j) := by
    rw [hpush]
    infer_instance
  have hj' : IsIso (V.map e.hom ≫ j) :=
    IsIso.of_isIso_comp_left (χ.app A₀) _
  have : IsIso j := IsIso.of_isIso_comp_left (V.map e.hom) j
  refine ⟨inferInstance, ?_⟩
  apply (cancel_epi (χ.app A₀ ≫ V.map e.hom)).mp
  calc
    (χ.app A₀ ≫ V.map e.hom) ≫ (V.map t ≫ q.hom) =
        χ.app A₀ ≫ V.map (T.map t₀) ≫ V.map c.hom ≫ q.hom := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun z ↦ χ.app A₀ ≫ V.map z ≫ q.hom) he.symm
    _ = S.map (U.map t₀) ≫ χ.app A₁ ≫ V.map c.hom ≫ q.hom := by
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (· ≫ V.map c.hom ≫ q.hom) (χ.naturality t₀).symm
    _ = S.map (U.map t₀) ≫ S.map p.hom ≫ c'.hom := by rw [hunit]
    _ = S.map i.hom ≫ S.map t₀' ≫ c'.hom := by
      rw [← S.map_comp_assoc, hi, S.map_comp, Category.assoc]
    _ = S.map i.hom ≫ e'.hom ≫ t' := by rw [he']
    _ = (χ.app A₀ ≫ V.map e.hom) ≫ (j ≫ t') := by
      simpa only [Category.assoc] using congrArg (· ≫ t') hpush.symm

private theorem modelExchange_naturality
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f)
    (D : DiagonalRightDerived (CondensedRing.lowerStar R f))
    (D' : DiagonalRightDerived (CondensedRing.lowerStar R f'))
    (e : D.R = derivedLower R f) (e' : D'.R = derivedLower R f')
    {K J : DerivedCategory (Modules R X)} (v : K ⟶ J) :
    (derivedUpper R hS).map (D.R.map v) ≫ modelExchange R f f' hX hS h D D' e e' J =
      modelExchange R f f' hX hS h D D' e e' K ≫
        D'.R.map ((derivedUpper R hX).map v) := by
  let α : D.R ⋙ derivedUpper R hS ⟶ derivedUpper R hX ⋙ D'.R :=
    Functor.whiskerRight (eqToIso e).hom (derivedUpper R hS) ≫
      derivedExchange R f f' hX hS h ≫
      Functor.whiskerLeft (derivedUpper R hX) (eqToIso e').inv
  simpa only [α, modelExchange, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_map, Category.assoc] using α.naturality v

private theorem scalar_trace_transfer
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (h : f' ≫ hS = hX ≫ f)
    (D₀ : DiagonalRightDerived (CondensedRing.lowerStar R f))
    (D₀' : DiagonalRightDerived (CondensedRing.lowerStar R f'))
    (D : DiagonalRightDerived (CondensedRing.lowerStar T f))
    (D' : DiagonalRightDerived (CondensedRing.lowerStar T f'))
    (e₀ : D₀.R = derivedLower R f) (e₀' : D₀'.R = derivedLower R f')
    (e : D.R = derivedLower T f) (e' : D'.R = derivedLower T f')
    (he₀ : IsCanonicalRightDerived (CondensedRing.lowerStar R f) D₀ e₀)
    (he₀' : IsCanonicalRightDerived (CondensedRing.lowerStar R f') D₀' e₀')
    (he : IsCanonicalRightDerived (CondensedRing.lowerStar T f) D e)
    (he' : IsCanonicalRightDerived (CondensedRing.lowerStar T f') D' e')
    {L₀ : Modules R X} {L₀' : Modules R X'} {L : Modules T X} {L' : Modules T X'}
    {m₀ : (upperStar Ab.{u + 1} hX).obj L₀.X ⟶ L₀'.X}
    {m : (upperStar Ab.{u + 1} hX).obj L.X ⟶ L'.X}
    {v : L₀.X ⟶ L.X} {v' : L₀'.X ⟶ L'.X}
    (line₀ : PullEndpoint R hX L₀ L₀' m₀) (line : PullEndpoint T hX L L' m)
    (c₀ : UnitPullEndpoint R hS) (c : UnitPullEndpoint T hS)
    (u : Endpoint a (Mod.regular (condensedRingObj R S))
      (Mod.regular (condensedRingObj T S)) (coefficientMap a S))
    (u' : Endpoint a (Mod.regular (condensedRingObj R S'))
      (Mod.regular (condensedRingObj T S')) (coefficientMap a S'))
    (l : Endpoint a L₀ L v) (l' : Endpoint a L₀' L' v')
    (hl : ScalarPullbackEndpointSquare a hX line₀ l l' line)
    (t₀ : D₀.R.obj (((DerivedCategory.singleFunctor (Modules R X) 0).obj L₀)⟦(2 : ℤ)⟧) ⟶
      unit R S)
    (t₀' : D₀'.R.obj (((DerivedCategory.singleFunctor (Modules R X') 0).obj L₀')⟦(2 : ℤ)⟧) ⟶
      unit R S')
    (t : D.R.obj (((DerivedCategory.singleFunctor (Modules T X) 0).obj L)⟦(2 : ℤ)⟧) ⟶
      unit T S)
    (t' : D'.R.obj (((DerivedCategory.singleFunctor (Modules T X') 0).obj L')⟦(2 : ℤ)⟧) ⟶
      unit T S')
    (ht₀ : TracePullback R f f' hX hS h D₀ D₀' e₀ e₀' line₀ c₀ t₀ t₀')
    (ht : TraceCompatibility a f u l D₀ D t₀ t)
    (ht' : TraceCompatibility a f' u' l' D₀' D' t₀' t') :
    TracePullback T f f' hX hS h D D' e e' line c t t' := by
  let K := ((DerivedCategory.singleFunctor (Modules R X) 0).obj L₀)⟦(2 : ℤ)⟧
  let K' := ((DerivedCategory.singleFunctor (Modules R X') 0).obj L₀')⟦(2 : ℤ)⟧
  let Q := ((DerivedCategory.singleFunctor (Modules T X) 0).obj L)⟦(2 : ℤ)⟧
  let Q' := ((DerivedCategory.singleFunctor (Modules T X') 0).obj L')⟦(2 : ℤ)⟧
  let E₀ := modelExchange R f f' hX hS h D₀ D₀' e₀ e₀' K
  let E := modelExchange T f f' hX hS h D D' e e' Q
  have : IsIso line₀.shift := by unfold PullEndpoint.shift PullEndpoint.derived; infer_instance
  have : IsIso line.shift := by unfold PullEndpoint.shift PullEndpoint.derived; infer_instance
  have : IsIso c₀.derived := by unfold PullEndpoint.derived; infer_instance
  have : IsIso c.derived := by unfold PullEndpoint.derived; infer_instance
  have : IsIso (l.shift a) := by unfold Endpoint.shift; infer_instance
  have : IsIso (l'.shift a) := by unfold Endpoint.shift; infer_instance
  have : IsIso E₀ := ht₀.1
  have : IsIso ((ht.square.mate a).app K) := ht.comparison_iso
  have : IsIso ((ht'.square.mate a).app K') := ht'.comparison_iso
  have : IsIso (scalarPullbackComparison a hS) := scalar_pullback_isIso a hS
  let i := asIso (E₀ ≫ D₀'.R.map line₀.shift)
  let eL := asIso ((ht.square.mate a).app K ≫ D.R.map (l.shift a))
  let eL' := asIso ((ht'.square.mate a).app K' ≫ D'.R.map (l'.shift a))
  have hpush : (scalarPullbackComparison a hS).app (D₀.R.obj K) ≫
      (derivedUpper T hS).map eL.hom ≫ (E ≫ D'.R.map line.shift) =
      (derivedScalars a S').map i.hom ≫ eL'.hom := by
    dsimp only [eL, eL', i, asIso_hom]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% modelExchange_naturality T f f' hX hS h D D' e e' (l.shift a)]
    rw [reassoc_of% scalar_model_exchange_cube a f f' hX hS h D₀ D₀' D D'
      e₀ e₀' e e' he₀ he₀' he he' ht.square ht'.square K]
    simp only [← D'.R.map_comp]
    rw [hl.comm]
    simp only [D'.R.map_comp]
    have hn := (ht'.square.mate a).naturality line₀.shift
    dsimp only [Functor.comp_map] at hn
    rw [← reassoc_of% hn]
  obtain ⟨hj, htrace⟩ := trace_scalar_paste
    (derivedUpper R hS) (derivedUpper T hS)
    (derivedScalars a S) (derivedScalars a S') (scalarPullbackComparison a hS)
    t₀ t₀' t t' i (asIso c₀.derived) eL u.iso eL' u'.iso
    (E ≫ D'.R.map line.shift) (asIso c.derived)
    (by simpa only [i, E₀, asIso_hom, Category.assoc] using ht₀.2)
    (by simpa only [eL, asIso_hom, Category.assoc] using ht.trace)
    (by simpa only [eL', asIso_hom, Category.assoc] using ht'.trace) hpush
    (scalar_unit_pullback_normalization a hS u u' c₀ c)
  have : IsIso (E ≫ D'.R.map line.shift) := hj
  have : IsIso E := IsIso.of_isIso_comp_right E (D'.R.map line.shift)
  exact ⟨inferInstance, by simpa only [E, asIso_hom, Category.assoc] using htrace⟩

/-- The three trace base-change squares after uniformizer reduction. This
contains exchange invertibility on the specified shifted lines but asserts no
compatibility of the diagonal class.

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3), compatibility of the
trace with the coefficient functors; original quotient-base-change proof, step 2.
(blueprint: lem-diagonal-quotient-trace-pullback).

Proof: Use the given scalar.q.comparison_iso and scalar'.q.comparison_iso
(and the p1 and p2 fields) on the shifted integral lines. After inverse image,
these comparisons remain invertible. The integral PullEndpoints identify the
pulled-back integral lines with those on the new base; naturality of the scalar
mates transports the second comparison_iso along this line isomorphism. Thus
all scalar/direct-image comparisons used in the pasting are already known to
be invertible. No assertion for arbitrary complexes or resolution of the
quotient coefficient is needed.
For each of q, p1 and p2, apply quotient extension to the integral trace square.
Paste with scalar.q.trace and scalar'.q.trace (respectively the p1 and p2
fields). The scalar/inverse-image compositors identify the coefficient-unit
endpoints by their ordinary adjunction normalization. They identify the line
endpoints by the two QuotientPullMap equations, checked after the epic tensor
quotient projection. Naturality of the compositor under shifting identifies the
shifted endpoints. The interchange identity for adjunction mates identifies the
pasted direct-image morphism with derivedExchange; q_unit, p1_unit and p2_unit
of the four diagrams identify their right derived presentations with the
canonical units, hence the resulting morphism is exactly modelExchange.
Its invertibility follows by cancelling the pulled-back scalar comparison in
the cube identity: the other boundary consists of the integral exchange
isomorphism, the scalar comparison on the new base, and the scalar/pullback
compositors. All these are isomorphisms on the specified shifted lines.
Cancel these isomorphisms in the pasted trace equality. This gives both
conjuncts of each TracePullback. No diagonal class equation, integration
identity, flatness of the quotient, or regularity of pi is needed. In particular
the argument applies at n = 0, at ramified levels, and even to an arbitrary pi
when the two scalar compatibilities are supplied. -/
theorem diagonalQuotient_tracePullback
    (l : ℕ) [Fact l.Prime] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsNoetherian Y] [IsNoetherian Y']
    (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (n : ℕ)
    (d₀ : Diagram (Profinite.padicIntegersRingObj.{u} l E.1) Y
      (fun X ↦ spIntegralTwist X l E))
    (d₀' : Diagram (Profinite.padicIntegersRingObj.{u} l E.1) Y'
      (fun X ↦ spIntegralTwist X l E))
    (integral : PullbackCompatibility (Profinite.padicIntegersRingObj.{u} l E.1) g
      (fun X ↦ spIntegralTwist X l E) d₀ d₀'
      (spIntegralComparison (baseP g) l E) (spIntegralComparison (baseW g) l E))
    (d : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      Y (quotientLine l E π n))
    (d' : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      Y' (quotientLine l E π n))
    (scalar : ScalarCompatibility (quotientMap l E π n) Y
      (fun X ↦ spIntegralTwist X l E) (quotientLine l E π n)
      (quotientLineMap l E π n) d₀ d)
    (scalar' : ScalarCompatibility (quotientMap l E π n) Y'
      (fun X ↦ spIntegralTwist X l E) (quotientLine l E π n)
      (quotientLineMap l E π n) d₀' d')
    (mP : (upperStar Ab.{u + 1} (baseP g)).obj
      (quotientLine l E π n (ProjectiveLine Y)).X ⟶
        (quotientLine l E π n (ProjectiveLine Y')).X)
    (mW : (upperStar Ab.{u + 1} (baseW g)).obj
      (quotientLine l E π n (diagonalSurface Y)).X ⟶
        (quotientLine l E π n (diagonalSurface Y')).X)
    (_hP : QuotientPullMap l E π n (baseP g) mP)
    (_hW : QuotientPullMap l E π n (baseW g) mW)
    (s : SourcePullback
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) g
      (quotientLine l E π n) mP mW) :
    TracePullbackSquares
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) g
      (quotientLine l E π n) d d' mP mW s := by
  have hP := diagonalQuotient_linePullbackNormalization l E π n (baseP g)
    integral.sourceData.endpoints.lineP scalar.lineP scalar'.lineP mP _hP s.endpoints.lineP
  have hW := diagonalQuotient_linePullbackNormalization l E π n (baseW g)
    integral.sourceData.endpoints.lineW scalar.lineW scalar'.lineW mW _hW s.endpoints.lineW
  refine ⟨?_, ?_, ?_⟩
  · exact scalar_trace_transfer (quotientMap l E π n) _ _ _ _ _
      d₀.Rq d₀'.Rq d.Rq d'.Rq
      d₀.q_canonical d₀'.q_canonical d.q_canonical d'.q_canonical
      d₀.q_unit d₀'.q_unit d.q_unit d'.q_unit
      integral.sourceData.endpoints.lineP s.endpoints.lineP
      integral.sourceData.endpoints.cY s.endpoints.cY
      (scalar.units Y) (scalar'.units Y') scalar.lineP scalar'.lineP hP
      d₀.traceq d₀'.traceq d.traceq d'.traceq integral.traceq scalar.q scalar'.q
  · exact scalar_trace_transfer (quotientMap l E π n) _ _ _ _ _
      d₀.R₁ d₀'.R₁ d.R₁ d'.R₁
      d₀.p₁_canonical d₀'.p₁_canonical d.p₁_canonical d'.p₁_canonical
      d₀.p₁_unit d₀'.p₁_unit d.p₁_unit d'.p₁_unit
      integral.sourceData.endpoints.lineW s.endpoints.lineW
      integral.sourceData.endpoints.cP s.endpoints.cP
      (scalar.units (ProjectiveLine Y)) (scalar'.units (ProjectiveLine Y'))
      scalar.lineW scalar'.lineW hW
      d₀.trace₁ d₀'.trace₁ d.trace₁ d'.trace₁ integral.trace₁ scalar.p₁ scalar'.p₁
  · exact scalar_trace_transfer (quotientMap l E π n) _ _ _ _ _
      d₀.R₂ d₀'.R₂ d.R₂ d'.R₂
      d₀.p₂_canonical d₀'.p₂_canonical d.p₂_canonical d'.p₂_canonical
      d₀.p₂_unit d₀'.p₂_unit d.p₂_unit d'.p₂_unit
      integral.sourceData.endpoints.lineW s.endpoints.lineW
      integral.sourceData.endpoints.cP s.endpoints.cP
      (scalar.units (ProjectiveLine Y)) (scalar'.units (ProjectiveLine Y'))
      scalar.lineW scalar'.lineW hW
      d₀.trace₂ d₀'.trace₂ d.trace₂ d'.trace₂ integral.trace₂ scalar.p₂ scalar'.p₂

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
