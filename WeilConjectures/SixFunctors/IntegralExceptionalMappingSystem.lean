/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteAdjunctionDiagramRealization
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import WeilConjectures.SixFunctors.FiniteExceptional
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
import WeilConjectures.AlgebraicGeometry.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.AlgebraicGeometry.SfDerivedCompleteLegacyComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.IntegralResidueTor

/-! # Finite exceptional adjunction on integral reduction mapping systems

Source: blueprint, prop-coef-integral-exceptional-adjoint, proof paragraphs 2--3
(blueprint: lem-coef-integral-exceptional-mapping-system).
The natural isomorphism below is the composite of actual system counits and the
specified enriched finite-operation realization, before evaluation or inverse limit.
The index n denotes the positive coefficient exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralExceptionalMapping
open FiniteAdjunctionDiagram

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

include hl in
/-- Integral constructible inputs reduce into the normalized finite-Tor system domain.
Source: node proof step 1
(blueprint: lem-coef-integral-exceptional-mapping-system).
Proof: integral constructibility bounds the first reduction. Apply
lem-coef-integral-residue-tor, since l is invertible over D.k, to bound the Tor
amplitude of every reduction. The calculus identifies its levels with these
reductions. Its strict quotient maps are normalized by
lem-sfb-successive-derived-quotient-normalization, including all triple compositions.
No extra finite-Tor hypothesis is imposed on the integral input. -/
theorem reduction_domain (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [IsSeparated (W ↘ Spec (.of D.k))] (S : CoefficientDerivedSystemCalculus l E W)
    (K : sfIntegralConstructibleCategory l E W) : domain l E W (S.reduction.obj K.obj) := by
  classical
  let (x : W) : Invertible (l : W.residueField x) :=
    (show IsUnit (l : W.residueField x) by
      simpa using (finiteFieldDatumPrimeUnit D l hl).map
        ((W ↘ Spec (.of D.k)).residueFieldAlgebraMap x)).invertible
  have hK := K.property
  obtain ⟨_, a, b, hab, hlevels⟩ := K.property
  have htor := (integral_residue_tor D l hl E W).1 K.obj hK a b hab
    (fun i hi ↦ (hlevels 0).2 hi)
  refine ⟨S.reduction_normalized K.obj, fun n ↦ ?_⟩
  let e := (S.reductionEvaluation n).app K.obj
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W) :=
    (proEtale_bounded_constructible_isTriangulated W A).1
  have hc : intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W
      ((coefficientSequenceDerivedEvaluation l E W n).obj (S.reduction.obj K.obj)) :=
    (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) W).prop_of_iso
      e.symm (hlevels n).1
  refine ⟨hc, a, b, (htor n).1, ?_⟩
  rintro N P ⟨q⟩ v hv hP M i hi
  exact (htor n).2 N P ⟨q ≪≫ e⟩ v hv hP M i hi

/-- The existing reduction functor restricted to integral constructible inputs.
Source: node first paragraph and proof step 1
(blueprint: lem-coef-integral-exceptional-mapping-system). -/
def R (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [IsSeparated (W ↘ Spec (.of D.k))] (S : CoefficientDerivedSystemCalculus l E W) :
    sfIntegralConstructibleCategory l E W ⥤ (domain l E W).FullSubcategory :=
  reducedConstructible W S (reduction_domain l E D hl W S)

private theorem globalEvaluation_naturality (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus l E W)
    (C : CoefficientDerivedSystemResolutionCoherence l E W S)
    (M N M' N' : coefficientSequenceDerived l E W)
    (hM : IsNormalizedCoefficientSequence l E W M)
    (hN : IsNormalizedCoefficientSequence l E W N)
    (hM' : IsNormalizedCoefficientSequence l E W M')
    (hN' : IsNormalizedCoefficientSequence l E W N')
    (v : M' ⟶ M) (w : N ⟶ N') (n : ℕ) :
    (coefficientMappingEvaluation.{u+1} n).map
        ((coefficientSequenceGlobalHom l E W).map (Prod.mkHom v.op w)) ≫
      (S.globalEvaluation M' N' hM' hN' n).hom =
    (S.globalEvaluation M N hM hN n).hom ≫
      (coefficientFiniteGlobalHom l E W n).map
        (Prod.mkHom (((coefficientSequenceDerivedEvaluation l E W n).map v).op)
          ((coefficientSequenceDerivedEvaluation l E W n).map w)) := by
  rw [C.globalEvaluation_model, C.globalEvaluation_model]
  have hn := (C.systemSectionsEvaluation n).hom.naturality
    ((coefficientSequenceInternalHom l E W).map (Prod.mkHom v.op w))
  simp only [Functor.comp_map] at hn
  dsimp only [coefficientSequenceGlobalHom, coefficientFiniteGlobalHom, Functor.comp_map]
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
    S.fiber_naturality M N M' N' hM hN hM' hN' v w n, Functor.map_comp]
  simp only [coefficientFiniteInternalHom, Category.assoc]

variable {l E D hl}
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] {c : Compactification f}
  {SX : CoefficientDerivedSystemCalculus l E X}
  {SZ : CoefficientDerivedSystemCalculus l E c.Z}
  {SY : CoefficientDerivedSystemCalculus l E Y}
  (r : Realization l E D hl f c SX SZ SY)

/-- The integral compact-support limit F = L_Y F_system R_X.
Source: node second paragraph
(blueprint: lem-coef-integral-exceptional-mapping-system). -/
def F : sfIntegralConstructibleCategory l E X ⥤
    DerivedCategory (scalarReductionSource l E Y) :=
  R l E D hl X SX ⋙ r.F ⋙ (domain l E Y).ι ⋙ coefficientSequenceLimit l E Y

/-- The exceptional candidate J = L_X E_system R_Y; no integral adjunction is assumed.
Source: node second paragraph
(blueprint: lem-coef-integral-exceptional-mapping-system). -/
def J : sfIntegralConstructibleCategory l E Y ⥤
    DerivedCategory (scalarReductionSource l E X) :=
  R l E D hl Y SY ⋙ r.G ⋙ (domain l E X).ι ⋙ coefficientSequenceLimit l E X

/-- The actual reduction-limit counit on the finite compact-support system.
Source: node display c_K and proof step 3
(blueprint: lem-coef-integral-exceptional-mapping-system). -/
def supportCounit : F r ⋙ SY.reduction ⟶ R l E D hl X SX ⋙ r.F ⋙ (domain l E Y).ι :=
  Functor.whiskerLeft (R l E D hl X SX ⋙ r.F ⋙ (domain l E Y).ι) SY.adjunction.counit

/-- The actual reduction-limit counit on the finite exceptional system.
Source: node display c_L and proof step 3
(blueprint: lem-coef-integral-exceptional-mapping-system). -/
def exceptionalCounit : J r ⋙ SX.reduction ⟶ R l E D hl Y SY ⋙ r.G ⋙ (domain l E X).ι :=
  Functor.whiskerLeft (R l E D hl Y SY ⋙ r.G ⋙ (domain l E X).ι) SX.adjunction.counit

/-- Constructibility of the actual compact-support limit and invertibility of its
actual system counit and of the exceptional candidate's actual system counit.
Source: node proof steps 2--3
(blueprint: lem-coef-integral-exceptional-mapping-system).
Proof: IntegralSupport identifies this very functor, including its projections,
with the recorded compact support. Apply lem-sf-integral-compact-support-constructible.
Both output systems are normalized by the finite realization. Apply
lem-coef-normalized-dvr-effectivity to their total-limit projections. The calculus
identifies these scalar adjuncts with the evaluations of the actual counits.
Conservativity of evaluations makes the actual counits invertible. Naturality is
already the naturality of the actual adjunction counit. -/
theorem support_and_counits :
    (∀ K : sfIntegralConstructibleCategory l E X, sfIntegralConstructible l E Y ((F r).obj K)) ∧
    (∀ K : sfIntegralConstructibleCategory l E X, IsIso ((supportCounit r).app K)) ∧
    (∀ L : sfIntegralConstructibleCategory l E Y, IsIso ((exceptionalCounit r).app L)) := by
  classical
  have hunit (W : Scheme.{u}) [W.Over (Spec (.of D.k))] :
      IsUnit (l : Γ(W, ⊤)) := by
    let ρ := (Scheme.ΓSpecIso (.of D.k)).inv ≫ (W ↘ Spec (.of D.k)).appTop
    simpa only [map_natCast] using (finiteFieldDatumPrimeUnit D l hl).map ρ.hom
  have hY := (purNormalizedReconstruction l E Y (hunit Y) SY).1
  have hX := (purNormalizedReconstruction l E X (hunit X) SX).1
  have hs (K : sfIntegralConstructibleCategory l E X) :
      IsIso ((supportCounit r).app K) :=
    (hY _ (r.F.obj ((R l E D hl X SX).obj K)).property.1).2
  have he (L : sfIntegralConstructibleCategory l E Y) :
      IsIso ((exceptionalCounit r).app L) :=
    (hX _ (r.G.obj ((R l E D hl Y SY).obj L)).property.1).2
  refine ⟨?_, hs, he⟩
  intro K
  have hcomplete : IsSfDerivedComplete l E Y ((F r).obj K) := by
    obtain ⟨D', hl', h⟩ :=
      (hY _ (r.F.obj ((R l E D hl X SX).obj K)).property.1).1
    exact (sfDerivedComplete_iff_legacy l E Y D' hl' _).mpr h
  have : IsIso ((supportCounit r).app K) := hs K
  let B := (sfCompactSupportFiniteIntegralFunctor l D.k
    (finiteFieldDatumPrimeUnit D l hl) c E).obj K
  have e (n : ℕ) :
      (scalarReductionDerivedExtension l E Y n).obj ((F r).obj K) ≅
        (scalarReductionDerivedExtension l E Y n).obj B.obj :=
    ((SY.reductionEvaluation n).app ((F r).obj K)).symm ≪≫
      (coefficientSequenceDerivedEvaluation l E Y n).mapIso
        (asIso ((supportCounit r).app K)) ≪≫
      (FiniteExceptional.domain l E Y n).ι.mapIso
        ((r.supportEvaluation n).app ((R l E D hl X SX).obj K)) ≪≫
      (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).mapIso
        ((SX.reductionEvaluation n).app K.obj) ≪≫
      (sfCompactSupportFiniteReductionIso l D.k (finiteFieldDatumPrimeUnit D l hl)
        c E K n).symm
  obtain ⟨_, a, b, hab, hred⟩ := B.property
  refine ⟨hcomplete, a, b, hab, fun n ↦ ?_⟩
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) Y) :=
    (proEtale_bounded_constructible_isTriangulated Y A).1
  refine ⟨ObjectProperty.prop_of_iso _ (e n).symm (hred n).1, ?_⟩
  intro j hj
  apply (hred n).2
  intro hz
  exact hj (((DerivedCategory.homologyFunctor _ j).mapIso (e n)).isZero_iff.mpr hz)

/-- The natural isomorphism c_K, with forward map literally the actual system counit.
Source: node display c_K (blueprint: lem-coef-integral-exceptional-mapping-system). -/
def supportIso : F r ⋙ SY.reduction ≅ R l E D hl X SX ⋙ r.F ⋙ (domain l E Y).ι :=
  letI : ∀ K, IsIso ((supportCounit r).app K) := (support_and_counits r).2.1
  letI : IsIso (supportCounit r) := NatIso.isIso_of_isIso_app (supportCounit r)
  asIso (supportCounit r)

/-- The natural isomorphism c_L, with forward map literally the actual system counit.
Source: node display c_L (blueprint: lem-coef-integral-exceptional-mapping-system). -/
def exceptionalIso : J r ⋙ SX.reduction ≅ R l E D hl Y SY ⋙ r.G ⋙ (domain l E X).ι :=
  letI : ∀ L, IsIso ((exceptionalCounit r).app L) := (support_and_counits r).2.2
  letI : IsIso (exceptionalCounit r) := NatIso.isIso_of_isIso_app (exceptionalCounit r)
  asIso (exceptionalCounit r)

/-- Source mapping bifunctor H_Y(R_Y F K,R_Y L).
Source: node display Psi (blueprint: lem-coef-integral-exceptional-mapping-system). -/
def mappingSource :=
  (F r ⋙ SY.reduction).op.prod
    ((sfIntegralConstructible l E Y).ι ⋙ SY.reduction) ⋙ coefficientSequenceGlobalHom l E Y

/-- Target mapping bifunctor H_X(R_X K,R_X J L).
Source: node display Psi (blueprint: lem-coef-integral-exceptional-mapping-system). -/
def mappingTarget :=
  ((sfIntegralConstructible l E X).ι ⋙ SX.reduction).op.prod
    (J r ⋙ SX.reduction) ⋙ coefficientSequenceGlobalHom l E X

variable {g : Geometry l E f SX SY} {s : SectionsPush g}
  {βX : @SymmetricCategory (coefficientSequenceDerived l E X) _ SX.systemClosed.monoidal}
  {βY : @SymmetricCategory (coefficientSequenceDerived l E Y) _ SY.systemClosed.monoidal}
  (a : Enriched r g s βX βY)

/-- The specified natural isomorphism Psi is the displayed three-factor composite.
Its first factor precomposes with c_K inverse and its last postcomposes with c_L
inverse. The middle is the actual enriched system transformation of the realization.
No map is chosen from its finite evaluations.
Source: node display Psi and proof step 4
(blueprint: lem-coef-integral-exceptional-mapping-system). -/
def psi (a : Enriched r g s βX βY) : mappingSource r ≅ mappingTarget r :=
  Functor.isoWhiskerRight
      (NatIso.prod (NatIso.op (supportIso r).symm)
        (Iso.refl ((sfIntegralConstructible l E Y).ι ⋙ SY.reduction)))
      (coefficientSequenceGlobalHom l E Y) ≪≫
    Functor.isoWhiskerLeft ((R l E D hl X SX).op.prod (R l E D hl Y SY)) a.iso ≪≫
    Functor.isoWhiskerRight
      (NatIso.prod (Iso.refl (((sfIntegralConstructible l E X).ι ⋙ SX.reduction).op))
        (exceptionalIso r).symm) (coefficientSequenceGlobalHom l E X)

/-- Finite c_K followed by the canonical compact-support coefficient comparison.
Source: node final paragraph and proof step 5
(blueprint: lem-coef-integral-exceptional-mapping-system). -/
def finiteSupport (n : ℕ) (K : sfIntegralConstructibleCategory l E X) :=
  (coefficientSequenceDerivedEvaluation l E Y n).mapIso ((supportIso r).app K) ≪≫
    (FiniteExceptional.domain l E Y n).ι.mapIso
      ((r.supportEvaluation n).app ((R l E D hl X SX).obj K))

/-- The evaluated actual counit is the canonical compact-support coefficient comparison.
The supplied IntegralSupport is precisely the projection-normalized identification of
these same finite-operation realizations with recorded integral compact support.
Source: node second paragraph and proof steps 2--3
(blueprint: lem-coef-integral-exceptional-mapping-system).
Proof: transpose IntegralSupport.projections through the finite scalar adjunction.
The calculus counit_projection identifies the left transpose with the evaluated
actual system counit. The right transpose is the recorded compact-support
coefficient comparison. Injectivity of the scalar-adjunction Hom bijection gives
the equation, naturally in the integral input. -/
theorem supportCoefficientComparison (i : IntegralSupport r) (n : ℕ)
    (K : sfIntegralConstructibleCategory l E X) :
    (SY.reductionEvaluation n).inv.app ((F r).obj K) ≫ (finiteSupport r n K).hom ≫
        (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
          ((SX.reductionEvaluation n).hom.app K.obj) =
      (coefficientFiniteDerivedExtension l E Y n).map (i.iso.hom.app K) ≫
        (sfCompactSupportFiniteReductionIso l D.k (finiteFieldDatumPrimeUnit D l hl)
          c E K n).hom := by
  apply ((coefficientFiniteAdjunction l E Y n).homEquiv _ _).injective
  simp only [finiteSupport, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    ObjectProperty.ι_map, supportIso, asIso_hom, supportCounit, Functor.whiskerLeft_app]
  rw [← Category.assoc, ← Category.assoc,
    Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  erw [SY.counit_projection]
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_unit]
  erw [← (coefficientFiniteAdjunction l E Y n).unit.naturality (i.iso.hom.app K)]
  simpa only [Functor.id_map, Functor.map_comp, Category.assoc, R, F, Functor.comp_obj,
    ObjectProperty.ι_obj] using i.projections K n

/-- Finite c_L followed by the specified exceptional evaluation comparison.
Source: node final paragraph and proof step 5
(blueprint: lem-coef-integral-exceptional-mapping-system). -/
def finiteExceptional (n : ℕ) (L : sfIntegralConstructibleCategory l E Y) :=
  (coefficientSequenceDerivedEvaluation l E X n).mapIso ((exceptionalIso r).app L) ≪≫
    (FiniteExceptional.domain l E X n).ι.mapIso
      ((r.exceptionalEvaluation n).app ((R l E D hl Y SY).obj L))

/-- Evaluate the actual Psi and use the calculus's finite global mapping identifications.
Source: node final paragraph and proof step 5
(blueprint: lem-coef-integral-exceptional-mapping-system). -/
def finitePsi (a : Enriched r g s βX βY) (n : ℕ)
    (K : sfIntegralConstructibleCategory l E X)
    (L : sfIntegralConstructibleCategory l E Y) :=
  (SY.globalEvaluation (SY.reduction.obj ((F r).obj K)) (SY.reduction.obj L.obj)
      (SY.reduction_normalized _) (SY.reduction_normalized _) n).inv ≫
    (coefficientMappingEvaluation.{u+1} n).map ((psi r a).hom.app (op K, L)) ≫
    (SX.globalEvaluation (SX.reduction.obj K.obj) (SX.reduction.obj ((J r).obj L))
      (SX.reduction_normalized _) (SX.reduction_normalized _) n).hom

/-- Finite evaluation in the derived category itself (hence in every cohomological
 degree), and the explicit degree-zero Hom formula for the specified Psi.
The finite enriched map is the ordinary etale adjunction transported through the
canonical etale/pro-etale and compact-support comparisons. Its unit, counit and
all quotient-transition equations are the fields of the given realization r.

Source: node final paragraph and proof step 5
(blueprint: lem-coef-integral-exceptional-mapping-system).
Proof: evaluate the three-factor composite. Naturality of global evaluation
identifies the outside factors with precomposition by c_K inverse and
postcomposition by c_L inverse. Enriched.finiteEvaluation identifies the middle
factor with its etale-origin finite mapping-complex isomorphism. This is an
equality in the derived category, so applying homology in any integer degree
gives the shifted-Hom assertion. Apply coefficientFiniteHomEquiv and
Enriched.finiteHom in degree zero for the displayed finite adjunction formula.
All factors were system transformations before evaluation, so the map respects
all transitions. Realization.unit, counit, supportTransition and
exceptionalTransition retain precisely the finite units, counits and quotient
mates of lem-coef-finite-exceptional; no integral adjunction is used. -/
theorem integralExceptionalMappingSystem
    (CX : CoefficientDerivedSystemResolutionCoherence l E X SX)
    (CY : CoefficientDerivedSystemResolutionCoherence l E Y SY) (n : ℕ)
    (K : sfIntegralConstructibleCategory l E X) (L : sfIntegralConstructibleCategory l E Y) :
    finitePsi r a n K L =
      (coefficientFiniteGlobalHom l E Y n).map
        (Prod.mkHom ((finiteSupport r n K).inv.op) (𝟙 _)) ≫
      (a.finiteIso n).hom.app
        (op ((evaluation l E X n).obj ((R l E D hl X SX).obj K)),
          (evaluation l E Y n).obj ((R l E D hl Y SY).obj L)) ≫
      (coefficientFiniteGlobalHom l E X n).map
        (Prod.mkHom (𝟙 _) ((finiteExceptional r n L).inv)) ∧
    ∀ x : (DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0).obj
        ((coefficientFiniteGlobalHom l E Y n).obj
          (op ((coefficientSequenceDerivedEvaluation l E Y n).obj
            (SY.reduction.obj ((F r).obj K))),
            (coefficientSequenceDerivedEvaluation l E Y n).obj (SY.reduction.obj L.obj))),
      coefficientFiniteHomEquiv l E X n _ _
        (((DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0).map
          (finitePsi r a n K L)) x) =
      (((FiniteExceptional.adjunction l E D hl f c n).homEquiv
        ((evaluation l E X n).obj ((R l E D hl X SX).obj K))
        ((evaluation l E Y n).obj ((R l E D hl Y SY).obj L))
        (ObjectProperty.homMk ((finiteSupport r n K).inv ≫
          coefficientFiniteHomEquiv l E Y n _
            ((coefficientSequenceDerivedEvaluation l E Y n).obj
              (SY.reduction.obj L.obj)) x))).hom) ≫
        (finiteExceptional r n L).inv := by
  classical
  let M := (R l E D hl X SX).obj K
  let N := (R l E D hl Y SY).obj L
  let eY := (supportIso r).app K
  let eX := (exceptionalIso r).app L
  have hY := globalEvaluation_naturality l E Y SY CY
    (SY.reduction.obj ((F r).obj K)) N.obj (r.F.obj M).obj N.obj
    (SY.reduction_normalized _) N.property.1 (r.F.obj M).property.1 N.property.1
    eY.inv (𝟙 _) n
  have hX := globalEvaluation_naturality l E X SX CX
    M.obj (r.G.obj N).obj M.obj (SX.reduction.obj ((J r).obj L))
    M.property.1 (r.G.obj N).property.1 M.property.1 (SX.reduction_normalized _)
    (𝟙 _) eX.inv n
  have hA := a.finiteEvaluation n M N
  let eFin := (FiniteExceptional.domain l E X n).ι.mapIso
    ((r.exceptionalEvaluation n).app N)
  let eMap := (coefficientFiniteGlobalHom l E X n).mapIso
    (Iso.prod (Iso.refl (op ((coefficientSequenceDerivedEvaluation l E X n).obj M.obj)))
      eFin)
  have heq : finitePsi r a n K L =
      (coefficientFiniteGlobalHom l E Y n).map
        (Prod.mkHom ((finiteSupport r n K).inv.op) (𝟙 _)) ≫
      (a.finiteIso n).hom.app
        (op ((evaluation l E X n).obj M), (evaluation l E Y n).obj N) ≫
      (coefficientFiniteGlobalHom l E X n).map
        (Prod.mkHom (𝟙 _) ((finiteExceptional r n L).inv)) := by
    have hA' :
        (coefficientMappingEvaluation.{u+1} n).map (a.iso.hom.app (op M, N)) ≫
          (SX.globalEvaluation M.obj (r.G.obj N).obj M.property.1
            (r.G.obj N).property.1 n).hom =
        (SY.globalEvaluation (r.F.obj M).obj N.obj (r.F.obj M).property.1
          N.property.1 n).hom ≫
          (coefficientFiniteGlobalHom l E Y n).map
            (Prod.mkHom (((r.supportEvaluation n).inv.app M).hom.op) (𝟙 _)) ≫
          (a.finiteIso n).hom.app
            (op ((evaluation l E X n).obj M), (evaluation l E Y n).obj N) ≫
          (coefficientFiniteGlobalHom l E X n).map
            (Prod.mkHom (𝟙 _) (((r.exceptionalEvaluation n).inv.app N).hom)) := by
      change _ ≫ _ ≫ eMap.hom = _ at hA
      have h := congrArg (fun z ↦ z ≫ eMap.inv) hA
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
      exact h
    dsimp only [finitePsi, psi]
    simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp]
    simp only [Category.assoc]
    change
      (SY.globalEvaluation _ _ (SY.reduction_normalized _) (SY.reduction_normalized _) n).inv ≫
        (coefficientMappingEvaluation.{u+1} n).map
          ((coefficientSequenceGlobalHom l E Y).map (Prod.mkHom eY.inv.op (𝟙 _))) ≫
        (coefficientMappingEvaluation.{u+1} n).map (a.iso.hom.app (op M, N)) ≫
        (coefficientMappingEvaluation.{u+1} n).map
          ((coefficientSequenceGlobalHom l E X).map (Prod.mkHom (𝟙 _) eX.inv)) ≫
        (SX.globalEvaluation _ _ (SX.reduction_normalized _) (SX.reduction_normalized _) n).hom = _
    simp only [op_id] at hX hY
    erw [hX, ← Category.assoc
      ((coefficientMappingEvaluation.{u+1} n).map (a.iso.hom.app (op M, N))), hA']
    simp only [Category.assoc]
    erw [← Category.assoc
      ((coefficientMappingEvaluation.{u+1} n).map
        ((coefficientSequenceGlobalHom l E Y).map (Prod.mkHom eY.inv.op (𝟙 _)))), hY]
    dsimp only [N, R, reducedConstructible, Functor.comp_obj,
      ObjectProperty.lift, ObjectProperty.ι_obj]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_assoc]
    simp only [CategoryTheory.Functor.map_id]
    simp only [op_id]
    rw [← Category.assoc
      ((coefficientFiniteGlobalHom l E Y n).map
        (Prod.mkHom ((coefficientSequenceDerivedEvaluation l E Y n).map eY.inv).op
          (𝟙 _))), ← Functor.map_comp]
    simp only [prod_comp, Category.id_comp]
    simp only [finiteSupport, finiteExceptional, Iso.trans_inv, Functor.mapIso_inv,
      Iso.app_inv, ObjectProperty.ι_map]
    simp only [op_comp]
    rw [← Functor.map_comp]
    simp only [prod_comp, Category.id_comp]
    rfl
  refine ⟨heq, ?_⟩
  intro x
  rw [heq]
  simp only [Functor.map_comp, AddCommGrpCat.comp_apply]
  have hfy := (coefficientHomZeroEquiv_exists.{u, u+1, u}
    (Scheme.ProEt.topology Y) (integralCoefficientCommRingSheaf l E Y n)).choose_spec.1.1
  have hfx := (coefficientHomZeroEquiv_exists.{u, u+1, u}
    (Scheme.ProEt.topology X) (integralCoefficientCommRingSheaf l E X n)).choose_spec.1.1
  have hpre := hfy _ _ _ _ (finiteSupport r n K).inv (𝟙 _) x
  change coefficientFiniteHomEquiv l E Y n _ _
    (((DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0).map
      ((coefficientFiniteGlobalHom l E Y n).map
        (Prod.mkHom (finiteSupport r n K).inv.op (𝟙 _)))) x) =
      (finiteSupport r n K).inv ≫ coefficientFiniteHomEquiv l E Y n _ _ x ≫ 𝟙 _ at hpre
  have hpost := hfx _ _ _ _ (𝟙 _) (finiteExceptional r n L).inv
    (((DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0).map
      ((a.finiteIso n).hom.app (op ((evaluation l E X n).obj M),
        (evaluation l E Y n).obj N)))
      (((DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0).map
        ((coefficientFiniteGlobalHom l E Y n).map
          (Prod.mkHom ((finiteSupport r n K).inv.op) (𝟙 _)))) x))
  change coefficientFiniteHomEquiv l E X n _ _
    (((DerivedCategory.homologyFunctor AddCommGrpCat.{u+1} 0).map
      ((coefficientFiniteGlobalHom l E X n).map
        (Prod.mkHom (𝟙 _) (finiteExceptional r n L).inv))) _) =
      𝟙 _ ≫ coefficientFiniteHomEquiv l E X n _ _ _ ≫ (finiteExceptional r n L).inv at hpost
  erw [hpost, a.finiteHom]
  simp only [Category.id_comp, Category.comp_id] at hpre ⊢
  erw [hpre]


end WeilConjectures.IntegralExceptionalMapping
