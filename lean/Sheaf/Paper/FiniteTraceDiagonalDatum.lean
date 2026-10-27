/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.FiniteTraceDiagonalCanonicalMaps
public import Sheaf.Paper.PurityFiniteSetting
public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal.Basic
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula
public import Sheaf.AlgebraicGeometry.ConstructibleLocalTorEtaleOrigin
public import Sheaf.AlgebraicGeometry.ProEtaleTorLocalGlobal
public import Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackIdentity
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TensorResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactifFiniteTor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Reduction
import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
import Sheaf.Paper.FiniteDiagonalContractionNaturality
import Sheaf.Paper.FiniteDiagonalExchangeNaturality

/-!
# Finite-coefficient trace-diagonal data

Source: blueprint sec-smooth-purity/sk-prop-a1-inv/def-pur-td-datum.md
(blueprint: def-pur-td-datum).

The two arrows are on the actual small pro-etale site, in the fixed module-valued
presentation of constant coefficients. The induced functors are restricted to Dctf.
Every comparison below is a specified projection, pullback, or compact-support map.
The two triangular composites are endomorphisms; no triangular identity is imposed.

## Main definitions

* `Datum`: the trace and supported diagonal class.
* `functor`, `compactFunctor`: the finite-Tor constructible restrictions.
* `Datum.unit`, `Datum.counit`: the specified canonical component formulas.
* `Datum.leftTriangle`, `Datum.rightTriangle`: the triangular endomorphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.FiniteTraceDiagonal

section ProjectionNaturality

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [QuasiCompact f]

omit [IsSeparated f] [QuasiCompact f] in
private theorem projectionCore_hom_naturality_right (c : Compactification f)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (L L' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K)
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y L)
    (hL' : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y L') (a : L ⟶ L') :
    ((tensorFor A Y).obj ((compactSupportFor A c).obj K)).map a ≫
        (projectionCore A f c K L' hK hL').hom =
      (projectionCore A f c K L hK hL).hom ≫
        (compactSupportFor A c).map (((tensorFor A X).obj K).map ((pullFor A f).map a)) := by
  have hp := ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app K).naturality a
  dsimp [derivedTensorRightDerivedLowerShriek,
    rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar] at hp
  exact hp


end ProjectionNaturality

private theorem finiteTor_origin (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T K) :
    ∃ K' : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)),
      Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T K' ∧
      Nonempty ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj K' ≅ K) := by
  obtain ⟨⟨K', hK', ⟨e⟩⟩, a, b, ht⟩ := hK
  refine ⟨K', ⟨hK', a, b, ?_⟩, ⟨e⟩⟩
  exact (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b K').1
    ((DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) T a b).prop_of_iso e.symm ht)

private theorem tensor_preserves (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) (K M : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T K)
    (hM : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T M) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T
      (((tensorFor A T).obj K).obj M) := by
  obtain ⟨K', hK', ⟨eK⟩⟩ := finiteTor_origin A T K hK
  obtain ⟨M', hM', ⟨eM⟩⟩ := finiteTor_origin A T M hM
  let e := (derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
    (ModuleCat.{u + 1} A) K').app M' ≪≫ tensorIso eK eM
  exact (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T).prop_of_iso e
    (DerivedCategory.constructibleFiniteTor_mapDerivedCategory A
      (Etale.constructibleFiniteTor_tensor A T hK' hM'))

variable (P : WeilConjectures.PurityFiniteSetting.{u})

/-- Finiteness of the coefficient quotient, inherited from the recorded construction.
Source: blueprint def-pur-conventions, finite coefficients (blueprint: def-pur-td-datum). -/
instance coefficientFinite : Finite P.Coefficient :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

/-- The existing ambient pro-etale category at the fixed finite coefficient stage.
Source: blueprint def-pur-td-datum, ambient notation (blueprint: def-pur-td-datum). -/
abbrev D (T : Scheme.{u}) :=
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))

/-- The published full finite-Tor constructible subcategory, at these coefficients.
Source: blueprint def-pur-td-datum, Dctf (blueprint: def-pur-td-datum). -/
abbrev Ctf (T : Scheme.{u}) := DerivedCategoryFiniteTor (ModuleCat.{u + 1} P.Coefficient) T

/-- The coefficient unit in the same native constant-coefficient presentation.
Source: blueprint def-pur-td-datum, Lambda_T (blueprint: def-pur-td-datum). -/
abbrev one (T : Scheme.{u}) : D P T := coefficientUnit (ModuleCat.{u + 1} P.Coefficient) T

/-- Exact derived pullback from the published fixed-coefficient pro-etale API.
Source: blueprint def-pur-td-datum, Lu* (blueprint: def-pur-td-datum). -/
abbrev pull {S T : Scheme.{u}} (h : S ⟶ T) : D P T ⥤ D P S :=
  pullFor P.Coefficient h

/-- The published compact-support candidate for the chosen compactification.
Source: blueprint def-pur-td-datum, Ru! (blueprint: def-pur-td-datum). -/
abbrev push {S T : Scheme.{u}} (h : S ⟶ T) [HasCompactification h] : D P S ⥤ D P T :=
  compactSupportFor P.Coefficient
    (HasCompactification.compactification h)

/-- The actual derived tensor bifunctor from def-weil-derived-tensor.
Source: blueprint def-pur-td-datum, tensor notation (blueprint: def-pur-td-datum). -/
abbrev tensor (T : Scheme.{u}) := tensorFor P.Coefficient T

/-- Tensor invertibility means existence of an inverse and the specified unit isomorphism.
Source: blueprint def-pur-td-datum, tensor-invertible L (blueprint: def-pur-td-datum). -/
def Invertible {T : Scheme.{u}} (L : Ctf P T) : Prop :=
  ∃ M : D P T, Nonempty (((tensor P T).obj L.obj).obj M ≅ one P T)

variable {P} {X Y : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
  [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Nagata's chosen compactification in the finite-type field setting.
Source: blueprint def-pur-td-datum, separated finite-type setting
(blueprint: def-pur-td-datum). -/
def compactification : Compactification f :=
  letI := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  letI := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of P.field.k))
  HasCompactification.compactification f

/-- The two defining arrows, for tensor-invertible L in the prescribed Dctf category.
No unit, counit, or triangular identity is additional data.
Source: blueprint def-pur-td-datum, the displayed pair (blueprint: def-pur-td-datum). -/
structure Datum
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (L : Ctf P X) (_hL : Invertible P L) where
  /-- The trace Rf! L -> Lambda_Y. -/
  trace : (compactSupportFor P.Coefficient (compactification (P := P) f)).obj L.obj ⟶ one P Y
  /-- The supported diagonal class RDelta! Lambda_X -> Lp2* L. -/
  diagonalClass : (push P (Etale.TraceDiagonalDatum.diagonal f)).obj (one P X) ⟶
    (pull P (pullback.snd f f)).obj L.obj


/-- The finite-level exceptional direct image for f, with its Nagata compactification.
Source: blueprint def-pur-td-datum, Rf! (blueprint: def-pur-td-datum). -/
abbrev shriek : D P X ⥤ D P Y :=
  compactSupportFor P.Coefficient
    (compactification (P := P) f)

/-- The second projection uses the base-changed compactification, so the self-square
exchange has precisely this endpoint before compactification comparisons are inserted.
Source: blueprint def-pur-td-datum, self-square (blueprint: def-pur-td-datum). -/
abbrev shriek₂ : D P (pullback f f) ⥤ D P X :=
  compactSupportFor P.Coefficient
    ((compactification (P := P) f).ofIsPullback (IsPullback.of_hasPullback f f))

/-- The ambient formula for G_L, before restricting the already specified functors.
Source: blueprint def-pur-td-datum, G_L (blueprint: def-pur-td-datum). -/
def twisted (L : Ctf P X) : D P Y ⥤ D P X :=
  pull P f ⋙ (tensor P X).flip.obj L.obj

set_option linter.unusedSectionVars false in
/-- The defining formula for G_L has values in the source's full Dctf category.
Source: blueprint def-pur-td-datum.proof.md, functoriality and typing
(blueprint: def-pur-td-datum).
Proof: native finite-coefficient pullback preserves constructible finite Tor amplitude.
Extract etale origins of that pullback and L, reflect their Tor intervals through
comparison, and apply native etale tensor closure. Transport through the monoidal
comparison and the origin isomorphisms to obtain this fixed-module tensor formula. -/
theorem twisted_preserves (L : Ctf P X) (K : Ctf P Y) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) X
      ((twisted (P := P) f L).obj K.obj) := by
  exact tensor_preserves P.Coefficient X _ L.obj
    (constructibleFiniteTor_leftDerivedFunctor_upperStar_obj f K.property) L.property

set_option linter.unusedSectionVars false in
/-- The Rf! restriction used by the unit and both triangular endomorphisms.
Source: blueprint def-pur-td-datum, the typed triangular composites
(blueprint: def-pur-td-datum).
Proof: the finite quotient is annihilated by ell^level, a positive integer invertible
on Y since ell differs from the characteristic. Apply clause (i) of
lem-sf-native-finite-tor-preservation to the Nagata compactification of f and A.
Its output is this same fixed-module compact-support candidate. -/
theorem shriek_preserves (A : Ctf P X) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) Y
      ((shriek (P := P) f).obj A.obj) := by
  let := P.finiteComparedInvertibleExponent (Y ↘ Spec (.of P.field.k))
  exact constructibleFiniteTor_rightDerivedLowerShriekOfCompactification P.Coefficient
    (Y ↘ Spec (.of P.field.k)) (compactification (P := P) f) A.property

set_option linter.unusedSectionVars false in
/-- The auxiliary finite-Tor inputs in the displayed diagonal-unit formula.
Source: blueprint def-pur-td-datum, canonical-map paragraph
(blueprint: def-pur-td-datum).
Proof: the finite constant coefficient sheaf is locally constant with finite stalks,
and is flat over itself; in degree zero it has Tor interval [0,0]. For A use
the native finite-coefficient pullback-preservation theorem on p1, the base change
of the separated finite-type map f. For the unit use the canonical monoidal
comparison from the etale tensor unit to the fixed-module tensor unit. -/
theorem diagonal_inputs (A : Ctf P X) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) X (one P X) ∧
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient)
      (pullback f f) ((pull P (pullback.fst f f)).obj A.obj) := by
  constructor
  · exact (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} P.Coefficient) X).prop_of_iso
      (DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso P.Coefficient X)
      (DerivedCategory.constructibleFiniteTor_mapDerivedCategory P.Coefficient
        (Etale.constructibleFiniteTor_tensorUnit P.Coefficient X))
  · exact constructibleFiniteTor_leftDerivedFunctor_upperStar_obj
      (pullback.fst f f) A.property

/-- G_L on the prescribed finite-Tor constructible categories; its morphism action
is the published pullback action tensored with 1_L.
Source: blueprint def-pur-td-datum, induced functor (blueprint: def-pur-td-datum). -/
def functor (L : Ctf P X) : Ctf P Y ⥤ Ctf P X :=
  ObjectProperty.lift _
    (DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} P.Coefficient) Y ⋙ twisted (P := P) f L)
    (fun K ↦ twisted_preserves (P := P) f L K)

/-- The same compact-support functor restricted to Dctf, keeping every ambient morphism.
Source: blueprint def-pur-td-datum, Rf! in the composites (blueprint: def-pur-td-datum). -/
def compactFunctor : Ctf P X ⥤ Ctf P Y :=
  ObjectProperty.lift _
    (DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} P.Coefficient) X ⋙ shriek (P := P) f)
    (fun A ↦ shriek_preserves (P := P) f A)

/-- The projection map for the chosen compactification, inverted at the finite-Tor input.
Source: blueprint def-pur-td-datum, counit projection formula
(blueprint: def-pur-td-datum). -/
def projection (L : Ctf P X) (K : Ctf P Y) :
    ((tensor P Y).obj ((shriek (P := P) f).obj L.obj)).obj K.obj ≅
      (shriek (P := P) f).obj (((tensor P X).obj L.obj).obj ((pull P f).obj K.obj)) :=
  projectionCore P.Coefficient f (compactification (P := P) f)
    L.obj K.obj L.property K.property

/-- The canonical pullback identification along Delta then p1.
Source: blueprint def-pur-td-datum, p1 Delta = id (blueprint: def-pur-td-datum). -/
def diagonalPullback :
    pull P (pullback.fst f f) ⋙ pull P (Etale.TraceDiagonalDatum.diagonal f) ≅ 𝟭 (D P X) :=
  diagonalPullbackCore P.Coefficient f

/-- The first unit isomorphism, in the contraction direction. Projection for Delta,
unit multiplication, the pullback section equation, and compact-support composition
are composed in exactly that order.
Source: blueprint def-pur-td-datum, first unit isomorphism (blueprint: def-pur-td-datum). -/
def diagonalContraction (A : Ctf P X) :
    (shriek₂ (P := P) f).obj (((tensor P (pullback f f)).obj
      ((pull P (pullback.fst f f)).obj A.obj)).obj
        ((push P (Etale.TraceDiagonalDatum.diagonal f)).obj (one P X))) ≅ A.obj :=
  contractionCore P.Coefficient f (compactification (P := P) f) A.obj
    A.property.plusEtaleOrigin (diagonal_inputs (P := P) f A).1
    (diagonal_inputs (P := P) f A).2

/-- The last unit isomorphism: inverse projection for p2, followed by inverse
self-square exchange, tensored with the identity of L.
Source: blueprint def-pur-td-datum, final unit isomorphism (blueprint: def-pur-td-datum). -/
def diagonalExchange (L A : Ctf P X) :
    (shriek₂ (P := P) f).obj (((tensor P (pullback f f)).obj
      ((pull P (pullback.fst f f)).obj A.obj)).obj
        ((pull P (pullback.snd f f)).obj L.obj)) ≅
      (twisted (P := P) f L).obj ((shriek (P := P) f).obj A.obj) :=
  exchangeCore P.Coefficient f (compactification (P := P) f) A.obj L.obj
    A.property L.property (diagonal_inputs (P := P) f A).2

private theorem diagonalContraction_naturality {A A' : Ctf P X} (a : A ⟶ A') :
    (shriek₂ (P := P) f).map (((tensor P (pullback f f)).map
      ((pull P (pullback.fst f f)).map a.hom)).app
        ((push P (Etale.TraceDiagonalDatum.diagonal f)).obj (one P X))) ≫
      (diagonalContraction (P := P) f A').hom =
    (diagonalContraction (P := P) f A).hom ≫ a.hom := by
  exact contractionCore_naturality P.Coefficient f (compactification (P := P) f)
    A.obj A'.obj A.property.plusEtaleOrigin A'.property.plusEtaleOrigin
    (diagonal_inputs (P := P) f A).1 (diagonal_inputs (P := P) f A).2
    (diagonal_inputs (P := P) f A').2 a.hom

private theorem diagonalExchange_naturality (L : Ctf P X)
    {A A' : Ctf P X} (a : A ⟶ A') :
    (shriek₂ (P := P) f).map (((tensor P (pullback f f)).map
      ((pull P (pullback.fst f f)).map a.hom)).app
        ((pull P (pullback.snd f f)).obj L.obj)) ≫
      (diagonalExchange (P := P) f L A').hom =
    (diagonalExchange (P := P) f L A).hom ≫
      ((tensor P X).map ((pull P f).map ((shriek (P := P) f).map a.hom))).app L.obj := by
  exact exchangeCore_naturality P.Coefficient f (compactification (P := P) f)
    A.obj A'.obj L.obj A.property A'.property L.property
    (diagonal_inputs (P := P) f A).2 (diagonal_inputs (P := P) f A').2 a.hom

namespace Datum

variable {f} {L : Ctf P X} {hL : Invertible P L} (d : Datum (P := P) f L hL)

/-- The displayed counit, using inverse projection, canonical signed symmetry,
1_K tensor trace, and the right multiplication constraint.
Source: blueprint def-pur-td-datum, epsilon_K (blueprint: def-pur-td-datum). -/
def counitMap (K : Ctf P Y) :
    (shriek (P := P) f).obj ((twisted (P := P) f L).obj K.obj) ⟶ K.obj :=
  (shriek (P := P) f).map
      (((signedSymmetry (ModuleCat.{u + 1} P.Coefficient) X).hom.app
        ((pull P f).obj K.obj)).app L.obj) ≫
    (projection (P := P) f L K).inv ≫
    (((signedSymmetry (ModuleCat.{u + 1} P.Coefficient) Y).hom.app
      ((shriek (P := P) f).obj L.obj)).app K.obj) ≫
    ((tensor P Y).obj K.obj).map d.trace ≫
    (unitRight (ModuleCat.{u + 1} P.Coefficient) Y K.obj).hom

/-- The unit component, using the specified two canonical isomorphisms and the
image of 1 tensor cl under Rp2!.
Source: blueprint def-pur-td-datum, eta_A (blueprint: def-pur-td-datum). -/
def unitMap (A : Ctf P X) :
    A.obj ⟶ (twisted (P := P) f L).obj ((shriek (P := P) f).obj A.obj) :=
  (diagonalContraction (P := P) f A).inv ≫
    (shriek₂ (P := P) f).map (((tensor P (pullback f f)).obj
      ((pull P (pullback.fst f f)).obj A.obj)).map d.diagonalClass) ≫
    (diagonalExchange (P := P) f L A).hom

/-- Naturality of the counit formula. Source: blueprint def-pur-td-datum,
naturality of epsilon (blueprint: def-pur-td-datum).
Proof: use naturality of the projection transformation, its inverse on Dctf,
the signed symmetry, and right unit constraint. Tensor functoriality commutes
1 tensor trace with a map K to K', since trace is fixed. Composing those
squares gives the displayed equation. -/
theorem counit_naturality {K K' : Ctf P Y} (a : K ⟶ K') :
    (shriek (P := P) f).map ((twisted (P := P) f L).map a.hom) ≫ d.counitMap K' =
      d.counitMap K ≫ a.hom := by
  let S := shriek (P := P) f
  let U := pull P f
  let TX := tensor P X
  let TY := tensor P Y
  let bX := signedSymmetry (ModuleCat.{u + 1} P.Coefficient) X
  let bY := signedSymmetry (ModuleCat.{u + 1} P.Coefficient) Y
  have hX : (TX.map (U.map a.hom)).app L.obj ≫ (bX.hom.app (U.obj K'.obj)).app L.obj =
      (bX.hom.app (U.obj K.obj)).app L.obj ≫ (TX.obj L.obj).map (U.map a.hom) := by
    simpa only [NatTrans.comp_app, Functor.flip_map_app] using
      NatTrans.congr_app (bX.hom.naturality (U.map a.hom)) L.obj
  have hP : S.map ((TX.obj L.obj).map (U.map a.hom)) ≫ (projection f L K').inv =
      (projection f L K).inv ≫ (TY.obj (S.obj L.obj)).map a.hom := by
    apply (Iso.comp_inv_eq _).2
    rw [Category.assoc]
    apply (Iso.eq_inv_comp _).2
    exact (projectionCore_hom_naturality_right P.Coefficient f
      (compactification (P := P) f) L.obj K.obj K'.obj L.property K.property K'.property
      a.hom).symm
  have hY := (bY.hom.app (S.obj L.obj)).naturality a.hom
  simp only [Functor.flip_obj_map] at hY
  have ht := (TY.map a.hom).naturality
    (X := S.obj L.obj) (Y := one P Y) d.trace
  have hu := rightUnitor_naturality a.hom
  change S.map ((TX.map (U.map a.hom)).app L.obj) ≫
      S.map ((bX.hom.app (U.obj K'.obj)).app L.obj) ≫ (projection f L K').inv ≫
      (bY.hom.app (S.obj L.obj)).app K'.obj ≫ (TY.obj K'.obj).map d.trace ≫
      (unitRight (ModuleCat.{u + 1} P.Coefficient) Y K'.obj).hom =
    (S.map ((bX.hom.app (U.obj K.obj)).app L.obj) ≫ (projection f L K).inv ≫
      (bY.hom.app (S.obj L.obj)).app K.obj ≫ (TY.obj K.obj).map d.trace ≫
      (unitRight (ModuleCat.{u + 1} P.Coefficient) Y K.obj).hom) ≫ a.hom
  simp only [Category.assoc]
  rw [← S.map_comp_assoc, hX, S.map_comp, Category.assoc, reassoc_of% hP]
  rw [reassoc_of% hY, ← reassoc_of% ht]
  exact congrArg (fun z ↦ S.map ((bX.hom.app (U.obj K.obj)).app L.obj) ≫
    (projection f L K).inv ≫ (bY.hom.app (S.obj L.obj)).app K.obj ≫
    (TY.obj K.obj).map d.trace ≫ z) hu

/-- Naturality of the unit formula. Source: blueprint def-pur-td-datum,
naturality of eta (blueprint: def-pur-td-datum).
Proof: projection, signed symmetry, the pullback compositor and identity map,
compact-support compositor and identity map, and self-square exchange are natural
transformations. Their inverse components on the full finite-Tor domain are
natural as well. Tensor functoriality commutes p1* a tensor 1 with 1 tensor cl.
Compose these squares in the order in unitMap. -/
theorem unit_naturality {A A' : Ctf P X} (a : A ⟶ A') :
    a.hom ≫ d.unitMap A' =
      d.unitMap A ≫ (twisted (P := P) f L).map ((shriek (P := P) f).map a.hom) := by
  let S₂ := shriek₂ (P := P) f
  let U₁ := pull P (pullback.fst f f)
  let TW := tensor P (pullback f f)
  let B := (push P (Etale.TraceDiagonalDatum.diagonal f)).obj (one P X)
  let B' := (pull P (pullback.snd f f)).obj L.obj
  have hc : a.hom ≫ (diagonalContraction f A').inv =
      (diagonalContraction f A).inv ≫ S₂.map ((TW.map (U₁.map a.hom)).app B) := by
    apply (Iso.comp_inv_eq _).2
    rw [Category.assoc]
    apply (Iso.eq_inv_comp _).2
    exact (diagonalContraction_naturality f a).symm
  have ht := (TW.map (U₁.map a.hom)).naturality (X := B) (Y := B') d.diagonalClass
  have hm := congrArg S₂.map ht.symm
  simp only [Functor.map_comp] at hm
  have he : S₂.map ((TW.map (U₁.map a.hom)).app B') ≫
      (diagonalExchange f L A').hom = (diagonalExchange f L A).hom ≫
        ((tensor P X).map ((pull P f).map ((shriek f).map a.hom))).app L.obj :=
    diagonalExchange_naturality f L a
  change a.hom ≫ (diagonalContraction f A').inv ≫
      S₂.map ((TW.obj (U₁.obj A'.obj)).map d.diagonalClass) ≫
      (diagonalExchange f L A').hom =
    ((diagonalContraction f A).inv ≫ S₂.map ((TW.obj (U₁.obj A.obj)).map d.diagonalClass) ≫
      (diagonalExchange f L A).hom) ≫
        ((tensor P X).map ((pull P f).map ((shriek f).map a.hom))).app L.obj
  simp only [Category.assoc]
  rw [reassoc_of% hc, reassoc_of% hm, he]


/-- The counit as a natural transformation on the full Dctf categories.
Source: blueprint def-pur-td-datum, epsilon (blueprint: def-pur-td-datum). -/
def counit : functor (P := P) f L ⋙ compactFunctor (P := P) f ⟶ 𝟭 (Ctf P Y) where
  app K := ObjectProperty.homMk (d.counitMap K)
  naturality _ _ a := by
    apply ObjectProperty.hom_ext
    exact d.counit_naturality a

/-- The unit as a natural transformation on the full Dctf categories.
Source: blueprint def-pur-td-datum, eta (blueprint: def-pur-td-datum). -/
def unit : 𝟭 (Ctf P X) ⟶ compactFunctor (P := P) f ⋙ functor (P := P) f L where
  app A := ObjectProperty.homMk (d.unitMap A)
  naturality _ _ a := by
    apply ObjectProperty.hom_ext
    exact d.unit_naturality a

/-- Rf! eta followed by epsilon Rf!: a natural endomorphism, without an identity axiom.
Source: blueprint def-pur-td-datum, first triangular composite
(blueprint: def-pur-td-datum). -/
def leftTriangle : compactFunctor (P := P) f ⟶ compactFunctor (P := P) f :=
  (Functor.leftUnitor (compactFunctor (P := P) f)).inv ≫
    Functor.whiskerRight d.unit (compactFunctor (P := P) f) ≫
    (Functor.associator (compactFunctor (P := P) f) (functor (P := P) f L)
      (compactFunctor (P := P) f)).hom ≫
    Functor.whiskerLeft (compactFunctor (P := P) f) d.counit ≫
    (Functor.rightUnitor (compactFunctor (P := P) f)).hom

/-- eta G_L followed by G_L epsilon: the other natural endomorphism.
Source: blueprint def-pur-td-datum, second triangular composite
(blueprint: def-pur-td-datum). -/
def rightTriangle : functor (P := P) f L ⟶ functor (P := P) f L :=
  (Functor.rightUnitor (functor (P := P) f L)).inv ≫
    Functor.whiskerLeft (functor (P := P) f L) d.unit ≫
    (Functor.associator (functor (P := P) f L) (compactFunctor (P := P) f)
      (functor (P := P) f L)).inv ≫
    Functor.whiskerRight d.counit (functor (P := P) f L) ≫
    (Functor.leftUnitor (functor (P := P) f L)).hom

end Datum

end AlgebraicGeometry.ProEtale.FiniteTraceDiagonal
