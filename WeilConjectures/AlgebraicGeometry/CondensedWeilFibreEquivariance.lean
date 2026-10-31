/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedConstantGlobalFrobenius
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.SixFunctors.DerivedConstructibleLowerShriek
public import WeilConjectures.SixFunctors.CondensedCompactSupportCompositionData
public import
WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedLocalFrobenius
public import WeilConjectures.SixFunctors.CondensedIsomorphismCohomologyTransport
import WeilConjectures.AlgebraicGeometry.AdicConstructibilityPredicateComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
import WeilConjectures.SixFunctors.FrobeniusSquareCartesian
public import WeilConjectures.SixFunctors.CondensedOperationComparisons
public import WeilConjectures.AlgebraicGeometry.CondensedConstantExtensionFrobenius

/-! # Frobenius equivariance of compact-support fibre base change

Source: latest blueprint, lem-fd-realness-pushforward.proof.md, Step 1
(blueprint: lem-fd-condensed-weil-fibre-equivariance).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing.WeilFibre

variable (D : WeilConjectures.FiniteFieldDatum.{u})

/-- Geometric base change with its inherited separated finite-type structure.
Source: latest blueprint, fibre identification in Step 1
(blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
abbrev base (T₀ : SepFinType D.k₀) : SepFinType D.k :=
  ⟨D.geometricFiber T₀.obj,
    ⟨inferInstance, inferInstance,
      inferInstanceAs (IsSeparated (pullback.snd T₀.obj.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))⟩⟩

/-- The inherited local finite-type instance of the geometric model.
Source: latest blueprint, Step 1
(blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
instance baseFiniteType (T₀ : SepFinType D.k₀) :
    LocallyOfFiniteType (base D T₀).obj.hom := (base D T₀).property.1

/-- The inherited quasi-compact instance of the geometric model.
Source: latest blueprint, Step 1
(blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
instance baseQuasiCompact (T₀ : SepFinType D.k₀) :
    QuasiCompact (base D T₀).obj.hom := (base D T₀).property.2.1

/-- The inherited separated instance of the geometric model.
Source: latest blueprint, Step 1
(blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
instance baseSeparated (T₀ : SepFinType D.k₀) :
    IsSeparated (base D T₀).obj.hom := (base D T₀).property.2.2

/-- The specified geometric base change of the model morphism.
Source: latest blueprint, fibre identification in Step 1
(blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
def map {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀) : base D X₀ ⟶ base D Y₀ :=
  ObjectProperty.homMk ((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀.hom)

/-- The geometric closed-point lift for the chosen base-compatible residue embedding.
Source: latest blueprint, Step 1 and the local return convention
(blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
abbrev point (Y₀ : SepFinType D.k₀)
    (y : {y : Y₀.obj.left // y ∈ closedPoints Y₀.obj.left})
    (ι : Y₀.obj.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.obj.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :=
  WeilConjectures.localClosedPoint D Y₀.obj y ι hι

/-- The base-changed morphism is separated and of finite type.
Source: latest blueprint, Step 1 (blueprint: lem-fd-condensed-weil-fibre-equivariance).
Proof: a morphism between separated finite-type schemes over a field is separated
and finite type. These properties are preserved by geometric base change. -/
theorem map_properties {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀) :
    IsSeparated (map D f₀).hom.left ∧ LocallyOfFiniteType (map D f₀).hom.left ∧
      QuasiCompact (map D f₀).hom.left := by
  have hs : IsSeparated ((map D f₀).hom.left ≫ (base D Y₀).obj.hom) := by
    rw [(map D f₀).hom.w]
    infer_instance
  have ht : LocallyOfFiniteType ((map D f₀).hom.left ≫ (base D Y₀).obj.hom) := by
    rw [(map D f₀).hom.w]
    infer_instance
  have hq : QuasiCompact ((map D f₀).hom.left ≫ (base D Y₀).obj.hom) := by
    rw [(map D f₀).hom.w]
    infer_instance
  exact ⟨IsSeparated.of_comp (map D f₀).hom.left (base D Y₀).obj.hom,
    locallyOfFiniteType_of_comp (map D f₀).hom.left (base D Y₀).obj.hom,
    QuasiCompact.of_comp (map D f₀).hom.left (base D Y₀).obj.hom⟩

/-- The fibre structure morphism is separated and of finite type.
Source: latest blueprint, Step 1 (blueprint: lem-fd-condensed-weil-fibre-equivariance).
Proof: its structure morphism is the base change of the separated finite-type map
f along z. The three properties follow from map_properties and stability under base change. -/
theorem fibre_properties {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀)
    (z : Spec (.of D.k) ⟶ (base D Y₀).obj.left) :
    IsSeparated (pullback.snd (map D f₀).hom.left z) ∧
      LocallyOfFiniteType (pullback.snd (map D f₀).hom.left z) ∧
        QuasiCompact (pullback.snd (map D f₀).hom.left z) := by
  let := (map_properties D f₀).1
  let := (map_properties D f₀).2.1
  let := (map_properties D f₀).2.2
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The geometric fibre, with its structure map to the geometric point.
Source: latest blueprint, Step 1 (blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
abbrev fibre {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀)
    (z : Spec (.of D.k) ⟶ (base D Y₀).obj.left) : SepFinType D.k :=
  ⟨Over.mk (pullback.snd (map D f₀).hom.left z),
    ⟨(fibre_properties D f₀ z).2.1, (fibre_properties D f₀ z).2.2,
      (fibre_properties D f₀ z).1⟩⟩

/-- The inherited finite-type instance of the geometric fibre.
Source: latest blueprint, Step 1
(blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
instance fibreFiniteType {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀)
    (z : Spec (.of D.k) ⟶ (base D Y₀).obj.left) :
    LocallyOfFiniteType (fibre D f₀ z).obj.hom := (fibre D f₀ z).property.1

/-- The inherited quasi-compact instance of the geometric fibre.
Source: latest blueprint, Step 1
(blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
instance fibreQuasiCompact {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀)
    (z : Spec (.of D.k) ⟶ (base D Y₀).obj.left) :
    QuasiCompact (fibre D f₀ z).obj.hom := (fibre D f₀ z).property.2.1

/-- The inherited separated instance of the geometric fibre.
Source: latest blueprint, Step 1
(blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
instance fibreSeparated {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀)
    (z : Spec (.of D.k) ⟶ (base D Y₀).obj.left) :
    IsSeparated (fibre D f₀ z).obj.hom := (fibre D f₀ z).property.2.2

/-- The geometric fibre projection to X.
Source: latest blueprint, Step 1 (blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
abbrev inclusion {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀)
    (z : Spec (.of D.k) ⟶ (base D Y₀).obj.left) :=
  pullback.fst (map D f₀).hom.left z

/-- The geometric Frobenius of the specified model.
Source: latest blueprint, Step 1 (blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
abbrev frobenius (T₀ : SepFinType D.k₀) := StrictWeil.modelFrobenius D T₀.obj

/-- Frobenius commutes with the base-changed map, hence its square is Cartesian.
Source: latest blueprint, Step 1 (blueprint: lem-fd-condensed-weil-fibre-equivariance).
Proof: compare both projections to X₀ and Spec k, as in
lem-weil-frobenius-square-cartesian; the horizontal arrows are isomorphisms. -/
theorem frobenius_square {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀) :
    IsPullback (frobenius D X₀).hom (map D f₀).hom.left
      (map D f₀).hom.left (frobenius D Y₀).hom := by
  exact (D.frobenius_square_cartesian X₀.obj Y₀.obj f₀.hom).2.2.2.2.2.1

open CohomologyTransport

variable (l : ℕ) [Fact l.Prime]

/-- The underlying total-derived Weil isomorphism, with the canonical exact comparison.
Source: latest blueprint, theta in Step 1
(blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
def theta (X₀ : SepFinType D.k₀)
    (K : StrictWeil.Complex (Profinite.padicAlgClRingObj l) (frobenius D X₀)) :
    (L (Profinite.padicAlgClRingObj l) (frobenius D X₀).hom).obj K.carrier.obj ≅
      K.carrier.obj :=
  (leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj l)
    (frobenius D X₀).hom).app K.carrier.obj ≪≫
    (ObjectProperty.ι _).mapIso K.str

/-- The normalized Frobenius structure on compact-support direct image.
Source: latest blueprint, Step 1, Rf!(theta) e_g
(blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
@[irreducible] def pushTheta (H : CompactSupportComposition.CoherentData
  (Profinite.padicAlgClRingObj l) D.k)
    {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀)
    (K : StrictWeil.Complex (Profinite.padicAlgClRingObj l) (frobenius D X₀)) :
    (L (Profinite.padicAlgClRingObj l) (frobenius D Y₀).hom).obj
      ((C (Profinite.padicAlgClRingObj l)
      (compactificationOverField (map D f₀).hom)).obj K.carrier.obj) ≅
      ((C (Profinite.padicAlgClRingObj l)
      (compactificationOverField (map D f₀).hom)).obj K.carrier.obj) :=
  (H.exchange (X := base D X₀) (Y := base D Y₀)
    (X' := base D X₀) (Y' := base D Y₀) (f := map D f₀) (f' := map D f₀)
    (frobenius_square D f₀) (compactificationOverField (map D f₀).hom)
    (compactificationOverField (map D f₀).hom)).app
      ((OperationComparisons.toLocalizing
        (CommMon.mk (Profinite.padicAlgClRingObj l)) (base D X₀).obj.left).obj K.carrier) ≪≫
    (C (Profinite.padicAlgClRingObj l)
      (compactificationOverField (map D f₀).hom)).mapIso (theta D l X₀ K)

/-- The structure map from the fibre to the geometric point.
Source: latest blueprint, Step 1 (blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
abbrev projection {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀)
    (z : Spec (.of D.k) ⟶ (base D Y₀).obj.left) :
    fibre D f₀ z ⟶ SepFinType.mk (CondensedRing.point D.k) :=
  ObjectProperty.homMk (Over.homMk (fibre D f₀ z).obj.hom (Category.comp_id _))

/-- Quasi-compactness of the literal fibre projection, inherited from its finite-type model.
Source: latest blueprint, fibre structure map in Step 1
(blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
instance projectionQuasiCompact {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀)
    (z : Spec (.of D.k) ⟶ (base D Y₀).obj.left) :
    QuasiCompact (projection D f₀ z).hom.left :=
  fibreQuasiCompact D f₀ z

/-- The canonical geometric fibre exchange, including its compactification comparison.
Source: latest blueprint, Step 1, beta_y
(blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
@[irreducible] def beta (H : CompactSupportComposition.CoherentData (Profinite.padicAlgClRingObj
  l) D.k)
    {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀)
    (z : Spec (.of D.k) ⟶ (base D Y₀).obj.left)
    (K : StrictWeil.Complex (Profinite.padicAlgClRingObj l) (frobenius D X₀)) :
    (L (Profinite.padicAlgClRingObj l) z).obj ((C (Profinite.padicAlgClRingObj l)
      (compactificationOverField (map D f₀).hom)).obj K.carrier.obj) ≅
      (C (Profinite.padicAlgClRingObj l)
        (compactificationOverField (projection D f₀ z).hom)).obj
          ((L (Profinite.padicAlgClRingObj l) (inclusion D f₀ z)).obj K.carrier.obj) :=
  (H.exchange (X := base D X₀) (Y := base D Y₀)
    (X' := fibre D f₀ z) (Y' := SepFinType.mk (CondensedRing.point D.k))
    (f := map D f₀) (f' := projection D f₀ z)
    (a := inclusion D f₀ z) (v := z)
    (IsPullback.of_hasPullback (map D f₀).hom.left z)
    (compactificationOverField (map D f₀).hom)
    (compactificationOverField (projection D f₀ z).hom)).app
      ((OperationComparisons.toLocalizing
        (CommMon.mk (Profinite.padicAlgClRingObj l)) (base D X₀).obj.left).obj K.carrier)

variable {X₀ Y₀ : SepFinType D.k₀} (f₀ : X₀ ⟶ Y₀)
  (y : {y : Y₀.obj.left // y ∈ closedPoints Y₀.obj.left})
  (ι : Y₀.obj.left.residueField y.val →+* D.k)
  (hι : ι.comp (Y₀.obj.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)

/-- The residue-degree index in the published positive-power convention.
Source: latest blueprint, d=[kappa(y):k0] in Step 1
(blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
abbrev index := WeilConjectures.localClosedPointDegree D Y₀.obj y - 1

/-- The unique fibre automorphism induced by the d-th geometric Frobenius on both
projections. It is the geometric Frobenius of the residue-field model C₀.
Source: latest blueprint, Step 1 (blueprint: lem-fd-condensed-weil-fibre-equivariance).
Proof: induction on the power index gives the d-th power of the Frobenius square,
and the closed-point return equation gives the base compatibility. The pullback map of
the three power automorphisms is an isomorphism; its projection equations are the
pullback lift equations, and uniqueness follows from pullback.hom_ext. -/
theorem fibreFrobenius_existsUnique :
    ∃! h : Aut (fibre D f₀ (point D Y₀ y ι hι)).obj.left,
      (h.hom ≫ inclusion D f₀ (point D Y₀ y ι hι) =
        inclusion D f₀ (point D Y₀ y ι hι) ≫
          WeilConjectures.localPositivePower (frobenius D X₀).hom (index D y)) ∧
      (h.hom ≫ (projection D f₀ (point D Y₀ y ι hι)).hom.left =
        (projection D f₀ (point D Y₀ y ι hι)).hom.left ≫
          WeilConjectures.localPositivePower (WeilConjectures.frobeniusPointIso D).hom
            (index D y)) := by
  have hnat : ∀ n : ℕ,
      WeilConjectures.localPositivePower (frobenius D X₀).hom n ≫ (map D f₀).hom.left =
        (map D f₀).hom.left ≫
          WeilConjectures.localPositivePower (frobenius D Y₀).hom n := by
    intro n
    induction n with
    | zero => exact (frobenius_square D f₀).w
    | succ n ih =>
      simp only [WeilConjectures.localPositivePower, Category.assoc]
      rw [(frobenius_square D f₀).w, ← Category.assoc, ih, Category.assoc]
  let n := index D y
  let G := WeilConjectures.CondensedWeil.positiveAut (frobenius D X₀) n
  let B := WeilConjectures.CondensedWeil.positiveAut (frobenius D Y₀) n
  let b := WeilConjectures.CondensedWeil.positiveAut
    (WeilConjectures.frobeniusPointIso D) n
  let z := point D Y₀ y ι hι
  have hz : z ≫ B.hom = b.hom ≫ z :=
    WeilConjectures.localClosedPoint_return D Y₀.obj y ι hι
  let h : Aut (fibre D f₀ z).obj.left :=
    asIso (pullback.map (map D f₀).hom.left z (map D f₀).hom.left z
      G.hom b.hom B.hom (hnat n).symm hz)
  have hs :
      (h.hom ≫ inclusion D f₀ z = inclusion D f₀ z ≫ G.hom) ∧
      (h.hom ≫ (projection D f₀ z).hom.left =
        (projection D f₀ z).hom.left ≫ b.hom) := by
    constructor
    · exact pullback.lift_fst _ _ _
    · exact pullback.lift_snd _ _ _
  refine ⟨h, hs, ?_⟩
  intro h' hs'
  apply Iso.ext
  apply pullback.hom_ext
  · exact hs'.1.trans hs.1.symm
  · exact hs'.2.trans hs.2.symm

/-- The specified residue-field geometric Frobenius, uniquely fixed by its projections.
Source: latest blueprint, Step 1 (blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
def fibreFrobenius : Aut (fibre D f₀ (point D Y₀ y ι hι)).obj.left :=
  (fibreFrobenius_existsUnique D f₀ y ι hι).exists.choose

/-- The restricted d-fold Weil structure, using the canonical square comparison.
Source: latest blueprint, Step 1, lambda=I(Theta) rho_i
(blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
@[irreducible] def restrictedTheta
    (K : StrictWeil.Complex (Profinite.padicAlgClRingObj l) (frobenius D X₀)) :
    (L (Profinite.padicAlgClRingObj l) (fibreFrobenius D f₀ y ι hι).hom).obj
      ((L (Profinite.padicAlgClRingObj l)
        (inclusion D f₀ (point D Y₀ y ι hι))).obj K.carrier.obj)
        ≅ ((L (Profinite.padicAlgClRingObj l) (inclusion D f₀ (point D Y₀ y ι hι))).obj
        K.carrier.obj) :=
  (pullbackSquareComparison (Profinite.padicAlgClRingObj l)
    (CommSq.mk (fibreFrobenius_existsUnique D f₀ y ι hι).exists.choose_spec.1)).symm.app
      K.carrier.obj ≪≫
    (L (Profinite.padicAlgClRingObj l) (inclusion D f₀ (point D Y₀ y ι hι))).mapIso
      (WeilConjectures.CondensedModule.derivedIterate (Profinite.padicAlgClRingObj l)
        (frobenius D X₀).hom K.carrier.obj (theta D l X₀ K) (index D y))

/-- The d-fold stalk structure, pulled from the specified structure on Rf!K.
Source: latest blueprint, Step 1, psi_y
(blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
@[irreducible] def stalkTheta
    (H : CompactSupportComposition.CoherentData (Profinite.padicAlgClRingObj l) D.k)
    (K : StrictWeil.Complex (Profinite.padicAlgClRingObj l) (frobenius D X₀)) :
    (L (Profinite.padicAlgClRingObj l) (WeilConjectures.localPositivePower
      (WeilConjectures.frobeniusPointIso D).hom
      (index D y))).obj
      ((L (Profinite.padicAlgClRingObj l) (point D Y₀ y ι hι)).obj ((C
        (Profinite.padicAlgClRingObj l)
      (compactificationOverField (map D f₀).hom)).obj K.carrier.obj)) ≅ ((L
        (Profinite.padicAlgClRingObj l) (point D Y₀ y ι hι)).obj
          ((C (Profinite.padicAlgClRingObj l)
      (compactificationOverField (map D f₀).hom)).obj K.carrier.obj)) :=
  (pullbackSquareComparison (Profinite.padicAlgClRingObj l)
    (CommSq.mk (WeilConjectures.localClosedPoint_return D Y₀.obj y ι hι).symm)).symm.app
      ((C (Profinite.padicAlgClRingObj l)
        (compactificationOverField (map D f₀).hom)).obj K.carrier.obj) ≪≫
    (L (Profinite.padicAlgClRingObj l) (point D Y₀ y ι hι)).mapIso
      (WeilConjectures.CondensedModule.derivedIterate (Profinite.padicAlgClRingObj l)
        (frobenius D Y₀).hom _ (pushTheta D l H f₀ K) (index D y))

/-- Compact-support pushforward of the restricted d-fold structure.
Source: latest blueprint, Step 1, psi_C
(blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
@[irreducible] def fibreTheta
    (H : CompactSupportComposition.CoherentData (Profinite.padicAlgClRingObj l) D.k)
    (K : StrictWeil.Complex (Profinite.padicAlgClRingObj l) (frobenius D X₀)) :
    (L (Profinite.padicAlgClRingObj l) (WeilConjectures.localPositivePower
      (WeilConjectures.frobeniusPointIso D).hom
      (index D y))).obj
      ((C (Profinite.padicAlgClRingObj l)
      (compactificationOverField (projection D f₀ (point D Y₀ y ι hι)).hom)).obj
        ((L (Profinite.padicAlgClRingObj l) (inclusion D f₀ (point D Y₀ y ι hι))).obj
          K.carrier.obj)) ≅ ((C (Profinite.padicAlgClRingObj l)
      (compactificationOverField (projection D f₀ (point D Y₀ y ι hι)).hom)).obj
        ((L (Profinite.padicAlgClRingObj l) (inclusion D f₀ (point D Y₀ y ι hι))).obj
          K.carrier.obj)) :=
  (H.exchange (X := fibre D f₀ (point D Y₀ y ι hι))
    (Y := SepFinType.mk (CondensedRing.point D.k))
    (X' := fibre D f₀ (point D Y₀ y ι hι))
    (Y' := SepFinType.mk (CondensedRing.point D.k))
    (f := projection D f₀ (point D Y₀ y ι hι))
    (f' := projection D f₀ (point D Y₀ y ι hι))
    (a := (fibreFrobenius D f₀ y ι hι).hom)
    (v := (WeilConjectures.CondensedWeil.positiveAut
      (WeilConjectures.frobeniusPointIso D) (index D y)).hom)
    (IsPullback.of_horiz_isIso
      (CommSq.mk (fibreFrobenius_existsUnique D f₀ y ι hι).exists.choose_spec.2))
    (compactificationOverField (projection D f₀ (point D Y₀ y ι hι)).hom)
    (compactificationOverField (projection D f₀ (point D Y₀ y ι hι)).hom)).app
      ((OperationComparisons.toLocalizing (CommMon.mk (Profinite.padicAlgClRingObj l))
        (fibre D f₀ (point D Y₀ y ι hι)).obj.left).obj
          ((OperationComparisons.pull (Λ := CommMon.mk (Profinite.padicAlgClRingObj l))
            H (fibre D f₀ (point D Y₀ y ι hι)) (base D X₀)
            (inclusion D f₀ (point D Y₀ y ι hι))).obj K.carrier)) ≪≫
    (C (Profinite.padicAlgClRingObj l)
      (compactificationOverField (projection D f₀ (point D Y₀ y ι hι)).hom)).mapIso
        (restrictedTheta D l f₀ y ι hι K)

/-- Terminal sections of the canonical base-change isomorphism.
Source: latest blueprint, Step 1, bar-beta
(blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
@[irreducible] def scalarBeta
    (H : CompactSupportComposition.CoherentData (Profinite.padicAlgClRingObj l) D.k)
    (K : StrictWeil.Complex (Profinite.padicAlgClRingObj l) (frobenius D X₀)) :
    (Γ (Profinite.padicAlgClRingObj l) (Spec (.of D.k))).obj ((L (Profinite.padicAlgClRingObj l)
      (point D Y₀ y ι hι)).obj ((C (Profinite.padicAlgClRingObj l)
      (compactificationOverField (map D f₀).hom)).obj K.carrier.obj)) ≅
      (Γ (Profinite.padicAlgClRingObj l) (Spec (.of D.k))).obj ((C (Profinite.padicAlgClRingObj l)
      (compactificationOverField (projection D f₀ (point D Y₀ y ι hι)).hom)).obj
        ((L (Profinite.padicAlgClRingObj l) (inclusion D f₀ (point D Y₀ y ι hι))).obj
          K.carrier.obj)) :=
  (Γ (Profinite.padicAlgClRingObj l) (Spec (.of D.k))).mapIso
    (beta D l H f₀ (point D Y₀ y ι hι) K)

/-- The closed-point return operator after terminal reparametrization by g_s^d.
Source: latest blueprint, Step 1, F_y=Gamma(psi_y) iota
(blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
@[irreducible] def stalkOperator
    (H : CompactSupportComposition.CoherentData (Profinite.padicAlgClRingObj l) D.k)
    (K : StrictWeil.Complex (Profinite.padicAlgClRingObj l) (frobenius D X₀)) :
    End ((Γ (Profinite.padicAlgClRingObj l) (Spec (.of D.k))).obj ((L (Profinite.padicAlgClRingObj
      l) (point D Y₀ y ι hι)).obj ((C (Profinite.padicAlgClRingObj l)
      (compactificationOverField (map D f₀).hom)).obj K.carrier.obj))) :=
  WeilConjectures.CondensedModule.derivedOperator (Profinite.padicAlgClRingObj l) D
    (frobenius D Y₀).hom
    ((C (Profinite.padicAlgClRingObj l)
      (compactificationOverField (map D f₀).hom)).obj K.carrier.obj)
    (pushTheta D l H f₀ K) (point D Y₀ y ι hι) (index D y)
    (WeilConjectures.localClosedPoint_return D Y₀.obj y ι hι)

/-- Compact-support geometric Frobenius over the residue field, after reparametrization.
Source: latest blueprint, Step 1, F_C=Gamma(psi_C) iota
(blueprint: lem-fd-condensed-weil-fibre-equivariance). -/
@[irreducible] def fibreOperator
    (H : CompactSupportComposition.CoherentData (Profinite.padicAlgClRingObj l) D.k)
    (K : StrictWeil.Complex (Profinite.padicAlgClRingObj l) (frobenius D X₀)) :
    End ((Γ (Profinite.padicAlgClRingObj l) (Spec (.of D.k))).obj ((C (Profinite.padicAlgClRingObj
      l)
      (compactificationOverField (projection D f₀ (point D Y₀ y ι hι)).hom)).obj
        ((L (Profinite.padicAlgClRingObj l) (inclusion D f₀ (point D Y₀ y ι hι))).obj
          K.carrier.obj))) :=
  End.of ((insertion (Profinite.padicAlgClRingObj l)
    (WeilConjectures.localPositivePower (WeilConjectures.frobeniusPointIso D).hom
      (index D y))).hom.app ((C (Profinite.padicAlgClRingObj l)
      (compactificationOverField (projection D f₀ (point D Y₀ y ι hι)).hom)).obj
        ((L (Profinite.padicAlgClRingObj l)
          (inclusion D f₀ (point D Y₀ y ι hι))).obj K.carrier.obj)) ≫
    (Γ (Profinite.padicAlgClRingObj l) (Spec (.of D.k))).map
      (fibreTheta D l f₀ y ι hι H K).hom)

/-- The restricted complex belongs to the same ordinary bounded constructible category.
Source: latest blueprint, Step 1 (blueprint: lem-fd-condensed-weil-fibre-equivariance).
Proof: pull back the finite constant local models and their stratifications along i.
Exact pullback commutes with cohomology and preserves its bounded interval. For the
field coefficient, the recorded comparison identifies constant-model constructibility
with the boundedConstructible predicate. No point or nonzero object is required. -/
theorem restricted_bounded
    (K : StrictWeil.Complex (Profinite.padicAlgClRingObj l) (frobenius D X₀)) :
    boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj l)
        (fibre D f₀ (point D Y₀ y ι hι)).obj.left)
      ((L (Profinite.padicAlgClRingObj l)
        (inclusion D f₀ (point D Y₀ y ι hι))).obj K.carrier.obj) := by
  let Λ := Profinite.padicAlgClRingObj.{u} l
  let a := (base D X₀).obj.hom
  let : IsNoetherian (base D X₀).obj.left :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian a
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace a }
  apply boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ
  rw [(adicConstructibilityPredicateComparison l (base D X₀).obj.left Λ
    (.algebraicClosure)).2]
  exact K.carrier.property.1

/-- The fibre operator is the specified global geometric Frobenius over kappa(y),
using the actual normalized compact transport of the global definition.
Source: latest blueprint, Step 1 (blueprint: lem-fd-condensed-weil-fibre-equivariance).
Proof: the projection equations identify the fibre automorphism with inverse arithmetic
Frobenius for the q^d-element residue field. The proper/open normalization of H.exchange
and the refinement normalization of P compare the same compactification maps. Their
comparison cocycle therefore identifies the exchanges. Apply insertion, then the
compact-support image of restrictedTheta, which is exactly the displayed global composite. -/
theorem fibreOperator_eq_compact (_hEll : l ≠ D.p)
    (H : CompactSupportComposition.CoherentData (Profinite.padicAlgClRingObj l) D.k)
    (P : {S : CompactData (Profinite.padicAlgClRingObj l) (Spec (.of D.k)) //
      Laws (Profinite.padicAlgClRingObj l) S})
    (K : StrictWeil.Complex (Profinite.padicAlgClRingObj l) (frobenius D X₀)) :
    fibreOperator D l f₀ y ι hι H K =
      WeilConjectures.CondensedConstant.globalCompact (Profinite.padicAlgClRingObj l) D.k P
        (projection D f₀ (point D Y₀ y ι hι)).hom.left
        (compactificationOverField (projection D f₀ (point D Y₀ y ι hι)).hom)
        (fibreFrobenius D f₀ y ι hι).hom
        (WeilConjectures.CondensedWeil.positiveAut
          (WeilConjectures.frobeniusPointIso D) (index D y)).hom
        (fibreFrobenius_existsUnique D f₀ y ι hι).exists.choose_spec.2
        ⟨(L (Profinite.padicAlgClRingObj l)
          (inclusion D f₀ (point D Y₀ y ι hι))).obj K.carrier.obj,
            restricted_bounded D l f₀ y ι hι K⟩
        (restrictedTheta D l f₀ y ι hι K) := by
  sorry

/-- The canonical fibre base-change map is an isomorphism of the specified d-fold
Weil pairs, and intertwines the terminal-section operators and every positive power
in every cohomological degree.

Source: latest blueprint, lem-fd-realness-pushforward.proof.md, Step 1
(blueprint: lem-fd-condensed-weil-fibre-equivariance).

Proof, following the seven DAG steps:
1. The closed-point return identity identifies g_Y^d ybar with ybar g_s^d.
The unique q^d-element subfield makes the induced fibre automorphism geometric
Frobenius over kappa(y). Both projection squares commute and are Cartesian.
2. Use det-thm-sfb-shriek-base-change on the k-linear fibre square. Proper exchange,
open extension, and the normalized compactification comparison identify beta with
sk-thm-sf-comp-composition. The semilinear squares use the native isomorphism exchange.
3. Iterate theta with lem-fix-condensed-pullback-coherence. Successive exchange pasting
from lem-pur-condensed-operation-comparisons identifies the d-fold direct-image structure
with pushforward of theta^(d), followed by the exchange for g^d.
4. Apply the isomorphism-cube equation of lem-fix-condensed-compactification-reindexing
to the fibre square, including its non-isomorphic point map, and descend through the
canonical compactification comparisons. This equates the two routes before theta.
5. Naturality of beta with respect to theta^(d) inserts the Weil map on both routes.
The resulting equation is precisely stalkTheta followed by beta = Lg_s^(d)* beta
followed by fibreTheta, the morphism-of-pairs condition.
6. Apply exact terminal sections. Naturality of the specified insertion along g_s^d
turns that equation into scalar intertwining. The normalized compact exchange identifies
the fibre operator with the transport-then-Weil-map global geometric Frobenius composite.
7. Induction gives every positive power; apply the homology functor in any integer
degree. Exact terminal sections identify these with the stalk cohomology operators.
Every construction also applies to K=0 and the empty fibre, where the same equations
are between the zero objects forced by base change. -/
theorem condensed_weil_fibre_equivariance (_hEll : l ≠ D.p)
    (H : CompactSupportComposition.CoherentData (Profinite.padicAlgClRingObj l) D.k)
    (K : StrictWeil.Complex (Profinite.padicAlgClRingObj l) (frobenius D X₀)) :
    (stalkTheta D l f₀ y ι hι H K).hom ≫
        (beta D l H f₀ (point D Y₀ y ι hι) K).hom =
      (L (Profinite.padicAlgClRingObj l)
        (WeilConjectures.localPositivePower (WeilConjectures.frobeniusPointIso D).hom
          (index D y))).map (beta D l H f₀ (point D Y₀ y ι hι) K).hom ≫
        (fibreTheta D l f₀ y ι hι H K).hom ∧
    (stalkOperator D l f₀ y ι hι H K ≫ (scalarBeta D l f₀ y ι hι H K).hom =
      (scalarBeta D l f₀ y ι hι H K).hom ≫ fibreOperator D l f₀ y ι hι H K) ∧
    (∀ (m : ℕ), 1 ≤ m →
      (stalkOperator D l f₀ y ι hι H K ^ m) ≫ (scalarBeta D l f₀ y ι hι H K).hom =
        (scalarBeta D l f₀ y ι hι H K).hom ≫ (fibreOperator D l f₀ y ι hι H K ^ m)) ∧
    (∀ (j : ℤ) (m : ℕ), 1 ≤ m →
      (WeilConjectures.CondensedModule.derivedScalarCohomology
        (Profinite.padicAlgClRingObj.{u} l) j).map (stalkOperator D l f₀ y ι hι H K ^ m) ≫
          (WeilConjectures.CondensedModule.derivedScalarCohomology
        (Profinite.padicAlgClRingObj.{u} l) j).map (scalarBeta D l f₀ y ι hι H K).hom =
        (WeilConjectures.CondensedModule.derivedScalarCohomology
        (Profinite.padicAlgClRingObj.{u} l) j).map (scalarBeta D l f₀ y ι hι H K).hom ≫
          (WeilConjectures.CondensedModule.derivedScalarCohomology
        (Profinite.padicAlgClRingObj.{u} l) j).map (fibreOperator D l f₀ y ι hι H K ^ m)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.WeilFibre
