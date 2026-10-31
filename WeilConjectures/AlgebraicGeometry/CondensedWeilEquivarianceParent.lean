/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.Transport
public import WeilConjectures.SixFunctors.ScalarSixExceptional
public import WeilConjectures.SixFunctors.CondensedCompactSupportCompositionData
public import WeilConjectures.SixFunctors.CondensedFrobeniusComparisonCoherence
import WeilConjectures.SixFunctors.FrobeniusSquareCartesian
import WeilConjectures.DeligneLaumon.CondensedLinePullCoherence

/-! # The condensed realization of the three purity equivariance squares

Source: latest blueprint, sec-six-functors/sk-thm-sf-package,
thm-pur-weil-equivariance-of-purity-and-trace.md, order 3546, all three squares.
This repairs the recorded interface: the old IntegralClause/RationalClause/CommonClause
use completed systems, localization and common-stage pairs. Here all four coefficients
use the ordinary derived internal-module category and its recorded Dctf subcategory.
(blueprint: thm-pur-weil-equivariance-of-purity-and-trace).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
universe u

attribute [local irreducible] DerivedCategory CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open CompactSupportComposition
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace WeilConjectures.PurityWeil.Condensed

variable (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
  (hEll : ell ≠ D.p)

/-- The normalized family is determined, not merely an arbitrary existing family.
Source: sk-thm-purity-transport, canonical integration normalization and uniqueness;
parent theorem order 3546, canonical normalized purity
(blueprint: thm-pur-weil-equivariance-of-purity-and-trace).
Proof: smooth_purity_transport supplies existence with all five properties. For
uniqueness, compare the finite integration counits locally on smooth charts.
The affine-line normalization and composition give affine-space integration;
Cartesian base change and etale descent identify the counits on every smooth chart.
Finite scalar compatibility identifies the integral, rational and closure counits
with those same normalized maps. Separated compactification descent identifies
the global counits. An adjunction with the fixed left and right functors is
determined by its counit; the membership fields are proof-irrelevant. Apply
function extensionality over the coefficient and geometric indices. -/
theorem existsUniqueNormalizedFamily :
    ∃! a : AdjunctionFamily ell D,
      BrownComparison ell D a ∧ ScalarCompatible ell D a ∧
        BaseChangeCompatible ell D a ∧ CompositionCompatible ell D hEll a ∧
          AffineNormalized ell D a := by
  sorry

/-- The normalized adjunction family of the recorded smooth-purity theorem.
Its maps are fixed by integration, scalar compatibility and the Brown counit
universal property, rather than by a bare existence of isomorphisms.
Source: sk-thm-purity-transport, normalized counit and uniqueness clauses
(blueprint: thm-pur-weil-equivariance-of-purity-and-trace). -/
def normalizedFamily : AdjunctionFamily ell D :=
  (existsUniqueNormalizedFamily ell D hEll).choose

/-- The recorded normalized coherent data are unique: proper/open normalization
and dense refinements determine every map; membership and laws are proof fields.
Source: sk-thm-sf-comp-composition, canonicity, and CoherentData
(blueprint: thm-pur-weil-equivariance-of-purity-and-trace).
Proof: coherentData_exists gives existence at the four admissible coefficients.
Refinement cancellation fixes comparison, the inverse open-adjunction mate fixes
openIso, and comp_normalized and exchange_normalized fix comp and exchange.
Independence extends these equalities to all compactification models. Apply
function extensionality and proof irrelevance to identify the whole record. -/
theorem coefficientCoherent_existsUnique (_hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (c : Coefficient ell)
    (_hc : IsPurityFrobeniusCoefficient ell E (c.bundled.{u} ell)) :
    ∃! H : CompactSupportComposition.CoherentData (c.obj.{u} ell) D.k, True := by
  sorry

/-- The canonical normalized support system in the published direct-data interface.
Its complete normalization laws fix its maps; no arbitrary isomorphism is chosen.
Source: sk-thm-sf-comp-composition
(blueprint: thm-pur-weil-equivariance-of-purity-and-trace). -/
def coefficientCoherent (_hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (c : Coefficient ell)
    (hc : IsPurityFrobeniusCoefficient ell E (c.bundled.{u} ell)) :
    CompactSupportComposition.CoherentData (c.obj.{u} ell) D.k :=
  (coefficientCoherent_existsUnique ell D _hEll E c hc).choose

-- Extract a normalized compositor without unfolding its large remaining coherence proof.
/-- The normalized support compositor, projected from the recorded coherent system.
Source: sk-thm-sf-comp-composition, proper/open normalization
(blueprint: thm-pur-weil-equivariance-of-purity-and-trace). -/
@[irreducible] def supportComposition
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] (h : CompactSupportComposition.CoherentData Λ D.k)
    {X Y Z : SepFinType D.k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f.hom.left ≫ g.hom.left)) :
    (localizingClosureProEtale Λ X.obj.left).ι ⋙
        (rightDerivedLowerShriekOfCompactification Λ cf ⋙
          rightDerivedLowerShriekOfCompactification Λ cg) ≅
      (localizingClosureProEtale Λ X.obj.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ cfg :=
  h.comp f g cf cg cfg

-- The proof is a projection of one large simultaneous coherence assertion.
/-- Membership for actual derived pullback, also along semilinear maps.
Source: sk-thm-sf-comp-composition, arbitrary pullback preservation.
This is the pullback_preserves proof field of the same CoherentData record;
its two conclusions are exactly localizing and Dctf preservation.
(blueprint: thm-pur-weil-equivariance-of-purity-and-trace). -/
abbrev pullPreserves
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] (h : CompactSupportComposition.CoherentData Λ D.k)
    (X Y : SepFinType D.k) (v : X.obj.left ⟶ Y.obj.left) :
    (∀ K, localizingClosureProEtale Λ Y.obj.left K →
      localizingClosureProEtale Λ X.obj.left ((actualPull Λ v).obj K)) ∧
    (∀ K, (constantModelBoundedConstructible Λ Y.obj.left K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      constantModelBoundedConstructible Λ X.obj.left ((actualPull Λ v).obj K) ∧
        DerivedCategory.finiteTorAmplitude _ ((actualPull Λ v).obj K)) :=
  h.pullback_preserves X Y v

-- The normalized exchange is a projection of the same coherent comparison system.
/-- The canonical support exchange, fixed by its proper/open and refinement equations.
Source: sk-thm-sf-comp-composition, exchange normalization
(blueprint: thm-pur-weil-equivariance-of-purity-and-trace). -/
@[irreducible] def supportExchange
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] (h : CompactSupportComposition.CoherentData Λ D.k)
    {X Y X' Y' : SepFinType D.k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X'.obj.left ⟶ X.obj.left} {v : Y'.obj.left ⟶ Y.obj.left}
    (sq : IsPullback a f'.hom.left f.hom.left v)
    (cf : Compactification f.hom.left) (cf' : Compactification f'.hom.left) :
    (localizingClosureProEtale Λ X.obj.left).ι ⋙
        (rightDerivedLowerShriekOfCompactification Λ cf ⋙ actualPull Λ v) ≅
      (localizingClosureProEtale Λ X.obj.left).ι ⋙
        (actualPull Λ a ⋙ rightDerivedLowerShriekOfCompactification Λ cf') :=
  h.exchange sq cf cf'

/-- Natural purity at an arbitrary smooth geometric index, through the same
normalized adjunction family used by the repaired parent theorem.
Source: sk-thm-purity-transport, unique counit-compatible gamma
(blueprint: thm-pur-weil-equivariance-of-purity-and-trace). -/
def canonicalPurity (c : Coefficient ell) (s : SmoothDatum D)
    (R : ScalarExceptionalAdjoint (c.bundled.{u} ell) s.compactification) :
    source ell c s.map s.dim (normalizedFamily ell D hEll c s).source_closed ≅ R.upper :=
  Adjunction.rightAdjointUniq (normalizedFamily ell D hEll c s).adjunction
    R.restrictedAdjunction

variable (E : PadicAlgCl.FiniteIntermediateField ell)
  (c : Coefficient ell) (hc : IsPurityFrobeniusCoefficient ell E (c.bundled.{u} ell))

/-- The actual derived pullback restricted to Dctf. Only its membership proof is supplied
by the coherent system. Source: the parent theorem, geometric pullback
(blueprint: thm-pur-weil-equivariance-of-purity-and-trace). -/
def pullCtf (X Y : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (v : X.left ⟶ Y.left) : c.ctf ell Y.left ⥤ c.ctf ell X.left :=
  (property ell c X.left).lift
    ((property ell c Y.left).ι ⋙ actualPull (c.obj ell) v)
    (fun K ↦ (pullPreserves D (coefficientCoherent ell D hEll E c hc)
      (SepFinType.mk X) (SepFinType.mk Y) v).2 K.obj K.property)

/-- Finite-type geometry of the recorded base change. Source: the standing model
hypotheses (blueprint: thm-pur-weil-equivariance-of-purity-and-trace). -/
instance fiberFinite (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom] :
    LocallyOfFiniteType (D.purityFrobeniusFiber T₀).hom := by
  change LocallyOfFiniteType (pullback.snd T₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
  infer_instance

/-- Quasi-compactness survives the recorded base change. Source: standing model
hypotheses (blueprint: thm-pur-weil-equivariance-of-purity-and-trace). -/
instance fiberQuasiCompact (T₀ : Over (Spec (.of D.k₀))) [QuasiCompact T₀.hom] :
    QuasiCompact (D.purityFrobeniusFiber T₀).hom := by
  change QuasiCompact (pullback.snd T₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
  infer_instance

/-- Separatedness survives the recorded base change. Source: standing model
hypotheses (blueprint: thm-pur-weil-equivariance-of-purity-and-trace). -/
instance fiberSeparated (T₀ : Over (Spec (.of D.k₀))) [IsSeparated T₀.hom] :
    IsSeparated (D.purityFrobeniusFiber T₀).hom := by
  change IsSeparated (pullback.snd T₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
  infer_instance

variable {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (f₀ : X₀ ⟶ Y₀)
  [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
  (d : ℕ) [SmoothOfRelativeDimension d (D.purityFrobeniusMap f₀)]
  (cf : Compactification (D.purityFrobeniusMap f₀))

/-- The smooth geometric base change of the model, with the specified compactification.
Source: parent theorem, standing geometric setting
(blueprint: thm-pur-weil-equivariance-of-purity-and-trace). -/
def smoothIndex : SmoothDatum D := by
  let X := D.purityFrobeniusFiber X₀
  let Y := D.purityFrobeniusFiber Y₀
  let f : X ⟶ Y :=
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀
  have : IsSeparated (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : IsSeparated f.left := IsSeparated.of_comp f.left Y.hom
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  exact { X := X, Y := Y, map := f.left, dim := d, compactification := cf }

/-- The canonical natural purity to any specified Brown right adjoint model.
It is constructed by the counit universal property; no purity orientation is a parameter.
Source: sk-thm-purity-transport, unique counit-compatible gamma
(blueprint: thm-pur-weil-equivariance-of-purity-and-trace). -/
def gamma (R : ScalarExceptionalAdjoint (c.bundled.{u} ell) cf) :
    source ell c (D.purityFrobeniusMap f₀) d
      (normalizedFamily ell D hEll c (smoothIndex D f₀ d cf)).source_closed ≅ R.upper :=
  canonicalPurity (ell := ell) (D := D) (hEll := hEll) c
    (smoothIndex D f₀ d cf) R

/-- The geometric-Frobenius square is Cartesian because its two horizontal maps are
scheme isomorphisms; it is not a statement about scheme Frobenius.
Source: def-pur-scheme-geometric-frobenius, first square
(blueprint: thm-pur-weil-equivariance-of-purity-and-trace).
Proof: geometric Galois pullback is induced by a field automorphism, hence both
horizontal maps are isomorphisms. Their commutativity is purityFrobenius_geometry.
A commuting square with isomorphisms on both horizontal sides is Cartesian. -/
theorem galoisSquare : IsPullback (D.purityGaloisMap X₀)
    (D.purityFrobeniusMap f₀) (D.purityFrobeniusMap f₀) (D.purityGaloisMap Y₀) := by
  exact (D.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.2.1

/-- Root projections and scalar/tensor normalization determine the Tate coordinates.
Source: def-pur-tate-datum, canonical tau_d
(blueprint: thm-pur-weil-equivariance-of-purity-and-trace).
Proof: the geometric-Frobenius scheme map is an isomorphism and ell is invertible
on both copies of the geometric fibre. Apply linePullCoordinates_nonempty. For
uniqueness compare every positive root projection: PullNormalized specifies its
adjunct uniquely by the root tensor map. Joint monicity of the inverse-limit
projections identifies the integral isomorphism. first_normalized identifies the
scalar extension and power_normalized recursively identifies every tensor power.
The remaining fields are propositions and hence proof-irrelevant. -/
theorem existsUniqueTateCoordinates (_hEll : ell ≠ D.p) :
    ∃! p : LinePullCoordinates ell c (D.purityGaloisMap X₀), True := by
  letI : ∀ x : (D.purityFrobeniusFiber X₀).left,
      Invertible (ell : (D.purityFrobeniusFiber X₀).left.residueField x) :=
    fun x ↦ by
      let f := ((D.purityFrobeniusFiber X₀).left ↘ Spec (.of D.k)).residueFieldAlgebraMap x
      have hu : IsUnit (f ell) := (primeUnit D ell _hEll).map f
      simpa only [map_natCast] using hu.invertible
  letI : Subsingleton (LinePullCoordinates ell c (D.purityGaloisMap X₀)) :=
    linePullCoordinates_subsingleton ell c (D.purityGaloisMap X₀)
  obtain ⟨p⟩ := linePullCoordinates_nonempty ell c (D.purityGaloisMap X₀)
  refine ⟨p, trivial, ?_⟩
  intro q _
  exact Subsingleton.elim _ _

/-- The root-normalized Tate comparison on the geometric-Frobenius map.
Its integral components are determined by the root projections; scalar extension and
positive tensor powers fix the remaining components, including d = 0.
Source: def-pur-tate-datum, canonical tau_d
(blueprint: thm-pur-weil-equivariance-of-purity-and-trace). -/
def tateCoordinates : LinePullCoordinates ell c (D.purityGaloisMap X₀) :=
  (existsUniqueTateCoordinates ell D c hEll (X₀ := X₀)).choose

/-- The independent source comparison b_K: pullback composition, tensorator, shift and
root-normalized Tate datum. In particular it is not defined by conjugating gamma.
Source: parent theorem, b_K and def-pur-tate-datum
(blueprint: thm-pur-weil-equivariance-of-purity-and-trace). -/
def sourceComparison (K : c.derived ell (D.purityFrobeniusFiber Y₀).left) :
    (actualPull (c.obj ell) (D.purityGaloisMap X₀)).obj
        ((c.smoothSource ell (D.purityFrobeniusMap f₀) d).obj K) ≅
      (c.smoothSource ell (D.purityFrobeniusMap f₀) d).obj
        ((actualPull (c.obj ell) (D.purityGaloisMap Y₀)).obj K) :=
  (Functor.Monoidal.μIso (actualPull (c.obj ell) (D.purityGaloisMap X₀)) _ _).symm ≪≫
    tensorIso ((pullbackSquareComparison (c.obj ell) (galoisSquare D f₀).toCommSq).symm.app K)
      ((tateCoordinates ell D hEll c (X₀ := X₀)).derived ell d)

/-- The specified compact-support B at any Dctf object, obtained from the normalized
proper/open exchange and compactification refinement. No Cartesianity of scheme
Frobenius is used. Source: parent theorem, B_M
(blueprint: thm-pur-weil-equivariance-of-purity-and-trace). -/
def compactComparison (M : c.ctf ell (D.purityFrobeniusFiber X₀).left) :=
  (supportExchange D (coefficientCoherent ell D hEll E c hc)
    (f := SepFinType.homMk
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀))
    (f' := SepFinType.homMk
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀))
    (galoisSquare D f₀) cf cf).hom.app ((inclusion ell c _).obj M)

/-- The three displayed parent equations, written on actual condensed Dctf objects.
The supplied R is an arbitrary model of the recorded Brown adjunction; gamma, b, B,
counit, and both induced data are fixed constructions, not additional hypotheses.
Source: parent theorem order 3546, all three squares
(blueprint: thm-pur-weil-equivariance-of-purity-and-trace). -/
def ThreeCondensedSquares (R : ScalarExceptionalAdjoint (c.bundled.{u} ell) cf) : Prop :=
  ∀ (K : c.ctf ell (D.purityFrobeniusFiber Y₀).left)
    (phi : (actualPull (c.obj ell) (D.purityGaloisMap Y₀)).obj K.obj ≅ K.obj),
  let a := normalizedFamily ell D hEll c (smoothIndex D f₀ d cf)
  let H := source ell c (D.purityFrobeniusMap f₀) d a.source_closed
  let P := pullCtf ell D hEll E c hc (D.purityFrobeniusFiber Y₀)
    (D.purityFrobeniusFiber Y₀) (D.purityGaloisMap Y₀)
  let phi' : P.obj K ≅ K := ObjectProperty.isoMk _ phi
  let Q := actualPull (c.obj ell) (D.purityGaloisMap X₀)
  let V := actualPull (c.obj ell) (D.purityGaloisMap Y₀)
  let F := rightDerivedLowerShriekOfCompactification (c.obj ell) cf
  let gammaK := (property ell c _).ι.mapIso
    ((gamma (ell := ell) (D := D) (hEll := hEll) (c := c) f₀ d cf R).app K)
  let gammaPK := (property ell c _).ι.mapIso
    ((gamma (ell := ell) (D := D) (hEll := hEll) (c := c) f₀ d cf R).app (P.obj K))
  let b := sourceComparison ell D hEll c f₀ d K.obj
  let hphi := (property ell c _).ι.mapIso (H.mapIso phi')
  let gphi := (property ell c _).ι.mapIso (R.upper.mapIso phi')
  let aexc := (Q.mapIso gammaK).symm ≪≫ b ≪≫ gammaPK ≪≫ gphi
  let eps := R.counit K
  let BH := compactComparison ell D hEll E c hc f₀ cf (H.obj K)
  let BG := compactComparison ell D hEll E c hc f₀ cf (R.upper.obj K)
  Q.map gammaK.hom ≫ aexc.hom = (b ≪≫ hphi).hom ≫ gammaK.hom ∧
    V.map eps ≫ phi.hom = (BG ≫ F.map aexc.hom) ≫ eps ∧
    V.map (F.map gammaK.hom ≫ eps) ≫ phi.hom =
      (BH ≫ F.map (b ≪≫ hphi).hom) ≫ (F.map gammaK.hom ≫ eps)

/-- Condensed replacement for the unusable recorded parent interface.
The coefficient predicate includes independently A_{E,n}, O_E, E, and Qbar_ell;
there is no tower, lattice, scalar-localization or common-stage requirement.
Source: latest blueprint thm-pur-weil-equivariance-of-purity-and-trace.md, order 3546,
and its proof, purity/counit/trace paragraphs
(blueprint: thm-pur-weil-equivariance-of-purity-and-trace).
Proof: the normalized purity comparison is the unique counit-compatible comparison
with the specified Brown right adjoint. Its geometric exchange is inverse Q(gamma),
then b, then gamma at PK. Naturality of gamma gives the first square. The normalized
proper/open compact-support exchange is the adjunction mate of that smooth exchange;
its counit equation gives the second square. Compose with F(gamma) and use naturality
of B to obtain the trace square. The same construction works in each of the four
condensed categories. Coefficient change, composition and Cartesian base change are
those of the normalized family and compact-support comparisons, not added hcoh data. -/
theorem weilEquivarianceOfPurityAndTrace
    (R : ScalarExceptionalAdjoint (c.bundled.{u} ell) cf) :
    ThreeCondensedSquares ell D hEll E c hc f₀ d cf R := by
  sorry

end WeilConjectures.PurityWeil.Condensed
