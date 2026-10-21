# Cartier interfaces and the ordinary boundary construction

## Reason

Separate the Cartier interface definitions from the existence proof, which now
constructs the class from the ordinary unique relative Kummer boundary. The original
module publicly re-exports every moved name. No target signature changes and no
WeilConjectures source-library file changes. Definitions used by targets are submitted
for renewed statement review: the changes below preserve their mathematical meanings.

The two pro-etale sheaf abbreviations become ordinary definitions with explicit sheaf
types. Large composites and normalization predicates become irreducible definitions.
The inverse-image commutation isomorphism is named geoCartierPullbackSquare; expanding
that name gives the original exchange formula. GeoCartierScalarUnit uses the existing
Sheaf.IsDerivedBaseChange predicate at its displayed degree-zero unit. Expanding that
predicate gives the original forall-target bijectivity property, with the composite
reassociated by Category.assoc. No unbounded target is omitted.

OrdinaryFiniteP1Kummer is unchanged (reviewer correction, 2026-10-21, as already at
head 9f44006e): the delivered abbrev-to-def change of ordinaryFiniteConstant broke the
unchanged consumer SupportedKummerSupportHomNaturality (lines 297, 1019, 1033), which
compiles against the published build. The module and its node
def-asd-ordinary-finite-p1-kummer-class keep their live text, without the
ordinaryFiniteIntegralExt/ordinaryFiniteModuleExt caches; every delivered module and every
listed user compiles against it.

OrdinarySupportedCartierKummer is not part of this delivery: C3's landing of
2026-10-21 00:29 (with SupportedDerivedUnitForget, SupportedKummerBoundaryPullback,
SupportedKummerBoundaryScalar, SupportedKummerChernRealization, DerivedSingleUnit and
DerivedSingleUnitExact) is the base and is used as it is. Of those modules only
SupportedDerivedUnitForget and DerivedSingleUnit change here, together with the
unclaimed OrdinarySupportedKummerSystem: supportedDerivedUnit is re-expressed through
the generic derivedSingleUnit cache, definitionally the same morphism (see
coord/changes/supported-derived-unit-comparison-cache.md).

The current N1-held CartierReductionData requires one forced import adaptation.
N1's refactor has moved the definitions from CartierReductionSiteComparison into
this foundation. The current comparison module preserves every proof and signature,
with one additional private proof import of GeoCartierCycleClass.
The original foundation import closes the cycle GeoCartierCycleClass ->
CartierReductionModulus -> GeoCartierCanonicalClass -> GeoCartierCanonicalEtale ->
OrdinarySupportedCartierKummer -> SupportedCartierBoundaryExistence ->
CartierReductionData -> GeoCartierCycleClass. The delivery import-cycle check
reported this exact cycle before the adaptation. Replace only the foundation's
line 9 public import of GeoCartierCycleClass with GeoCartierCycleClassDefs.
All its declarations, signatures, visibility, attributes and proof bodies stay identical.
The comparison module needs the existence theorem at line 208: its original file
against the changed foundation reports Unknown identifier exists_geoCartierCycleClass.
Add only import Sheaf.AlgebraicGeometry.GeoCartierCycleClass to that module.
This is a proof import and introduces no cycle, since the ordinary boundary
construction imports only the foundation.
The current CartierProIntegralScalar also requires one forced proof line. After
its existing erw [← hh], the original proof leaves the equality of the same
composite with its last object written respectively as the constant-sheaf formula
and geoCartierConstant A D. Add rfl to close that definitionally equal goal.
No signature, attribute, visibility or other proof line is changed.
CartierProIntegralDerivedUnit and CartierProKummerDerivedUnit require explicit
unfolding of GeoCartierScalarCompatibility before their existing obtain, because
the predicate is irreducible. Their original proofs report that hcompat is not
an inductive datatype. Unfold GeoCartierScalarUnit at the extracted unit and use
simp only with Functor.DerivedUnit, Sheaf.IsDerivedBaseChange,
Sheaf.derivedRestrictScalars and Category.assoc to recover exactly the former
Hom bijectivity property. Without this normalization their original change tactic
reports that the two predicates are not definitionally equal. Feed the normalized
unit to the unchanged composition argument. Only these forced proof lines change.
The six new direct users named by return C-9f440 are listed under Users below.

The earlier packet's profiling evidence follows; it concerns the pre-refactor module.
The artifact-producing compile also hit 60 s in its exposed cartierProBoundary.
A profile identified the generated localization-smallness proof as the expensive
term. GeoCartierCycleClassDefs now names the existing HasExt proposition for integral
and module-coefficient pro-etale sheaves as geoCartierIntegralExt and
geoCartierModuleExt. It uses the existing
library instance, changes no Ext data or operations, and lets the unchanged N1 data
bodies reuse a short proof constant. The exact one-import N1 adaptation then compiles
with artifacts in 24.5 s; the interface itself compiles in 24.7 s. This proved API helper is attached to the interface node.

## Old

Original Cartier interfaces:

```lean
namespace AlgebraicGeometry.ProEtale

/-- The ordinary pro-etale constant module used in the Cartier class.
Source: blueprint sk-lem-geo-cartier, statement (blueprint: sk-lem-geo-cartier). -/
abbrev geoCartierConstant (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u}) :=
  (constantSheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)

/-- The finite Tate line is exactly comparison inverse image of the etale roots tensor.
Source: blueprint sk-lem-geo-cartier, displayed definition of Λ(1)
(blueprint: sk-lem-geo-cartier). -/
abbrev geoCartierLine (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (Z : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj
    (Scheme.finiteEtaleTateLine Z N A hA)

/-- The supported cycle class, represented through the canonical degree-two Ext/Hom
bijection. Its source uses ordinary closed direct image, not an arbitrary support object.
Source: blueprint sk-lem-geo-cartier, displayed c_D (blueprint: sk-lem-geo-cartier). -/
abbrev GeoCartierClass (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    {D Z : Scheme.{u}} (i : D ⟶ Z) :=
  Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D))
    (geoCartierLine A N hA Z) 2

/-- A simultaneous family allows coefficient, exponent and geometric compatibility
between its actual members. Invertibility of ℓ^r equals invertibility of ℓ for r > 0.
Source: blueprint sk-lem-geo-cartier, statement (blueprint: sk-lem-geo-cartier). -/
def GeoCartierClassFamily (ℓ : ℕ) : Type (u + 2) :=
  ∀ (r : ℕ) (_hr : 0 < r) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ℓ ^ r : ℕ) : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (_hI : i.ker.IsInvertible) (_hZ : IsUnit ((ℓ ^ r : ℕ) : Γ(Z, ⊤))),
    GeoCartierClass A (ℓ ^ r) hA i

/-- The comparison on the ordinary supported constant, with its canonical mate and
constant-sheaf identification. Invertibility is asserted in the main statement.
Source: blueprint sk-lem-geo-cartier, proof paragraph 1 (blueprint: sk-lem-geo-cartier). -/
def geoCartierSourceComparison (A : Type (u + 1)) [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj (Etale.ordinaryFiniteConstant A D)) ⟶
      (lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D) :=
  (lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A)).app
      (Etale.ordinaryFiniteConstant A D) ≫
    (lowerStar (ModuleCat.{u + 1} A) i).map
      ((comparisonUpperStarConstantSheafIso A D).app (ModuleCat.of A A)).hom

/-- Canonical pro-etale closed exchange, as the adjoint of inverse-image commutation
followed by the counit and the pullback of constants. This formula works for arbitrary
base morphisms; no weakly-etale or flatness restriction is imposed.
Source: blueprint sk-lem-geo-cartier, proof paragraph 6 (blueprint: sk-lem-geo-cartier). -/
def geoCartierExchange (A : Type (u + 1)) [CommRing A]
    {D D' Z Z' : Scheme.{u}} (i : D ⟶ Z) (i' : D' ⟶ Z')
    (g : Z' ⟶ Z) (gD : D' ⟶ D) (sq : CommSq gD i' i g) :
    (upperStar (ModuleCat.{u + 1} A) g).obj
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D)) ⟶
      (lowerStar (ModuleCat.{u + 1} A) i').obj (geoCartierConstant A D') :=
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i').homEquiv _ _
    (((upperStarComp (ModuleCat.{u + 1} A) i' g).symm ≪≫
      eqToIso (congrArg (upperStar (ModuleCat.{u + 1} A)) sq.w.symm) ≪≫
      upperStarComp (ModuleCat.{u + 1} A) gD i).hom.app _ ≫
        (upperStar (ModuleCat.{u + 1} A) gD).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).counit.app
            (geoCartierConstant A D)) ≫
        Scheme.proEtaleConstantInverseImageMap gD (ModuleCat.{u + 1} A) (ModuleCat.of A A))

/-- Pull back the finite Tate line through the canonical comparison square and the
existing roots-normalized etale transport.
Source: blueprint sk-lem-geo-cartier, base-change clause (blueprint: sk-lem-geo-cartier). -/
def geoCartierLinePullback (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    {Z Z' : Scheme.{u}} (g : Z' ⟶ Z) (hZ : IsUnit (N : Γ(Z, ⊤))) :
    (upperStar (ModuleCat.{u + 1} A) g).obj (geoCartierLine A N hA Z) ≅
      geoCartierLine A N hA Z' :=
  (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) g).app
      (Scheme.finiteEtaleTateLine Z N A hA) ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z').mapIso (t.line g hZ)

/-- The Chern equation is the actual Kummer boundary of the dual ideal line, expressed
in module Ext and then pulled back by ν. The integral generator fixes the usual
cohomological normalization; it does not supply an arbitrary Chern class.
Source: blueprint sk-lem-geo-cartier, statement and proof paragraph 5
(blueprint: sk-lem-geo-cartier). -/
def GeoCartierChernEquation (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z)
    (hI : i.ker.IsInvertible) (hZ : IsUnit (N : Γ(Z, ⊤)))
    (c : GeoCartierClass A N hA i) : Prop :=
  ∃ c₁ : Ext (Etale.ordinaryFiniteConstant A Z) (Scheme.finiteEtaleTateLine Z N A hA) 2,
    (Ext.mk₀ (Etale.ordinaryFiniteIntegralGenerator A Z)).comp
        (c₁.mapExactFunctor (Etale.RawModuleScalarComparison.forget A Z)) (zero_add 2) =
      Etale.supportedKummerChern A N hA i hI hZ ∧
    (Ext.mk₀ (((comparisonUpperStarConstantSheafIso A Z).app (ModuleCat.of A A)).hom ≫
      Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A) (ModuleCat.of A A))).comp
        c (zero_add 2) = c₁.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} A) Z)

/-- Derived extension at a specified sheaf map is characterized by its Hom universal
property against every unbounded complex. This is a property of the given coefficient
unit, not a choice of a replacement scalar-extension functor.
Source: Stacks 07A6; blueprint sk-lem-geo-cartier, coefficient clause
(blueprint: sk-lem-geo-cartier). -/
def GeoCartierScalarUnit {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (Z : Scheme.{u})
    (F : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R))
    (G : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).obj G) : Prop :=
  ∀ K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} S)),
    Function.Bijective (fun f : (DerivedCategory.singleFunctor _ 0).obj G ⟶ K ↦
      (DerivedCategory.singleFunctor _ 0).map η ≫
        ((Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).mapDerivedCategorySingleFunctor
          0).inv.app G ≫
        (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).mapDerivedCategory.map f)

/-- Coefficient compatibility with the canonical supported-constant and Tate-line
units. Normalization is on constants and on pure root tensors through the comparison
adjunction unit. These generate after sheafification, so the comparisons are fixed.
Source: blueprint sk-lem-geo-cartier, coefficient clause (blueprint: sk-lem-geo-cartier). -/
def GeoCartierScalarCompatibility {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (N : ℕ) (hR : (N : R) = 0) (hS : (N : S) = 0)
    {D Z : Scheme.{u}} (i : D ⟶ Z)
    (cR : GeoCartierClass R N hR i) (cS : GeoCartierClass S N hS i) : Prop :=
  ∃ (η : geoCartierConstant R D ⟶
        (Sheaf.restrictScalars (Scheme.ProEt.topology D) φ).obj (geoCartierConstant S D))
    (θ : geoCartierLine R N hR Z ⟶
        (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).obj (geoCartierLine S N hS Z)),
    (∀ (W : D.ProEtᵒᵖ) (a : R),
      η.hom.app W ((toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of R R))).app W a) =
      (toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of S S))).app W (φ a)) ∧
    (∀ (W : Z.Etaleᵒᵖ) (a : R) (z : (Z.rootsOfUnitySheaf N).obj.obj W),
      θ.hom.app ((Scheme.toProEt Z).op.obj W)
        (((comparisonAdjunction (ModuleCat.{u + 1} R) Z).unit.app
          (Scheme.finiteEtaleTateLine Z N R hR)).hom.app W
            (Scheme.finiteEtaleTateOneGenerator R N Z hR W a z)) =
      ((comparisonAdjunction (ModuleCat.{u + 1} S) Z).unit.app
        (Scheme.finiteEtaleTateLine Z N S hS)).hom.app W
          (Scheme.finiteEtaleTateOneGenerator S N Z hS W (φ a) z)) ∧
    GeoCartierScalarUnit φ Z
      ((lowerStar (ModuleCat.{u + 1} R) i).obj (geoCartierConstant R D))
      ((lowerStar (ModuleCat.{u + 1} S) i).obj (geoCartierConstant S D))
      ((lowerStar (ModuleCat.{u + 1} R) i).map η) ∧
    GeoCartierScalarUnit φ Z (geoCartierLine R N hR Z) (geoCartierLine S N hS Z) θ ∧
    (Ext.mk₀ ((lowerStar (ModuleCat.{u + 1} R) i).map η)).comp
        (cS.mapExactFunctor (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ))
        (zero_add 2) = cR.comp (Ext.mk₀ θ) (add_zero 2)

/-- Cartier-preserving pullback of a simultaneous class family, using the counit mate
for the source and the roots-normalized finite Tate-line comparison for the target.
Source: blueprint sk-lem-geo-cartier, final clause (blueprint: sk-lem-geo-cartier). -/
def GeoCartierBaseChange (ℓ : ℕ) (c : GeoCartierClassFamily.{u} ℓ) : Prop :=
  ∀ (r : ℕ) (hr : 0 < r) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ℓ ^ r : ℕ) : A) = 0),
    ∃ t : Etale.OrdinaryFiniteTwistTransport A (ℓ ^ r) hA,
      ∀ {D D' Z Z' : Scheme.{u}} (i : D ⟶ Z) (i' : D' ⟶ Z')
        [IsClosedImmersion i] [IsClosedImmersion i'] (g : Z' ⟶ Z) (gD : D' ⟶ D)
        (sq : IsPullback gD i' i g) (hI : i.ker.IsInvertible) (hI' : i'.ker.IsInvertible)
        (hZ : IsUnit ((ℓ ^ r : ℕ) : Γ(Z, ⊤))) (hZ' : IsUnit ((ℓ ^ r : ℕ) : Γ(Z', ⊤))),
        IsIso (geoCartierExchange A i i' g gD sq.toCommSq) ∧
        (Ext.mk₀ (geoCartierExchange A i i' g gD sq.toCommSq)).comp
            (c r hr A hA i' hI' hZ') (zero_add 2) =
          ((c r hr A hA i hI hZ).mapExactFunctor (upperStar (ModuleCat.{u + 1} A) g)).comp
            (Ext.mk₀ (geoCartierLinePullback A (ℓ ^ r) hA t g hZ).hom) (add_zero 2)

/-- Independence of the killing exponent under the actual roots projection. The map
on roots is pinned by its inclusion into G_m, and the line map by its pure tensors.
Source: blueprint sk-lem-geo-cartier, exponent sentence (blueprint: sk-lem-geo-cartier). -/
def GeoCartierExponentIndependence (ℓ : ℕ) (c : GeoCartierClassFamily.{u} ℓ) : Prop :=
  ∀ (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (_hrs : r ≤ s)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ℓ ^ r : ℕ) : A) = 0) (hA' : ((ℓ ^ s : ℕ) : A) = 0)
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hZ : IsUnit ((ℓ ^ r : ℕ) : Γ(Z, ⊤))) (hZ' : IsUnit ((ℓ ^ s : ℕ) : Γ(Z, ⊤))),
    ∃ (q : Z.rootsOfUnitySheaf (ℓ ^ s) ⟶ Z.rootsOfUnitySheaf (ℓ ^ r))
      (e : Scheme.finiteEtaleTateLine Z (ℓ ^ s) A hA' ≅
        Scheme.finiteEtaleTateLine Z (ℓ ^ r) A hA),
      q ≫ kernel.ι ((ℓ ^ r) • 𝟙 Z.gmSheaf) =
        (ℓ ^ s / ℓ ^ r) • kernel.ι ((ℓ ^ s) • 𝟙 Z.gmSheaf) ∧
      (∀ (W : Z.Etaleᵒᵖ) (a : A) (z : (Z.rootsOfUnitySheaf (ℓ ^ s)).obj.obj W),
        e.hom.hom.app W (Scheme.finiteEtaleTateOneGenerator A (ℓ ^ s) Z hA' W a z) =
          Scheme.finiteEtaleTateOneGenerator A (ℓ ^ r) Z hA W a (q.hom.app W z)) ∧
      (c s hs A hA' i hI hZ').comp
          (Ext.mk₀ ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).map e.hom)) (add_zero 2) =
        c r hr A hA i hI hZ

```

Original N1-held CartierReductionData dependency (line 9):

```lean
public import Sheaf.AlgebraicGeometry.GeoCartierCycleClass
```

## New

Extracted Cartier interfaces, re-exported by the original module:

```lean
namespace AlgebraicGeometry.ProEtale

/-- Cache the existing smallness proof used by integral pro-etale Ext classes.
Source: the existing Grothendieck-abelian sheaf category and its Ext instance
(blueprint: def-sfb-geo-cartier-interface).
Proof: apply the library instance for Ext in this sheaf category. This names only
its smallness proof, so it does not alter the Ext objects or their operations. -/
instance (priority := 10000) geoCartierIntegralExt (Z : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1}) := by
  infer_instance

/-- Cache finite-coefficient pro-etale Ext smallness, without changing any Ext data.
Source: the existing Grothendieck-abelian sheaf Ext instance
(blueprint: def-sfb-geo-cartier-interface). The proof only specializes that instance. -/
instance (priority := 10000) geoCartierModuleExt
    (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) := by
  infer_instance

/-- The ordinary pro-etale constant module used in the Cartier class.
Source: blueprint sk-lem-geo-cartier, statement (blueprint: def-sfb-geo-cartier-interface). -/
def geoCartierConstant (A : Type (u + 1)) [CommRing A] (Z : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A) :=
  (constantSheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)

/-- The finite Tate line is exactly comparison inverse image of the etale roots tensor.
Source: blueprint sk-lem-geo-cartier, displayed definition of Λ(1)
(blueprint: def-sfb-geo-cartier-interface). -/
def geoCartierLine (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (Z : Scheme.{u}) : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj
    (Scheme.finiteEtaleTateLine Z N A hA)

/-- The supported cycle class, represented through the canonical degree-two Ext/Hom
bijection. Its source uses ordinary closed direct image, not an arbitrary support object.
Source: blueprint sk-lem-geo-cartier, displayed c_D (blueprint: def-sfb-geo-cartier-interface). -/
abbrev GeoCartierClass (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    {D Z : Scheme.{u}} (i : D ⟶ Z) :=
  Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D))
    (geoCartierLine A N hA Z) 2

/-- A simultaneous family allows coefficient, exponent and geometric compatibility
between its actual members. Invertibility of ℓ^r equals invertibility of ℓ for r > 0.
Source: blueprint sk-lem-geo-cartier, statement (blueprint: def-sfb-geo-cartier-interface). -/
def GeoCartierClassFamily (ℓ : ℕ) : Type (u + 2) :=
  ∀ (r : ℕ) (_hr : 0 < r) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ℓ ^ r : ℕ) : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i]
    (_hI : i.ker.IsInvertible) (_hZ : IsUnit ((ℓ ^ r : ℕ) : Γ(Z, ⊤))),
    GeoCartierClass A (ℓ ^ r) hA i

/-- The comparison on the ordinary supported constant, with its canonical mate and
constant-sheaf identification. Invertibility is asserted in the main statement.
Source: blueprint sk-lem-geo-cartier, proof paragraph 1
(blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
def geoCartierSourceComparison (A : Type (u + 1)) [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj (Etale.ordinaryFiniteConstant A D)) ⟶
      (lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D) :=
  (lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A)).app
      (Etale.ordinaryFiniteConstant A D) ≫
    (lowerStar (ModuleCat.{u + 1} A) i).map
      ((comparisonUpperStarConstantSheafIso A D).app (ModuleCat.of A A)).hom

/-- The inverse-image commutation isomorphism for the specified square.
Source: blueprint sk-lem-geo-cartier, opening comparison and paragraph 6
(blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
def geoCartierPullbackSquare (A : Type (u + 1)) [CommRing A]
    {D D' Z Z' : Scheme.{u}} (i : D ⟶ Z) (i' : D' ⟶ Z')
    (g : Z' ⟶ Z) (gD : D' ⟶ D) (sq : CommSq gD i' i g) :
    upperStar (ModuleCat.{u + 1} A) g ⋙ upperStar (ModuleCat.{u + 1} A) i' ≅
      upperStar (ModuleCat.{u + 1} A) i ⋙ upperStar (ModuleCat.{u + 1} A) gD :=
  (upperStarComp (ModuleCat.{u + 1} A) i' g).symm ≪≫
    eqToIso (congrArg (upperStar (ModuleCat.{u + 1} A)) sq.w.symm) ≪≫
    upperStarComp (ModuleCat.{u + 1} A) gD i

/-- Canonical pro-etale closed exchange, as the adjoint of inverse-image commutation
followed by the counit and the pullback of constants. This formula works for arbitrary
base morphisms; no weakly-etale or flatness restriction is imposed.
Source: blueprint sk-lem-geo-cartier, proof paragraph 6
(blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
def geoCartierExchange (A : Type (u + 1)) [CommRing A]
    {D D' Z Z' : Scheme.{u}} (i : D ⟶ Z) (i' : D' ⟶ Z')
    (g : Z' ⟶ Z) (gD : D' ⟶ D) (sq : CommSq gD i' i g) :
    (upperStar (ModuleCat.{u + 1} A) g).obj
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D)) ⟶
      (lowerStar (ModuleCat.{u + 1} A) i').obj (geoCartierConstant A D') :=
  (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i').homEquiv _ _
    ((geoCartierPullbackSquare A i i' g gD sq).hom.app _ ≫
        (upperStar (ModuleCat.{u + 1} A) gD).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).counit.app
            (geoCartierConstant A D)) ≫
        Scheme.proEtaleConstantInverseImageMap gD (ModuleCat.{u + 1} A) (ModuleCat.of A A))

/-- Pull back the finite Tate line through the canonical comparison square and the
existing roots-normalized etale transport.
Source: blueprint sk-lem-geo-cartier, base-change clause
(blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
def geoCartierLinePullback (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    {Z Z' : Scheme.{u}} (g : Z' ⟶ Z) (hZ : IsUnit (N : Γ(Z, ⊤))) :
    (upperStar (ModuleCat.{u + 1} A) g).obj (geoCartierLine A N hA Z) ≅
      geoCartierLine A N hA Z' :=
  (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) g).app
      (Scheme.finiteEtaleTateLine Z N A hA) ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z').mapIso (t.line g hZ)

/-- The Chern equation is the actual Kummer boundary of the dual ideal line, expressed
in module Ext and then pulled back by ν. The integral generator fixes the usual
cohomological normalization; it does not supply an arbitrary Chern class.
Source: blueprint sk-lem-geo-cartier, statement and proof paragraph 5
(blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
def GeoCartierChernEquation (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) {D Z : Scheme.{u}} (i : D ⟶ Z)
    (hI : i.ker.IsInvertible) (hZ : IsUnit (N : Γ(Z, ⊤)))
    (c : GeoCartierClass A N hA i) : Prop :=
  ∃ c₁ : Ext (Etale.ordinaryFiniteConstant A Z) (Scheme.finiteEtaleTateLine Z N A hA) 2,
    (Ext.mk₀ (Etale.ordinaryFiniteIntegralGenerator A Z)).comp
        (c₁.mapExactFunctor (Etale.RawModuleScalarComparison.forget A Z)) (zero_add 2) =
      Etale.supportedKummerChern A N hA i hI hZ ∧
    (Ext.mk₀ (((comparisonUpperStarConstantSheafIso A Z).app (ModuleCat.of A A)).hom ≫
      Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A) (ModuleCat.of A A))).comp
        c (zero_add 2) = c₁.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} A) Z)

/-- Derived extension at a specified sheaf map is characterized by its Hom universal
property against every unbounded complex. This is a property of the given coefficient
unit, not a choice of a replacement scalar-extension functor.
Source: Stacks 07A6; blueprint sk-lem-geo-cartier, coefficient clause
(blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
def GeoCartierScalarUnit {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (Z : Scheme.{u})
    (F : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R))
    (G : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).obj G) : Prop :=
  Sheaf.IsDerivedBaseChange
    ((DerivedCategory.singleFunctor _ 0).map η ≫
      ((Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).mapDerivedCategorySingleFunctor
        0).inv.app G)


/-- Coefficient compatibility with the canonical supported-constant and Tate-line
units. Normalization is on constants and on pure root tensors through the comparison
adjunction unit. These generate after sheafification, so the comparisons are fixed.
Source: blueprint sk-lem-geo-cartier, coefficient clause
(blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
def GeoCartierScalarCompatibility {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (N : ℕ) (hR : (N : R) = 0) (hS : (N : S) = 0)
    {D Z : Scheme.{u}} (i : D ⟶ Z)
    (cR : GeoCartierClass R N hR i) (cS : GeoCartierClass S N hS i) : Prop :=
  ∃ (η : geoCartierConstant R D ⟶
        (Sheaf.restrictScalars (Scheme.ProEt.topology D) φ).obj (geoCartierConstant S D))
    (θ : geoCartierLine R N hR Z ⟶
        (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).obj (geoCartierLine S N hS Z)),
    (∀ (W : D.ProEtᵒᵖ) (a : R),
      η.hom.app W ((toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of R R))).app W a) =
      (toSheafify (Scheme.ProEt.topology D)
        ((Functor.const D.ProEtᵒᵖ).obj (ModuleCat.of S S))).app W (φ a)) ∧
    (∀ (W : Z.Etaleᵒᵖ) (a : R) (z : (Z.rootsOfUnitySheaf N).obj.obj W),
      θ.hom.app ((Scheme.toProEt Z).op.obj W)
        (((comparisonAdjunction (ModuleCat.{u + 1} R) Z).unit.app
          (Scheme.finiteEtaleTateLine Z N R hR)).hom.app W
            (Scheme.finiteEtaleTateOneGenerator R N Z hR W a z)) =
      ((comparisonAdjunction (ModuleCat.{u + 1} S) Z).unit.app
        (Scheme.finiteEtaleTateLine Z N S hS)).hom.app W
          (Scheme.finiteEtaleTateOneGenerator S N Z hS W (φ a) z)) ∧
    GeoCartierScalarUnit φ Z
      ((lowerStar (ModuleCat.{u + 1} R) i).obj (geoCartierConstant R D))
      ((lowerStar (ModuleCat.{u + 1} S) i).obj (geoCartierConstant S D))
      ((lowerStar (ModuleCat.{u + 1} R) i).map η) ∧
    GeoCartierScalarUnit φ Z (geoCartierLine R N hR Z) (geoCartierLine S N hS Z) θ ∧
    (Ext.mk₀ ((lowerStar (ModuleCat.{u + 1} R) i).map η)).comp
        (cS.mapExactFunctor (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ))
        (zero_add 2) = cR.comp (Ext.mk₀ θ) (add_zero 2)

/-- Cartier-preserving pullback of a simultaneous class family, using the counit mate
for the source and the roots-normalized finite Tate-line comparison for the target.
Source: blueprint sk-lem-geo-cartier, final clause (blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
def GeoCartierBaseChange (ℓ : ℕ) (c : GeoCartierClassFamily.{u} ℓ) : Prop :=
  ∀ (r : ℕ) (hr : 0 < r) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ℓ ^ r : ℕ) : A) = 0),
    ∃ t : Etale.OrdinaryFiniteTwistTransport A (ℓ ^ r) hA,
      ∀ {D D' Z Z' : Scheme.{u}} (i : D ⟶ Z) (i' : D' ⟶ Z')
        [IsClosedImmersion i] [IsClosedImmersion i'] (g : Z' ⟶ Z) (gD : D' ⟶ D)
        (sq : IsPullback gD i' i g) (hI : i.ker.IsInvertible) (hI' : i'.ker.IsInvertible)
        (hZ : IsUnit ((ℓ ^ r : ℕ) : Γ(Z, ⊤))) (hZ' : IsUnit ((ℓ ^ r : ℕ) : Γ(Z', ⊤))),
        IsIso (geoCartierExchange A i i' g gD sq.toCommSq) ∧
        (Ext.mk₀ (geoCartierExchange A i i' g gD sq.toCommSq)).comp
            (c r hr A hA i' hI' hZ') (zero_add 2) =
          ((c r hr A hA i hI hZ).mapExactFunctor (upperStar (ModuleCat.{u + 1} A) g)).comp
            (Ext.mk₀ (geoCartierLinePullback A (ℓ ^ r) hA t g hZ).hom) (add_zero 2)

/-- Independence of the killing exponent under the actual roots projection. The map
on roots is pinned by its inclusion into G_m, and the line map by its pure tensors.
Source: blueprint sk-lem-geo-cartier, exponent sentence
(blueprint: def-sfb-geo-cartier-interface). -/
@[irreducible]
def GeoCartierExponentIndependence (ℓ : ℕ) (c : GeoCartierClassFamily.{u} ℓ) : Prop :=
  ∀ (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (_hrs : r ≤ s)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ((ℓ ^ r : ℕ) : A) = 0) (hA' : ((ℓ ^ s : ℕ) : A) = 0)
    {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hZ : IsUnit ((ℓ ^ r : ℕ) : Γ(Z, ⊤))) (hZ' : IsUnit ((ℓ ^ s : ℕ) : Γ(Z, ⊤))),
    ∃ (q : Z.rootsOfUnitySheaf (ℓ ^ s) ⟶ Z.rootsOfUnitySheaf (ℓ ^ r))
      (e : Scheme.finiteEtaleTateLine Z (ℓ ^ s) A hA' ≅
        Scheme.finiteEtaleTateLine Z (ℓ ^ r) A hA),
      q ≫ kernel.ι ((ℓ ^ r) • 𝟙 Z.gmSheaf) =
        (ℓ ^ s / ℓ ^ r) • kernel.ι ((ℓ ^ s) • 𝟙 Z.gmSheaf) ∧
      (∀ (W : Z.Etaleᵒᵖ) (a : A) (z : (Z.rootsOfUnitySheaf (ℓ ^ s)).obj.obj W),
        e.hom.hom.app W (Scheme.finiteEtaleTateOneGenerator A (ℓ ^ s) Z hA' W a z) =
          Scheme.finiteEtaleTateOneGenerator A (ℓ ^ r) Z hA W a (q.hom.app W z)) ∧
      (c s hs A hA' i hI hZ').comp
          (Ext.mk₀ ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).map e.hom)) (add_zero 2) =
        c r hr A hA i hI hZ

end AlgebraicGeometry.ProEtale
```

Replacement N1-held CartierReductionData dependency (the only changed line):

```lean
public import Sheaf.AlgebraicGeometry.GeoCartierCycleClassDefs
```

The new canonical ordinary class is chosen only from an existence-and-uniqueness
statement fixing its Ext equality. The pro-etale class is a concrete exact functor
image precomposed with the inverse of the specified source comparison. These contain
no data holes and introduce no arbitrary witness of mere existence.

Reviewer addition (2026-10-21) to GeoCartierCycleClassDefs, so that instance search
sees through the typed constant as it did through the abbreviation:

```lean
instance geoCartierSourceConstant_isIso (A : Type (u + 1)) [CommRing A]
    {D Z : Scheme.{u}} (i : D ⟶ Z) :
    IsIso ((lowerStar (ModuleCat.{u + 1} A) i).map
      ((comparisonUpperStarConstantSheafIso A D).app (ModuleCat.of A A)).hom :
        _ ⟶ (lowerStar (ModuleCat.{u + 1} A) i).obj (geoCartierConstant A D))
```

## Users

This table includes every transitive importer reported by tools/downstream.py for the
three original modules and all adapted modules. Unchanged consumers retain the same
names, types and formulas. The ordinary constant is unchanged;
Cartier names are publicly re-exported. No consumer statement becomes weaker or
stronger. New normalization predicates have the same expanded formulas (the scalar
unit additionally uses associativity). Target meaning is reopened for review.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SpP1BaseChangeOfNormalized | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| Sheaf.AlgebraicGeometry.SpP1NormalizedFamilyCore | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| Sheaf.AlgebraicGeometry.SpP1RationalPointChern | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| TargetsCheck | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| WeilConjectures | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Transitive importer; all referenced names remain public with the same types and expanded formulas. No source adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleP1DiagonalComponents | unclaimed (P4 landing) | Current direct user of geoCartierConstant, geoCartierLine, GeoCartierClass and ordinaryFiniteConstant; public re-exports preserve the names, types and constant/roots formulas. Compiled unchanged against this repair in 55.1 s. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase | unclaimed (P4 landing) | Direct user of ordinaryFiniteConstant, which stays unchanged (the Ext caches are withdrawn by the reviewer); no adaptation. |
| Sheaf.AlgebraicGeometry.CartierComplementFrame | unclaimed (N1 landing) | Current transitive importer; all referenced interfaces and formulas remain available. No adaptation. |
| Sheaf.AlgebraicGeometry.CartierEtaleKummerDerivedUnit | unclaimed (N1 landing) | Current transitive importer; all referenced interfaces and formulas remain available. No adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalTraceCalculation | unclaimed | Current transitive importer; all referenced interfaces and formulas remain available. No adaptation. |
| Sheaf.AlgebraicGeometry.ResidueFiniteRootMapIso | unclaimed (N1 landing) | Current transitive importer; all referenced interfaces and formulas remain available. No adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalChernComponents | unclaimed | Current direct user of ordinaryFiniteConstant; its type and constant-sheaf formula are preserved. |
| Sheaf.AlgebraicGeometry.EtaleSupportedIntegralDerivedUnit | unclaimed (N1 landing) | Current direct user of ordinaryFiniteConstant; its type and constant-sheaf formula are preserved. |
| Sheaf.AlgebraicGeometry.SupportedIntegralResidueSequence | unclaimed (N1 landing) | Current direct user of ordinaryFiniteConstant; its type and constant-sheaf formula are preserved. |
| Sheaf.AlgebraicGeometry.ComparisonConstantGenerator | unclaimed (N1 landing) | Current direct user of ordinaryFiniteConstant; its type and constant-sheaf formula are preserved. |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalData | unclaimed | Current direct user of supportedDerivedUnit; signature and canonical derived-unit formula preserved. |
| Sheaf.AlgebraicGeometry.AffineLinearActionFamily | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineLinearActionRigidity | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineLinearTraceAction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineLinearUniversalAction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction | M4 | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineSpaceTopTrace | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineTraceConstruction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineTraceLineCounitBaseChange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineTraceLineLocalization | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineTraceLineOpenCounitBaseChange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineTraceLinePurity | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineTraceRightNormalForm | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.AffineTraceTowerCounitBaseChange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.CartierProIntegralDerivedUnit | N1 | Explicitly unfold the two irreducible scalar predicates and reassociate their Hom map before applying the unchanged composition argument; signature unchanged. |
| Sheaf.AlgebraicGeometry.CartierProIntegralResidueDerivedUnit | N1 | Unchanged consumer; uses geoCartierConstant and geoCartierSourceComparison. |
| Sheaf.AlgebraicGeometry.CartierProIntegralScalar | N1 | Add one rfl after the existing naturality rewrite in private source_comparison_unit; the typed constant leaves a definitionally equal goal. Existing signatures and every other proof line stay identical. |
| Sheaf.AlgebraicGeometry.CartierProKummerDerivedUnit | N1 | Explicitly unfold the two irreducible scalar predicates and reassociate their Hom map before applying the unchanged composition argument; signature unchanged. |
| Sheaf.AlgebraicGeometry.CartierProRootScalar | N1 | Unchanged consumer; uses geoCartierLine. |
| Sheaf.AlgebraicGeometry.CartierReductionData | N1 | Forced one-line import adaptation to GeoCartierCycleClassDefs to break the cycle; declarations unchanged and uses geoCartierConstant, geoCartierLine and GeoCartierClass. |
| Sheaf.AlgebraicGeometry.CartierDerivedRealization | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.CartierPoleBoundary | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.CartierReductionModulus | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.CartierReductionPullback | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.CartierReductionScalar | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.CartierReductionSiteComparison | N1 | Current N1 refactor preserved; add only a private GeoCartierCycleClass proof import for its existence-theorem application. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.FiniteEtaleCup | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.TraceCupNaturality | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals | G5 | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.GeoCartierCanonicalChern | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.GeoCartierCanonicalClass | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.GeoCartierCanonicalEtale | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.GeoCartierCycleClass | T3 | Interfaces re-exported; existence assembled from the ordinary class. |
| Sheaf.AlgebraicGeometry.GeoCartierCycleClassDefs | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.GeoCartierSourceComparison | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | W3 | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.OrdinaryEtaleCup | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.OrdinaryEtaleCupFunctoriality | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction | B2 | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition | A6 | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.EtaleDegreeZeroHom | unclaimed | Unchanged new consumer; compiles against the unchanged ordinary constant and the repaired Cartier interface. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteClassInjectivity | unclaimed | Unchanged new consumer; compiles against the unchanged ordinary constant and the repaired Cartier interface. |
| Sheaf.AlgebraicGeometry.VectorIntegrationLocalTraceCompatibility | unclaimed | Unchanged new consumer; compiles against the unchanged ordinary constant and the repaired Cartier interface. |
| Sheaf.SixFunctors.GeoCartierCoeffExtension | unclaimed | Unchanged consumer; the canonical constant object and its Ext types are preserved definitionally. |
| Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula | unclaimed | Unchanged consumer; the canonical constant object and its Ext types are preserved definitionally. |
| Sheaf.AlgebraicGeometry.FiniteP1DiagonalAlpha | unclaimed | Add a proved private generic cached-unit pasting helper and specialize it; public signature and composite-adjunction argument unchanged. |
| Sheaf.AlgebraicGeometry.FiniteP1DiagonalChernComponents | unclaimed | Unchanged consumer; the canonical constant object and its Ext types are preserved definitionally. |
| Sheaf.AlgebraicGeometry.FiniteP1KummerNaturality | unclaimed | Transitive ordinary-interface consumer; the constant formula and every existing signature remain definitionally identical; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteP1KummerSplitting | unclaimed | Transitive ordinary-interface consumer; the constant formula and every existing signature remain definitionally identical; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DatumUniqueness | unclaimed | Transitive ordinary-interface consumer; the constant formula and every existing signature remain definitionally identical; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DiagonalUnit | unclaimed | Transitive ordinary-interface consumer; the constant formula and every existing signature remain definitionally identical; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps | unclaimed | Transitive ordinary-interface consumer; the constant formula and every existing signature remain definitionally identical; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteTraceCounit | unclaimed | Transitive ordinary-interface consumer; the constant formula and every existing signature remain definitionally identical; no adaptation. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts | unclaimed | Transitive ordinary-interface consumer; the constant formula and every existing signature remain definitionally identical; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness | unclaimed | Unchanged consumer of the public ordinary constant and Ext-smallness interface; compiled against the repair. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteClassComparison | B2 | Unchanged consumer; compiles against the unchanged ordinary constant and the irreducible Cartier interfaces. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedChernNormalization | unclaimed | Restore this checked consumer after batch recovery; replace witness destructuring with composition of supported_derived_unit_forget and supported_kummer_chern_realization. Same signature; proved with no holes. |
| Sheaf.AlgebraicGeometry.SupportedDerivedUnitForget | unclaimed (B3 restoration) | Unchanged consumer; compiles against the unchanged ordinary constant and the irreducible Cartier interfaces. |
| Sheaf.AlgebraicGeometry.SupportedKummerScalarDerived | C2 | Unchanged consumer; its derived scalar-unit statement mentions ordinaryFiniteConstant, which is unchanged; compiles against the delivery. |
| Sheaf.AlgebraicGeometry.SupportedKummerScalarMaps | C2 | Unchanged consumer; its scalar-map statement mentions ordinaryFiniteConstant, which is unchanged; compiles against the delivery. |
| Sheaf.AlgebraicGeometry.SupportedKummerBoundaryPullback | unclaimed (B3 restoration) | Unchanged consumer; compiles against the unchanged ordinary constant and the irreducible Cartier interfaces. |
| Sheaf.AlgebraicGeometry.SupportedKummerBoundaryScalar | unclaimed (B3 restoration) | Unchanged consumer; compiles against the unchanged ordinary constant and the irreducible Cartier interfaces. |
| Sheaf.AlgebraicGeometry.SupportedKummerChernRealization | unclaimed (B3 restoration) | Unchanged consumer; compiles against the unchanged ordinary constant and the irreducible Cartier interfaces. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer | unclaimed | Unchanged (reviewer correction: the abbrev-to-def change and the two Ext caches are withdrawn). |
| Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer | C3 (current); B3 (restored landing) | Restores reviewed B3 cf48da8d1bd verbatim after batch recovery, as required by return A1/2; no new proof adaptation. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerScalar | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedKummerSystem | unclaimed | Restore B3's canonical derived-unit cache after batch recovery; same signature and mathematical data. See supported-derived-unit-comparison-cache.md. |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace | unclaimed | Its private cartierSource_isIso (unfold geoCartierSourceComparison; infer_instance) fails against the typed geoCartierConstant ("failed to synthesize IsIso", line 192); the reviewer-added instance geoCartierSourceConstant_isIso in GeoCartierCycleClassDefs restores it. No source adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTraceSystem | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals | A7 | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProjectiveLineTrace | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.SupportedCartierBoundaryExistence | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.SupportedKummerScalarSource | D3 | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality | E1 | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | F1 | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.VectorIntegrationMate | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.AlgebraicGeometry.VectorIntegrationTensorCounit | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.AdicLocalFrobeniusModelConjugacy | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.AffineLineSupportGeometry | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CartesianCoefficientTwists | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CoefficientHeart | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CoefficientHeartFiltration | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CompactSupportReductionTower | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.DiagonalTowerSystem | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FieldTwistInverse | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteTateSiteDescent | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteWindow | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FixedFinitePositiveCoefficientTwist | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.HomFiniteProjective | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralHeartLocalModel | C2 | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralModels | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralModelsOperations | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralTwistBaseChange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.KummerAdditivity | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.MixedReductionUnit | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PbcCoefficientTwists | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProjectionCoefficientTensorTotal | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PurityAffineLineDatum | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PurityConventions | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PurityFiniteKummerLevel | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PurityFrameClass | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PurityFrameKummer | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PurityFramePrincipalBoundary | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SignedTwistReductionComparison | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SmoothTrace | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.StratifiedLatticeRank | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SupportedAffineLineHomotopy | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SupportedCupFunctoriality | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SupportedHomPullback | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TateTwistLocallyFree | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TowerClassChern | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TowerClassFinite | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TowerClassProjective | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TowerClassPullback | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TowerClassReduction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TowerClassSystems | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TraceBaseChangeFirst | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TwConventions | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.TwistPreservesFiniteness | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.VectorPurityBaseChange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.VectorPurityDirectSum | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.VectorPurityNormalization | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.VectorPurityScalarSingle | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.VerdierExchange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.BrownHypothesesSmall | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralModelsGenerators | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.Targets.VectorBundlePurity | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Same names, types and formulas; no adaptation required. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Same names, types and formulas; no adaptation required. |

## Additional compatibility proofs

The generic DerivedSingleUnit cache exposes derivedSingleUnit_eq, proved by
unfolding its original full adjunction-unit/single-comparison composite and
reflexivity. The concrete supportedDerivedUnit is re-expressed through this cache (supported-derived-unit-comparison-cache.md).

FiniteP1DiagonalAlpha originally fails after unfolding supportedDerivedUnit: the
resulting Adjunction.derivedSingleUnit composite does not match the explicit
adjunction-unit conclusion of isIso_pasted_units (compiler Type mismatch at
the original final application). Its new private isIso_pasted_single_units helper
expands the cache at abstract categories and applies exactly the existing
isIso_pasted_units argument to the two derived adjunctions and single-comparison
isomorphisms. The final proof specializes this helper directly, selecting the
captured category proofs locally and respecting transparency. Existing public
signatures, visibility and mathematical arguments are unchanged. The module is unclaimed.

OrdinarySupportedChernNormalization's old existential-witness destructuring
exceeded the file time limit during the required consumer recheck. Its statement
is unchanged. The new proof unfolds ordinaryFiniteClass and composes the existing
proved supported_derived_unit_forget and supported_kummer_chern_realization
identities. The private proof imports follow those two lemmas; transparency
annotations are respected. Its mathematical node now records that shorter route.
The revised proof compiles without warnings in 44.3 s; the revised diagonal proof
compiles without warnings in 25.2 s. The file and node, authored by A7 and present in cf48da8d1bd, were absent from the
post-recovery branch; their restoration provenance is recorded. It has zero holes.

## Status

landed 20261021T134548-L-1367600 2026-10-21 (merge of deliver/T3/Sheaf.AlgebraicGeometry.GeoCartierCycleClass)
