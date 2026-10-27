module

public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import WeilConjectures.RingTheory.PairHenselization
public import Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.HenselizationUniversalProperty
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Pointed common refinements of affine SNC charts

Source: Stacks 0A02, 09ZS, 0BND; ILO VIII Remark 4.2.2(i), p.118.
(blueprint: lem-sfb-snc-pointed-affine-common-refinement).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- An affine chart with labelled component ideals, a parameter subtuple at every prime,
and a connected regular residual scheme with its specified geometric point.
Source: ILO VIII 4.2.2(i)
(blueprint: lem-sfb-snc-pointed-affine-common-refinement). -/
structure SNCPointedAffineChart {X : Scheme.{u}} {L : Type v} [Fintype L]
    (C : L → X.IdealSheafData) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X) where
  B : CommRingCat.{u}
  v : Spec B ⟶ X
  etale : Etale v
  t : L → B
  equations : ∀ i, (C i).comap v = Scheme.IdealSheafData.ofIdealTop
    (Ideal.span {(Scheme.ΓSpecIso B).inv (t i)})
  parameters : ∀ q : PrimeSpectrum B,
    ∃ (_h : IsNoetherianRing (Localization.AtPrime q.asIdeal))
      (e : Fin (Fintype.card L) ≃ L) (p : List (Localization.AtPrime q.asIdeal)),
      IsLocalRing.IsRegularSystemOfParameters p ∧
      List.Nodup ((List.ofFn (t ∘ e)).filter
        (fun z ↦ @decide (z ∈ q.asIdeal) (Classical.propDecidable _))) ∧
      List.Sublist (((List.ofFn (t ∘ e)).filter
        (fun z ↦ @decide (z ∈ q.asIdeal) (Classical.propDecidable _))).map
          (algebraMap B (Localization.AtPrime q.asIdeal))) p
  residual_regular : IsRegularScheme (Spec (.of (B ⧸ Ideal.span (Set.range t))))
  residual_connected : ConnectedSpace (Spec (.of (B ⧸ Ideal.span (Set.range t))))
  point : Spec (.of Ω) ⟶ Spec (.of (B ⧸ Ideal.span (Set.range t)))
  point_base : point ≫ Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (Ideal.span (Set.range t)))) ≫ v = s

/-- The ideal of the labelled residual intersection; no radical is inserted.
Source: ILO VIII 4.2.2(i)
(blueprint: lem-sfb-snc-pointed-affine-common-refinement). -/
abbrev SNCPointedAffineChart.ideal {X : Scheme.{u}} {L : Type v} [Fintype L]
    {C : L → X.IdealSheafData} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {s : Spec (.of Ω) ⟶ X} (Q : SNCPointedAffineChart C s) : Ideal Q.B :=
  Ideal.span (Set.range Q.t)

attribute [instance] SNCPointedAffineChart.residual_connected

/-- A pointed étale refinement, oriented in the direction of the coordinate-ring map.
Source: pointed affine refinement in ILO VIII 4.2.2(i)
(blueprint: lem-sfb-snc-pointed-affine-common-refinement). -/
structure SNCAffineRefinement {X : Scheme.{u}} {L : Type v} [Fintype L]
    {C : L → X.IdealSheafData} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {s : Spec (.of Ω) ⟶ X} (Q R : SNCPointedAffineChart C s) where
  ringMap : Q.B ⟶ R.B
  over_base : Spec.map ringMap ≫ Q.v = R.v
  etale : Etale (Spec.map ringMap)
  pointed : R.point ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk R.ideal)) ≫
    Spec.map ringMap = Q.point ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Q.ideal))

/-- An actual pair henselization, together with affine models of its pointed universal
cover and its reduction. The residual isomorphism preserves the marked point and the base.
No object is selected from a mere existence assertion.
Source: Stacks 0A02, 09ZS, 0BND
(blueprint: lem-sfb-snc-pointed-affine-common-refinement). -/
structure SNCAffineCoverData {X : Scheme.{u}} {L : Type v} [Fintype L]
    {C : L → X.IdealSheafData} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {s : Spec (.of Ω) ⟶ X} (Q : SNCPointedAffineChart C s) where
  henselization : Cocone (ObjectProperty.ι (fun A : Under Q.B ↦
    Etale (Spec.map A.hom) ∧ Function.Bijective
      (Ideal.quotientMap (Q.ideal.map A.hom.hom) A.hom.hom Ideal.le_comap_map)))
  isColimit : IsColimit henselization
  henselian : HenselianRing henselization.pt.right (Q.ideal.map henselization.pt.hom.hom)
  residual_bijective : Function.Bijective (Ideal.quotientMap
    (Q.ideal.map henselization.pt.hom.hom) henselization.pt.hom.hom Ideal.le_comap_map)
  connected : ConnectedSpace (Spec henselization.pt.right)
  henselizationPoint : Spec (.of Ω) ⟶ Spec henselization.pt.right
  henselizationPoint_base : henselizationPoint ≫ Spec.map henselization.pt.hom =
    Q.point ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Q.ideal))
  H : CommRingCat.{u}
  h : henselization.pt.right ⟶ H
  b : Q.B ⟶ H
  b_factor : henselization.pt.hom ≫ h = b
  coverPoint : Spec (.of Ω) ⟶ Spec H
  universalIso : Spec H ≅
    @Scheme.UniversalCover.cover _ connected Ω _ _ henselizationPoint
  universalIso_base : universalIso.hom ≫
    @Scheme.UniversalCover.proj _ connected Ω _ _ henselizationPoint = Spec.map h
  universalIso_point : coverPoint ≫ universalIso.hom =
    @Scheme.UniversalCover.pt _ connected Ω _ _ henselizationPoint
  residualCoverIso : Spec (.of (H ⧸ Q.ideal.map b.hom)) ≅
    Scheme.UniversalCover.cover Q.point
  residualCoverIso_base : residualCoverIso.hom ≫ Scheme.UniversalCover.proj Q.point =
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Q.ideal.map b.hom) b.hom
      Ideal.le_comap_map))
  residualCoverIso_point : Scheme.UniversalCover.pt Q.point ≫ residualCoverIso.inv ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Q.ideal.map b.hom))) = coverPoint

/-- The three ring maps with all henselization, base, and reduction squares. The pointed
conditions characterize the universal-cover maps independently of the chosen small systems.
Source: Stacks 0A02 and 0BND
(blueprint: lem-sfb-snc-pointed-affine-common-refinement). -/
structure SNCAffineCoverMap {X : Scheme.{u}} {L : Type v} [Fintype L]
    {C : L → X.IdealSheafData} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {s : Spec (.of Ω) ⟶ X} {Q R : SNCPointedAffineChart C s}
    (f : SNCAffineRefinement Q R) (E : SNCAffineCoverData Q) (F : SNCAffineCoverData R)
    where
  henselizationMap : E.henselization.pt.right ⟶ F.henselization.pt.right
  henselization_base : E.henselization.pt.hom ≫ henselizationMap =
    f.ringMap ≫ F.henselization.pt.hom
  henselization_point : F.henselizationPoint ≫ Spec.map henselizationMap = E.henselizationPoint
  coverMap : E.H ⟶ F.H
  cover_henselization : E.h ≫ coverMap = henselizationMap ≫ F.h
  cover_base : E.b ≫ coverMap = f.ringMap ≫ F.b
  cover_point : F.coverPoint ≫ Spec.map coverMap = E.coverPoint
  residualBaseMap : CommRingCat.of (Q.B ⧸ Q.ideal) ⟶ CommRingCat.of (R.B ⧸ R.ideal)
  residualBase_reduction : CommRingCat.ofHom (Ideal.Quotient.mk Q.ideal) ≫
    residualBaseMap = f.ringMap ≫ CommRingCat.ofHom (Ideal.Quotient.mk R.ideal)
  residualMap : CommRingCat.of (E.H ⧸ Q.ideal.map E.b.hom) ⟶
    CommRingCat.of (F.H ⧸ R.ideal.map F.b.hom)
  reduction : CommRingCat.ofHom (Ideal.Quotient.mk (Q.ideal.map E.b.hom)) ≫
    residualMap = coverMap ≫ CommRingCat.ofHom (Ideal.Quotient.mk (R.ideal.map F.b.hom))
  residual_base : CommRingCat.ofHom (Ideal.quotientMap (Q.ideal.map E.b.hom) E.b.hom
    Ideal.le_comap_map) ≫ residualMap = residualBaseMap ≫
      CommRingCat.ofHom (Ideal.quotientMap (R.ideal.map F.b.hom) F.b.hom Ideal.le_comap_map)
  residual_point : Scheme.UniversalCover.pt R.point ≫ F.residualCoverIso.inv ≫
    Spec.map residualMap = Scheme.UniversalCover.pt Q.point ≫ E.residualCoverIso.inv

/-- The existence conclusion for a finite family: one pointed common affine chart,
equality of extended residual ideals, and compatible maps on actual henselizations and
both universal covers. This is just the explicit existential conclusion of the node.
Source: Stacks 0A02, 09ZS; ILO VIII 4.2.2(i)
(blueprint: lem-sfb-snc-pointed-affine-common-refinement). -/
def HasSNCPointedAffineCommonRefinement {X : Scheme.{u}} {L : Type v} [Fintype L]
    {C : L → X.IdealSheafData} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {s : Spec (.of Ω) ⟶ X} {A : Type w}
    (Q : A → SNCPointedAffineChart C s) : Prop :=
  ∃ (W : SNCPointedAffineChart C s) (f : (i : A) → SNCAffineRefinement (Q i) W),
    (∀ i, (Q i).ideal.map (f i).ringMap.hom = W.ideal) ∧
    ∃ (E : (i : A) → SNCAffineCoverData (Q i)) (F : SNCAffineCoverData W),
      ∀ i, Nonempty (SNCAffineCoverMap (f i) (E i) F)

/-- Finite pointed affine SNC charts have a pointed affine common refinement, including
zero input charts and zero labels. Source: Stacks 0A02 and 09ZS; ILO VIII 4.2.2(i).
(blueprint: lem-sfb-snc-pointed-affine-common-refinement).

Proof: choose a reference labelled affine stratum chart through the point, even if the
input family is empty (lem-sfb-snc-labelled-affine-stratum-charts). Regularity and étaleness
make the input rings Noetherian (pqf-lem-locnoeth-lft, pqf-lem-affine-open-locnoeth).
Form the finite pointed fibre product, and choose an affine neighbourhood of its point
(def-pc-fibre-product, lem-weil-pbc-affine-opens-basis). Pull back the reference equations;
étale parameter transport preserves the parameter condition and makes the residual
intersection regular (lem-trf-etale-coordinate-divisor-parameters and
lem-trf-etale-coordinate-intersection-geometry). The residual Noetherian component through
the point is clopen (lem-sfb-noetherian-connected-components-open). Lift its idempotent to
an element of the affine ring and localize at that element, not at an idempotent of the
ambient ring (lem-weil-pbc-spec-clopen-idempotent and
lem-weil-pbc-principal-localization-open-immersion). Its residual scheme is exactly that
connected component. For no labels, perform this construction on the entire chart.
Equal pulled-back component ideals give equality of the extended summed ideals.
The henselian residual-cover lift supplies each cover datum
(lem-sfb-henselian-pointed-residual-cover-lift). The universal property of pair
henselization gives its map, and pointed-limit functoriality gives the unique map of
universal covers (lem-weil-pbc-henselization-universal-property,
lem-sfb-pointed-limit-finite-splitting). Quotienting gives the reduction map; pointed
uniqueness identifies it with the residual universal-cover map. -/
theorem exists_sncPointedAffineCommonRefinement
    {k : Type u} [Field k] (Y : Scheme.{u}) (a : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType a] [QuasiCompact a] [IsSeparated a]
    (_hY : IsRegularScheme Y) (D : Y.IdealSheafData)
    (_hD : IsStrictNormalCrossingsBoundary D) (n : ℕ) (C : Fin n → Y.IdealSheafData)
    (_hC : Function.Injective (fun i ↦ (C i).support) ∧
      (∀ i, IsIntegral (C i).subscheme ∧ IsRegularScheme (C i).subscheme) ∧
      D.support = ⨆ i, (C i).support ∧
      ∀ J : Finset (Fin n), ∀ z : (⨆ i ∈ J, C i).subscheme,
        IsRegularScheme ((⨆ i ∈ J, C i).subscheme) ∧
        ringKrullDim (Y.presheaf.stalk ((⨆ i ∈ J, C i).subschemeι z)) =
          ringKrullDim ((⨆ i ∈ J, C i).subscheme.presheaf.stalk z) + (J.card : ℕ))
    (I : Finset (Fin n)) (U : Y.Opens)
    (_hU : U = (⨆ j : {j : Fin n // j ∉ I}, (C j.val).support).compl)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ ((⨆ i ∈ I, (C i).comap U.ι).radical).subscheme)
    {A : Type w} [Finite A]
    (Q : A → SNCPointedAffineChart (Ω := Ω) (fun i : I ↦ (C i.val).comap U.ι)
      (s ≫ ((⨆ i ∈ I, (C i).comap U.ι).radical).subschemeι)) :
    HasSNCPointedAffineCommonRefinement Q := by
  sorry

/-- Maps of henselizations and pointed universal covers are unique and therefore commute
under further refinements and under the canonical isomorphisms of cover presentations.
Source: Stacks 0A02 and 0BND
(blueprint: lem-sfb-snc-pointed-affine-common-refinement).

Proof: equal component ideals give equality of their extensions, hence the residual base
map. The henselization universal property uniquely extends the coefficient map, preserving
the marked point by its quotient description. Pointed-limit functoriality gives the cover
map; its reduction is pointed and hence is the corresponding residual cover map. For a
composite refinement the composites obey these same equations, so uniqueness gives the
composition laws. For different small cofinal systems apply the same uniqueness to their
canonical pointed identifications. This is steps 4--6 of the node, using
lem-weil-pbc-henselization-universal-property, lem-sfb-henselian-pointed-residual-cover-lift,
and lem-sfb-pointed-limit-finite-splitting. -/
theorem sncAffineCoverMap_unique {X : Scheme.{u}} {L : Type v} [Fintype L]
    {C : L → X.IdealSheafData} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {s : Spec (.of Ω) ⟶ X} {Q R : SNCPointedAffineChart C s}
    (f : SNCAffineRefinement Q R) (E : SNCAffineCoverData Q) (F : SNCAffineCoverData R) :
    Q.ideal.map f.ringMap.hom = R.ideal ∧
      Nonempty (SNCAffineCoverMap f E F) ∧ Subsingleton (SNCAffineCoverMap f E F) := by
  sorry

/-- Composition on each of the four ring levels, and hence every comparison square,
agrees with the comparison of the composite pointed refinement.
Source: Stacks 0A02 and 0BND
(blueprint: lem-sfb-snc-pointed-affine-common-refinement).

Proof: composing the displayed base and marked-point equations gives those for the
composite refinement. The henselization universal property gives the first equality;
pointed-limit uniqueness gives the cover equality. Surjectivity of quotient maps gives
both residual equalities. Applying this to identity refinements also proves independence
of the affine model and small cofinal presentation, with their canonical identifications.
These are exactly the uniqueness and quotient arguments of node step 6. -/
theorem sncAffineCoverMap_composition {X : Scheme.{u}} {L : Type v} [Fintype L]
    {C : L → X.IdealSheafData} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {s : Spec (.of Ω) ⟶ X} {Q R T : SNCPointedAffineChart C s}
    (f : SNCAffineRefinement Q R) (g : SNCAffineRefinement R T)
    (fg : SNCAffineRefinement Q T) (_hfg : fg.ringMap = f.ringMap ≫ g.ringMap)
    (E : SNCAffineCoverData Q) (F : SNCAffineCoverData R) (G : SNCAffineCoverData T)
    (m : SNCAffineCoverMap f E F) (n : SNCAffineCoverMap g F G)
    (mn : SNCAffineCoverMap fg E G) :
    mn.henselizationMap = m.henselizationMap ≫ n.henselizationMap ∧
      mn.coverMap = m.coverMap ≫ n.coverMap ∧
      mn.residualBaseMap = m.residualBaseMap ≫ n.residualBaseMap ∧
      mn.residualMap = m.residualMap ≫ n.residualMap := by
  sorry

end AlgebraicGeometry
