module
public import Sheaf.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The map of tuple open subschemes to the pullback of the source tuple open.
It uses the actual inclusions of opens, not a choice of a comparison map.
Source: Stacks Project, Tag 01FD, tuple restriction maps.
(blueprint: lem-pbc-etale-additive-cech-pullback-total-map) -/
noncomputable def additiveCechTuplePullback
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (V : ι → Y.Opens)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (p : ℕ) (y : Fin (p + 1) → ι) :
    (additiveCechOpenInclusion Y).obj (∏ᶜ fun l ↦ V (y l)) ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ g).obj
        ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l))) :=
  (additiveCechOpenInclusion Y).map (homOfLE
    ((TopCat.Presheaf.piObj_le_iInf V y).trans
      ((hinter p y).trans (g.preimage_mono (TopCat.Presheaf.iInf_le_piObj U y))))) ≫
    Etale.openSectionPullback g (∏ᶜ fun l ↦ U (y l))

/-- Explicit product of tuple section transfers in bidegree (p,q).
Source: Stacks Project, Tag 01FD, map of double complexes.
(blueprint: lem-pbc-etale-additive-cech-pullback-total-map) -/
noncomputable def additiveCechPullbackBidegree
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (V : ι → Y.Opens)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (I : InjectiveResolution X.etaleAdditiveSheaf)
    (J : InjectiveResolution Y.etaleAdditiveSheaf)
    (α : I.cocomplex ⟶
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
        (.up ℕ)).obj J.cocomplex) (p q : ℕ) :
    ((etaleOpenCechResolutionDoubleComplex X (additiveCechOpenInclusion X) U I).X p).X q ⟶
      ((etaleOpenCechResolutionDoubleComplex Y (additiveCechOpenInclusion Y) V J).X p).X q :=
  Pi.lift (fun y : Fin (p + 1) → ι ↦ Pi.π _ y ≫
    (Etale.resolutionSectionTransfer g I.cocomplex J.cocomplex α _ _
      (additiveCechTuplePullback g U V hinter p y)).f q)

/-- Specification on all total summands; it determines the total map uniquely.
Source: Stacks Project, Tag 01FD; the coproduct universal property.
(blueprint: lem-pbc-etale-additive-cech-pullback-total-map) -/
def IsAdditiveCechPullbackTotalMap
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (V : ι → Y.Opens)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (I : InjectiveResolution X.etaleAdditiveSheaf)
    (J : InjectiveResolution Y.etaleAdditiveSheaf)
    (α : I.cocomplex ⟶
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
        (.up ℕ)).obj J.cocomplex)
    (t : additiveCechTotal U I ⟶ additiveCechTotal V J) : Prop :=
  ∀ p q n (h : p + q = n),
    (etaleOpenCechResolutionDoubleComplex X (additiveCechOpenInclusion X) U I).ιTotal
        (.up ℕ) p q n h ≫ t.f n =
      additiveCechPullbackBidegree g U V hinter I J α p q ≫
        (etaleOpenCechResolutionDoubleComplex Y (additiveCechOpenInclusion Y) V J).ιTotal
          (.up ℕ) p q n h

/-- Tuplewise restriction maps assemble to a total cochain map satisfying the alpha square.
Source: Stacks Project, Tag 01FD, Lemma 20.15.1, double-complex construction.
(blueprint: lem-pbc-etale-additive-cech-pullback-total-map)
Proof: Use additiveCechPullbackBidegree in each bidegree. For every tuple deletion,
the square of additiveCechTuplePullback maps commutes: composing with the two
pullback projections gives respectively the same inclusion followed by g, and
the same target open inclusion. The naturality of resolutionSectionTransfer
then makes these maps commute with each face restriction, hence with their
alternating sum. The vertical equation is the chain-map equation of
resolutionSectionTransfer. These equations define a morphism of double
complexes. Totalize it; total inclusion naturality gives the stated summand
specification, with unchanged bidegree and therefore unchanged signs.
For alpha, the analogous square with the terminal etale objects commutes by
the same two pullback projections. Section-transfer naturality, product
extensionality in Cech degree zero, and total inclusion naturality give the
alpha square. No augmentation equation is used. Empty tuple families give
zero products and degree zero uses the same identities without any negative
index. The specification on all total summands determines t uniquely. -/
theorem exists_additiveCech_pullback_total_map
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (V : ι → Y.Opens)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (I : InjectiveResolution X.etaleAdditiveSheaf)
    (J : InjectiveResolution Y.etaleAdditiveSheaf)
    (α : I.cocomplex ⟶
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
        (.up ℕ)).obj J.cocomplex) (n : ℕ) :
    ∃ t : additiveCechTotal U I ⟶ additiveCechTotal V J,
      IsAdditiveCechPullbackTotalMap g U V hinter I J α t ∧
      (additiveCechAlpha U I n ≫ t.f n =
        (Etale.globalResolutionSectionTransfer g I.cocomplex J.cocomplex α).f n ≫
          additiveCechAlpha V J n) := by sorry
end AlgebraicGeometry.Scheme.Modules
