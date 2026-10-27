/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.AlgebraicGeometry.NodalBranchSchemeRepair
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import WeilConjectures.RingTheory.AssociatedGradedRing

/-! # Gluing the affine graph cones without separatedness

Source: Stacks Project, Divisors, Tags 0630--0635; Constructions, Tags 01NQ and 01O3;
Curves, Tag 0CBT (3) (blueprint: lem-sfb-graph-cone-gluing).

The presentation uses the existing affine-basis model of quasi-coherent graded algebras.
Every chart is the actual associated graded ring of the kernel of the affine graph map.
All comparisons are normalized on homogeneous ideal representatives. Relative Proj is the
existing canonical gluing construction, and the branch scheme is the actual blow-up fibre.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.GraphCone

/-- A closed centre in a completely arbitrary scheme morphism.
Source: Divisors, Tags 0630--0633 (blueprint: lem-sfb-graph-cone-gluing). -/
structure Diagram where
  Z : Scheme.{u}
  X : Scheme.{u}
  T : Scheme.{u}
  i : Z ⟶ X
  f : X ⟶ T
  [closed : IsClosedImmersion i]

attribute [instance] Diagram.closed

/-- An affine pair in the diagram, with the containment required in the statement.
Source: Divisors, Tag 0633 (blueprint: lem-sfb-graph-cone-gluing). -/
structure Chart (d : Diagram.{u}) where
  V : d.T.affineOpens
  U : d.X.affineOpens
  le : U.1 ≤ d.f ⁻¹ᵁ V.1

/-- The affine open of the centre, with its actual inverse-image open.
Source: Divisors, Tag 0633 (blueprint: lem-sfb-graph-cone-gluing). -/
def Chart.centre {d : Diagram.{u}} (c : Chart d) : d.Z.affineOpens :=
  ⟨d.i ⁻¹ᵁ c.U.1, c.U.2.preimage d.i⟩

/-- The restricted family over the chosen affine base.
Source: Schemes, Tag 01JQ (blueprint: lem-sfb-graph-cone-gluing). -/
def Chart.family {d : Diagram.{u}} (c : Chart d) : c.U.1.toScheme ⟶ c.V.1.toScheme :=
  d.f.resLE c.V.1 c.U.1 c.le

/-- The restricted closed centre.
Source: Divisors, Tag 0633 (blueprint: lem-sfb-graph-cone-gluing). -/
def Chart.inclusion {d : Diagram.{u}} (c : Chart d) :
    c.centre.1.toScheme ⟶ c.U.1.toScheme := d.i ∣_ c.U.1

/-- The affine ambient fibre product of the graph.
Source: Schemes, Tags 01I4 and 01JQ (blueprint: lem-sfb-graph-cone-gluing). -/
def Chart.ambient {d : Diagram.{u}} (c : Chart d) : Scheme.{u} :=
  pullback c.family (c.inclusion ≫ c.family)

/-- The actual graph, with first component the inclusion and second component identity.
Source: Divisors, Tag 0633 (blueprint: lem-sfb-graph-cone-gluing). -/
def Chart.graph {d : Diagram.{u}} (c : Chart d) : c.centre.1.toScheme ⟶ c.ambient :=
  pullback.lift c.inclusion (𝟙 _) (Category.id_comp _).symm

/-- The affine graph ideal in the actual ambient section ring.
Source: Divisors, Tag 0633 (blueprint: lem-sfb-graph-cone-gluing). -/
def Chart.ideal {d : Diagram.{u}} (c : Chart d) : Ideal Γ(c.ambient, ⊤) :=
  RingHom.ker (c.graph.app ⊤).hom

/-- The restriction of an ideal-power representative, followed by its quotient class.
The bound inclusion is the exact ideal-power condition, not a chosen image class.
Source: Divisors, Tags 0633--0635 (blueprint: lem-sfb-graph-cone-gluing). -/
def pieceClass {R S : Type u} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)
    (φ : R →+* S) (n : ℕ) (h : I ^ n ≤ (J ^ n).comap φ) (a : ↥(I ^ n)) :
    Ideal.associatedGradedPiece J n :=
  Submodule.Quotient.mk ⟨φ a, h a.property⟩

/-- The ambient of the global graph. Its graph need not be closed.
Source: Divisors, Tag 0630 (blueprint: lem-sfb-graph-cone-gluing). -/
def Diagram.ambient (d : Diagram.{u}) : Scheme.{u} := pullback d.f (d.i ≫ d.f)

/-- The global graph, specified by its two projections.
Source: Divisors, Tag 0630 (blueprint: lem-sfb-graph-cone-gluing). -/
def Diagram.graph (d : Diagram.{u}) : d.Z ⟶ d.ambient :=
  pullback.lift d.i (𝟙 _) (Category.id_comp _).symm

/-- The canonical map of an affine graph ambient into the global ambient.
Source: Schemes, Tags 01I4 and 01JQ (blueprint: lem-sfb-graph-cone-gluing). -/
def Chart.globalMap {d : Diagram.{u}} (c : Chart d) : c.ambient ⟶ d.ambient :=
  pullback.map _ _ _ _ c.U.1.ι c.centre.1.ι c.V.1.ι
    (by simp [Chart.family]) (by simp [Chart.family, Chart.inclusion, Chart.centre])

/-- An affine open neighbourhood in the global graph ambient, with its actual closed graph.
A section-ring presentation allows an affine open's own ring, without identifying it
silently with the global sections of its open subscheme. The kernel equation fixes its ideal.
Source: Divisors, Tags 0630--0635 (blueprint: lem-sfb-graph-cone-gluing). -/
structure LocalChart (d : Diagram.{u}) where
  Y : Scheme.{u}
  [affine : IsAffine Y]
  centre : d.Z.affineOpens
  j : centre.1.toScheme ⟶ Y
  [closed : IsClosedImmersion j]
  ambient : Y ⟶ d.ambient
  [openImmersion : IsOpenImmersion ambient]
  square : IsPullback j centre.1.ι ambient d.graph
  R : CommRingCat.{u}
  sections : R ≅ Γ(Y, ⊤)
  ideal : Ideal R
  kernel : ideal = (RingHom.ker j.appTop.hom).comap sections.hom.hom

attribute [instance] LocalChart.affine LocalChart.closed LocalChart.openImmersion

/-- The ring map of an actual local graph square, including the section-ring transports.
Source: Divisors, Tags 0633--0635 (blueprint: lem-sfb-graph-cone-gluing). -/
def LocalChart.ringMap {d : Diagram.{u}} (c c' : LocalChart d) (g : c.Y ⟶ c'.Y) :
    c'.R →+* c.R :=
  c.sections.inv.hom.comp (g.appTop.hom.comp c'.sections.hom.hom)

/-- Affine graph charts are open subspaces of the global ambient and have the actual
inverse-image centre. The affine graph itself is closed.
Source: Schemes, Tags 01I4, 01JQ and 01QO (blueprint: lem-sfb-graph-cone-gluing).
Proof: write the affine graph as A tensor_R B -> B, a tensor b -> a-bar b.
This is surjective by 1 tensor b, hence closed. The factor inclusions U -> X and Z_U -> Z
are open immersions; base change and composition make the ambient map open. The two graph
components identify its inverse image with Z_U, giving the asserted pullback square. -/
theorem Chart.local_properties {d : Diagram.{u}} (c : Chart d) :
    IsAffine c.ambient ∧ IsClosedImmersion c.graph ∧ IsOpenImmersion c.globalMap ∧
      IsPullback c.graph c.centre.1.ι c.globalMap d.graph := by
  sorry

/-- An original affine graph chart as a closed affine graph neighbourhood.
Source: Divisors, Tag 0633 (blueprint: lem-sfb-graph-cone-gluing). -/
def Chart.local {d : Diagram.{u}} (c : Chart d) : LocalChart d where
  Y := c.ambient
  affine := c.local_properties.1
  centre := c.centre
  j := c.graph
  closed := c.local_properties.2.1
  ambient := c.globalMap
  openImmersion := c.local_properties.2.2.1
  square := c.local_properties.2.2.2
  R := Γ(c.ambient, ⊤)
  sections := Iso.refl _
  ideal := c.ideal
  kernel := rfl

/-- Isomorphisms of the full diagram, with both squares specified.
Source: Divisors, Tag 0634 (blueprint: lem-sfb-graph-cone-gluing). -/
structure DiagramIso (d e : Diagram.{u}) where
  z : d.Z ≅ e.Z
  x : d.X ≅ e.X
  t : d.T ≅ e.T
  wi : d.i ≫ x.hom = z.hom ≫ e.i
  wf : d.f ≫ t.hom = x.hom ≫ e.f

/-- The induced affine graph square. Its map is constrained by both fibre-product
projections, so it is the unique canonical map, rather than an arbitrary ambient map.
Identity diagram maps give affine refinements, including common refinements of overlaps.
Source: Divisors, Tags 0633--0635 (blueprint: lem-sfb-graph-cone-gluing). -/
structure ChartSquare {d e : Diagram.{u}} (x : d.X ⟶ e.X) (z : d.Z ⟶ e.Z)
    (c : Chart d) (c' : Chart e) where
  hU : c.U.1 ≤ x ⁻¹ᵁ c'.U.1
  hZ : c.centre.1 ≤ z ⁻¹ᵁ c'.centre.1
  g : c.ambient ⟶ c'.ambient
  fst : g ≫ pullback.fst c'.family (c'.inclusion ≫ c'.family) =
    pullback.fst c.family (c.inclusion ≫ c.family) ≫ x.resLE c'.U.1 c.U.1 hU
  snd : g ≫ pullback.snd c'.family (c'.inclusion ≫ c'.family) =
    pullback.snd c.family (c.inclusion ≫ c.family) ≫
      z.resLE c'.centre.1 c.centre.1 hZ
  graph : c.graph ≫ g = z.resLE c'.centre.1 c.centre.1 hZ ≫ c'.graph

/-- The specified graph square carries every power of the target graph ideal into
that of the source graph ideal. This supplies the inclusion used by the local class map.
Source: Divisors, Tag 0634 (blueprint: lem-sfb-graph-cone-gluing).
Proof: apply global sections to `s.graph`. If a section vanishes on the target graph,
its pullback vanishes on the source graph, by the commutative square. This gives the
kernel inclusion. Taking powers and using `Ideal.map_pow` gives the displayed inclusion,
including n = 0, when both ideals are the unit ideal. -/
theorem ChartSquare.idealPower_le {d e : Diagram.{u}} {x : d.X ⟶ e.X} {z : d.Z ⟶ e.Z}
    {c : Chart d} {c' : Chart e} (s : ChartSquare x z c c') (n : ℕ) :
    c'.ideal ^ n ≤ (c.ideal ^ n).comap s.g.appTop.hom := by
  sorry

/-- The class of the pullback of an ideal-power representative through the specified
ambient map. The quotient class is [g-sharp(a)] in degree n.
Source: Divisors, Tags 0633--0635 (blueprint: lem-sfb-graph-cone-gluing). -/
def ChartSquare.pieceMap {d e : Diagram.{u}} {x : d.X ⟶ e.X} {z : d.Z ⟶ e.Z}
    {c : Chart d} {c' : Chart e} (s : ChartSquare x z c c') (n : ℕ)
    (a : ↥(c'.ideal ^ n)) : Ideal.associatedGradedPiece c.ideal n :=
  pieceClass c'.ideal c.ideal s.g.appTop.hom n (s.idealPower_le n) a

/-- A graded algebra map over a base morphism, on every affine pair. Restrictions,
scalars, homogeneous degrees and the irrelevant ideal all use the existing APIs.
Source: Divisors, Tags 0634--0635; Constructions, Tag 01NQ
(blueprint: lem-sfb-graph-cone-gluing). -/
structure AlgebraMapOver {Z Z' : Scheme.{u}} (z : Z ⟶ Z')
    (A : Z.GradedAlgebraData) (B : Z'.GradedAlgebraData) where
  app : ∀ (U : Z.affineOpens) (V : Z'.affineOpens) (_h : U.1 ≤ z ⁻¹ᵁ V.1),
    B.grading V →+*ᵍ A.grading U
  scalar : ∀ (U : Z.affineOpens) (V : Z'.affineOpens) (h : U.1 ≤ z ⁻¹ᵁ V.1)
    (r : Γ(Z', V.1)),
    app U V h (algebraMap _ _ r) = algebraMap _ _ (z.appLE V.1 U.1 h r)
  naturality : ∀ (U W : Z.affineOpens) (V V' : Z'.affineOpens)
    (h : U.1 ≤ z ⁻¹ᵁ V.1) (hnew : W.1 ≤ z ⁻¹ᵁ V'.1)
    (a : W ≤ U) (b : V ≤ V') (q : B.obj V'),
    A.res a (app U V h (B.res b q)) = app W V' hnew q
  irrelevant : ∀ (U : Z.affineOpens) (V : Z'.affineOpens) (h : U.1 ≤ z ⁻¹ᵁ V.1),
    HomogeneousIdeal.irrelevant (A.grading U) ≤
      (HomogeneousIdeal.irrelevant (B.grading V)).map (app U V h)

/-- A global graded algebra with all affine graph charts. Ring equivalences preserve
units and multiplication. Restrictions send [a] to [g-sharp(a)], not just to some
homogeneous class. Local closed neighbourhoods use the same representative formula.
The restriction formula is required for every induced graph square, so it also fixes
all overlap transitions after affine refinement, without assuming intersections affine.
Source: Divisors, Tags 0630--0635 (blueprint: lem-sfb-graph-cone-gluing). -/
structure Gluing (d : Diagram.{u}) where
  algebra : d.Z.GradedAlgebraData
  chart : ∀ c : Chart d, algebra.obj c.centre ≃+* Ideal.associatedGraded c.ideal
  homogeneous : ∀ (c : Chart d) (n : ℕ) (a : algebra.obj c.centre),
    a ∈ algebra.grading c.centre n ↔
      ∃ b : Ideal.associatedGradedPiece c.ideal n,
        chart c a = DirectSum.of (Ideal.associatedGradedPiece c.ideal) n b
  scalar : ∀ (c : Chart d) (a : Γ(c.ambient, ⊤)),
    chart c (algebraMap _ _ (c.centre.1.topIso.hom (c.graph.app ⊤ a))) =
      Ideal.associatedGradedRingHom c.ideal a
  degreeZero : ∀ U : d.Z.affineOpens,
    Function.Injective (algebraMap Γ(d.Z, U.1) (algebra.obj U)) ∧
      Set.range (algebraMap Γ(d.Z, U.1) (algebra.obj U)) =
        (algebra.grading U 0 : Set (algebra.obj U))
  restriction : ∀ (c c' : Chart d) (s : ChartSquare (𝟙 d.X) (𝟙 d.Z) c c')
    (h : c.centre ≤ c'.centre) (n : ℕ) (a : ↥(c'.ideal ^ n)),
    chart c (algebra.res h ((chart c').symm
      (DirectSum.of (Ideal.associatedGradedPiece c'.ideal) n (Submodule.Quotient.mk a)))) =
        DirectSum.of (Ideal.associatedGradedPiece c.ideal) n
          (s.pieceMap n a)
  localChart : ∀ c : LocalChart d, algebra.obj c.centre ≃+* Ideal.associatedGraded c.ideal
  localChart_agrees : ∀ c : Chart d, localChart c.local = chart c
  localHomogeneous : ∀ (c : LocalChart d) (n : ℕ) (a : algebra.obj c.centre),
    a ∈ algebra.grading c.centre n ↔
      ∃ b : Ideal.associatedGradedPiece c.ideal n,
        localChart c a = DirectSum.of (Ideal.associatedGradedPiece c.ideal) n b
  localScalar : ∀ (c : LocalChart d) (a : c.R),
    localChart c (algebraMap _ _
      (c.centre.1.topIso.hom (c.j.appTop (c.sections.hom a)))) =
        Ideal.associatedGradedRingHom c.ideal a
  localRestriction : ∀ (c c' : LocalChart d) (g : c.Y ⟶ c'.Y)
    (h : c.centre ≤ c'.centre) (_ambient : g ≫ c'.ambient = c.ambient)
    (_graph : c.j ≫ g = d.Z.homOfLE h ≫ c'.j) (n : ℕ)
    (hn : c'.ideal ^ n ≤ (c.ideal ^ n).comap (c.ringMap c' g)) (a : ↥(c'.ideal ^ n)),
    localChart c (algebra.res h ((localChart c').symm
      (DirectSum.of (Ideal.associatedGradedPiece c'.ideal) n (Submodule.Quotient.mk a)))) =
        DirectSum.of (Ideal.associatedGradedPiece c.ideal) n
          (pieceClass c'.ideal c.ideal (c.ringMap c' g) n hn a)

/-- The fixed first-Fitting diagram, with no nodal or flatness hypothesis.
Source: Curves, Tag 0CBT (3) (blueprint: lem-sfb-graph-cone-gluing). -/
def singularDiagram {X T : Scheme.{u}} (f : X ⟶ T) [LocallyOfFiniteType f] : Diagram where
  Z := (Scheme.firstFittingIdealSheaf f).subscheme
  X := X
  T := T
  i := Scheme.firstFittingSingularSubscheme f
  f := f

/-- The centre open above an affine open of the fixed coborder neighbourhood.
Source: Divisors, Tag 01OG (blueprint: lem-sfb-graph-cone-gluing). -/
def branchCentre {X T : Scheme.{u}} (f : X ⟶ T) [LocallyOfFiniteType f]
    (W : (Scheme.nodalBranchGraph f).coborderRange.toScheme.affineOpens) :
    (singularDiagram f).Z.affineOpens :=
  ⟨Scheme.nodalBranchClosedGraph f ⁻¹ᵁ W.1,
    W.2.preimage (Scheme.nodalBranchClosedGraph f)⟩

/-- The fixed coborder blow-up chart has exactly the closed graph's kernel ideal and
inverse-image centre, with the canonical section-ring transport.
Source: Divisors, Tags 0633, 01OG and 0804 (blueprint: lem-sfb-graph-cone-gluing).
Proof: restrict the coborder factorization of the graph to W. The closed factor remains
closed and the open factor remains open. Paste its restriction square with the coborder
square to obtain the displayed pullback. The kernel ideal on W is the kernel of j-sharp
by the quasi-compact kernel formula; the topIso transports the same map to W.toScheme. -/
theorem branchChart_properties {X T : Scheme.{u}} (f : X ⟶ T) [LocallyOfFiniteType f]
    (W : (Scheme.nodalBranchGraph f).coborderRange.toScheme.affineOpens) :
    IsPullback (Scheme.nodalBranchClosedGraph f ∣_ W.1) (branchCentre f W).1.ι
      (W.1.ι ≫ (Scheme.nodalBranchGraph f).coborderRange.ι) (singularDiagram f).graph ∧
    (Scheme.nodalBranchClosedGraph f).ker.ideal W =
      (RingHom.ker (Scheme.nodalBranchClosedGraph f ∣_ W.1).appTop.hom).comap
        W.1.topIso.inv.hom := by
  sorry

/-- The actual affine coborder chart, with the ideal used in the actual blow-up.
Source: Divisors, Tags 01OG and 0804 (blueprint: lem-sfb-graph-cone-gluing). -/
def branchChart {X T : Scheme.{u}} (f : X ⟶ T) [LocallyOfFiniteType f]
    (W : (Scheme.nodalBranchGraph f).coborderRange.toScheme.affineOpens) :
    LocalChart (singularDiagram f) where
  Y := W.1.toScheme
  affine := W.2
  centre := branchCentre f W
  j := Scheme.nodalBranchClosedGraph f ∣_ W.1
  ambient := W.1.ι ≫ (Scheme.nodalBranchGraph f).coborderRange.ι
  square := (branchChart_properties f W).1
  R := Γ((Scheme.nodalBranchGraph f).coborderRange.toScheme, W.1)
  sections := W.1.topIso.symm
  ideal := (Scheme.nodalBranchClosedGraph f).ker.ideal W
  kernel := (branchChart_properties f W).2

/-- The Step-8 normalization of the branch identification on every actual blow-up chart.
The tensor quotient is expressed by its balanced pure-tensor formula: a tensor r-bar is
q(a X^n) times the degree-zero scalar r-bar, and its image is the class of ar.
The final equality fixes the map to the blow-up on its affine-base Proj charts; together
with the projection to Z it fixes the map to the actual exceptional fibre.
Source: Divisors, Tags 0633, 01OG and 0804; Constructions, Tag 01O3
(blueprint: lem-sfb-graph-cone-gluing). -/
structure BranchNormalization {X T : Scheme.{u}} (f : X ⟶ T) [LocallyOfFiniteType f]
    (G : Gluing (singularDiagram f))
    (e : G.algebra.relProj ≅ Scheme.nodalBranchScheme f) where
  reesMap : ∀ W : (Scheme.nodalBranchGraph f).coborderRange.toScheme.affineOpens,
    reesGrading (branchChart f W).ideal →+*ᵍ G.algebra.grading (branchChart f W).centre
  quotient : ∀ (W : (Scheme.nodalBranchGraph f).coborderRange.toScheme.affineOpens)
    (n : ℕ) (a : ↥((branchChart f W).ideal ^ n)) (r : (branchChart f W).R),
    G.localChart (branchChart f W)
      (reesMap W (reesMonomial (branchChart f W).ideal a a.property) *
        algebraMap _ _ ((branchChart f W).centre.1.topIso.hom
          ((branchChart f W).j.appTop ((branchChart f W).sections.hom r)))) =
      DirectSum.of (Ideal.associatedGradedPiece (branchChart f W).ideal) n
        (Submodule.Quotient.mk ⟨a.val * r,
          Ideal.mul_mem_right r ((branchChart f W).ideal ^ n) a.property⟩)
  irrelevant : ∀ W : (Scheme.nodalBranchGraph f).coborderRange.toScheme.affineOpens,
    HomogeneousIdeal.irrelevant (G.algebra.grading (branchChart f W).centre) ≤
      (HomogeneousIdeal.irrelevant (reesGrading (branchChart f W).ideal)).map (reesMap W)
  chart : ∀ W : (Scheme.nodalBranchGraph f).coborderRange.toScheme.affineOpens,
    G.algebra.relProjι (branchChart f W).centre ≫ e.hom ≫ pullback.fst _ _ =
      Proj.map (reesMap W) (irrelevant W) ≫
        (Scheme.nodalBranchClosedGraph f).ker.blowupι W

/-- Simultaneous canonical gluing and functoriality. Algebra maps are uniquely normalized
on the same affine ideal classes. Proj maps are uniquely normalized by their local Proj
charts, and preserve the structural maps to the centre. Thus all affine choices, units,
products and overlap cocycles refer to the same construction.
Source: Divisors, Tags 0630--0635; Constructions, Tags 01NQ and 01O3; Curves, Tag 0CBT (3)
(blueprint: lem-sfb-graph-cone-gluing). -/
structure Construction where
  obj : ∀ d : Diagram.{u}, Gluing d
  algebraMap : ∀ {d e : Diagram.{u}} (h : DiagramIso d e),
    AlgebraMapOver h.z.hom (obj d).algebra (obj e).algebra
  algebraMap_bijective : ∀ {d e : Diagram.{u}} (h : DiagramIso d e)
    (U : d.Z.affineOpens) (V : e.Z.affineOpens) (q : U.1 ≤ h.z.hom ⁻¹ᵁ V.1),
    U.1 = h.z.hom ⁻¹ᵁ V.1 → Function.Bijective ((algebraMap h).app U V q)
  algebraMap_class : ∀ {d e : Diagram.{u}} (h : DiagramIso d e)
    (c : Chart d) (c' : Chart e) (s : ChartSquare h.x.hom h.z.hom c c')
    (n : ℕ) (a : ↥(c'.ideal ^ n)),
    (obj d).chart c ((algebraMap h).app c.centre c'.centre s.hZ
      (((obj e).chart c').symm
        (DirectSum.of (Ideal.associatedGradedPiece c'.ideal) n (Submodule.Quotient.mk a)))) =
      DirectSum.of (Ideal.associatedGradedPiece c.ideal) n
        (s.pieceMap n a)
  algebraMap_id : ∀ (d : Diagram.{u}) (h : DiagramIso d d)
    (_hz : h.z.hom = 𝟙 d.Z) (_hx : h.x.hom = 𝟙 d.X) (_ht : h.t.hom = 𝟙 d.T)
    (U V : d.Z.affineOpens) (q : U.1 ≤ h.z.hom ⁻¹ᵁ V.1) (r : U ≤ V),
    (algebraMap h).app U V q = (obj d).algebra.res r
  algebraMap_comp : ∀ {d e k : Diagram.{u}} (h : DiagramIso d e) (h' : DiagramIso e k)
    (h'' : DiagramIso d k) (_hz : h''.z.hom = h.z.hom ≫ h'.z.hom)
    (_hx : h''.x.hom = h.x.hom ≫ h'.x.hom)
    (_ht : h''.t.hom = h.t.hom ≫ h'.t.hom)
    (U : d.Z.affineOpens) (V : e.Z.affineOpens) (W : k.Z.affineOpens)
    (a : U.1 ≤ h.z.hom ⁻¹ᵁ V.1) (b : V.1 ≤ h'.z.hom ⁻¹ᵁ W.1)
    (c : U.1 ≤ h''.z.hom ⁻¹ᵁ W.1),
    (algebraMap h'').app U W c = ((algebraMap h).app U V a).comp
      ((algebraMap h').app V W b)
  projMap : ∀ {d e : Diagram.{u}} (_h : DiagramIso d e),
    (obj d).algebra.relProj ⟶ (obj e).algebra.relProj
  projMap_isIso : ∀ {d e : Diagram.{u}} (h : DiagramIso d e), IsIso (projMap h)
  projMap_over : ∀ {d e : Diagram.{u}} (h : DiagramIso d e),
    projMap h ≫ (obj e).algebra.relProjHom = (obj d).algebra.relProjHom ≫ h.z.hom
  projMap_chart : ∀ {d e : Diagram.{u}} (h : DiagramIso d e)
    (U : d.Z.affineOpens) (V : e.Z.affineOpens) (q : U.1 ≤ h.z.hom ⁻¹ᵁ V.1),
    (obj d).algebra.relProjι U ≫ projMap h =
      Proj.map ((algebraMap h).app U V q) ((algebraMap h).irrelevant U V q) ≫
        (obj e).algebra.relProjι V
  projMap_id : ∀ (d : Diagram.{u}) (h : DiagramIso d d)
    (_hz : h.z.hom = 𝟙 d.Z) (_hx : h.x.hom = 𝟙 d.X) (_ht : h.t.hom = 𝟙 d.T),
    projMap h = 𝟙 _
  projMap_comp : ∀ {d e k : Diagram.{u}} (h : DiagramIso d e) (h' : DiagramIso e k)
    (h'' : DiagramIso d k) (_hz : h''.z.hom = h.z.hom ≫ h'.z.hom)
    (_hx : h''.x.hom = h.x.hom ≫ h'.x.hom)
    (_ht : h''.t.hom = h.t.hom ≫ h'.t.hom), projMap h'' = projMap h ≫ projMap h'
  branch : ∀ {X T : Scheme.{u}} (f : X ⟶ T) [LocallyOfFiniteType f],
    ∃ e : (obj (singularDiagram f)).algebra.relProj ≅ Scheme.nodalBranchScheme f,
      e.hom ≫ Scheme.nodalBranchMap f = (obj (singularDiagram f)).algebra.relProjHom ∧
        Nonempty (BranchNormalization f (obj (singularDiagram f)) e)

/-- All affine graph cones glue, with their canonical algebra and Proj functoriality,
and the singular-diagram Proj is the actual branch scheme over the singular centre.
Source: Stacks Project, Divisors, Tags 0630--0635; Constructions, Tags 01NQ and 01O3;
Curves, Tag 0CBT (3) (blueprint: lem-sfb-graph-cone-gluing).

Proof (the eight steps of the node):
1. On an affine pair Spec A over Spec R with centre Spec B, the graph corresponds to
   A tensor_R B -> B, a tensor b -> a-bar b. It is surjective since 1 tensor b maps to b.
   Use `lem-weil-pbc-fibre-product-affine-spectra` and the affine closed-immersion criterion.
2. The global graph is an immersion by `lem-zl-immersion-cancellation`, since its first
   projection is the closed inclusion. Factor it through its open coborder as a closed
   immersion. Apply `lem-pur-conormal-graded-algebra` to that actual closed graph.
3. Intersect the closed neighbourhood with each affine graph ambient open. Open immersions
   are flat; `lem-pur-conormal-algebra-flat-base-change` identifies the conormal algebras.
   Its representative formula is exactly the formula in `Gluing.restriction`.
4. Compare two charts through the global algebra. Their transition sends each ideal class
   to its restriction. Inverse and identity laws follow by cancellation, as does the triple
   cocycle law. Ring maps preserve units and multiplication. Refine overlaps by affines.
5. The centre opens cover Z. These comparisons identify the global algebra with the gluing.
   Compare two neighbourhoods on their intersection; the same representative normalization
   gives the unique comparison. The global algebra is quasi-coherent with degree zero O_Z.
6. Apply `lemma-nagata-relative-proj-exists` and `prop-nagata-relative-proj-functoriality` to
   this algebra. The canonical relative Proj has all affine restrictions and their laws.
7. An isomorphism of diagrams identifies the graph ambients. Apply flat conormal comparison
   on the closed neighbourhoods. Its formula on ideal representatives determines the
   algebra map; identity and composition follow on those representatives. Proj maps have
   the same laws, by the homogeneous localization formula on their covering charts.
8. For the first-Fitting diagram use the fixed branch closed graph. Arbitrary Proj base
   change (`lemma-nagata-relative-proj-base-change-arbitrary`) identifies its blow-up fibre
   with Proj of the Rees algebra tensor O_Z. Degree n is J^n/J^(n+1), with the same product,
   unit and restriction formulas. `BranchNormalization.quotient` states the balanced
   pure-tensor formula and `BranchNormalization.chart` fixes the induced Proj map to each
   actual blow-up chart. Thus the identification is canonical and over Z.
No step assumes separatedness, nodality, flatness of the family, or quasi-compactness. -/
theorem exists_graphCone_gluing :
    (∀ (d : Diagram.{u}) (c : Chart d), IsClosedImmersion c.graph) ∧
      Nonempty (Construction.{u}) := by
  sorry

end AlgebraicGeometry.GraphCone
