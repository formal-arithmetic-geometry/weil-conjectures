/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.Connected.Basic
import Sheaf.AlgebraicGeometry.LocallyNoetherianComponentsLocallyFinite
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import WeilConjectures.AlgebraicGeometry.FieldExtensionFpqcCover
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Irreducible
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Topology.Defs.Filter
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Minimal component envelopes over a trait

Source: Anantharaman, Groupes de dimension un, 4.1 and Lemma 4.2.4,
printed pp.54-55 and 59-61; the corrected neutral-product assertion is restricted
to a strictly henselian trait (blueprint: lem-sfb-trait-component-minimal-envelope).

The envelope is the intersection of all candidate subfunctors, rather than a choice
from an existence assertion. The theorem asserts that this intersection is itself
an open candidate and has the required finiteness and compatibility properties.
All auxiliary declarations unpack notions in this same statement.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.TraitComponentEnvelope

/-- The special-point map. Source: Anantharaman 4.2.4
(blueprint: lem-sfb-trait-component-minimal-envelope). -/
noncomputable def specialMap (R : Type u) [CommRing R] [IsLocalRing R] :
    Spec (.of (IsLocalRing.ResidueField R)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))

/-- The generic-point map. Source: Anantharaman 4.2.4
(blueprint: lem-sfb-trait-component-minimal-envelope). -/
noncomputable def genericMap (R : Type u) [CommRing R] [IsDomain R] :
    Spec (.of (FractionRing R)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))

/-- A representing scheme for a base change of the given group functor.
Its group operations are transported by `GrpObj.ofRepresentableBy`.
Source: Anantharaman 4.1 and 4.2.4
(blueprint: lem-sfb-trait-component-minimal-envelope). -/
structure FibreModel {S B : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ GrpCat.{u}) (b : B ⟶ S) where
  /-- The representing scheme over the new base. -/
  X : Over B
  /-- The natural bijection of sections with morphisms into the model. -/
  repr : (((Over.map b).op ⋙ F) ⋙ forget GrpCat).RepresentableBy X

/-- Exactly the fpqc-sheaf and local separated flat lfp representability hypotheses.
Source: Anantharaman 4.A and 4.2.4
(blueprint: lem-sfb-trait-component-minimal-envelope). -/
def IsForm {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ GrpCat.{u}) : Prop :=
  Presheaf.IsSheaf (Scheme.fpqcTopology.over S) (F ⋙ forget GrpCat) ∧
    ∃ (T : Scheme.{u}) (p : T ⟶ S),
      Presieve.singleton p ∈ Scheme.fpqcPrecoverage S ∧
      ∃ P : FibreModel F p,
        IsSeparated P.X.hom ∧ Flat P.X.hom ∧ LocallyOfFinitePresentation P.X.hom

/-- The morphism of representing schemes induced by a map of group functors.
Source: Anantharaman 4.2.4, functoriality
(blueprint: lem-sfb-trait-component-minimal-envelope). -/
def modelMap {S B : Scheme.{u}} {F F' : (Over S)ᵒᵖ ⥤ GrpCat.{u}}
    (a : F ⟶ F') {b : B ⟶ S} (M : FibreModel F b) (M' : FibreModel F' b) :
    M.X ⟶ M'.X :=
  M'.repr.homEquiv.symm
    ((a.app (op ((Over.map b).obj M.X))).hom (M.repr.homEquiv (𝟙 M.X)))

/-- Equality of the restriction of a subfunctor with a subscheme specified by its points.
The condition is imposed on every scheme test, including nonreduced tests.
Source: Anantharaman 4.2.4
(blueprint: lem-sfb-trait-component-minimal-envelope). -/
def HasFibre {S B : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ GrpCat.{u}} {b : B ⟶ S}
    (E : Subfunctor (F ⋙ forget GrpCat)) (M : FibreModel F b) (C : Set M.X.left) : Prop :=
  ∀ (V : Over B) (x : (((Over.map b).op ⋙ F) ⋙ forget GrpCat).obj (op V)),
    x ∈ E.obj (op ((Over.map b).obj V)) ↔
      Set.range (M.repr.homEquiv.symm x).left.base ⊆ C

/-- The generic-fibre condition: a union of entire connected components, not necessarily finite.
Source: Anantharaman 4.2.4, component-saturated minimality
(blueprint: lem-sfb-trait-component-minimal-envelope). -/
def IsComponentUnion {S B : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ GrpCat.{u}} {b : B ⟶ S}
    (E : Subfunctor (F ⋙ forget GrpCat)) (M : FibreModel F b) : Prop :=
  ∃ I : Set (ConnectedComponents M.X.left), HasFibre E M (ConnectedComponents.mk ⁻¹' I)

/-- The finite-union conclusion for the generic fibre.
Source: Anantharaman 4.2.4(ii)
(blueprint: lem-sfb-trait-component-minimal-envelope). -/
def IsFiniteComponentUnion {S B : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ GrpCat.{u}} {b : B ⟶ S}
    (E : Subfunctor (F ⋙ forget GrpCat)) (M : FibreModel F b) : Prop :=
  ∃ I : Set (ConnectedComponents M.X.left), I.Finite ∧
    HasFibre E M (ConnectedComponents.mk ⁻¹' I)

/-- A candidate open with prescribed special component and component-saturated generic fibre.
Openness is Mathlib's relatively representable open-immersion property on all scheme tests.
Source: Anantharaman 4.2.4(i)-(ii)
(blueprint: lem-sfb-trait-component-minimal-envelope). -/
def IsCandidate {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    {F : (Over (Spec (.of R)))ᵒᵖ ⥤ GrpCat.{u}}
    (Ms : FibreModel F (specialMap R)) (Mg : FibreModel F (genericMap R))
    (C : Set Ms.X.left) (E : Subfunctor (F ⋙ forget GrpCat)) : Prop :=
  MorphismProperty.presheaf
    (fun {X Y : Over (Spec (.of R))} (f : X ⟶ Y) ↦ IsOpenImmersion f.left) E.ι ∧
    HasFibre E Ms C ∧ IsComponentUnion E Mg

/-- The canonical envelope, defined without choosing any unknown object: intersect all candidates.
The theorem below asserts that this intersection is itself a candidate.
Source: Anantharaman 4.2.4, smallest open
(blueprint: lem-sfb-trait-component-minimal-envelope). -/
noncomputable def envelope {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    {F : (Over (Spec (.of R)))ᵒᵖ ⥤ GrpCat.{u}}
    (Ms : FibreModel F (specialMap R)) (Mg : FibreModel F (genericMap R))
    (C : Set Ms.X.left) : Subfunctor (F ⋙ forget GrpCat) :=
  sInf {E | IsCandidate Ms Mg C E}

/-- The neutral component of a field model, with the group structure transported from F.
Source: Anantharaman 4.1
(blueprint: lem-sfb-trait-component-minimal-envelope). -/
noncomputable def neutral {S : Scheme.{u}} {k : Type u} [Field k]
    {F : (Over S)ᵒᵖ ⥤ GrpCat.{u}} {b : Spec (.of k) ⟶ S} (M : FibreModel F b) :
    Set M.X.left :=
  connectedComponent (@GrpObj.onePoint k _ M.X
    (GrpObj.ofRepresentableBy M.X ((Over.map b).op ⋙ F) M.repr))

/-- All field components are clopen finite-type open subschemes of a locally finite-type scheme.
Source: Anantharaman 4.1, field reduction in 4.2.4
(blueprint: lem-sfb-trait-component-minimal-envelope). -/
def FieldComponents {S : Scheme.{u}} {k : Type u} [Field k]
    {F : (Over S)ᵒᵖ ⥤ GrpCat.{u}} {b : Spec (.of k) ⟶ S} (M : FibreModel F b) : Prop :=
  LocallyOfFiniteType M.X.hom ∧
    ∀ x : M.X.left, ∃ U : M.X.left.Opens,
      (U : Set M.X.left) = connectedComponent x ∧ IsClosed (U : Set M.X.left) ∧
      LocallyOfFiniteType (U.ι ≫ M.X.hom) ∧ QuasiCompact (U.ι ≫ M.X.hom)

/-- The neutral component is geometrically connected and a subgroup on every scheme test.
The open-subscheme representation makes this exactly the subgroup-scheme assertion.
Source: Anantharaman 4.1 and pp.60-61
(blueprint: lem-sfb-trait-component-minimal-envelope). -/
def NeutralProperties {S : Scheme.{u}} {k : Type u} [Field k]
    {F : (Over S)ᵒᵖ ⥤ GrpCat.{u}} {b : Spec (.of k) ⟶ S} (M : FibreModel F b) : Prop :=
  (∃ U : M.X.left.Opens, (U : Set M.X.left) = neutral M ∧
    GeometricallyConnected (U.ι ≫ M.X.hom)) ∧
  (∀ V : Over (Spec (.of k)),
    ∃ H : Subgroup (((Over.map b).op ⋙ F).obj (op V)),
      (H : Set (((Over.map b).op ⋙ F).obj (op V))) =
        {x | Set.range (M.repr.homEquiv.symm x).left.base ⊆ neutral M}) ∧
  (∀ M2 : FibreModel (prod F F) b,
    neutral M2 = (modelMap prod.fst M2 M).left ⁻¹' neutral M ∩
      (modelMap prod.snd M2 M).left ⁻¹' neutral M)

/-- Finite presentation, flatness and separatedness on each fpqc representing chart.
Source: Anantharaman 4.2.4(iii)
(blueprint: lem-sfb-trait-component-minimal-envelope). -/
def FiniteOnCharts {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ GrpCat.{u}}
    (E : Subfunctor (F ⋙ forget GrpCat)) : Prop :=
  ∀ (T : Scheme.{u}) (p : T ⟶ S), Presieve.singleton p ∈ Scheme.fpqcPrecoverage S →
    ∀ P : FibreModel F p,
      IsSeparated P.X.hom → Flat P.X.hom → LocallyOfFinitePresentation P.X.hom →
      ∃ Q : Over T,
        Nonempty (((Over.map p).op ⋙ E.toFunctor).RepresentableBy Q) ∧
        IsSeparated Q.hom ∧ Flat Q.hom ∧ LocallyOfFinitePresentation Q.hom ∧
        QuasiCompact Q.hom ∧ QuasiSeparated Q.hom

/-- Local representability by a flat locally finitely presented morphism after an fpqc change.
Source: Anantharaman 4.2.4, mapping assertion
(blueprint: lem-sfb-trait-component-minimal-envelope). -/
def IsLocallyFlatLfp {S : Scheme.{u}} {F F' : (Over S)ᵒᵖ ⥤ GrpCat.{u}}
    (a : F ⟶ F') : Prop :=
  ∃ (T : Scheme.{u}) (p : T ⟶ S), Presieve.singleton p ∈ Scheme.fpqcPrecoverage S ∧
    MorphismProperty.presheaf
      (fun {X Y : Over T} (f : X ⟶ Y) ↦ Flat f.left ∧ LocallyOfFinitePresentation f.left)
        (Functor.whiskerRight (Functor.whiskerLeft (Over.map p).op a) (forget GrpCat))

/-- Envelopes respect isomorphisms, with the component transported by the induced fibre map.
Source: Anantharaman 4.2.4, smallestness
(blueprint: lem-sfb-trait-component-minimal-envelope). -/
def IsoCompatibility {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    {F : (Over (Spec (.of R)))ᵒᵖ ⥤ GrpCat.{u}}
    (Ms : FibreModel F (specialMap R)) (Mg : FibreModel F (genericMap R)) : Prop :=
  ∀ (F' : (Over (Spec (.of R)))ᵒᵖ ⥤ GrpCat.{u}), IsForm F' →
    ∀ (Ms' : FibreModel F' (specialMap R)) (Mg' : FibreModel F' (genericMap R))
      (a : F ≅ F') (x : Ms.X.left),
      (envelope Ms Mg (connectedComponent x)).image (Functor.whiskerRight a.hom (forget GrpCat)) =
        envelope Ms' Mg' ((modelMap a.hom Ms Ms').left '' connectedComponent x)

/-- Neutral envelopes commute with products over a strictly henselian trait.
The product subfunctor is expressed by the inverse images along the two actual projections.
Source: Anantharaman pp.60-61, corrected strict-local product argument
(blueprint: lem-sfb-trait-component-minimal-envelope). -/
def ProductCompatibility {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    {F : (Over (Spec (.of R)))ᵒᵖ ⥤ GrpCat.{u}}
    (Ms : FibreModel F (specialMap R)) (Mg : FibreModel F (genericMap R)) : Prop :=
  ∀ (F' : (Over (Spec (.of R)))ᵒᵖ ⥤ GrpCat.{u}), IsForm F' →
    ∀ (Ms' : FibreModel F' (specialMap R)) (Mg' : FibreModel F' (genericMap R))
      (Mps : FibreModel (prod F F') (specialMap R))
      (Mpg : FibreModel (prod F F') (genericMap R)),
      envelope Mps Mpg (neutral Mps) =
        (envelope Ms Mg (neutral Ms)).preimage (Functor.whiskerRight prod.fst (forget GrpCat)) ⊓
          (envelope Ms' Mg' (neutral Ms')).preimage (Functor.whiskerRight prod.snd (forget GrpCat))

/-- Flat lfp maps carrying the special component onto another carry its envelope into that envelope.
Source: Anantharaman 4.2.4, functoriality
(blueprint: lem-sfb-trait-component-minimal-envelope). -/
def MapCompatibility {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    {F : (Over (Spec (.of R)))ᵒᵖ ⥤ GrpCat.{u}}
    (Ms : FibreModel F (specialMap R)) (Mg : FibreModel F (genericMap R)) : Prop :=
  ∀ (F' : (Over (Spec (.of R)))ᵒᵖ ⥤ GrpCat.{u}), IsForm F' →
    ∀ (Ms' : FibreModel F' (specialMap R)) (Mg' : FibreModel F' (genericMap R))
      (a : F ⟶ F'), IsLocallyFlatLfp a →
      ∀ (x : Ms.X.left) (x' : Ms'.X.left),
        (modelMap a Ms Ms').left '' connectedComponent x = connectedComponent x' →
        (envelope Ms Mg (connectedComponent x)).image (Functor.whiskerRight a (forget GrpCat)) ≤
          envelope Ms' Mg' (connectedComponent x')

/-- The canonical minimal envelopes, including every field, identity and compatibility clause.

Source: Anantharaman 4.1 and Lemma 4.2.4, printed pp.54-55 and 59-61;
neutral-product compatibility uses the corrected strictly henselian argument
(blueprint: lem-sfb-trait-component-minimal-envelope).

Proof:
1. Base change the fpqc chart to both fields and apply
   lem-sfb-field-fpqc-group-form-effectivity to represent the fibres.
2. Local finite type implies local Noetherianness (pqf-lem-locnoeth-lft).
   Local finiteness of irreducible components (lem-sc-locnoeth-components-locally-finite)
   and lem-sfb-group-local-minimal-prime make the components disjoint and clopen.
   Lift components to an algebraic closure (lem-sfb-field-extension-irreducible-components).
   Translation identifies each lifted component with the finite-type neutral one by
   lem-sfb-lft-field-group-neutral-component. Their images are quasi-compact, hence finite type.
3. The same neutral-component theorem gives geometric connectedness and the subgroup.
   The product component theorem (lem-weil-pbc-geometrically-connected-product-components)
   identifies its square with the neutral component of the square.
4. A candidate is determined by its two fibres on every scheme test. Pull back its
   point subset to the fpqc chart and descend compatible opens using
   lem-weil-pbc-open-subscheme-fpqc-descent.
5. Take finitely many affine pieces of the chart covering S. Each special component
   on these pieces has a finite affine neighborhood with exactly that special fibre.
   Inverting a uniformizer gives quasi-compact generic neighborhoods, meeting finitely
   many components. Saturate these finitely many components and descend the resulting open.
6. In that finite component set, for each component omitted by some candidate choose
   one such candidate. Their finite intersection is a candidate contained in all others.
   It equals the explicitly defined intersection and has finite component generic fibre.
7. On each affine chart the two fibres of the envelope are quasi-compact, so their union
   is quasi-compact. Restriction preserves separatedness, flatness and lfp; the closed
   diagonal is quasi-compact. Thus the chart envelope is of finite presentation.
8. The inverse image under the identity is an open of local Spec R containing its closed
   point, hence all of Spec R. Isomorphisms identify the candidate sets, hence their infima.
9. Pull back the target envelope along a given flat lfp map and intersect with the source
   envelope. Connected components have connected image, so this is a candidate. Smallestness
   gives the required inclusion.
10. Over a strictly henselian R, a common fpqc chart makes the product a separated flat lfp
    group form by base change and composition. The product of the two neutral envelopes is
    a candidate, so it contains the product envelope.
11. Apply lem-sfb-henselian-unavoidable-component-valuation-section to the unavoidable
    components of both generic envelopes over an algebraic closure of Frac R. Paired
    valuation-ring sections specialize into the product special neutral component. The
    inverse image of the product envelope is an open containing the closed point of a local
    valuation scheme, hence contains its generic point. Thus every geometric product
    component is met and, by saturation, contained. Field-extension surjectivity and the
    two-fibre criterion give the reverse inclusion and the product equality. -/
theorem minimal_envelope (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (F : (Over (Spec (.of R)))ᵒᵖ ⥤ GrpCat.{u}) (hF : IsForm F) :
    ∃ (Ms : FibreModel F (specialMap R)) (Mg : FibreModel F (genericMap R)),
      FieldComponents Ms ∧ FieldComponents Mg ∧ NeutralProperties Ms ∧
      (∀ x : Ms.X.left,
        IsLeast {E | IsCandidate Ms Mg (connectedComponent x) E}
          (envelope Ms Mg (connectedComponent x)) ∧
        IsFiniteComponentUnion (envelope Ms Mg (connectedComponent x)) Mg ∧
        FiniteOnCharts (envelope Ms Mg (connectedComponent x))) ∧
      (∀ V : Over (Spec (.of R)),
        (1 : F.obj (op V)) ∈ (envelope Ms Mg (neutral Ms)).obj (op V)) ∧
      IsoCompatibility Ms Mg ∧
      (IsStrictlyHenselianLocalRing R → ProductCompatibility Ms Mg) ∧
      MapCompatibility Ms Mg := by
  sorry

end AlgebraicGeometry.TraitComponentEnvelope
