/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.CategoryTheory.Sites.FiniteCoproductToposCoherent
public import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Topology.Constructible
import Sheaf.AlgebraicGeometry.EtaleToposPointsGeometric
import Sheaf.TraceFormula.FinitarySiteCoherentGenerators
import Sheaf.Paper.FinitarySiteEnoughPoints
import Sheaf.Paper.QcqsOrientedTriplePresentation
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import Sheaf.CategoryTheory.Sites.CoherentToposRepair
import Sheaf.CategoryTheory.Sites.GeometricMorphism

/-!
# The coherent conservative cover by stratified oriented products

Source: Orgogozo, Modifications et cycles proches sur une base générale, §8.1,
printed p. 17; ILO, Exposé XI §§1.4, 1.6, 1.8--1.9 and Lemma 2.5
(blueprint: lem-trf-stratified-product-coherent-conservative).

The auxiliary data only spell out the constructions in the statement: the actual triple
sites, universal projection data, their compatible lifts, and the finite coproduct witness.
Both existence and the conclusion for every such compatible construction are asserted.
The containing universe is `max (u + 1) v`, as for the recorded vanishing topos;
`AsSmall` transports the étale sites into that universe.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option warn.sorry false

universe u v

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CoherentToposRepair
open AlgebraicGeometry.OrientedNearbyCycles

namespace AlgebraicGeometry.StratifiedOrientedCover

/-- The finite set of pairs of strata, lifted into the common site universe.
Source: Orgogozo §8.1 (blueprint: lem-trf-stratified-product-coherent-conservative). -/
abbrev Index {X S : Scheme.{u}} (A : X.FiniteLocallyClosedStratification)
    (B : S.FiniteLocallyClosedStratification) := ULift.{max (u + 1) v} (Fin A.n × Fin B.n)

/-- The triple category for `f i_α` and `j_β`, using the recorded étale site transport.
Source: ILO XI §1.1 (blueprint: lem-trf-stratified-product-coherent-conservative). -/
abbrev ComponentSite {X S : Scheme.{u}} (f : X ⟶ S)
    (A : X.FiniteLocallyClosedStratification) (B : S.FiniteLocallyClosedStratification)
    (k : Index.{u, v} A B) :=
  OrientedProduct.Triples (etaleBaseChange.{u, v} (A.immersion k.down.1 ≫ f))
    (etaleBaseChange.{u, v} (B.immersion k.down.2))

/-- The three generating covering types on the component oriented product.
Source: ILO XI §1.1(ii) (blueprint: lem-trf-stratified-product-coherent-conservative). -/
def componentTopology {X S : Scheme.{u}} (f : X ⟶ S)
    (A : X.FiniteLocallyClosedStratification) (B : S.FiniteLocallyClosedStratification)
    (k : Index.{u, v} A B) : GrothendieckTopology (ComponentSite f A B k) :=
  OrientedProduct.topology
    (etaleTopology.{u, v} (A.domain k.down.1)).toPretopology
    (etaleTopology.{u, v} (B.domain k.down.2)).toPretopology
    (etaleBaseChange (A.immersion k.down.1 ≫ f)) (etaleBaseChange (B.immersion k.down.2))

/-- The actual stratum oriented-product topos, rather than an unspecified replacement.
Source: ILO XI §1.7 (blueprint: lem-trf-stratified-product-coherent-conservative). -/
abbrev ComponentTopos {X S : Scheme.{u}} (f : X ⟶ S)
    (A : X.FiniteLocallyClosedStratification) (B : S.FiniteLocallyClosedStratification)
    (k : Index.{u, v} A B) := Sheaf (componentTopology f A B k) (Type (max (u + 1) v))

/-- Projections and the structural arrow of a component, with their universal property.
Source: ILO XI Theorem 1.4 (blueprint: lem-trf-stratified-product-coherent-conservative). -/
structure Component {X S : Scheme.{u}} (f : X ⟶ S)
    (A : X.FiniteLocallyClosedStratification) (B : S.FiniteLocallyClosedStratification)
    (k : Index.{u, v} A B) where
  first : GeometricMorphism (ComponentTopos f A B k)
    (Sheaf (etaleTopology.{u, v} (A.domain k.down.1)) (Type (max (u + 1) v)))
  second : GeometricMorphism (ComponentTopos f A B k)
    (Sheaf (etaleTopology.{u, v} (B.domain k.down.2)) (Type (max (u + 1) v)))
  orientation : (second.comp (etaleMorphism (B.immersion k.down.2))).direct ⟶
    (first.comp (etaleMorphism (A.immersion k.down.1 ≫ f))).direct
  universal : OrientedProduct.IsUniversal.{max (u + 1) v, max (u + 1) v + 1, max (u + 1) v}
    (etaleMorphism (A.immersion k.down.1 ≫ f)) (etaleMorphism (B.immersion k.down.2))
    first second orientation

/-- The component structural arrow, transported only by the canonical étale composition
isomorphism and associativity, as a cone to the vanishing topos of `f`.
Source: ILO XI §§1.4, 1.9 (blueprint: lem-trf-stratified-product-coherent-conservative). -/
def componentOrientation {X S : Scheme.{u}} {f : X ⟶ S}
    {A : X.FiniteLocallyClosedStratification} {B : S.FiniteLocallyClosedStratification}
    {k : Index.{u, v} A B} (d : Component f A B k) :
    (((d.second.comp (etaleMorphism (B.immersion k.down.2))).comp (identity _)).direct) ⟶
      (((d.first.comp (etaleMorphism (A.immersion k.down.1))).comp
        (etaleMorphism f)).direct) :=
  (Functor.rightUnitor _).hom ≫ d.orientation ≫
    Functor.whiskerLeft d.first.direct (etaleComposition (A.immersion k.down.1) f).inv ≫
    (Functor.associator _ _ _).inv

/-- The universal-property lift of precisely `(i_α p₁,j_β p₂,τ)`, with its projection
identifications and the orientation compatibility equation retained in `Lift`.
Source: ILO XI Theorem 1.4 (blueprint: lem-trf-stratified-product-coherent-conservative). -/
abbrev ComponentLift {X S : Scheme.{u}} {f : X ⟶ S}
    {A : X.FiniteLocallyClosedStratification} {B : S.FiniteLocallyClosedStratification}
    {k : Index.{u, v} A B} (d : Component f A B k) :=
  Lift.{u, v} f (ComponentTopos f A B k)
    (d.first.comp (etaleMorphism (A.immersion k.down.1)))
    (d.second.comp (etaleMorphism (B.immersion k.down.2))) (componentOrientation d)

/-- All construction data of the stated stratified coproduct morphism. The coproduct is
specified by its actual disjoint-union site and the dependency's full witness. The component
identifications and inverse-image tuple formula specify the induced geometric morphism.
Source: Orgogozo §8.1; ILO XI §§1.4, 1.9
(blueprint: lem-trf-stratified-product-coherent-conservative). -/
structure Data {X S : Scheme.{u}} (f : X ⟶ S)
    (A : X.FiniteLocallyClosedStratification) (B : S.FiniteLocallyClosedStratification) where
  component : ∀ k : Index.{u, v} A B, Component f A B k
  lift : ∀ k : Index.{u, v} A B, ComponentLift (component k)
  topology : GrothendieckTopology (Σ k : Index.{u, v} A B, ComponentSite f A B k)
  coproduct : FiniteCoproductTopos.Witness.{max (u + 1) v, max (u + 1) v + 1,
      max (u + 1) v + 1}
    (componentTopology f A B) (ComponentTopos f A B)
    (fun _ ↦ CategoryTheory.Equivalence.refl) topology
  morphism : GeometricMorphism (Sheaf topology (Type (max (u + 1) v)))
    (VanishingTopos.{u, v} f)
  component_iso : ∀ k : Index.{u, v} A B,
    ((coproduct.inclusion k).comp morphism).direct ≅ (lift k).morphism.direct
  inverse_formula : Nonempty
    (morphism.inverse ⋙ coproduct.equivalence.functor ≅
      Functor.pi' (fun k ↦ (lift k).morphism.inverse))

/-- Finite constructible stratifications give a coherent conservative morphism from the
finite coproduct of their oriented products to `V_f`. Construction data exist, and the
conclusion holds for every compatible choice of the universal and coproduct data.

Source: Orgogozo, Modifications et cycles proches sur une base générale, §8.1, printed p. 17;
ILO Exposé XI §§1.4, 1.6, 1.8--1.9 and Lemma 2.5
(blueprint: lem-trf-stratified-product-coherent-conservative).

Proof (postponed), following the six DAG steps:
1. Finite presentation implies finite type. By lem-weil-pbc-finite-type-over-noetherian,
   X is Noetherian. Factor each stratum immersion as a closed immersion into an open.
   That open is Noetherian by lem-weil-pbc-noetherian-open-subscheme-noetherian. A closed
   immersion is of finite type (affine locally it is a quotient R → R/I), so each stratum
   is Noetherian too. They are all quasi-compact and quasi-separated by
   lem-weil-pbc-locally-noetherian-quasi-separated.
2. Apply lem-weil-pbc-qcqs-morphism-permanence to the three scheme maps. The finite-limit
   sites of lem-trf-qcqs-oriented-triple-presentation have finite covering generators of
   types (a),(b),(c). Base change preserves them and finite successive compositions remain
   finite. Apply lem-trf-finitary-site-coherent-generators to get coherent topoi and coherent
   associated representables. Transport the sites along AsSmall.equiv.
3. There are finitely many pairs of strata. Use lem-trf-finite-coproduct-topos-coherent for
   the source and componentwise coherence. Base change of a triple representable along a
   component lift is represented by (U ×_X X_α → V ← W ×_S S_β), by
   lem-trf-qcqs-oriented-triple-presentation. The tuple inverse formula therefore preserves
   these coherent generators. The morphism criterion of
   lem-trf-finitary-site-coherent-generators proves coherence on every coherent object.
4. By lem-trf-finitary-site-enough-points the target has enough set-valued points.
   Its two point projections come from geometric scheme points by
   lem-trf-etale-topos-points-geometric. The uniqueness part of
   lem-trf-oriented-product-universal identifies each point, including its structural arrow,
   with the triple of those projections and that arrow.
5. Each geometric point belongs to a unique stratum. It factors through that stratum as
   a scheme map: after factoring through the open in the immersion, on Spec R the map
   R → Ω kills I because I lies in its prime kernel, hence factors through R/I. This does
   not require the stratum to be reduced. The natural germ bijections of
   lem-weil-pbc-sets-etale-inverse-image-stalk-germ identify the composite point functors.
   The existence and uniqueness parts of lem-trf-oriented-product-universal now lift the
   point, with the same structural arrow, to the component, then to its coproduct.
6. If the total inverse image of a set-sheaf map is invertible, every lifted stalk map
   is invertible, hence so is every target stalk map. Apply
   lem-trf-finitary-site-enough-points to reflect isomorphisms. Empty components contribute
   no points; an empty point family is allowed by the same reflection criterion.
-/
theorem stratified_product_coherent_conservative
    {X S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (A : X.FiniteLocallyClosedStratification) (B : S.FiniteLocallyClosedStratification)
    (_hA : ∀ a, Topology.IsConstructible (A.stratum a))
    (_hB : ∀ b, Topology.IsConstructible (B.stratum b)) :
    Nonempty (Data.{u, v} f A B) ∧
      ∀ d : Data.{u, v} f A B,
        ∃ hE : CoherentToposRepair.IsCoherentTopos.{max (u + 1) v}
            (Sheaf d.topology (Type (max (u + 1) v))),
        ∃ hF : CoherentToposRepair.IsCoherentTopos.{max (u + 1) v} (VanishingTopos.{u, v} f),
          CoherentToposRepair.IsCoherentGeometricMorphism hE hF d.morphism ∧
            CoherentToposRepair.IsConservativeGeometricMorphism hE hF d.morphism := by
  sorry

end AlgebraicGeometry.StratifiedOrientedCover
