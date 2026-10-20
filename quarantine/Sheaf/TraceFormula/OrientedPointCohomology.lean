/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q140
-/
module

public import Sheaf.Paper.OrientedNearbyCycles
public import Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Sheaf.CategoryTheory.ConstantRingModuleSheaves
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyLimit
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.SitePointFibre
import Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization
import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
import Sheaf.Paper.OrientedAffineNeighbourhoodLimit
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# The restriction comparison at an oriented point

Source: Illusie, Around the Thom--Sebastiani theorem, §§1.1--1.3, especially (1.3.1)
(blueprint: lem-trf-oriented-point-cohomology).

We use the actual triple topology, strict localizations and constant-ring module categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.OrientedNearbyCycles
open CategoryTheory.AdicSites

namespace CategoryTheory.OrientedPointCohomology

/-- The two-map oriented triple site. Source: Illusie §1.1
(blueprint: lem-trf-oriented-point-cohomology). -/
abbrev Triples {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :=
  OrientedProduct.Triples (etaleBaseChange.{u, v + 1} f) (etaleBaseChange.{u, v + 1} g)

/-- The three generating covering types of the oriented product. Source: Illusie §1.1
(blueprint: lem-trf-oriented-point-cohomology). -/
def topology {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :=
  OrientedProduct.topology (etaleTopology.{u, v + 1} X).toPretopology
    (etaleTopology Y).toPretopology (etaleBaseChange f) (etaleBaseChange g)

/-- The actual oriented product, as a small-site datum. Source: Illusie §1.1
(blueprint: lem-trf-oriented-point-cohomology). -/
def datum {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    Site.{max u v + 1} := ⟨Triples.{u, v} f g, topology.{u, v} f g⟩

/-- The underlying X-neighbourhood. Source: Illusie §1.1
(blueprint: lem-trf-oriented-point-cohomology). -/
abbrev U {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (T : Triples.{u, v} f g) :=
  (AsSmall.down.obj T.left.1 : X.Etale)

/-- The underlying Y-neighbourhood. Source: Illusie §1.1
(blueprint: lem-trf-oriented-point-cohomology). -/
abbrev W {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (T : Triples.{u, v} f g) :=
  (AsSmall.down.obj T.left.2 : Y.Etale)

/-- The underlying S-neighbourhood. Source: Illusie §1.1
(blueprint: lem-trf-oriented-point-cohomology). -/
abbrev V {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (T : Triples.{u, v} f g) :=
  (AsSmall.down.obj T.right : S.Etale)

/-- The arrow U → V, obtained from U → f*V. Source: Illusie §1.1
(blueprint: lem-trf-oriented-point-cohomology). -/
def a {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (T : Triples.{u, v} f g) :
    (U T).left ⟶ (V T).left :=
  (AsSmall.down.map T.hom.1).left ≫ pullback.fst (V T).hom f

/-- The arrow W → V, obtained from W → g*V. Source: Illusie §1.1
(blueprint: lem-trf-oriented-point-cohomology). -/
def b {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (T : Triples.{u, v} f g) :
    (W T).left ⟶ (V T).left :=
  (AsSmall.down.map T.hom.2).left ≫ pullback.fst (V T).hom g

/-- The canonical scheme represented by the inverse image of a triple.
Source: Illusie §1.2 after (1.2.1) (blueprint: lem-trf-oriented-point-cohomology). -/
abbrev D {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (T : Triples.{u, v} f g) :=
  pullback (a T) (b T)

/-- The two maps to X and Y agree over S.
Source: Illusie §1.2 (blueprint: lem-trf-oriented-point-cohomology).
Proof: the two triple arrows are over X and Y, respectively; compose those equations
with f and g and use the pullback condition for U ×_V W. -/
theorem D_condition {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (T : Triples.{u, v} f g) :
    (pullback.fst (a T) (b T) ≫ (U T).hom) ≫ f =
      (pullback.snd (a T) (b T) ≫ (W T).hom) ≫ g := by
  sorry

/-- The natural map U ×_V W → X ×_S Y. Source: Illusie §1.2
(blueprint: lem-trf-oriented-point-cohomology). -/
def t {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (T : Triples.{u, v} f g) :
    D T ⟶ pullback f g :=
  pullback.lift (pullback.fst (a T) (b T) ≫ (U T).hom)
    (pullback.snd (a T) (b T) ≫ (W T).hom) (D_condition T)

/-- The natural map attached to a triple is étale.
Source: Illusie §1.2 (blueprint: lem-trf-oriented-point-cohomology).
Proof: U ×_S W is étale over X ×_S Y. Since V → S is étale its diagonal is open;
U ×_V W → U ×_S W is its base change, so is an open immersion, hence étale.
The composite is étale. -/
theorem t_etale {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (T : Triples.{u, v} f g) : Etale (t T) := by
  sorry

attribute [instance] t_etale

/-- Restrict the represented schemes along a triple morphism.
Source: Illusie §1.2 (blueprint: lem-trf-oriented-point-cohomology).
Proof: compose the U- and W-projections with the two components of h. Its comma square
and the source pullback equation give equality over V'. The pullback universal property
gives the unique map. Projection equality also proves it is over X ×_S Y. -/
theorem D_map_unique {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {T T' : Triples.{u, v} f g} (h : T ⟶ T') :
    ∃! d : D T ⟶ D T',
      d ≫ pullback.fst (a T') (b T') =
        pullback.fst (a T) (b T) ≫ (AsSmall.down.map h.left.1).left ∧
      d ≫ pullback.snd (a T') (b T') =
        pullback.snd (a T) (b T) ≫ (AsSmall.down.map h.left.2).left := by
  sorry

/-- The uniquely determined map between represented schemes.
Source: Illusie §1.2 (blueprint: lem-trf-oriented-point-cohomology). -/
def Dmap {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {T T' : Triples.{u, v} f g} (h : T ⟶ T') : D T ⟶ D T' :=
  (D_map_unique h).choose

/-- Functor laws and the over-Z equation follow by the two pullback projections.
Source: Illusie §1.2 (blueprint: lem-trf-oriented-point-cohomology).
Proof: take the projection equations in D_map_unique; use the comma equations and
functor laws for AsSmall.down. Uniqueness proves identity and composition. -/
theorem Dmap_laws {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} :
    (∀ T : Triples.{u, v} f g, Dmap (𝟙 T) = 𝟙 (D T)) ∧
    (∀ {T T' T'' : Triples.{u, v} f g} (h : T ⟶ T') (k : T' ⟶ T''),
      Dmap (h ≫ k) = Dmap h ≫ Dmap k) ∧
    (∀ {T T' : Triples.{u, v} f g} (h : T ⟶ T'), Dmap h ≫ t T' = t T) := by
  sorry

/-- The actual inverse-image functor on triple generators, T ↦ U ×_V W.
Source: Illusie §1.2 (blueprint: lem-trf-oriented-point-cohomology). -/
def psiSite {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    Triples.{u, v} f g ⥤ EtaleSite.{u, v + 1} (pullback f g) where
  obj T := AsSmall.up.obj (Scheme.Etale.mk (t T))
  map h := AsSmall.up.map (MorphismProperty.Over.homMk (Dmap h) ((Dmap_laws).2.2 h))
  map_id T := by
    apply ULift.ext
    apply MorphismProperty.Comma.Hom.ext
    · exact (Dmap_laws).1 T
    · rfl
  map_comp h k := by
    apply ULift.ext
    apply MorphismProperty.Comma.Hom.ext
    · exact (Dmap_laws).2.1 h k
    · rfl

/-- The triple inverse-image functor is continuous and preserves finite limits.
Source: Illusie §§1.1--1.2 (blueprint: lem-trf-oriented-point-cohomology).
Proof: limits of triples are componentwise and finite limits commute with fibre products.
The first two covering types give étale covers after base change. Type (c) maps become
isomorphisms of U ×_V W. These verify continuity on the generating covering families. -/
theorem psiSite_properties {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    (psiSite.{u, v} f g).IsContinuous (topology f g) (etaleTopology (pullback f g)) ∧
      PreservesFiniteLimits (psiSite.{u, v} f g) := by
  sorry

/-- Continuity of the specified triple functor. Source: Illusie §1.2
(blueprint: lem-trf-oriented-point-cohomology). -/
instance psiSite_continuous {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    (psiSite.{u, v} f g).IsContinuous (topology f g) (etaleTopology (pullback f g)) :=
  (psiSite_properties f g).1

/-- Finite-limit preservation of the specified triple functor. Source: Illusie §1.2
(blueprint: lem-trf-oriented-point-cohomology). -/
instance psiSite_finiteLimits {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    PreservesFiniteLimits (psiSite.{u, v} f g) := (psiSite_properties f g).2

/-- Finite limits on the concrete comma category of triples.
Source: Illusie §1.1 (blueprint: lem-trf-oriented-point-cohomology).
Proof: the two base-change functors preserve finite limits; compute the comma limits
componentwise, using finite limits in the three étale sites. -/
theorem triples_finiteLimits {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    HasFiniteLimits (Triples.{u, v} f g) := by
  sorry

attribute [instance] triples_finiteLimits

/-- The geometric morphism specified by U ×_V W on generators. Source: Illusie §1.2
(blueprint: lem-trf-oriented-point-cohomology). -/
def psi {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :=
  siteMorphism (topology.{u, v} f g) (etaleTopology (pullback f g)) (psiSite f g)

section Point
variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  {Ωx Ωy : Type u} [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
  (x : Spec (.of Ωx) ⟶ X) (y : Spec (.of Ωy) ⟶ Y)
  (c : Scheme.strictHenselizationScheme (y ≫ g) ⟶
    Scheme.strictHenselizationScheme (x ≫ f))
  (hc : c ≫ Scheme.strictHenselizationStructuralMap (x ≫ f) =
    Scheme.strictHenselizationStructuralMap (y ≫ g))

/-- The Milnor tube, formed with the actual specialization c.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
abbrev M := pullback (Scheme.strictHenselizationMap f x)
  (Scheme.strictHenselizationMap g y ≫ c)

include hc in
/-- The two canonical maps from the Milnor tube agree over S.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology).
Proof: compose the defining pullback equation with the structural map of S_(f(x)).
Use strictHenselizationMap_over for f and g and the given over-S equation hc. -/
theorem M_condition :
    (pullback.fst (Scheme.strictHenselizationMap f x)
      (Scheme.strictHenselizationMap g y ≫ c) ≫
        Scheme.strictHenselizationStructuralMap x) ≫ f =
    (pullback.snd (Scheme.strictHenselizationMap f x)
      (Scheme.strictHenselizationMap g y ≫ c) ≫
        Scheme.strictHenselizationStructuralMap y) ≫ g := by
  sorry

/-- The natural map from the Milnor tube to X ×_S Y.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
def r : M f g x y c ⟶ pullback f g :=
  pullback.lift
    (pullback.fst (Scheme.strictHenselizationMap f x)
      (Scheme.strictHenselizationMap g y ≫ c) ≫ Scheme.strictHenselizationStructuralMap x)
    (pullback.snd (Scheme.strictHenselizationMap f x)
      (Scheme.strictHenselizationMap g y ≫ c) ≫ Scheme.strictHenselizationStructuralMap y)
    (M_condition f g x y c hc)

/-- A pointed triple is a compatible pair of strict-local lifts. The lift to V is
included explicitly; étale uniqueness identifies this description with (x,y,c).
Source: Illusie §§1.1,1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
@[ext] structure Lift (T : Triples.{u, v} f g) where
  u : Scheme.strictHenselizationScheme x ⟶ (U T).left
  w : Scheme.strictHenselizationScheme y ⟶ (W T).left
  v : Scheme.strictHenselizationScheme (x ≫ f) ⟶ (V T).left
  u_over : u ≫ (U T).hom = Scheme.strictHenselizationStructuralMap x
  w_over : w ≫ (W T).hom = Scheme.strictHenselizationStructuralMap y
  v_over : v ≫ (V T).hom = Scheme.strictHenselizationStructuralMap (x ≫ f)
  uv : u ≫ a T = Scheme.strictHenselizationMap f x ≫ v
  wv : w ≫ b T = Scheme.strictHenselizationMap g y ≫ c ≫ v

/-- Composition transports pointed triples along their three components.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology).
Proof: compose u,v,w with the three components. The equations follow from the comma
square and the two over-base conditions. The composite formulas determine the lift uniquely. -/
theorem lift_map_unique {T T' : Triples.{u, v} f g} (h : T ⟶ T')
    (l : Lift f g x y c T) :
    ∃! l' : Lift f g x y c T',
      l'.u = l.u ≫ (AsSmall.down.map h.left.1).left ∧
      l'.w = l.w ≫ (AsSmall.down.map h.left.2).left ∧
      l'.v = l.v ≫ (AsSmall.down.map h.right).left := by
  sorry

/-- The specified transport of a pointed triple.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
def liftMap {T T' : Triples.{u, v} f g} (h : T ⟶ T') (l : Lift f g x y c T) :=
  (lift_map_unique f g x y c h l).choose

/-- The lift transport obeys the functor laws.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology).
Proof: uniqueness in lift_map_unique and associativity give both equations componentwise. -/
theorem liftMap_laws :
    (∀ (T : Triples.{u, v} f g) (l : Lift f g x y c T), liftMap f g x y c (𝟙 T) l = l) ∧
    (∀ {T T' T'' : Triples.{u, v} f g} (h : T ⟶ T') (k : T' ⟶ T'')
      (l : Lift f g x y c T),
      liftMap f g x y c (h ≫ k) l = liftMap f g x y c k (liftMap f g x y c h l)) := by
  sorry

/-- The fibre functor of the actual triple (x,y,c), with a universe lift of its sets.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
def fiber : Triples.{u, v} f g ⥤ Type (max u v + 1) where
  obj T := ULift.{max u v + 1} (Lift f g x y c T)
  map h := TypeCat.ofHom (fun l ↦ ⟨liftMap f g x y c h l.down⟩)
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro l
    exact congrArg ULift.up ((liftMap_laws f g x y c).1 T l.down)
  map_comp h k := by
    apply ConcreteCategory.hom_ext
    intro l
    exact congrArg ULift.up ((liftMap_laws f g x y c).2 h k l.down)

include hc in
/-- The strict-local fibre defines a point of the oriented site.
Source: Illusie §§1.1,1.3; ILO XI 1.4
(blueprint: lem-trf-oriented-point-cohomology).
Proof: finite compatible pointed triples admit a common refinement by the cofiltered
pointed étale neighbourhood categories. Equality is similarly equalized after refinement.
For the first two covering types lift a point to one member of the étale cover, using
strict henselianity. For type (c) the Cartesian square determines the required lift.
These assertions extend to the generated topology. Essential smallness follows from
the chosen universe for the triple category and the sets of lifts. -/
theorem point_properties :
    IsCofiltered (fiber.{u, v} f g x y c).Elements ∧
    InitiallySmall.{max u v + 1} (fiber.{u, v} f g x y c).Elements ∧
    (∀ (T : Triples.{u, v} f g) (R : Sieve T), R ∈ topology f g T →
      ∀ l : (fiber f g x y c).obj T,
        ∃ (T' : Triples.{u, v} f g) (h : T' ⟶ T) (_ : R h)
          (l' : (fiber f g x y c).obj T'), (fiber f g x y c).map h l' = l) := by
  sorry

/-- The resulting site point, fixed by (x,y,c) rather than supplied independently.
Source: Illusie §§1.1,1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
def z : (topology.{u, v} f g).Point.{max u v + 1} where
  fiber := fiber f g x y c
  isCofiltered := (point_properties f g x y c hc).1
  initiallySmall := (point_properties f g x y c hc).2.1
  jointly_surjective := fun R h l ↦ (point_properties f g x y c hc).2.2 _ R h l

/-- A pointed triple gives the map from the Milnor tube to its represented scheme.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology).
Proof: the equations uv and wv, together with the defining pullback equation of M,
give compatibility of the two maps. The pullback universal property gives a unique q. -/
theorem q_unique (T : Triples.{u, v} f g) (l : Lift f g x y c T) :
    ∃! q : M f g x y c ⟶ D T,
      q ≫ pullback.fst (a T) (b T) =
        pullback.fst (Scheme.strictHenselizationMap f x)
          (Scheme.strictHenselizationMap g y ≫ c) ≫ l.u ∧
      q ≫ pullback.snd (a T) (b T) =
        pullback.snd (Scheme.strictHenselizationMap f x)
          (Scheme.strictHenselizationMap g y ≫ c) ≫ l.w := by
  sorry

/-- The actual restriction map to a pointed triple.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
def q (T : Triples.{u, v} f g) (l : Lift f g x y c T) : M f g x y c ⟶ D T :=
  (q_unique f g x y c T l).choose

include hc in
/-- The restriction map is over Z. Source: Illusie §1.3
(blueprint: lem-trf-oriented-point-cohomology).
Proof: compare the two projections to X,Y using q_unique, u_over and w_over. -/
theorem q_over (T : Triples.{u, v} f g) (l : Lift f g x y c T) :
    q f g x y c T l ≫ t T = r f g x y c hc := by
  sorry

/-- A fixed final object of the transported small étale site.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
def finalEtale (N : Scheme.{u}) : EtaleSite.{u, v + 1} N :=
  AsSmall.up.obj (Scheme.Etale.mk (𝟙 N))

/-- The map from the final M-object to the pullback of the represented triple.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
def qEtale (T : Triples.{u, v} f g) (l : Lift f g x y c T) :
    finalEtale.{u, v} (M f g x y c) ⟶
      (etaleBaseChange (r f g x y c hc)).obj ((psiSite f g).obj T) :=
  AsSmall.up.map (MorphismProperty.Over.homMk
    (pullback.lift (q f g x y c T l) (𝟙 _) (by
        change q f g x y c T l ≫ t T = 𝟙 _ ≫ r f g x y c hc
        simpa only [Category.id_comp] using q_over f g x y c hc T l))
    (by change pullback.lift _ _ _ ≫ pullback.snd _ _ = 𝟙 _
        exact pullback.lift_snd _ _ _))

end Point

section Coefficients
universe s
variable {C : Type s} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type s) [CommRing A]

/-- Modules over the actual constant ring sheaf, using the recorded dependency.
Source: Stacks 03CY; Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
abbrev Modules := ringedSiteModules.{s} ((constantSheaf J RingCat.{s}).obj (RingCat.of A))

/-- The canonical scalar-restriction equivalence, fixed by its sectionwise functor.
Source: Stacks 03CY (blueprint: lem-trf-oriented-point-cohomology). -/
def fixed : Modules J A ≌ Sheaf J (ModuleCat.{s} A) :=
  (constant_ring_module_sheaves J A).1.choose

/-- Scalar restriction is additive. Source: Stacks 03CY
(blueprint: lem-trf-oriented-point-cohomology). -/
instance fixed_additive : (fixed J A).functor.Additive :=
  (constant_ring_module_sheaves J A).1.choose_spec.2.1

/-- Constant ring modules have enough injectives. Source: Stacks 07A5
(blueprint: lem-trf-oriented-point-cohomology). -/
instance modules_enoughInjectives : EnoughInjectives (Modules J A) :=
  letI := SheafOfModules.isGrothendieckAbelian
    ((constantSheaf J RingCat.{s}).obj (RingCat.of A))
  inferInstance

/-- The equivalent fixed-ring encoding has enough injectives too. Source: Stacks 07A5
(blueprint: lem-trf-oriented-point-cohomology). -/
instance fixed_enoughInjectives : EnoughInjectives (Sheaf J (ModuleCat.{s} A)) :=
  EnoughInjectives.of_equivalence (fixed J A).inverse

/-- Standard derived localization of the ringed module category. Source: Stacks 05RR
(blueprint: lem-trf-oriented-point-cohomology). -/
instance modules_hasDerived : HasDerivedCategory (Modules J A) := HasDerivedCategory.standard _

/-- Standard derived localization of the equivalent fixed-ring category. Source: Stacks 05RR
(blueprint: lem-trf-oriented-point-cohomology). -/
instance fixed_hasDerived : HasDerivedCategory (Sheaf J (ModuleCat.{s} A)) :=
  HasDerivedCategory.standard _

/-- Standard derived localization of coefficient modules. Source: Stacks 05RR
(blueprint: lem-trf-oriented-point-cohomology). -/
instance coefficient_hasDerived (B : Type v) [CommRing B] :
    HasDerivedCategory (ModuleCat.{s} B) :=
  HasDerivedCategory.standard _

end Coefficients

section Comparison
variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  (Λ : Type v) [CommRing Λ]
  {Ωx Ωy : Type u} [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
  (x : Spec (.of Ωx) ⟶ X) (y : Spec (.of Ωy) ⟶ Y)
  (c : Scheme.strictHenselizationScheme (y ≫ g) ⟶
    Scheme.strictHenselizationScheme (x ≫ f))
  (hc : c ≫ Scheme.strictHenselizationStructuralMap (x ≫ f) =
    Scheme.strictHenselizationStructuralMap (y ≫ g))

/-- Return lifted coefficient modules to the original ring by its canonical ring equivalence.
Source: Illusie §1.3; Mathlib ULift.ringEquiv
(blueprint: lem-trf-oriented-point-cohomology). -/
def downCoefficients : ModuleCat.{max u v + 1} (ULift.{max u v + 1} Λ) ⥤
    ModuleCat.{max u v + 1} Λ :=
  ModuleCat.restrictScalars ULift.ringEquiv.symm.toRingHom

/-- The actual continuous direct image with constant coefficients.
Source: Illusie §1.2 (blueprint: lem-trf-oriented-point-cohomology). -/
def pushFixed := (psiSite.{u, v} f g).sheafPushforwardContinuous
  (ModuleCat.{max u v + 1} (ULift.{max u v + 1} Λ)) (topology f g)
  (etaleTopology (pullback f g))

/-- The actual exact scheme inverse image on fixed-ring sheaves.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
def pullFixed := Functor.sheafPullbackConstruction.sheafPullback
  (etaleBaseChange.{u, v + 1} (r f g x y c hc))
  (ModuleCat.{max u v + 1} (ULift.{max u v + 1} Λ)) (etaleTopology (pullback f g))
    (etaleTopology (M f g x y c))

/-- Sections at the final object of the transported étale site.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
def sectionsFixed (N : Scheme.{u}) :=
  (sheafSections (etaleTopology.{u, v + 1} N)
    (ModuleCat.{max u v + 1} (ULift.{max u v + 1} Λ))).obj (op (finalEtale N)) ⋙
      downCoefficients.{u, v} Λ

/-- The oriented-point inverse image, computed by its filtered-colimit fibre functor.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
def fiberFixed := (z.{u, v} f g x y c hc).sheafFiber
  (A := ModuleCat.{max u v + 1} (ULift.{max u v + 1} Λ)) ⋙ downCoefficients.{u, v} Λ

/-- Direct image on the node's ringed constant-module category.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
def push := (fixed (etaleTopology.{u, v + 1} (pullback f g)) (ULift.{max u v + 1} Λ)).functor ⋙
  pushFixed f g Λ

/-- Exact inverse image on the node's ringed constant-module category.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
def pull := (fixed (etaleTopology.{u, v + 1} (pullback f g)) (ULift.{max u v + 1} Λ)).functor ⋙
  pullFixed f g Λ x y c hc

/-- Additivity and exactness of the specified functors, without extra hypotheses.
Source: Stacks 00YA, 03CY; Illusie §1.3
(blueprint: lem-trf-oriented-point-cohomology).
Proof: direct image and evaluation are sectionwise additive. Scheme inverse image
preserves finite limits and colimits. Point inverse image is a filtered colimit of
module sections: filtered module colimits are exact. The scalar-restriction equivalence
is additive and preserves limits and colimits, so its composites have the same properties. -/
theorem coefficient_properties :
    (pushFixed.{u, v} f g Λ).Additive ∧
    (pullFixed.{u, v} f g Λ x y c hc).Additive ∧
    PreservesFiniteLimits (pullFixed.{u, v} f g Λ x y c hc) ∧
    PreservesFiniteColimits (pullFixed.{u, v} f g Λ x y c hc) ∧
    (sectionsFixed.{u, v} Λ (M f g x y c)).Additive ∧
    (fiberFixed.{u, v} f g Λ x y c hc).Additive ∧
    PreservesFiniteLimits (fiberFixed.{u, v} f g Λ x y c hc) ∧
    PreservesFiniteColimits (fiberFixed.{u, v} f g Λ x y c hc) := by
  sorry

/-- Additivity of direct image. Source: Illusie §1.3
(blueprint: lem-trf-oriented-point-cohomology). -/
instance pushFixed_additive : (pushFixed.{u, v} f g Λ).Additive where
  map_add := by intros; rfl

/-- Exact inverse image is additive. Source: Illusie §1.3
(blueprint: lem-trf-oriented-point-cohomology). -/
instance pullFixed_additive : (pullFixed.{u, v} f g Λ x y c hc).Additive :=
  (coefficient_properties f g Λ x y c hc).2.1

/-- Inverse image preserves finite limits. Source: Illusie §1.3
(blueprint: lem-trf-oriented-point-cohomology). -/
instance pullFixed_limits : PreservesFiniteLimits (pullFixed.{u, v} f g Λ x y c hc) :=
  (coefficient_properties f g Λ x y c hc).2.2.1

/-- Inverse image preserves finite colimits. Source: Illusie §1.3
(blueprint: lem-trf-oriented-point-cohomology). -/
instance pullFixed_colimits : PreservesFiniteColimits (pullFixed.{u, v} f g Λ x y c hc) :=
  (coefficient_properties f g Λ x y c hc).2.2.2.1

/-- Evaluation at the final étale object is additive. Source: Illusie §1.3
(blueprint: lem-trf-oriented-point-cohomology). -/
instance sectionsFixed_additive (N : Scheme.{u}) : (sectionsFixed.{u, v} Λ N).Additive := by
  let _ : ((sheafSections (etaleTopology.{u, v + 1} N)
      (ModuleCat.{max u v + 1} (ULift.{max u v + 1} Λ))).obj
        (op (finalEtale N))).Additive :=
    Functor.additive_of_iso (sheafSectionsNatIsoEvaluation
      (J := etaleTopology.{u, v + 1} N)
      (A := ModuleCat.{max u v + 1} (ULift.{max u v + 1} Λ))
      (X := finalEtale N)).symm
  unfold sectionsFixed downCoefficients
  infer_instance

/-- Point inverse image is additive. Source: Illusie §1.3
(blueprint: lem-trf-oriented-point-cohomology). -/
instance fiberFixed_additive : (fiberFixed.{u, v} f g Λ x y c hc).Additive :=
  (coefficient_properties f g Λ x y c hc).2.2.2.2.2.1

/-- Point inverse image preserves finite limits. Source: Illusie §1.3
(blueprint: lem-trf-oriented-point-cohomology). -/
instance fiberFixed_limits : PreservesFiniteLimits (fiberFixed.{u, v} f g Λ x y c hc) :=
  (coefficient_properties f g Λ x y c hc).2.2.2.2.2.2.1

/-- Point inverse image preserves finite colimits. Source: Illusie §1.3
(blueprint: lem-trf-oriented-point-cohomology). -/
instance fiberFixed_colimits : PreservesFiniteColimits (fiberFixed.{u, v} f g Λ x y c hc) :=
  (coefficient_properties f g Λ x y c hc).2.2.2.2.2.2.2

/-- The source change of coefficient encoding is additive.
Source: Stacks 03CY (blueprint: lem-trf-oriented-point-cohomology). -/
instance push_additive : (push.{u, v} f g Λ).Additive := by
  unfold push
  infer_instance

/-- The exact composite inverse image is additive.
Source: Stacks 03CY (blueprint: lem-trf-oriented-point-cohomology). -/
instance pull_additive : (pull.{u, v} f g Λ x y c hc).Additive := by
  unfold pull
  infer_instance

/-- The composite inverse image preserves finite limits.
Source: Stacks 03CY (blueprint: lem-trf-oriented-point-cohomology). -/
instance pull_limits : PreservesFiniteLimits (pull.{u, v} f g Λ x y c hc) := by
  unfold pull
  infer_instance

/-- The composite inverse image preserves finite colimits.
Source: Stacks 03CY (blueprint: lem-trf-oriented-point-cohomology). -/
instance pull_colimits : PreservesFiniteColimits (pull.{u, v} f g Λ x y c hc) := by
  unfold pull
  infer_instance

/-- Restrict a section to M using q and the actual inverse-image adjunction unit.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
def sectionRestriction
    (H : Sheaf (etaleTopology.{u, v + 1} (pullback f g))
      (ModuleCat.{max u v + 1} (ULift.{max u v + 1} Λ)))
    (T : Triples.{u, v} f g) (l : Lift f g x y c T) :
    H.obj.obj (op ((psiSite f g).obj T)) ⟶
      ((pullFixed f g Λ x y c hc).obj H).obj.obj (op (finalEtale (M f g x y c))) :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (etaleBaseChange.{u, v + 1} (r f g x y c hc))
    (ModuleCat.{max u v + 1} (ULift.{max u v + 1} Λ))
    (etaleTopology (pullback f g)) (etaleTopology (M f g x y c))).unit.app H).hom.app
      (op ((psiSite f g).obj T)) ≫
    ((pullFixed f g Λ x y c hc).obj H).obj.map (qEtale f g x y c hc T l).op

/-- Restriction on all pointed triples uniquely specifies the ordinary comparison.
This includes the affine triples used in Illusie's inverse-limit description.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology).
Proof: the sectionRestriction maps form a cocone over pointed triples, by the over-Z
condition on q and naturality of the inverse-image unit. The defining filtered-colimit
universal property of the site-point fibre gives a unique linear map. Its uniqueness
gives naturality in H and uniqueness as a natural transformation. -/
theorem restrictionFixed_unique :
    ∃! ρ : pushFixed.{u, v} f g Λ ⋙ fiberFixed f g Λ x y c hc ⟶
        pullFixed f g Λ x y c hc ⋙ sectionsFixed Λ (M f g x y c),
      ∀ (H : Sheaf (etaleTopology.{u, v + 1} (pullback f g))
          (ModuleCat.{max u v + 1} (ULift.{max u v + 1} Λ)))
        (T : Triples.{u, v} f g) (l : Lift f g x y c T),
        (downCoefficients.{u, v} Λ).map
            ((z f g x y c hc).toPresheafFiber T ⟨l⟩ ((pushFixed f g Λ).obj H).obj) ≫
          ρ.app H = (downCoefficients.{u, v} Λ).map
            (sectionRestriction f g Λ x y c hc H T l) := by
  sorry

/-- The canonical ordinary restriction comparison, determined on every colimit generator.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
def restrictionFixed := (restrictionFixed_unique.{u, v} f g Λ x y c hc).choose

/-- The same restriction with the ringed constant-module source of the node.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
def restriction : push.{u, v} f g Λ ⋙ fiberFixed f g Λ x y c hc ⟶
    pull f g Λ x y c hc ⋙ sectionsFixed Λ (M f g x y c) :=
  Functor.whiskerLeft (fixed (etaleTopology (pullback f g)) (ULift.{max u v + 1} Λ)).functor
    (restrictionFixed f g Λ x y c hc)

/-- Rψ_* computed by the bounded-below right-derived construction.
Source: Illusie §§1.2--1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
def Rpsi :
    DerivedCategory.Plus
      (Modules (etaleTopology.{u, v + 1} (pullback f g)) (ULift.{max u v + 1} Λ)) ⥤
      DerivedCategory.Plus
      (Sheaf (topology.{u, v} f g) (ModuleCat.{max u v + 1} (ULift.{max u v + 1} Λ))) :=
  (push.{u, v} f g Λ).rightDerivedFunctorPlus

/-- Exact point inverse image, with the recorded derived-inverse-image construction.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
def zStar :
    DerivedCategory.Plus
      (Sheaf (topology.{u, v} f g) (ModuleCat.{max u v + 1} (ULift.{max u v + 1} Λ))) ⥤
      DerivedCategory.Plus (ModuleCat.{max u v + 1} Λ) :=
  (fiberFixed.{u, v} f g Λ x y c hc).mapDerivedCategoryPlus

/-- Exact inverse image along the natural map r, with no resolution required.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
def rStar :
    DerivedCategory.Plus
      (Modules (etaleTopology.{u, v + 1} (pullback f g)) (ULift.{max u v + 1} Λ)) ⥤
      DerivedCategory.Plus
      (Sheaf (etaleTopology.{u, v + 1} (M f g x y c))
        (ModuleCat.{max u v + 1} (ULift.{max u v + 1} Λ))) :=
  (pull.{u, v} f g Λ x y c hc).mapDerivedCategoryPlus

/-- RΓ computed by the bounded-below right-derived construction.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
def RGamma :
    DerivedCategory.Plus
      (Sheaf (etaleTopology.{u, v + 1} (M f g x y c))
        (ModuleCat.{max u v + 1} (ULift.{max u v + 1} Λ))) ⥤
      DerivedCategory.Plus (ModuleCat.{max u v + 1} Λ) :=
  (sectionsFixed.{u, v} Λ (M f g x y c)).rightDerivedFunctorPlus

/-- The source comparison from complexes to z*Rψ, using the actual right-derived unit.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
def sourceUnit :=
  Functor.whiskerLeft (push.{u, v} f g Λ).mapHomotopyCategoryPlus
      (fiberFixed f g Λ x y c hc).mapDerivedCategoryPlusFactorsh.inv ≫
    Functor.whiskerRight (push f g Λ).rightDerivedFunctorPlusUnit
      (zStar f g Λ x y c hc)

/-- The target comparison to RΓ r*, using the actual right-derived unit.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
def targetUnit :=
  Functor.whiskerLeft (pull.{u, v} f g Λ x y c hc).mapHomotopyCategoryPlus
      (sectionsFixed Λ (M f g x y c)).rightDerivedFunctorPlusUnit ≫
    Functor.whiskerRight (pull f g Λ x y c hc).mapDerivedCategoryPlusFactorsh.inv
      (RGamma f g Λ x y c)

/-- The ordinary restriction applied termwise on the bounded-below homotopy category.
Source: Illusie §1.3 (blueprint: lem-trf-oriented-point-cohomology). -/
def restrictionHomotopy :=
  (Functor.mapHomotopyCategoryPlusCompIso
      (Iso.refl (push.{u, v} f g Λ ⋙ fiberFixed f g Λ x y c hc))).hom ≫
    NatTrans.mapHomotopyCategoryPlus (restriction f g Λ x y c hc) ≫
    (Functor.mapHomotopyCategoryPlusCompIso
      (Iso.refl (pull f g Λ x y c hc ⋙ sectionsFixed Λ (M f g x y c)))).inv

end Comparison

/-- The canonical restriction comparison is an isomorphism natural in every bounded-below K.
The displayed equation specifies its actual restriction map, rather than mere isomorphism
of the two objects.

Source: Illusie, Around the Thom--Sebastiani theorem, §1.3 (1.3.1)
(blueprint: lem-trf-oriented-point-cohomology).

Proof (the seven steps of the DAG):
1. The triple construction and OrientedProduct.universal give ψ and z. The initial affine
pointed-triple neighbourhoods have represented schemes D_i, étale over Z, with affine
transition maps and limit M (lem-trf-oriented-affine-neighbourhood-limit).
2. Choose a bounded-below injective representative J of K. Right-derived direct image is
computed by ψ_*J. The point-fibre colimit description (lem-trf-site-point-fibre) identifies
its stalk complex with L = colim J(D_i).
3. Filtered module colimits are exact, so H^n(L) = colim H^n(J(D_i)).
4. Localization at D_i and the inverse-image restriction/unit comparisons identify these
cohomology groups with H^n(D_i,t_i* K), compatibly with transitions. Use the scalar-forgetting
interfaces lem-pe-left-module-derived-evaluation-forget and
lem-pe-constant-left-module-inverse-image, without assuming forgetful functors preserve
injectives.
5. Restriction along q_i gives J(D_i) → Γ(M,r*J). Compose with a K-injective resolution
r*J → A. Its colimit is the canonical chain map L → Γ(M,A). The adjunction unit in
sectionRestriction makes it precisely the stated restriction map.
6. Derived étale inverse-limit continuity (lem-weil-pbc-derived-etale-cohomology-limit)
makes H^n of that map an isomorphism: D_i are affine, transitions affine, and J is bounded
below. Forgetting scalars detects the resulting module isomorphisms.
7. The chain map is a quasi-isomorphism. Localization gives the required derived isomorphism.
Functorial resolutions and uniqueness of the right-derived units give naturality and
independence of resolutions. Their universal property gives exactly the displayed
normalization and its uniqueness. No qcqs, finite-type or torsion hypothesis is needed. -/
theorem orientedPointCohomology
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (Λ : Type v) [CommRing Λ]
    {Ωx Ωy : Type u} [Field Ωx] [IsAlgClosed Ωx] [Field Ωy] [IsAlgClosed Ωy]
    (x : Spec (.of Ωx) ⟶ X) (y : Spec (.of Ωy) ⟶ Y)
    (c : Scheme.strictHenselizationScheme (y ≫ g) ⟶
      Scheme.strictHenselizationScheme (x ≫ f))
    (hc : c ≫ Scheme.strictHenselizationStructuralMap (x ≫ f) =
      Scheme.strictHenselizationStructuralMap (y ≫ g)) :
    ∃! e : Rpsi.{u, v} f g Λ ⋙ zStar f g Λ x y c hc ≅
        rStar f g Λ x y c hc ⋙ RGamma f g Λ x y c,
      sourceUnit f g Λ x y c hc ≫ Functor.whiskerLeft DerivedCategory.Plus.Qh e.hom =
        Functor.whiskerRight (restrictionHomotopy f g Λ x y c hc) DerivedCategory.Plus.Qh ≫
          targetUnit f g Λ x y c hc := by
  sorry

end CategoryTheory.OrientedPointCohomology
