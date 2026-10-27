/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.ModuliChartNormalization
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism

/-! # Intrinsic morphism properties of Deligne--Mumford stacks

Source: Stacks, stacks-morphisms.tex, Tags 0CL5, 06PU and 06UF;
stacks-properties.tex, underlying topological space
(blueprint: def-sfb-dm-stack-morphism-properties).

Field objects are identified by arrows (hence by common field extensions and
isomorphisms). Closed subsets are detected on étale scheme charts. Scheme tests
for universal closedness suffice, by descent of closed subsets along atlases.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- A field-valued object, retaining its field scheme and its object over it.
Source: Stacks, topology of stacks
(blueprint: def-sfb-dm-stack-morphism-properties). -/
def ModuliFieldObject {S : Scheme.{u}} (F : BasedCategory.{v₁, w₁} (Over S)) :=
  {x : F.obj // ∃ (K : Type u) (_ : Field K),
    Nonempty ((F.p.obj x).left ≅ Spec (.of K))}

/-- Field objects are related by arrows over field extensions; the quotient takes
its equivalence closure, including isomorphisms and common extensions.
Source: Stacks, topology of stacks
(blueprint: def-sfb-dm-stack-morphism-properties). -/
def ModuliFieldRelation {S : Scheme.{u}} (F : BasedCategory.{v₁, w₁} (Over S))
    (x y : ModuliFieldObject F) : Prop := Nonempty (x.val ⟶ y.val)

/-- The point set of a stack is the quotient of its field-valued objects.
Source: Stacks, topology of stacks
(blueprint: def-sfb-dm-stack-morphism-properties). -/
abbrev ModuliPoints {S : Scheme.{u}} (F : BasedCategory.{v₁, w₁} (Over S)) :=
  Quot (ModuliFieldRelation F)

/-- The actual image of a field object under a morphism of stacks.
Source: Stacks, topology of stacks
(blueprint: def-sfb-dm-stack-morphism-properties). -/
def moduliFieldMap {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) (x : ModuliFieldObject F) : ModuliFieldObject G :=
  ⟨f.obj x.val, by simpa only [f.w_obj] using x.property⟩

/-- The induced map on point classes is induced by the given functor.
Source: Stacks, topology of stacks
(blueprint: def-sfb-dm-stack-morphism-properties). -/
def moduliPointMap {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : ModuliPoints F → ModuliPoints G :=
  Quot.map (moduliFieldMap f) (fun {_ _} h ↦ h.elim (fun a ↦ ⟨f.map a⟩))

/-- A representable property on all actual scheme base changes, with projection
comparison over the base. This is used for proper and closed-immersion diagonals.
Source: Stacks, representable morphism conventions
(blueprint: def-sfb-dm-stack-morphism-properties). -/
def ModuliSchemeTest {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : Prop :=
  ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) G),
    ∃ (R : Over S) (p : R ⟶ T)
        (e : BasedFunctor (discreteModuli (yoneda.obj R)) (moduliTwoFiberProduct t f)),
      IsSchemeModuliBaseChange e p ∧ P p.left

/-- A source-local representable property, tested on all étale scheme charts of
all algebraic-space base changes. Properness is not tested this way.
Source: Stacks, properties of representable morphisms
(blueprint: def-sfb-dm-stack-morphism-properties). -/
def ModuliSpaceTest {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : Prop :=
  ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) G),
    ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
      HasSpaceBaseChange f T t Z p ∧
        ∀ (U : Over S) (a : yoneda.obj U ⟶ Z.obj.obj), AlgebraicSpace.IsEtale a →
          P (yoneda.preimage (a ≫ p)).left

/-- An étale scheme atlas, with surjectivity tested on the actual base changes.
Source: Stacks, Tag 025Y
(blueprint: def-sfb-dm-stack-morphism-properties). -/
def IsEtaleModuliAtlas {S : Scheme.{u}} {F : BasedCategory.{v₁, w₁} (Over S)}
    {U : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj U)) F) : Prop :=
  IsEtaleModuliMap a ∧
    ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
      ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange a T t Z p ∧ SpaceMapIsSurjective Z T p

/-- Inverse image of a set of stack points on a scheme chart. A scheme point is
represented by any field-valued point above it, with its actual chart object.
Source: Stacks, topology of stacks
(blueprint: def-sfb-dm-stack-morphism-properties). -/
def moduliChartPreimage {S : Scheme.{u}} {F : BasedCategory.{v₁, w₁} (Over S)}
    {U : Over S} (a : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (C : Set (ModuliPoints F)) : Set U.left :=
  {z | ∃ x : ModuliFieldObject (discreteModuli (yoneda.obj U)),
    C (moduliPointMap a (Quot.mk _ x)) ∧
      z ∈ Set.range ((yoneda.preimage x.val.hom).left)}

/-- Closed sets are exactly those whose inverse images on all étale atlases are
closed; no atlas or topology is chosen arbitrarily.
Source: Stacks, topology of DM stacks
(blueprint: def-sfb-dm-stack-morphism-properties). -/
def ModuliPointIsClosed {S : Scheme.{u}} (F : BasedCategory.{v₁, w₁} (Over S))
    (C : Set (ModuliPoints F)) : Prop :=
  ∀ (U : Over S) (a : BasedFunctor (discreteModuli (yoneda.obj U)) F),
    IsEtaleModuliAtlas a → IsClosed (moduliChartPreimage a C)

/-- A relative diagonal sends an object to its pair and the identity comparison.
Source: Stacks, relative diagonals
(blueprint: def-sfb-dm-stack-morphism-properties). -/
def moduliRelativeDiagonal {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : BasedFunctor F (moduliTwoFiberProduct f f) where
  toFunctor :=
    { obj := fun x ↦ ⟨⟨x, x, 𝟙 (f.obj x)⟩, inferInstance, inferInstance⟩
      map := fun a ↦ ObjectProperty.homMk ⟨a, a, by simp⟩ }
  w := rfl

/-- Relative local finite type, tested on étale scheme charts of every scheme
base change; for DM stacks these are also smooth charts, and give the intrinsic
locally-finite-type property. The chart need not be quasi-compact.
Source: Stacks, finite-type morphisms and Tag 06UF
(blueprint: def-sfb-dm-stack-morphism-properties). -/
def IsLocallyFiniteTypeModuliMap {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : Prop :=
  ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) G)
      (U : Over S)
      (a : BasedFunctor (discreteModuli (yoneda.obj U)) (moduliTwoFiberProduct t f))
      (p : U ⟶ T),
    IsEtaleModuliAtlas a →
      Nonempty (ModuliTwoIso (a.comp (moduliTwoFiberFst t f))
        (discreteModuliMap (yoneda.map p))) → LocallyOfFiniteType p.left

/-- Quasi-compactness: the pullback to each affine test scheme has a
quasi-compact étale scheme atlas.
Source: Stacks, quasi-compact morphisms of DM stacks
(blueprint: def-sfb-dm-stack-morphism-properties). -/
def IsQuasiCompactModuliMap {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : Prop :=
  ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) G),
    IsAffine T.left → ∃ (U : Over S)
      (a : BasedFunctor (discreteModuli (yoneda.obj U)) (moduliTwoFiberProduct t f)),
      IsEtaleModuliAtlas a ∧ IsCompact (Set.univ : Set U.left)

/-- Universal closedness, tested after every scheme base change on point spaces.
Closedness descends from these tests to arbitrary stack base changes by atlases.
Source: Stacks, universally closed morphisms
(blueprint: def-sfb-dm-stack-morphism-properties). -/
def IsUniversallyClosedModuliMap {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : Prop :=
  ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) G)
      (C : Set (ModuliPoints (moduliTwoFiberProduct t f))),
    ModuliPointIsClosed (moduliTwoFiberProduct t f) C →
      ModuliPointIsClosed (discreteModuli (yoneda.obj T))
        (moduliPointMap (moduliTwoFiberFst t f) '' C)

/-- Properness retains finite type, quasi-compactness, universal closedness and
properness of the relative diagonal, with no representability hypothesis on f.
For DM diagonals proper algebraic-space tests are finite, hence scheme tests.
Source: Stacks, Tag 0CL5
(blueprint: def-sfb-dm-stack-morphism-properties). -/
def IsProperModuliMap {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : Prop :=
  IsLocallyFiniteTypeModuliMap f ∧ IsQuasiCompactModuliMap f ∧
    IsUniversallyClosedModuliMap f ∧ ModuliSchemeTest @IsProper (moduliRelativeDiagonal f)

/-- Locally quasi-finite means locally of finite type, locally quasi-finite
relative diagonal, and discrete field fibres. Discreteness is expressed by
closed complements of singletons in the atlas-detected point topology.
Source: Stacks, Tags 06PU and 06UF
(blueprint: def-sfb-dm-stack-morphism-properties). -/
def IsLocallyQuasiFiniteModuliMap {S : Scheme.{u}}
    {F : BasedCategory.{v₁, w₁} (Over S)} {G : BasedCategory.{v₂, w₂} (Over S)}
    (f : BasedFunctor F G) : Prop :=
  IsLocallyFiniteTypeModuliMap f ∧
    ModuliSpaceTest @Scheme.Hom.IsLocallyQuasiFinite (moduliRelativeDiagonal f) ∧
    ∀ (K : Type u) [Field K] (b : Spec (.of K) ⟶ S)
      (t : BasedFunctor (discreteModuli (yoneda.obj (Over.mk b))) G)
      (x : ModuliPoints (moduliTwoFiberProduct t f)),
      ModuliPointIsClosed (moduliTwoFiberProduct t f) ({x}ᶜ)

/-- Ordinary chartwise local quasi-finiteness of an algebraic-space morphism.
Every pair of étale scheme charts and compatible scheme map is tested, including
nonsurjective charts. Source: Stacks, Spaces, Tag 03XJ
(blueprint: def-sfb-dm-stack-morphism-properties). -/
def SpaceMapIsLocallyQuasiFinite {S : Scheme.{u}} {E F : AlgebraicSpace S}
    (f : E ⟶ F) : Prop :=
  ∀ (U V : Over S) (a : yoneda.obj U ⟶ E.obj.obj) (b : yoneda.obj V ⟶ F.obj.obj)
      (p : U ⟶ V),
    AlgebraicSpace.IsEtale a → AlgebraicSpace.IsEtale b →
      a ≫ f.hom.hom = yoneda.map p ≫ b → Scheme.Hom.IsLocallyQuasiFinite p.left

/-- Ordinary properness for spaces: local finite type on compatible étale scheme
charts, quasi-compactness on the ordinary point spaces over affine schemes,
and closed point maps after every scheme base change. Separatedness is the
closed-immersion property of the actual presheaf relative diagonal. These use
the existing algebraic-space point classes and atlas topology independently of
the stack predicates. Scheme tests suffice for universal closedness by descent
of closed subsets along an atlas of an arbitrary algebraic-space base change.
Source: Stacks, Morphisms of Spaces, definition-locally-finite-type,
definition-closed, definition-proper and Tag 04YS
(blueprint: def-sfb-dm-stack-morphism-properties). -/
def SpaceMapIsProper {S : Scheme.{u}} {E F : AlgebraicSpace S} (f : E ⟶ F) : Prop :=
  (∀ (U V : Over S) (a : yoneda.obj U ⟶ E.obj.obj) (b : yoneda.obj V ⟶ F.obj.obj)
      (p : U ⟶ V),
    AlgebraicSpace.IsEtale a → AlgebraicSpace.IsEtale b →
      a ≫ f.hom.hom = yoneda.map p ≫ b → LocallyOfFiniteType p.left) ∧
    AlgebraicSpace.MapIsQuasiCompact f.hom.hom ∧
    (∀ (T : Over S) (a : yoneda.obj T ⟶ F.obj.obj),
      IsClosedMap (AlgebraicSpace.mapPoint (pullback.snd f.hom.hom a))) ∧
    AlgebraicSpace.IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (pullback.diagonal f.hom.hom)

end CategoryTheory
