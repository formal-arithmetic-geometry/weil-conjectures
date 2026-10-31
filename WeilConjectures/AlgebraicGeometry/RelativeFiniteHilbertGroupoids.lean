/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StablePointedModuliGroupoids
public import WeilConjectures.CategoryTheory.SiteStackification
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.UnramifiedMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.Data.PNat.Basic
public import WeilConjectures.AlgebraicGeometry.LciCotangentPresentation

/-! # Relative finite Hilbert groupoids

Source: Stacks Project, examples-stacks.tex, construction preceding Tag 05WC;
criteria.tex, section-lci and equation-relative-map; spaces-morphisms.tex, Tag 03ZH;
spaces-more-morphisms.tex, Tag 06C4; divisors.tex, Tag 063J
(blueprint: def-sfb-relative-finite-hilbert-groupoids).

A cartesian arrow `F(x) → y` over `p` encodes the inverse of `α : p* y ≅ F(x)`.
The relative fibre is the explicit category of triples in the node: its comparison
arrow determines the map to the base. It is a costructured-arrow category, without
quotienting objects by isomorphism. A representative includes an equivalence over
the scheme base, so its inverse gives the specified map to the representing space.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Objects of the degree `d` finite Hilbert category. The comparison arrow is the
inverse-α convention explained above, and its base is exactly `p`.
Source: Stacks 05WC, preceding construction
(blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
structure RelativeFiniteHilbert {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    (F : BasedFunctor X Y) (d : ℕ+) where
  T : Over S
  Z : Over S
  p : Z ⟶ T
  finite : p.left.IsFiniteLocallyFreeOfDegree d
  y : Functor.Fiber Y.p T
  x : Functor.Fiber X.p Z
  comparison : F.obj x.val ⟶ y.val
  comparison_lift : Y.p.IsHomLift p comparison

namespace RelativeFiniteHilbert

variable {S : Scheme.{u}} {X : BasedCategory.{v₁, w₁} (Over S)}
  {Y : BasedCategory.{v₂, w₂} (Over S)} {F : BasedFunctor X Y} {d : ℕ+}

/-- Arrows retain the cartesian scheme square, the two cartesian arrows (equivalently
isomorphisms to the pullbacks), and the comparison square.
Source: Stacks 05WC, preceding construction
(blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
@[ext]
structure Hom (A B : RelativeFiniteHilbert F d) where
  g : A.T ⟶ B.T
  h : A.Z ⟶ B.Z
  cartesian : IsPullback h A.p B.p g
  b : A.y.val ⟶ B.y.val
  b_lift : Y.p.IsHomLift g b
  a : A.x.val ⟶ B.x.val
  a_lift : X.p.IsHomLift h a
  comm : F.map a ≫ B.comparison = A.comparison ≫ b

/-- Identity and composite comparison squares and cartesian scheme squares.
Source: Stacks 05WC, composition in the preceding construction
(blueprint: def-sfb-relative-finite-hilbert-groupoids).
Proof: identities give identity pullback squares and identity lifts. For composition,
paste the two pullback squares; lifts compose. Apply functoriality of F and the two
comparison equations to obtain the composite comparison equation. -/
theorem hom_operations :
    (∀ A : RelativeFiniteHilbert F d,
      IsPullback (𝟙 A.Z) A.p A.p (𝟙 A.T) ∧
      Y.p.IsHomLift (𝟙 A.T) (𝟙 A.y.val) ∧
      X.p.IsHomLift (𝟙 A.Z) (𝟙 A.x.val) ∧
      F.map (𝟙 A.x.val) ≫ A.comparison = A.comparison ≫ 𝟙 A.y.val) ∧
    (∀ {A B C : RelativeFiniteHilbert F d} (f : Hom A B) (g : Hom B C),
      IsPullback (f.h ≫ g.h) A.p C.p (f.g ≫ g.g) ∧
      Y.p.IsHomLift (f.g ≫ g.g) (f.b ≫ g.b) ∧
      X.p.IsHomLift (f.h ≫ g.h) (f.a ≫ g.a) ∧
      F.map (f.a ≫ g.a) ≫ C.comparison = A.comparison ≫ (f.b ≫ g.b)) := by
  sorry

/-- The total category has componentwise identity and composition.
Source: Stacks 05WC (blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
instance category : Category (RelativeFiniteHilbert F d) where
  Hom := Hom
  id A := ⟨𝟙 _, 𝟙 _, (hom_operations.1 A).1, 𝟙 _, (hom_operations.1 A).2.1,
    𝟙 _, (hom_operations.1 A).2.2.1, (hom_operations.1 A).2.2.2⟩
  comp f g := ⟨f.g ≫ g.g, f.h ≫ g.h, (hom_operations.2 f g).1,
    f.b ≫ g.b, (hom_operations.2 f g).2.1, f.a ≫ g.a,
    (hom_operations.2 f g).2.2.1, (hom_operations.2 f g).2.2.2⟩
  id_comp f := by ext <;> simp
  comp_id f := by ext <;> simp
  assoc f g h := by ext <;> simp [Category.assoc]

/-- The requested `p_d` remembers the target object `y`, including its arrows.
Source: Stacks 05WC (blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
def target : RelativeFiniteHilbert F d ⥤ Y.obj where
  obj A := A.y.val
  map f := f.b

/-- The projection to the scheme base remembers `T` and `g`.
Source: Stacks 05WC (blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
def base : RelativeFiniteHilbert F d ⥤ Over S where
  obj A := A.T
  map f := f.g

/-- The finite Hilbert groupoid over the big fppf scheme category. Its hypotheses
use the recorded fppf stack predicate, rather than the étale-only stack predicate.
The positive degree excludes zero, precisely as in the source.
Source: Stacks 05WC (blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
def groupoid (F : BasedFunctor X Y) (d : ℕ+)
    (_hX : IsFppfModuliStack X) (_hY : IsFppfModuliStack Y) : BasedCategory (Over S) :=
  BasedCategory.ofFunctor (base (F := F) (d := d))

/-- The fibre category over a test scheme is `H_d(F)(T)`.
Source: Stacks 05WC (blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
abbrev Fiber (T : Over S) := Functor.Fiber (base (F := F) (d := d)) T

/-- The pullback object in `X`, on the actual scheme fibre product.
Source: Stacks 05WC (blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
def pullbackX (hX : IsFibredInGroupoids X) (A : RelativeFiniteHilbert F d)
    {T' : Over S} (g : T' ⟶ A.T) : X.obj :=
  letI := hX.1
  Functor.IsPreFibered.pullbackObj A.x.property (pullback.fst A.p g)

/-- The pullback object in `Y` along the given base arrow.
Source: Stacks 05WC (blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
def pullbackY (hY : IsFibredInGroupoids Y) (A : RelativeFiniteHilbert F d)
    {T' : Over S} (g : T' ⟶ A.T) : Y.obj :=
  letI := hY.1
  Functor.IsPreFibered.pullbackObj A.y.property g

/-- The actual cartesian arrow from the pullback of x to x.
Source: Stacks 05WC (blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
def pullbackXArrow (hX : IsFibredInGroupoids X) (A : RelativeFiniteHilbert F d)
    {T' : Over S} (g : T' ⟶ A.T) : A.pullbackX hX g ⟶ A.x.val :=
  letI := hX.1
  Functor.IsPreFibered.pullbackMap A.x.property (pullback.fst A.p g)

/-- The actual cartesian arrow from the pullback of y to y.
Source: Stacks 05WC (blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
def pullbackYArrow (hY : IsFibredInGroupoids Y) (A : RelativeFiniteHilbert F d)
    {T' : Over S} (g : T' ⟶ A.T) : A.pullbackY hY g ⟶ A.y.val :=
  letI := hY.1
  Functor.IsPreFibered.pullbackMap A.y.property g

/-- The comparison after pullback is the unique lift of the composite comparison
through the cartesian pullback of `y`. Thus the pullback includes the specified α.
Source: Stacks 05WC (blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
def pullbackComparison (hX : IsFibredInGroupoids X) (hY : IsFibredInGroupoids Y)
    (A : RelativeFiniteHilbert F d) {T' : Over S} (g : T' ⟶ A.T) :
    F.obj (A.pullbackX hX g) ⟶ A.pullbackY hY g :=
  letI := hX.1
  letI := hY.1
  letI := A.comparison_lift
  Functor.IsStronglyCartesian.map Y.p g
    (Functor.IsPreFibered.pullbackMap A.y.property g)
    (f' := pullback.fst A.p g ≫ A.p) (g := pullback.snd A.p g)
    (pullback.condition (f := A.p) (g := g))
    (F.map (Functor.IsPreFibered.pullbackMap A.x.property (pullback.fst A.p g)) ≫
      A.comparison)

/-- The proof obligations for the explicit pullback: finite degree, the two base
identities, and the base and comparison square of its cartesian arrow.
Source: Stacks 05WC (blueprint: def-sfb-relative-finite-hilbert-groupoids).
Proof: the scheme square is a pullback; finite locally free of degree d is stable
under base change. The two object-base identities are the cartesian lift identities.
The comparison is the unique strong cartesian lift, so has the stipulated base and
its composite with the pullback arrow of y is the original comparison after the
pullback arrow of x. These give the required Hilbert arrow over g. -/
theorem pullback_properties (hX : IsFibredInGroupoids X) (hY : IsFibredInGroupoids Y)
    (A : RelativeFiniteHilbert F d) {T' : Over S} (g : T' ⟶ A.T) :
    (pullback.snd A.p g).left.IsFiniteLocallyFreeOfDegree d ∧
    X.p.obj (A.pullbackX hX g) = pullback A.p g ∧
    Y.p.obj (A.pullbackY hY g) = T' ∧
    Y.p.IsHomLift (pullback.snd A.p g) (A.pullbackComparison hX hY g) ∧
    X.p.IsHomLift (pullback.fst A.p g) (A.pullbackXArrow hX g) ∧
    Y.p.IsHomLift g (A.pullbackYArrow hY g) ∧
    F.map (A.pullbackXArrow hX g) ≫ A.comparison =
      A.pullbackComparison hX hY g ≫ A.pullbackYArrow hY g := by
  sorry

/-- Pullback has the scheme base change as its cover and cartesian pullbacks as its
objects. All data are explicit; only their named property proofs are postponed.
Source: Stacks 05WC (blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
def pullback (hX : IsFibredInGroupoids X) (hY : IsFibredInGroupoids Y)
    (A : RelativeFiniteHilbert F d) {T' : Over S} (g : T' ⟶ A.T) :
    RelativeFiniteHilbert F d where
  T := T'
  Z := Limits.pullback A.p g
  p := Limits.pullback.snd A.p g
  finite := (A.pullback_properties hX hY g).1
  x := ⟨A.pullbackX hX g, (A.pullback_properties hX hY g).2.1⟩
  y := ⟨A.pullbackY hY g, (A.pullback_properties hX hY g).2.2.1⟩
  comparison := A.pullbackComparison hX hY g
  comparison_lift := (A.pullback_properties hX hY g).2.2.2.1

/-- The pullback arrow retains both specified cartesian object arrows and the
canonical cartesian scheme square. Source: Stacks 05WC
(blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
def pullbackArrow (hX : IsFibredInGroupoids X) (hY : IsFibredInGroupoids Y)
    (A : RelativeFiniteHilbert F d) {T' : Over S} (g : T' ⟶ A.T) :
    A.pullback hX hY g ⟶ A where
  g := g
  h := Limits.pullback.fst A.p g
  cartesian := IsPullback.of_hasPullback A.p g
  b := A.pullbackYArrow hY g
  b_lift := (A.pullback_properties hX hY g).2.2.2.2.2.1
  a := A.pullbackXArrow hX g
  a_lift := (A.pullback_properties hX hY g).2.2.2.2.1
  comm := (A.pullback_properties hX hY g).2.2.2.2.2.2

/-- The relative fibre over `y` has objects `ξ` with an arrow `F(ξ) → y`.
Its projected base arrow is the inverse-β convention for the node's triples
`(t, ξ, β : t*y ≅ F(ξ))`. All arrows satisfy the comparison triangle.
Source: criteria.tex, section-lci, equation-relative-map; Stacks 003R and 05WC
(blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
def relativeFiber (y : Y.obj) : BasedCategory (Over S) :=
  BasedCategory.ofFunctor (CostructuredArrow.proj F.toFunctor y ⋙ X.p)

/-- Projection of the explicit relative fibre to the scheme underlying `y`.
Source: criteria.tex, equation-relative-map
(blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
def relativeProjection (y : Y.obj) (z : (relativeFiber (F := F) y).obj) :
    X.p.obj z.left ⟶ Y.p.obj y :=
  eqToHom (F.w_obj z.left).symm ≫ Y.p.map z.hom

/-- A chosen algebraic-space representative of the explicit 2-fibre, over `T`.
The based equivalence retains all automorphisms. Projection compatibility identifies
its structural projection.
Source: criteria.tex, section-lci, equation-relative-map
(blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
structure Representative (T : Over S) (y : Functor.Fiber Y.p T) where
  space : AlgebraicSpace S
  projection : space.obj.obj ⟶ yoneda.obj T
  equivalence : BasedFunctor (discreteModuli space.obj.obj) (relativeFiber (F := F) y.val)
  isEquivalence : equivalence.toFunctor.IsEquivalence
  projection_compatibility : ∀ z : (discreteModuli space.obj.obj).obj,
    eqToHom (equivalence.w_obj z).symm ≫
      relativeProjection y.val (equivalence.obj z) ≫ eqToHom y.property =
        yoneda.preimage (z.hom ≫ projection)

/-- The triple `(p,x,α)` as an actual object of the represented relative fibre.
Source: criteria.tex, equation-relative-map
(blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
def relativePoint (A : RelativeFiniteHilbert F d) :
    (relativeFiber (F := F) A.y.val).obj :=
  CostructuredArrow.mk A.comparison

/-- The inverse image under the chosen representing equivalence, with no arbitrary map.
Source: criteria.tex, equation-relative-map
(blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
def representativePoint (A : RelativeFiniteHilbert F d) (R : Representative (F := F) A.T A.y) :
    (discreteModuli R.space.obj.obj).obj :=
  letI := R.isEquivalence
  R.equivalence.toFunctor.asEquivalence.inverse.obj A.relativePoint

/-- The base isomorphism of the inverse image, obtained from the equivalence counit.
Source: criteria.tex, equation-relative-map
(blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
def representativeBaseIso (A : RelativeFiniteHilbert F d) (R : Representative (F := F) A.T A.y) :
    (A.representativePoint R).left ≅ A.Z :=
  letI := R.isEquivalence
  eqToIso (R.equivalence.w_obj (A.representativePoint R)).symm ≪≫
    (relativeFiber (F := F) A.y.val).p.mapIso
      (R.equivalence.toFunctor.asEquivalence.counitIso.app A.relativePoint) ≪≫
    eqToIso A.x.property

/-- The specified map `u : Z → X_y`, transported along the equivalence counit.
It is determined by `(p,x,α)`, rather than supplied as independent data.
Source: criteria.tex, equation-relative-map
(blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
def inducedMap (A : RelativeFiniteHilbert F d) (R : Representative (F := F) A.T A.y) :
    yoneda.obj A.Z ⟶ R.space.obj.obj :=
  yoneda.map (A.representativeBaseIso R).inv ≫ (A.representativePoint R).hom

/-- The induced map has the specified structural map `p`, hence is a map over T.
Source: criteria.tex, equation-relative-map
(blueprint: def-sfb-relative-finite-hilbert-groupoids).
Proof: apply the representative's projection compatibility to the inverse-image
point. Naturality of the equivalence counit identifies its comparison arrow with
the comparison of A. Apply Y.p to that identity; the lift condition of A.comparison
identifies its base arrow with p. The inverse base isomorphism in inducedMap cancels
the base isomorphism of the counit, leaving yoneda.map p. -/
theorem inducedMap_over (A : RelativeFiniteHilbert F d)
    (R : Representative (F := F) A.T A.y) :
    A.inducedMap R ≫ R.projection = yoneda.map A.p := by
  sorry

/-- Scheme lci: locally a closed immersion into a smooth scheme, with finite
Koszul-regular generators for the closed ideal. The empty sequence is included.
Source: Stacks, More on Morphisms, Tag 069F; Divisors, Tag 063J
(blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
def SchemeLci {U V : Scheme.{u}} (f : U ⟶ V) : Prop :=
  ∀ x : U, ∃ W : U.Opens, x ∈ W ∧
    ∃ (P : Scheme.{u}) (i : W.toScheme ⟶ P) (q : P ⟶ V),
      IsClosedImmersion i ∧ Smooth q ∧ i ≫ q = W.ι ≫ f ∧
        CotangentPresentation.IsKoszulImmersion i

/-- The two-surjective-chart test in the node. The source chart maps to the literal
presheaf fibre product `E ×_B V`; its composite to `V` is represented by `q`.
Source: Stacks, Morphisms of Spaces, Tag 03MJ
(blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
def SpaceProperty (P : MorphismProperty Scheme.{u})
    {E B : (Over S)ᵒᵖ ⥤ Type u} (f : E ⟶ B) : Prop :=
  ∃ (V U : Over S) (b : yoneda.obj V ⟶ B)
    (a : yoneda.obj U ⟶ Limits.pullback f b) (q : U ⟶ V),
      AlgebraicSpace.IsEtale b ∧ AlgebraicSpace.IsSurjective b ∧
      AlgebraicSpace.IsEtale a ∧ AlgebraicSpace.IsSurjective a ∧
      a ≫ Limits.pullback.snd f b = yoneda.map q ∧ P q.left

/-- Flatness and local finite presentation of each represented fibre projection.
The representative is fixed, as requested in the node.
Source: criteria.tex, section-lci
(blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
def FlatLfp (R : ∀ (T : Over S) (y : Functor.Fiber Y.p T), Representative (F := F) T y) :
    Prop :=
  ∀ (T : Over S) (y : Functor.Fiber Y.p T),
    SpaceProperty (fun _ _ f ↦ Flat f) (R T y).projection ∧
      SpaceProperty (fun _ _ f ↦ LocallyOfFinitePresentation f) (R T y).projection

/-- Membership in `L_d`: the canonical induced map is unramified and lci, using
exactly the two-chart interpretation. These are two separate properties.
Source: criteria.tex, section-lci
(blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
def IsLciObject (A : RelativeFiniteHilbert F d) (R : Representative (F := F) A.T A.y) : Prop :=
  SpaceProperty (fun _ _ f ↦ IsUnramified f) (A.inducedMap R) ∧
    SpaceProperty (fun _ _ f ↦ SchemeLci f) (A.inducedMap R)

/-- `L_d(F)` is the full subcategory, under the node's representability, flatness,
and lfp hypotheses. All Hilbert arrows between its objects are retained.
Source: criteria.tex, section-lci
(blueprint: def-sfb-relative-finite-hilbert-groupoids). -/
abbrev Lci (_hX : IsFppfModuliStack X) (_hY : IsFppfModuliStack Y)
    (_hF : IsRepresentableByAlgebraicSpaces F)
    (R : ∀ (T : Over S) (y : Functor.Fiber Y.p T), Representative (F := F) T y)
    (_hflat : FlatLfp R) :=
  ObjectProperty.FullSubcategory (fun A : RelativeFiniteHilbert F d ↦ IsLciObject A (R A.T A.y))

end RelativeFiniteHilbert
end AlgebraicGeometry
