/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchlessingerDescentCategory
import WeilConjectures.RingTheory.SemilocalRestrictionLength
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Length

/-! # Minimal Artinian rings of definition

Source: Stacks Project, Formal Deformation Theory, Tag 06T1
(`lemma-smallest-where-descends`) and its preceding paragraphs
(blueprint: lem-sfb-artin-minimal-descent-transport).

The descent category uses literal subalgebras, with commuting triangles inherited
from the over category of the Grothendieck construction. Image transport uses the
actual image algebra and the cocartesian transport arrow, retaining its square.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ArtinDeformation

variable {R k : Type u} [CommRing R] [Field k] [Algebra R k]

/-- The image is the actual range of the restricted algebra map.
Source: Stacks, construction before Tag 06T1
(blueprint: lem-sfb-artin-minimal-descent-transport). -/
def descentImageRing {A B : TestCategory R k} (f : B ⟶ A)
    (S : Subalgebra R (ring B)) : Subalgebra R (ring A) :=
  ((map f).comp S.val).range

/-- The image of a test subalgebra is a test subalgebra.
Source: Stacks, construction before Tag 06T1
(blueprint: lem-sfb-artin-minimal-descent-transport).
Proof: the range restriction is surjective, so its image is Artinian. The
restricted augmentation is onto k, with nilpotent kernel the image of the source
maximal ideal. Elements outside this kernel are units by lifting an inverse modulo
that nilpotent ideal. Thus this is a local ring with the required marked residue. -/
theorem descentImage_valid {A B : TestCategory R k} (f : B ⟶ A)
    (S : Subalgebra R (ring B))
    (h : IsTestAlgebra R k (A := CommAlgCat.of R S) ((residue B).comp S.val)) :
    IsTestAlgebra R k (A := CommAlgCat.of R (descentImageRing f S))
      ((residue A).comp (descentImageRing f S).val) := sorry

/-- Range restriction preserves the specified residue marking.
Source: Stacks, construction before Tag 06T1
(blueprint: lem-sfb-artin-minimal-descent-transport).
Proof: on s in S the left side is the residue of f(s); the test arrow f preserves
residues, so this is the residue of s. Extensionality gives the equality. -/
theorem descentImage_residue {A B : TestCategory R k} (f : B ⟶ A)
    (S : Subalgebra R (ring B)) :
    ((residue A).comp (descentImageRing f S).val).comp
      ((map f).comp S.val).rangeRestrict = (residue B).comp S.val := sorry

/-- The canonical surjection from a subalgebra to its image, as a test arrow.
Source: Stacks, construction before Tag 06T1
(blueprint: lem-sfb-artin-minimal-descent-transport). -/
def descentImageMap {A B : TestCategory R k} (f : B ⟶ A)
    (S : Subalgebra R (ring B))
    (h : IsTestAlgebra R k (A := CommAlgCat.of R S) ((residue B).comp S.val)) :
    subalgebraTest B S h ⟶
      subalgebraTest A (descentImageRing f S) (descentImage_valid f S h) :=
  ObjectProperty.homMk (Over.homMk
    (CommAlgCat.ofHom ((map f).comp S.val).rangeRestrict)
    (congrArg CommAlgCat.ofHom (descentImage_residue f S)))

/-- The factorization through the image commutes as test arrows.
Source: Stacks, construction before Tag 06T1
(blueprint: lem-sfb-artin-minimal-descent-transport).
Proof: both composites send s to f(s), by the definition of range restriction.
Apply extensionality of algebra maps and of arrows in the full over category. -/
theorem descentImage_factor {A B : TestCategory R k} (f : B ⟶ A)
    (S : Subalgebra R (ring B))
    (h : IsTestAlgebra R k (A := CommAlgCat.of R S) ((residue B).comp S.val)) :
    descentImageMap f S h ≫
      subalgebraInclusion A (descentImageRing f S) (descentImage_valid f S h) =
        subalgebraInclusion B S h ≫ f := sorry

/-- Image transport of a descent object, using the two composition constraints
and the given arrow u. Source: Stacks, construction before Tag 06T1
(blueprint: lem-sfb-artin-minimal-descent-transport). -/
def descentImage {F : CofibredGroupoids.{u, v, w} R k} {A B : TestCategory R k}
    {x : fibre F A} {y : fibre F B} (u : totalObject F y ⟶ totalObject F x)
    (D : DescentCategory F y) : DescentCategory F x where
  subring := descentImageRing u.base D.subring
  valid := descentImage_valid u.base D.subring D.valid
  obj := (push F (descentImageMap u.base D.subring D.valid)).obj D.obj
  arrow :=
    (compIso F (descentImageMap u.base D.subring D.valid)
      (subalgebraInclusion A (descentImageRing u.base D.subring)
        (descentImage_valid u.base D.subring D.valid))).hom.app D.obj ≫
      eqToHom (congrArg (fun f ↦ (push F f).obj D.obj)
        (descentImage_factor u.base D.subring D.valid)) ≫
      (compIso F (subalgebraInclusion B D.subring D.valid) u.base).inv.app D.obj ≫
      (push F u.base).map D.arrow ≫ u.fiber

/-- The cocartesian arrow from a descent source to its transported image source.
Source: Stacks, construction before Tag 06T1
(blueprint: lem-sfb-artin-minimal-descent-transport). -/
def descentImageArrow {F : CofibredGroupoids.{u, v, w} R k}
    {A B : TestCategory R k} {x : fibre F A} {y : fibre F B}
    (u : totalObject F y ⟶ totalObject F x) (D : DescentCategory F y) :
    (descentOver D).left ⟶ (descentOver (descentImage u D)).left :=
  { base := descentImageMap u.base D.subring D.valid, fiber := 𝟙 _ }

/-- The defining square of image transport commutes.
Source: Stacks, construction before Tag 06T1
(blueprint: lem-sfb-artin-minimal-descent-transport).
Proof: substitute the explicit image arrow and composition formula in the
Grothendieck category. The inverse composition constraints cancel; naturality
identifies the remaining composite with the transported original arrow followed
by u. The base equality is descentImage_factor. -/
theorem descentImage_square {F : CofibredGroupoids.{u, v, w} R k}
    {A B : TestCategory R k} {x : fibre F A} {y : fibre F B}
    (u : totalObject F y ⟶ totalObject F x) (D : DescentCategory F y) :
    descentImageArrow u D ≫ (descentOver (descentImage u D)).hom =
      (descentOver D).hom ≫ u := sorry

/-- The unique map on image descents induced by a commuting triangle.
Source: Stacks, functor construction before Tag 06T1
(blueprint: lem-sfb-artin-minimal-descent-transport).
Proof: the map between source subalgebras induces the inclusion between their
images. The cocartesian property of the range transport arrow gives a unique
arrow of transported objects over this inclusion. Its composite to x agrees by
the original commuting triangle and descentImage_square. Uniqueness follows
since the transport arrow has identity fibre component and the target
inclusion is injective. -/
theorem descentImage_hom_existsUnique {F : CofibredGroupoids.{u, v, w} R k}
    {A B : TestCategory R k} {x : fibre F A} {y : fibre F B}
    (u : totalObject F y ⟶ totalObject F x) {D E : DescentCategory F y} (h : D ⟶ E) :
    ∃! g : descentImage u D ⟶ descentImage u E,
      descentImageArrow u D ≫ g.hom.left = h.hom.left ≫ descentImageArrow u E := sorry

/-- The map on arrows determined uniquely by its cocartesian square.
Source: Stacks, functor construction before Tag 06T1
(blueprint: lem-sfb-artin-minimal-descent-transport). -/
def descentImageHom {F : CofibredGroupoids.{u, v, w} R k}
    {A B : TestCategory R k} {x : fibre F A} {y : fibre F B}
    (u : totalObject F y ⟶ totalObject F x) {D E : DescentCategory F y} (h : D ⟶ E) :
    descentImage u D ⟶ descentImage u E :=
  Classical.choose (descentImage_hom_existsUnique u h)

/-- Image transport preserves identity arrows.
Source: Stacks, functor construction before Tag 06T1
(blueprint: lem-sfb-artin-minimal-descent-transport).
Proof: the identity satisfies the square defining descentImageHom. Apply the
uniqueness clause of descentImage_hom_existsUnique. -/
theorem descentImageHom_id {F : CofibredGroupoids.{u, v, w} R k}
    {A B : TestCategory R k} {x : fibre F A} {y : fibre F B}
    (u : totalObject F y ⟶ totalObject F x) (D : DescentCategory F y) :
    descentImageHom u (𝟙 D) = 𝟙 (descentImage u D) := sorry

/-- Image transport preserves composite arrows.
Source: Stacks, functor construction before Tag 06T1
(blueprint: lem-sfb-artin-minimal-descent-transport).
Proof: paste the two defining squares. The composite satisfies the square for
h followed by h', so uniqueness gives the asserted equality. -/
theorem descentImageHom_comp {F : CofibredGroupoids.{u, v, w} R k}
    {A B : TestCategory R k} {x : fibre F A} {y : fibre F B}
    (u : totalObject F y ⟶ totalObject F x) {D E G : DescentCategory F y}
    (h : D ⟶ E) (h' : E ⟶ G) :
    descentImageHom u (h ≫ h') = descentImageHom u h ≫ descentImageHom u h' := sorry

/-- The image functor f_* on categories of subrings of definition.
Source: Stacks, construction before Tag 06T1
(blueprint: lem-sfb-artin-minimal-descent-transport). -/
def descentImageFunctor {F : CofibredGroupoids.{u, v, w} R k}
    {A B : TestCategory R k} {x : fibre F A} {y : fibre F B}
    (u : totalObject F y ⟶ totalObject F x) : DescentCategory F y ⥤ DescentCategory F x where
  obj := descentImage u
  map := descentImageHom u
  map_id := descentImageHom_id u
  map_comp := descentImageHom_comp u

/-- Minimal descents exist below every descent, survive arbitrary image transport,
and lift along surjections with the specified commuting square and surjective
subring map. Source: Stacks, Tag 06T1 and the finite-length paragraph before it
(blueprint: lem-sfb-artin-minimal-descent-transport).

Proof:
1. Nakayama (lem-weil-pbc-nakayama-jacobson) shows that the maximal ideal of R
   kills k, so k is finite over the residue field of R.
2. Artinian self-length (lem-weil-pbc-artinian-ring-self-finite-length) and
   semilocal restriction (lem-exc-semilocal-restriction-length) show each test
   algebra has finite R-length. Choose a descent below the given one with least
   length (def-weil-pbc-module-length). A proper incoming subring would have
   smaller length, proving minimality.
3. For a minimal descent over B' and an incoming subring A'' of f(B'), apply (S1)
   to A'' -> f(B') <- B'. The pullback is the inverse-image subring of B'.
   Minimality makes it all of B', and surjectivity onto f(B') forces A'' = f(B').
4. If f is onto, apply (S1) to A' -> A <- B to lift a minimal descent over A'
   to the inverse-image subring in B. Its image is the original descent.
5. Choose a minimal descent below that lift by step 2. Functoriality maps its
   arrow to the original minimal descent; the subrings are therefore equal and
   the arrow is an isomorphism. Hence B' -> A' is onto. Pasting its triangle with
   descentImage_square gives exactly the asserted commuting square. -/
theorem artin_minimal_descent_transport [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R k] (F : CofibredGroupoids.{u, v, w} R k)
    (hS1 : IsSchlessingerOne F) :
    (∀ (A : TestCategory R k) (x : fibre F A) (D : DescentCategory F x),
      ∃ M : DescentCategory F x, IsMinimalDescent M ∧ Nonempty (M ⟶ D)) ∧
    (∀ (A B : TestCategory R k) (x : fibre F A) (y : fibre F B)
      (u : totalObject F y ⟶ totalObject F x) (D : DescentCategory F y),
      IsMinimalDescent D → IsMinimalDescent ((descentImageFunctor u).obj D)) ∧
    (∀ (A B : TestCategory R k) (x : fibre F A) (y : fibre F B)
      (u : totalObject F y ⟶ totalObject F x), Function.Surjective (map u.base) →
      ∀ D : DescentCategory F x, IsMinimalDescent D →
      ∃ E : DescentCategory F y, IsMinimalDescent E ∧
        ∃ e : (descentImageFunctor u).obj E ≅ D,
          Function.Surjective (map (descentImageArrow u E ≫ e.hom.hom.left).base) ∧
            (descentImageArrow u E ≫ e.hom.hom.left) ≫ (descentOver D).hom =
              (descentOver E).hom ≫ u) := sorry

end AlgebraicGeometry.ArtinDeformation
