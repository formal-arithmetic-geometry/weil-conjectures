/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
public import Mathlib.Algebra.Homology.ExactSequence
import WeilConjectures.CategoryTheory.Triangulated.TStructure.HeartAbelianKernelSplitting
import WeilConjectures.CategoryTheory.Triangulated.TExactFixedPairHeartCohomology

/-! # The perverse heart on a smooth curve with condensed coefficients

Source: literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/
sk-lem-wft-curve-heart/_section.md and sk-lem-wft-curve-heart.proof.md.
(blueprint: sk-lem-wft-curve-heart)

The two classes are defined by ordinary module-sheaf cohomology. Finite closed support
is expressed by zero restriction off a finite set of closed points. The geometric
category is exactly the recorded finite-constant-model bounded constructible category.
Weil objects are strict Frobenius pairs in its heart, using the recorded Dctf category;
for these rational coefficients Dctf equals Dbc. No triangulated structure on strict
pairs is used. All support tests and subobjects in the two classes are geometric.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedCurve

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The actual category of modules over the pulled-back condensed coefficient ring.
Source: current blueprint, ambient category in sk-lem-wft-curve-heart
(blueprint: sk-lem-wft-curve-heart). -/
abbrev Modules (C : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology C) Ab.{u + 1}) (condensedRingObj Λ C)

/-- A constructible sheaf is punctual when it vanishes off a finite set of closed points.
This includes the zero sheaf and allows the empty finite set. Zero inverse image on the
complement is the support condition for a sheaf, with no choice of a geometric stalk.
Source: current blueprint sk-lem-wft-curve-heart, opening definition
(blueprint: sk-lem-wft-curve-heart). -/
def IsPunctual (C : Scheme.{u}) (F : Modules Λ C) : Prop :=
  IsConstantModelConstructible Λ C F ∧
    ∃ U : C.Opens, ((U : Set C)ᶜ).Finite ∧
      (∀ x ∈ (U : Set C)ᶜ, IsClosed ({x} : Set C)) ∧
      IsZero ((CondensedRing.upperStar Λ U.ι).obj F)

/-- Absence of a nonzero punctual subsheaf is tested on geometric module monomorphisms,
without imposing a Weil structure on the subobject.
Source: current blueprint sk-lem-wft-curve-heart, lower-class formula
(blueprint: sk-lem-wft-curve-heart). -/
def HasNoPunctualSubsheaf (C : Scheme.{u}) (F : Modules Λ C) : Prop :=
  ∀ (G : Modules Λ C) (i : G ⟶ F), Mono i → IsPunctual Λ C G → IsZero G

/-- The upper curve class at n: cohomology above n vanishes and H^n is punctual.
This is the shift by -n of the displayed class at zero.
Source: current blueprint sk-lem-wft-curve-heart, first displayed class
(blueprint: sk-lem-wft-curve-heart). -/
def upper (C : Scheme.{u}) (n : ℤ) : ObjectProperty (DerivedCategory (Modules Λ C)) :=
  fun K ↦ (∀ a : ℤ, n < a → IsZero ((DerivedCategory.homologyFunctor _ a).obj K)) ∧
    IsPunctual Λ C ((DerivedCategory.homologyFunctor _ n).obj K)

/-- The lower curve class at n: cohomology below n-1 vanishes and H^(n-1) has no
nonzero punctual subsheaf. This is the shift by -n of the displayed class at zero.
Source: current blueprint sk-lem-wft-curve-heart, second displayed class
(blueprint: sk-lem-wft-curve-heart). -/
def lower (C : Scheme.{u}) (n : ℤ) : ObjectProperty (DerivedCategory (Modules Λ C)) :=
  fun K ↦ (∀ a : ℤ, a < n - 1 → IsZero ((DerivedCategory.homologyFunctor _ a).obj K)) ∧
    HasNoPunctualSubsheaf Λ C ((DerivedCategory.homologyFunctor _ (n - 1)).obj K)

/-- The interval [a,b] in the geometric bounded constructible category.
Source: current blueprint sk-lem-wft-curve-heart, notation paragraph
(blueprint: sk-lem-wft-curve-heart). -/
def interval (C : Scheme.{u}) (a b : ℤ) :
    ObjectProperty (ConstantModelBoundedConstructible Λ C) :=
  fun K ↦ upper Λ C b K.obj ∧ lower Λ C a K.obj

/-- The perverse heart, retaining its ambient geometric derived morphisms.
Source: current blueprint sk-lem-wft-curve-heart, heart definition
(blueprint: sk-lem-wft-curve-heart). -/
def heart (C : Scheme.{u}) : ObjectProperty (DerivedCategory (Modules Λ C)) :=
  constantModelBoundedConstructible Λ C ⊓ (upper Λ C 0 ⊓ lower Λ C 0)

/-- Perverse cohomology H^n, once the t-structure with the specified classes is supplied.
It is H^0(K[n]) with values in the actual Mathlib heart, using the existing cohomology
functor of the recorded t-structure dependency.
Source: current blueprint sk-lem-wft-curve-heart, notation paragraph
(blueprint: sk-lem-wft-curve-heart). -/
abbrev cohomology (C : Scheme.{u})
    [(constantModelBoundedConstructible Λ C).IsTriangulated]
    (t : TStructure (ConstantModelBoundedConstructible Λ C)) (n : ℤ) :=
  shiftFunctor (ConstantModelBoundedConstructible Λ C) n ⋙ t.homology₀

/-- The geometric clauses of the node, with the inherited triangulated structure.
The existential instance is the proposition that the recorded full subcategory is
triangulated, not a choice of unrelated triangles. The aisle and coaisle formulas at
all indices determine the t-structure. Basic objects use ordinary, underived j_*.
Source: current blueprint sk-lem-wft-curve-heart, geometric assertions
(blueprint: sk-lem-wft-curve-heart). -/
def GeometricAssertions (C : Scheme.{u}) : Prop :=
  (Exists fun [_hTri : (constantModelBoundedConstructible Λ C).IsTriangulated] ↦
    ∃ t : TStructure (ConstantModelBoundedConstructible Λ C),
      (∀ (K : ConstantModelBoundedConstructible Λ C) (n : ℤ),
        t.le n K ↔ upper Λ C n K.obj) ∧
      (∀ (K : ConstantModelBoundedConstructible Λ C) (n : ℤ),
        t.ge n K ↔ lower Λ C n K.obj) ∧
      t.bounded = ⊤ ∧
      (∀ K : ConstantModelBoundedConstructible Λ C,
        t.heart K ↔ upper Λ C 0 K.obj ∧ lower Λ C 0 K.obj)) ∧
  Nonempty (Abelian (heart Λ C).FullSubcategory) ∧
  (∀ K : ConstantModelBoundedConstructible Λ C,
    heart Λ C K.obj ↔
      (∀ a : ℤ, a ≠ -1 → a ≠ 0 →
        IsZero ((DerivedCategory.homologyFunctor _ a).obj K.obj)) ∧
      IsPunctual Λ C ((DerivedCategory.homologyFunctor _ 0).obj K.obj) ∧
      HasNoPunctualSubsheaf Λ C ((DerivedCategory.homologyFunctor _ (-1)).obj K.obj)) ∧
  (∀ F : Modules Λ C, IsPunctual Λ C F →
    heart Λ C ((DerivedCategory.singleFunctor _ 0).obj F)) ∧
  (∀ (U : Scheme.{u}) (j : U ⟶ C), IsOpenImmersion j → DenseRange j →
    ∀ M : Modules Λ U, IsLisseCoefficientModule Λ M →
      heart Λ C (((DerivedCategory.singleFunctor _ 0).obj
        ((CondensedRing.lowerStar Λ j).obj M))⟦(1 : ℤ)⟧))

/-- Perverse Weil sheaves are the full subcategory of the recorded strict Weil pairs
whose underlying geometric complex lies in the perverse heart.
Source: current blueprint sk-lem-wft-curve-heart, Weil definition paragraph
(blueprint: sk-lem-wft-curve-heart). -/
abbrev WeilHeart {C : Scheme.{u}} (g : C ≅ C) :=
  ObjectProperty.FullSubcategory (fun K : CondensedRing.StrictWeil.Complex Λ g ↦
    upper Λ C 0 K.carrier.obj ∧ lower Λ C 0 K.carrier.obj)

/-- The canonical forgetful functor retains the carrier and its geometric derived arrow.
Dctf membership already includes bounded constructibility; its extra finite-Tor proof
is simply forgotten. Source: current blueprint sk-lem-wft-curve-heart, final paragraph
(blueprint: sk-lem-wft-curve-heart). -/
def forget {C : Scheme.{u}} (g : C ≅ C) :
    WeilHeart Λ g ⥤ (heart Λ C).FullSubcategory where
  obj K := ⟨K.obj.carrier.obj, K.obj.carrier.property.1, K.property⟩
  map f := ObjectProperty.homMk f.hom.hom.f.hom

/-- Abelianness and exactness of the canonical functor, including reflection of exactness
for arbitrary two composable arrows. The endpoint clauses spell out reflection of
short exact sequences as well. Abelian structures are asserted, not assumed.
Source: current blueprint sk-lem-wft-curve-heart, final paragraph
(blueprint: sk-lem-wft-curve-heart). -/
def WeilAssertions {C : Scheme.{u}} (g : C ≅ C) : Prop :=
  Exists fun [_hGeom : Abelian (heart Λ C).FullSubcategory] ↦
    Exists fun [_hWeil : Abelian (WeilHeart Λ g)] ↦
      PreservesFiniteLimits (forget Λ g) ∧ PreservesFiniteColimits (forget Λ g) ∧
      (∀ (A B D : WeilHeart Λ g) (f : A ⟶ B) (h : B ⟶ D),
        (ComposableArrows.mk₂ f h).Exact ↔
          (ComposableArrows.mk₂ ((forget Λ g).map f) ((forget Λ g).map h)).Exact) ∧
      (∀ (A B : WeilHeart Λ g) (f : A ⟶ B), Mono f ↔ Mono ((forget Λ g).map f)) ∧
      (∀ (A B : WeilHeart Λ g) (f : A ⟶ B), Epi f ↔ Epi ((forget Λ g).map f))

/-- The geometric perverse t-structure and all its stated heart descriptions and examples.
Source: current blueprint sk-lem-wft-curve-heart, geometric assertions
(blueprint: sk-lem-wft-curve-heart).

Proof: The restriction-calculus and punctual-kernel lemmas supply the inherited
triangulated bounded constructible category, its standard truncations, and the largest
punctual subobject F_p = ker(F → j_*j^*F), with punctual-free quotient. Shift stability
is H^a(K[1]) = H^(a+1)(K). For upper A and lower B in perverse degree at least one,
standard truncation adjunctions identify Hom(A,B) with Hom(H^0 A,H^0 B). The image is
punctual and embeds in a punctual-free sheaf, so is zero. For K set K' = τ^{≤0}K and
Q = H^0(K)/F_p. The fibre of K' → Q[0] is upper; the octahedron with K' → K gives
A → K → B with H^{<0}B = 0 and H^0B = Q, so B is perverse ≥1. All cones remain
constructible. Standard amplitude [a,b] implies perverse amplitude [a,b+1], proving
boundedness. The general heart theorem gives abelianness, and intersecting the two
formulas gives exactly the displayed degree -1,0 description. A punctual F[0] has
zero H^-1. The punctual-kernel lemma says ordinary j_*M is constructible and has no
punctual subobject, so its shift by one belongs to the heart. These are steps 1--5 of
the DAG proof, using lem-per-condensed-curve-restriction-calculus,
lem-per-condensed-curve-punctual-kernel, sk-p-real-integral,
lem-weil-heart-short-exact-triangles, def-weil-triangulated-category,
def-weil-t-structure, and prop-weil-heart-abelian. -/
theorem curve_perverse_heart (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [PerfectField k] (_hEll : IsUnit (ell : k))
    (C : Over (Spec (.of k))) [Smooth C.hom] [QuasiCompact C.hom]
    [IsSeparated C.hom] (_hPure : C.left.IsPureDimension 1) :
    GeometricAssertions (Profinite.padicAlgClRingObj ell) C.left := by
  sorry

/-- The perverse Weil heart is abelian and its canonical forgetful functor is exact
and reflects exactness, on the geometric fibre of any smooth curve over the fixed
finite field. Source: current blueprint sk-lem-wft-curve-heart, Weil assertions
(blueprint: sk-lem-wft-curve-heart).

Proof: Use the preceding geometric construction. Geometric Frobenius inverse image
and its inverse are exact equivalences and commute with ordinary cohomology. They
reindex finite closed sets and preserve monomorphisms, hence preserve punctual
sheaves and the absence of punctual subobjects. They preserve both perverse classes.
Apply lem-zl-texact-fixed-pair-heart-cohomology to this t-exact autoequivalence, with
both geometric categories equal and the identity comparison. Kernels and cokernels
are created in the geometric heart with their induced invertible Frobenius maps.
This gives abelianness and exactness. Faithful forgetting detects zero objects, so
vanishing geometric homology implies vanishing equivariant homology, and it also
reflects the endpoint mono and epi conditions. These are steps 6--7 of the DAG proof;
the Frobenius and the strict-pair morphisms are exactly sk-def-sf-weil-complexes. -/
theorem curve_perverse_weil_heart (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ D.p)
    (C₀ : Over (Spec (.of D.k₀))) [Smooth C₀.hom] [QuasiCompact C₀.hom]
    [IsSeparated C₀.hom] (_hPure : C₀.left.IsPureDimension 1) :
    WeilAssertions (Profinite.padicAlgClRingObj ell)
      (CondensedRing.StrictWeil.modelFrobenius D C₀) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedCurve
