/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q90
-/
module

public import Sheaf.CategoryTheory.SheafPolynomialCotangentComparison
public import Sheaf.RingTheory.NaiveCotangentComparison
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Mathlib.Topology.Sheaves.CommRingCat
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Topology.InverseImageStalk
import WeilConjectures.Topology.InverseImageModule
import Mathlib.Topology.Sheaves.Functors

/-!
# Stalk comparison for the naive cotangent complex

Source: Stacks Project, Modules, Tag 0D09 (`lemma-stalk-NL`), via
`lemma-pullback-NL`; `section-netherlander` and
`equation-commutative-square-sheaves`
(blueprint: lem-sfb-naive-cotangent-stalk-comparison).

The target is the existing actual two-term conormal complex. Comparisons retain
all section maps, their germ formulas, and naturality under squares of ring sheaves.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Algebra.CotangentResolution

namespace TopCat.NaiveCotangent

/-- The canonical polynomial presentation on all elements of the target ring.
Source: Stacks, Modules, section-netherlander and Algebra, Tag 00S0
(blueprint: lem-sfb-naive-cotangent-stalk-comparison). -/
def presentation (f : Arrow CommRingCat.{u}) : Naive.Presentation f where
  ring := CommRingCat.of (MvPolynomial f.right f.left)
  base := CommRingCat.ofHom MvPolynomial.C
  augmentation := CommRingCat.ofHom (MvPolynomial.eval₂Hom f.hom.hom id)
  triangle := by ext a; simp
  surjective b := ⟨MvPolynomial.X b, by simp⟩

/-- The polynomial map of a ring square: coefficients follow its left side and
`X b` goes to `X (beta b)`. Source: Stacks, equation-commutative-square-sheaves
(blueprint: lem-sfb-naive-cotangent-stalk-comparison). -/
def presentationMap {f g : Arrow CommRingCat.{u}} (q : f ⟶ g) :
    Naive.PresentationMap q (presentation f) (presentation g) where
  map := CommRingCat.ofHom (MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp q.left.hom) (fun b ↦ MvPolynomial.X (q.right b)))
  base := by ext a; simp [presentation]
  augmentation := by
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [presentation, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
        RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      exact congrArg (fun k : f.left ⟶ g.right ↦ k a) q.w
    · intro b
      simp [presentation]

/-- The section ring arrow. Source: Stacks, Modules, section-netherlander
(blueprint: lem-sfb-naive-cotangent-stalk-comparison). -/
def sectionArrow {T : TopCat.{u}} {A B : T.Sheaf CommRingCat.{u}} (f : A ⟶ B)
    (W : Opens T) : Arrow CommRingCat.{u} := Arrow.mk (f.hom.app (op W))

/-- The stalk ring arrow, using the recorded categorical stalks.
Source: Stacks, Tag 0D09 (blueprint: lem-sfb-naive-cotangent-stalk-comparison). -/
def stalkArrow {T : TopCat.{u}} {A B : T.Sheaf CommRingCat.{u}} (f : A ⟶ B) (t : T) :
    Arrow CommRingCat.{u} :=
  Arrow.mk ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} t).map f.hom)

/-- The two germ homomorphisms as a ring square. Source: Stacks, Tag 0D09
(blueprint: lem-sfb-naive-cotangent-stalk-comparison). -/
def germs {T : TopCat.{u}} {A B : T.Sheaf CommRingCat.{u}} (f : A ⟶ B)
    (W : Opens T) (t : T) (ht : t ∈ W) : sectionArrow f W ⟶ stalkArrow f t :=
  Arrow.homMk' (TopCat.Presheaf.germ A.obj W t ht) (TopCat.Presheaf.germ B.obj W t ht)
    (TopCat.Presheaf.stalkFunctor_map_germ W t ht f.hom)

/-- The sectionwise polynomial included into the sheaf polynomial algebra.
Source: Stacks, section-netherlander
(blueprint: lem-sfb-naive-cotangent-stalk-comparison). -/
def polynomialSection {T : TopCat.{u}} {A B : T.Sheaf CommRingCat.{u}}
    (f : A ⟶ B) (W : Opens T) :
    (presentation (sectionArrow f W)).ring ⟶
      (CategoryTheory.SheafPolynomialCotangent.polynomialSheaf A
        (CategoryTheory.SheafPolynomialCotangent.sets B)).obj.obj (op W) :=
  (toSheafify (Opens.grothendieckTopology T)
    (CategoryTheory.SheafPolynomialCotangent.polynomials A
      (CategoryTheory.SheafPolynomialCotangent.sets B))).app (op W)

/-- Package the given ring sheaf as a ringed space, to use the recorded module
stalk functor. Source: Stacks, Tag 0D09
(blueprint: lem-sfb-naive-cotangent-stalk-comparison). -/
def ringedSpace {T : TopCat.{u}} (B : T.Sheaf CommRingCat.{u}) :
    AlgebraicGeometry.RingedSpace.{u} where
  carrier := T
  presheaf := B.obj
  IsSheaf := B.property

/-- The actual termwise module stalk, with Mathlib's commutative stalk-ring action.
Source: Stacks, Tag 0D09 (blueprint: lem-sfb-naive-cotangent-stalk-comparison). -/
def stalkComplex {T : TopCat.{u}} {A B : T.Sheaf CommRingCat.{u}} {f : A ⟶ B}
    (K : CategoryTheory.SheafPolynomialCotangent.Model
      (CategoryTheory.SheafPolynomialCotangent.canonical f)) (t : T) :=
  ((AlgebraicGeometry.RingedSpace.moduleStalkFunctor (ringedSpace B) t).mapHomologicalComplex
    (.up ℤ)).obj K.complex

/-- A section of a module complex sent to its germ in the recorded module stalk.
Source: Stacks, Tag 0D09 (blueprint: lem-sfb-naive-cotangent-stalk-comparison). -/
def germ {T : TopCat.{u}} {A B : T.Sheaf CommRingCat.{u}} {f : A ⟶ B}
    (K : CategoryTheory.SheafPolynomialCotangent.Model
      (CategoryTheory.SheafPolynomialCotangent.canonical f))
    (W : Opens T) (t : T) (ht : t ∈ W) (i : ℤ)
    (x : (K.complex.X i).val.obj (op W)) : (stalkComplex K t).X i :=
  TopCat.Presheaf.germ (K.complex.X i).val.presheaf W t ht x

/-- The sectionwise evaluation of the given standard sheaf complex.
Source: Stacks, section-netherlander
(blueprint: lem-sfb-naive-cotangent-stalk-comparison). -/
def sectionComplex {T : TopCat.{u}} {A B : T.Sheaf CommRingCat.{u}} {f : A ⟶ B}
    (K : CategoryTheory.SheafPolynomialCotangent.Model
      (CategoryTheory.SheafPolynomialCotangent.canonical f)) (W : Opens T) :=
  ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (op W)).mapHomologicalComplex
    (.up ℤ)).obj K.complex

/-- Forgetting module structure on the given standard sheaf complex.
Source: Stacks, equation-commutative-square-sheaves
(blueprint: lem-sfb-naive-cotangent-stalk-comparison). -/
def additiveComplex {T : TopCat.{u}} {A B : T.Sheaf CommRingCat.{u}} {f : A ⟶ B}
    (K : CategoryTheory.SheafPolynomialCotangent.Model
      (CategoryTheory.SheafPolynomialCotangent.canonical f)) :=
  ((SheafOfModules.toSheaf _).mapHomologicalComplex (.up ℤ)).obj K.complex

/-- All canonical maps and stalk comparisons, normalized on sectionwise
polynomials, conormal classes and differential tensors. `ringMaps` uses the existing
`NaiveMap` interface, so its two formulas specify coefficients, variable renaming,
kernel classes and universal differential tensors under arbitrary ring squares.
The last field is the naturality square, evaluated on every germ of every degree;
every stalk element is such a germ. Coefficient changes are restriction of scalars,
equivalently the adjoint maps from extension of source coefficients.
Source: Stacks, Tag 0D09 and equation-commutative-square-sheaves
(blueprint: lem-sfb-naive-cotangent-stalk-comparison). -/
structure Comparison (T : TopCat.{u})
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)] where
  ringMaps : ∀ {f g : Arrow CommRingCat.{u}} (q : f ⟶ g),
    Naive.NaiveMap (presentationMap q)
  sectionKernel : ∀ {A B : T.Sheaf CommRingCat.{u}} (f : A ⟶ B) (W : Opens T),
    RingHom.ker (presentation (sectionArrow f W)).augmentation.hom →
      (CategoryTheory.SheafPolynomialCotangent.kernelIdeal
        (CategoryTheory.SheafPolynomialCotangent.canonical f)).sections W
  sectionKernel_formula : ∀ {A B : T.Sheaf CommRingCat.{u}} (f : A ⟶ B)
    (W : Opens T) (h : RingHom.ker (presentation (sectionArrow f W)).augmentation.hom),
    (sectionKernel f W h).val = polynomialSection f W h
  sections : ∀ {A B : T.Sheaf CommRingCat.{u}} (f : A ⟶ B)
    (K : CategoryTheory.SheafPolynomialCotangent.Model
      (CategoryTheory.SheafPolynomialCotangent.canonical f)) (W : Opens T),
    Naive.complex (presentation (sectionArrow f W)) ⟶ sectionComplex K W
  sections_neg_one : ∀ {A B : T.Sheaf CommRingCat.{u}} (f : A ⟶ B)
    (K : CategoryTheory.SheafPolynomialCotangent.Model
      (CategoryTheory.SheafPolynomialCotangent.canonical f)) (W : Opens T)
    (h : RingHom.ker (presentation (sectionArrow f W)).augmentation.hom),
    (sections f K W).f (-1)
      ((Naive.conormalIso _).inv (Naive.kernelClass _ h)) =
        K.quotient.val.app (op W) (sectionKernel f W h)
  sections_zero : ∀ {A B : T.Sheaf CommRingCat.{u}} (f : A ⟶ B)
    (K : CategoryTheory.SheafPolynomialCotangent.Model
      (CategoryTheory.SheafPolynomialCotangent.canonical f)) (W : Opens T)
    (b : B.obj.obj (op W)) (p : (presentation (sectionArrow f W)).ring),
    K.degreeZero.hom.val.app (op W)
      ((sections f K W).f 0 ((Naive.differentialsIso _).inv
        (Naive.tensorGenerator _ b p))) =
      CategoryTheory.SheafPolynomialCotangent.tensorD
        (CategoryTheory.SheafPolynomialCotangent.canonical f) (op W) b (polynomialSection f W p)
  stalks : ∀ {A B : T.Sheaf CommRingCat.{u}} (f : A ⟶ B)
    (K : CategoryTheory.SheafPolynomialCotangent.Model
      (CategoryTheory.SheafPolynomialCotangent.canonical f)) (t : T),
    stalkComplex K t ⟶ Naive.complex (presentation (stalkArrow f t))
  derived_iso : ∀ {A B : T.Sheaf CommRingCat.{u}} (f : A ⟶ B)
    (K : CategoryTheory.SheafPolynomialCotangent.Model
      (CategoryTheory.SheafPolynomialCotangent.canonical f)) (t : T),
    IsIso (DerivedCategory.Q.map (stalks f K t))
  germ_formula : ∀ {A B : T.Sheaf CommRingCat.{u}} (f : A ⟶ B)
    (K : CategoryTheory.SheafPolynomialCotangent.Model
      (CategoryTheory.SheafPolynomialCotangent.canonical f))
    (W : Opens T) (t : T) (ht : t ∈ W) (i : ℤ)
    (x : (Naive.complex (presentation (sectionArrow f W))).X i),
    (stalks f K t).f i (germ K W t ht i ((sections f K W).f i x)) =
      (ringMaps (germs f W t ht)).map.f i x
  sheafMaps : ∀ {f g : Arrow (T.Sheaf CommRingCat.{u})} (_q : f ⟶ g)
    (K : CategoryTheory.SheafPolynomialCotangent.Model
      (CategoryTheory.SheafPolynomialCotangent.canonical f.hom))
    (L : CategoryTheory.SheafPolynomialCotangent.Model
      (CategoryTheory.SheafPolynomialCotangent.canonical g.hom)),
    additiveComplex K ⟶ additiveComplex L
  sheafMaps_semilinear : ∀ {f g : Arrow (T.Sheaf CommRingCat.{u})} (q : f ⟶ g)
    (K : CategoryTheory.SheafPolynomialCotangent.Model
      (CategoryTheory.SheafPolynomialCotangent.canonical f.hom))
    (L : CategoryTheory.SheafPolynomialCotangent.Model
      (CategoryTheory.SheafPolynomialCotangent.canonical g.hom))
    (W : Opens T) (i : ℤ) (b : f.right.obj.obj (op W))
    (x : (K.complex.X i).val.obj (op W)),
    ((sheafMaps q K L).f i).hom.app (op W) (b • x) =
      @SMul.smul (g.right.obj.obj (op W)) ((L.complex.X i).val.obj (op W))
        inferInstance (q.right.hom.app (op W) b)
        (((sheafMaps q K L).f i).hom.app (op W) x)
  sheafMaps_sections : ∀ {f g : Arrow (T.Sheaf CommRingCat.{u})} (q : f ⟶ g)
    (K : CategoryTheory.SheafPolynomialCotangent.Model
      (CategoryTheory.SheafPolynomialCotangent.canonical f.hom))
    (L : CategoryTheory.SheafPolynomialCotangent.Model
      (CategoryTheory.SheafPolynomialCotangent.canonical g.hom))
    (W : Opens T) (i : ℤ)
    (x : (Naive.complex (presentation (sectionArrow f.hom W))).X i),
    ((sheafMaps q K L).f i).hom.app (op W) ((sections f.hom K W).f i x) =
      (sections g.hom L W).f i
        ((ringMaps (((sheafToPresheaf _ CommRingCat ⋙
          (CategoryTheory.evaluation _ _).obj (op W)).mapArrow.map q))).map.f i x)
  naturality : ∀ {f g : Arrow (T.Sheaf CommRingCat.{u})} (q : f ⟶ g)
    (K : CategoryTheory.SheafPolynomialCotangent.Model
      (CategoryTheory.SheafPolynomialCotangent.canonical f.hom))
    (L : CategoryTheory.SheafPolynomialCotangent.Model
      (CategoryTheory.SheafPolynomialCotangent.canonical g.hom))
    (W : Opens T) (t : T) (ht : t ∈ W) (i : ℤ)
    (x : (K.complex.X i).val.obj (op W)),
    (ringMaps ((TopCat.Sheaf.forget CommRingCat T ⋙
      TopCat.Presheaf.stalkFunctor CommRingCat t).mapArrow.map q)).map.f i
        ((stalks f.hom K t).f i (germ K W t ht i x)) =
      (stalks g.hom L t).f i (germ L W t ht i
        (((sheafMaps q K L).f i).hom.app (op W) x))

/-- The naive cotangent complex commutes with stalks, by the canonical map,
compatibly with every section-to-germ square and every square of ring sheaves.
Source: Stacks Project, Modules, Tag 0D09 (`lemma-stalk-NL`), via
`lemma-pullback-NL`; section-netherlander, equation-commutative-square-sheaves
(blueprint: lem-sfb-naive-cotangent-stalk-comparison).

Proof, following the four DAG steps:
1. Inverse image to the one-point subspace identifies ring and additive sheaves
   with their stalks. The inverse-image unit is the germ map, and its module action
   is multiplication of representatives on a common neighborhood
   (inverse-image finite limits and colimits, inverse-image stalk comparison, and
   the recorded inverse-image module and module-stalk constructions).
2. Apply the general topos naive-cotangent pullback comparison to that geometric
   morphism. Its polynomial, kernel, conormal, differential and tensor
   identifications give the actual canonical chain map. Localization gives
   `derived_iso`; no flatness assumption or derived scalar extension is used.
3. The unit sends coefficients to germs and `X b` to `X (germ b)`. It preserves
   evaluation, hence kernel classes, and the universal derivation sends `dp` to
   `d(p_t)`. Tensor functoriality sends `b ⊗ dp` to `b_t ⊗ d(p_t)`. These are
   `sectionKernel_formula`, `sections_neg_one`, `sections_zero` and `germ_formula`.
4. For every square of ring sheaves the two composites agree on polynomial
   coefficients and variables, and therefore on kernel classes and differential
   tensors. Germs represent all stalk elements and these generators locally span
   both terms, giving `sheafMaps_sections` and `naturality` in all degrees.
   There is no separation or finiteness condition on the space.
-/
theorem naive_cotangent_stalk_comparison (T : TopCat.{u})
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)] :
    Nonempty (Comparison T) := by
  sorry

end TopCat.NaiveCotangent
