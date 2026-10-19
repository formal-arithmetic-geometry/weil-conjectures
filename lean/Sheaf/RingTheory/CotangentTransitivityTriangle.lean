/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Adjunction.Additive
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Kaehler.Polynomial
import Sheaf.CategoryTheory.DerivedColimitBar

/-!
# The cotangent transitivity triangle

Source: Stacks Project, Cotangent Complex, Tags 08QL and 08QX,
section-triangle (blueprint: lem-trf-cotangent-transitivity-triangle).

The standard differential complex is bounded above with free terms. Consequently
its termwise scalar extension is a concrete representative of its derived scalar
extension, without a flatness assumption on the target ring. All maps below are
constructed from the recorded standard-resolution maps and tensor adjunction.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Pretriangulated

namespace Algebra.CotangentResolution

variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]

/-- The recorded standard differential complex. Source: Stacks, Tag 08PN
(blueprint: lem-trf-cotangent-transitivity-triangle). -/
def standardComplex (C : Coherence.{u}) (f : Arrow CommRingCat.{u}) :=
  differentialComplex (C.differentials (C.standard f))

/-- The canonical semilinear map of the recorded standard complexes.
Source: Stacks, Tag 08QL (blueprint: lem-trf-cotangent-transitivity-triangle). -/
def standardComplexMap (C : Coherence.{u}) {f f' : Arrow CommRingCat.{u}} (q : f ⟶ f') :=
  (C.differentialMap (C.standardMap q)).map

/-- Tensor extension of complexes and its ordinary tensor/restriction adjunction.
Source: Stacks, Tag 08QX (blueprint: lem-trf-cotangent-transitivity-triangle). -/
def tensorComplexAdj {P B : CommRingCat.{u}} (g : P ⟶ B) :=
  letI := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} g.hom).left_adjoint_additive
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} g.hom).mapHomologicalComplex (.up ℤ)

/-- The standard bounded-above free model of `L[P/A] ⊗ᴸ[P] B`.
Its terms are the actual tensors with `B`, not an unspecified derived object.
Source: Stacks, Tags 08PN and 08QX
(blueprint: lem-trf-cotangent-transitivity-triangle). -/
def transitivityFirstComplex (C : Coherence.{u}) {A P B : CommRingCat.{u}}
    (f : A ⟶ P) (g : P ⟶ B) :=
  ((ModuleCat.extendScalars g.hom).mapHomologicalComplex (.up ℤ)).obj
    (standardComplex C (Arrow.mk f))

/-- The first functoriality arrow, transposed under tensor adjunction.
Source: Stacks, Tags 08QL and 08QX
(blueprint: lem-trf-cotangent-transitivity-triangle). -/
def transitivityFirstMap (C : Coherence.{u}) {A P B : CommRingCat.{u}}
    (f : A ⟶ P) (g : P ⟶ B) :
    DerivedCategory.Q.obj (transitivityFirstComplex C f g) ⟶
      cotangentComplex C (Arrow.mk (f ≫ g)) :=
  DerivedCategory.Q.map
    (((tensorComplexAdj g).homEquiv _ _).symm
      (standardComplexMap C (Arrow.homMk' (𝟙 A) g (Category.id_comp (f ≫ g)))))

/-- The second functoriality arrow, changing the base from `A` to `P`.
Source: Stacks, Tags 08QL and 08QX
(blueprint: lem-trf-cotangent-transitivity-triangle). -/
def transitivitySecondMap (C : Coherence.{u}) {A P B : CommRingCat.{u}}
    (f : A ⟶ P) (g : P ⟶ B) :
    cotangentComplex C (Arrow.mk (f ≫ g)) ⟶ cotangentComplex C (Arrow.mk g) :=
  DerivedCategory.Q.map
    (standardComplexMap C (Arrow.homMk' f (𝟙 B) (Category.comp_id (f ≫ g)).symm) ≫
      (NatIso.mapHomologicalComplex (ModuleCat.restrictScalarsId B) (.up ℤ)).hom.app
        (standardComplex C (Arrow.mk g)) ≫
      (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} B) (.up ℤ)).hom.app
        (standardComplex C (Arrow.mk g)))

/-- Scalar extension of a semilinear standard map in a diagram of triples.
This is the tensor map `b₀ ⊗ x ↦ b(b₀) ⊗ p_*(x)` degree by degree.
Source: Stacks, Tags 08QL and 08QX
(blueprint: lem-trf-cotangent-transitivity-triangle). -/
def transitivityFirstComplexMap (C : Coherence.{u})
    {A P B A' P' B' : CommRingCat.{u}}
    (f : A ⟶ P) (g : P ⟶ B) (f' : A' ⟶ P') (g' : P' ⟶ B')
    (a : A ⟶ A') (p : P ⟶ P') (b : B ⟶ B')
    (s : CommSq f a p f') (t : CommSq g p b g') :
    transitivityFirstComplex C f g ⟶
      (restrictComplex b).obj (transitivityFirstComplex C f' g') :=
  ((tensorComplexAdj g).homEquiv _ _).symm
    (standardComplexMap C (Arrow.homMk' a p s.w.symm) ≫
      (restrictComplex p).map ((tensorComplexAdj g').unit.app
        (standardComplex C (Arrow.mk f'))) ≫
      (NatIso.mapHomologicalComplex
        (ModuleCat.restrictScalarsComp' p.hom g'.hom (g ≫ b).hom
          (congrArg CommRingCat.Hom.hom t.w)) (.up ℤ)).inv.app
        (transitivityFirstComplex C f' g') ≫
      (NatIso.mapHomologicalComplex
        (ModuleCat.restrictScalarsComp g.hom b.hom) (.up ℤ)).hom.app
        (transitivityFirstComplex C f' g'))

/-- The induced standard map on the first derived-tensor terms, with target
restricted to the source coefficient ring. Source: Stacks, Tags 08QL and 08QX
(blueprint: lem-trf-cotangent-transitivity-triangle). -/
def transitivityFirstBaseChange (C : Coherence.{u})
    {A P B A' P' B' : CommRingCat.{u}}
    (f : A ⟶ P) (g : P ⟶ B) (f' : A' ⟶ P') (g' : P' ⟶ B')
    (a : A ⟶ A') (p : P ⟶ P') (b : B ⟶ B')
    (s : CommSq f a p f') (t : CommSq g p b g') :
    DerivedCategory.Q.obj (transitivityFirstComplex C f g) ⟶
      (ModuleCat.restrictScalars b.hom).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (transitivityFirstComplex C f' g')) :=
  DerivedCategory.Q.map (transitivityFirstComplexMap C f g f' g' a p b s t) ≫
    (ModuleCat.restrictScalars b.hom).mapDerivedCategoryFactors.inv.app
      (transitivityFirstComplex C f' g')

/-- The triangle with its two prescribed standard arrows and a boundary.
Source: Stacks, equation-triangle, Tag 08QX
(blueprint: lem-trf-cotangent-transitivity-triangle). -/
def transitivityTriangle (C : Coherence.{u}) {A P B : CommRingCat.{u}}
    (f : A ⟶ P) (g : P ⟶ B)
    (δ : cotangentComplex C (Arrow.mk g) ⟶
      (DerivedCategory.Q.obj (transitivityFirstComplex C f g))⟦(1 : ℤ)⟧) :=
  Triangle.mk (transitivityFirstMap C f g) (transitivitySecondMap C f g) δ

/-- The canonical transitivity triangles for all triples of commutative rings,
with the standard first two arrows, are distinguished and natural under every
commutative diagram of triples. A morphism of triangles asserts all three squares,
including the shifted first-term square with the boundary. The first term uses
its bounded-above free standard model, so it is precisely the derived tensor.
Source: Stacks, Tags 08QL and 08QX, proposition-triangle and equation-triangle
(blueprint: lem-trf-cotangent-transitivity-triangle).

Proof:
1. Use the four identity-cover polynomial-presentation sites and the three
projection functors of lem-trf-cotangent-lower-shriek. The differential sheaves
of lem-trf-cotangent-sheaf-model have values Ω[P/A] ⊗ C, Ω[Q/A] ⊗ C,
and Ω[Q/P] ⊗ C, the last by the canonical differential base-change isomorphism
of lem-weil-pbc-kahler-differentials-base-change (08QU).
2. Choose polynomial coordinates for P over A and Q over P. By
lem-weil-pbc-polynomial-ring-kahler-basis-any-variables the two differential maps
are inclusion and projection of the two sets of differential basis vectors.
After tensoring with C they are still split exact, without flatness of C.
The maps are natural on differential generators, although their splittings
need not be. This gives the canonical short exact sequence of sheaves.
3. Apply lem-trf-derived-colimit-bar: its bar complexes form a degreewise short
exact sequence. The boundary of lem-weil-pbc-complex-ses-triangle gives its
canonical distinguished triangle and is natural in maps of these sequences.
4. The lower-shriek comparison and the sheaf-model comparison identify the
second and third objects with the standard cotangent complexes. The first
presheaf has free values by the polynomial differential basis. Apply the flat
presheaf clause of lem-trf-derived-colimit-change-rings, then the standard
comparison, to identify its derived colimit with the derived scalar extension.
The standard differential complex is bounded above and free termwise, so its
termwise tensor is the displayed model transitivityFirstComplex.
5. For the first arrow use the index functor P ↦ (P → C). The maps P → Q give
a natural transformation of index functors. The prism homotopy clause of the
bar lemma identifies its differential map with standard functoriality; on
generators it is dp ⊗ r ⊗ c ↦ dp ⊗ rc. Tensor adjunction is exactly
transitivityFirstMap.
6. For the second arrow use Q ↦ Q ⊗_A B and the quotient to Q ⊗_P B.
The bar prism identity and sheaf-model compatibility identify its generator
formula dq ⊗ c ↦ d(q ⊗ 1) ⊗ c with transitivitySecondMap.
7. For an arbitrary diagram of triples, base-change polynomial presentations
by A → A', using the tensor-associativity identification on the third site.
The three semilinear maps on differential generators commute with both arrows.
They induce a morphism of short exact bar complexes. Naturality of the
short-exact-sequence boundary supplies the third, shifted square.
8. The lower-shriek bar maps and standard comparisons commute with these maps
on every bar generator. Transporting the boundary gives the stated morphism
of triangles; its first component is transitivityFirstBaseChange and the
others are cotangentMap. The same generator formulas preserve identities and
composition. Relabel A → B → C as A → P → B. -/
theorem exists_transitivity_triangles (C : Coherence.{u}) :
    ∃ δ : ∀ (A P B : CommRingCat.{u}) (f : A ⟶ P) (g : P ⟶ B),
        cotangentComplex C (Arrow.mk g) ⟶
          (DerivedCategory.Q.obj (transitivityFirstComplex C f g))⟦(1 : ℤ)⟧,
      (∀ (A P B : CommRingCat.{u}) (f : A ⟶ P) (g : P ⟶ B),
        transitivityTriangle C f g (δ A P B f g) ∈
          distTriang (DerivedCategory (ModuleCat.{u} B))) ∧
      (∀ (A P B A' P' B' : CommRingCat.{u})
          (f : A ⟶ P) (g : P ⟶ B) (f' : A' ⟶ P') (g' : P' ⟶ B')
          (a : A ⟶ A') (p : P ⟶ P') (b : B ⟶ B')
          (s : CommSq f a p f') (t : CommSq g p b g'),
        ∃ φ : transitivityTriangle C f g (δ A P B f g) ⟶
            (ModuleCat.restrictScalars b.hom).mapDerivedCategory.mapTriangle.obj
              (transitivityTriangle C f' g' (δ A' P' B' f' g')),
          φ.hom₁ = transitivityFirstBaseChange C f g f' g' a p b s t ∧
          φ.hom₂ = cotangentMap C (Arrow.homMk' a b (s.horiz_comp t).w.symm) ∧
          φ.hom₃ = cotangentMap C (Arrow.homMk' p b t.w.symm)) := by
  sorry

end Algebra.CotangentResolution
