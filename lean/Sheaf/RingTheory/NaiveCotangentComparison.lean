/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q101
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.RingTheory.PresentationsHomotopyEquivalent
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# The natural projection to the naive cotangent complex

Source: Stacks Project, Cotangent Complex, Tags 08RB and 08UP; Algebra, Tags 00S1
and 00S7; Cotangent Complex, Tag 08SF
(blueprint: lem-trf-lci-naive-cotangent-model).

The two-term complex has actual conormal and differential modules. Its comparison
is normalized on standard-resolution generators, including under base-ring changes.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped ChangeOfRings ZeroObject

namespace Algebra.CotangentResolution.Naive

/-- A surjective presentation of a ring map. Source: Stacks, Algebra, Tag 00S0
(blueprint: lem-trf-lci-naive-cotangent-model). -/
structure Presentation (f : Arrow CommRingCat.{u}) where
  ring : CommRingCat.{u}
  base : f.left ⟶ ring
  augmentation : ring ⟶ f.right
  triangle : base ≫ augmentation = f.hom
  surjective : Function.Surjective augmentation

/-- The existing Mathlib extension associated to a presentation, with its actual
ring and surjection. Source: Stacks, Tag 00S0
(blueprint: lem-trf-lci-naive-cotangent-model). -/
def extension {f : Arrow CommRingCat.{u}} (P : Presentation f) :
    letI := f.hom.hom.toAlgebra
    Algebra.Extension.{u} f.left f.right :=
  letI := f.hom.hom.toAlgebra
  letI := P.base.hom.toAlgebra
  Algebra.Extension.ofSurjective
    { toRingHom := P.augmentation.hom
      commutes' := fun a ↦ congrArg (fun k : f.left ⟶ f.right ↦ k a) P.triangle }
    P.surjective

/-- The conormal module `ker(P → B)/ker(P → B)²`, using Mathlib's quotient and
its `B`-action. Source: Stacks, Tags 00S0 and 08UP
(blueprint: lem-trf-lci-naive-cotangent-model). -/
def conormal {f : Arrow CommRingCat.{u}} (P : Presentation f) : ModuleCat.{u} f.right :=
  letI := f.hom.hom.toAlgebra
  ModuleCat.of f.right (extension P).Cotangent

/-- The class of a kernel element in the conormal module. Source: Stacks, Tag 08UP
(blueprint: lem-trf-lci-naive-cotangent-model). -/
def kernelClass {f : Arrow CommRingCat.{u}} (P : Presentation f)
    (h : RingHom.ker P.augmentation.hom) : conormal P :=
  letI := f.hom.hom.toAlgebra
  Algebra.Extension.Cotangent.mk (P := extension P) h

/-- The actual differential module `B ⊗_P Ω¹[P/A]`. Source: Stacks, Tag 08UP
(blueprint: lem-trf-lci-naive-cotangent-model). -/
def differentials {f : Arrow CommRingCat.{u}} (P : Presentation f) :
    ModuleCat.{u} f.right :=
  (ModuleCat.extendScalars P.augmentation.hom).obj (CommRingCat.KaehlerDifferential P.base)

/-- The generating tensor `b ⊗ dx`. Source: Stacks, Tag 08UP
(blueprint: lem-trf-lci-naive-cotangent-model). -/
def tensorGenerator {f : Arrow CommRingCat.{u}} (P : Presentation f)
    (b : f.right) (x : P.ring) : differentials P :=
  b ⊗ₜ[_, P.augmentation.hom] CommRingCat.KaehlerDifferential.d x

/-- The conormal differential `[h] ↦ 1 ⊗ dh`, constructed by Mathlib's existing
cotangent differential. Source: Stacks, Tags 00S0 and 08UP
(blueprint: lem-trf-lci-naive-cotangent-model). -/
def differential {f : Arrow CommRingCat.{u}} (P : Presentation f) :
    conormal P ⟶ differentials P :=
  letI := f.hom.hom.toAlgebra
  ModuleCat.ofHom (extension P).cotangentComplex

/-- The terms in degrees `-1,0`, with zero elsewhere. Source: Stacks, Tag 08UP
(blueprint: lem-trf-lci-naive-cotangent-model). -/
def term {f : Arrow CommRingCat.{u}} (P : Presentation f) (i : ℤ) :
    ModuleCat.{u} f.right :=
  if i = -1 then conormal P else if i = 0 then differentials P else 0

/-- Identification of degree minus one. Source: Stacks, Tag 08UP
(blueprint: lem-trf-lci-naive-cotangent-model).
Proof: evaluate the first branch of `term`. -/
theorem term_neg_one {f : Arrow CommRingCat.{u}} (P : Presentation f) :
    term P (-1) = conormal P := by
  sorry

/-- Identification of degree zero. Source: Stacks, Tag 08UP
(blueprint: lem-trf-lci-naive-cotangent-model).
Proof: evaluate the second branch of `term`, since zero differs from minus one. -/
theorem term_zero {f : Arrow CommRingCat.{u}} (P : Presentation f) :
    term P 0 = differentials P := by
  sorry

/-- The only nonzero differential is the conormal differential. Source: Stacks,
Tag 08UP (blueprint: lem-trf-lci-naive-cotangent-model). -/
def boundary {f : Arrow CommRingCat.{u}} (P : Presentation f) (i : ℤ) :
    term P i ⟶ term P (i + 1) :=
  if h : i = -1 then
    eqToHom (congrArg (term P) h) ≫ eqToHom (term_neg_one P) ≫ differential P ≫
      eqToHom (term_zero P).symm ≫
      eqToHom (congrArg (term P) (congrArg (· + 1) h).symm)
  else 0

/-- The two-term differential squares to zero. Source: Stacks, Tag 08UP
(blueprint: lem-trf-lci-naive-cotangent-model).
Proof: the only potentially nonzero arrow has source degree minus one, so either
factor of every consecutive composite is zero. -/
theorem boundary_comp {f : Arrow CommRingCat.{u}} (P : Presentation f) (i : ℤ) :
    boundary P i ≫ boundary P (i + 1) = 0 := by
  sorry

/-- The actual complex `[J/J² → Ω¹[P/A] ⊗_P B]` in degrees `-1,0`.
Source: Stacks, Tag 08UP (blueprint: lem-trf-lci-naive-cotangent-model). -/
def complex {f : Arrow CommRingCat.{u}} (P : Presentation f) :
    CochainComplex (ModuleCat.{u} f.right) ℤ :=
  CochainComplex.of (term P) (boundary P) (boundary_comp P)

/-- Coordinate identification of degree minus one. Source: Stacks, Tag 08UP
(blueprint: lem-trf-lci-naive-cotangent-model). -/
def conormalIso {f : Arrow CommRingCat.{u}} (P : Presentation f) :
    (complex P).X (-1) ≅ conormal P := eqToIso (term_neg_one P)

/-- Coordinate identification of degree zero. Source: Stacks, Tag 08UP
(blueprint: lem-trf-lci-naive-cotangent-model). -/
def differentialsIso {f : Arrow CommRingCat.{u}} (P : Presentation f) :
    (complex P).X 0 ≅ differentials P := eqToIso (term_zero P)

/-- Localizations of polynomial `A`-algebras on arbitrary sets; localization at
`{1}` includes polynomial algebras themselves. Source: Stacks, Tags 00S1 and 00S7
(blueprint: lem-trf-lci-naive-cotangent-model). -/
def IsLocalizedPolynomial {f : Arrow CommRingCat.{u}} (P : Presentation f) : Prop :=
  ∃ (E : Type u) (a : CommRingCat.of (MvPolynomial E f.left) ⟶ P.ring)
    (W : Submonoid (MvPolynomial E f.left)),
    (∀ x : f.left, a (MvPolynomial.C x) = P.base x) ∧
    (letI := a.hom.toAlgebra; IsLocalization W P.ring)

/-- A compatible map of surjective presentations over a ring square. Source:
Stacks, Algebra, equation-functoriality-NL (blueprint: lem-trf-lci-naive-cotangent-model). -/
structure PresentationMap {f g : Arrow CommRingCat.{u}} (q : f ⟶ g)
    (P : Presentation f) (P' : Presentation g) where
  map : P.ring ⟶ P'.ring
  base : P.base ≫ map = q.left ≫ P'.base
  augmentation : map ≫ P'.augmentation = P.augmentation ≫ q.right

/-- The degree-zero presentation of the specified standard resolution. Source:
Stacks, Tag 08UP (blueprint: lem-trf-lci-naive-cotangent-model). -/
def standardPresentation
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (C : Coherence.{u}) (f : Arrow CommRingCat.{u}) : Presentation f where
  ring := (C.standard f).algebra.obj (op ⦋0⦌)
  base := (C.standard f).base.app (op ⦋0⦌)
  augmentation := (C.standard f).augmentation.app (op ⦋0⦌)
  triangle := (C.standard f).triangle 0
  surjective := (C.standard_resolution f).2.1 0

/-- The semilinear chain map on naive complexes, pinned on conormal classes and
on differential tensors. Source: Stacks, Algebra, equation-functoriality-NL
(blueprint: lem-trf-lci-naive-cotangent-model). -/
structure NaiveMap {f g : Arrow CommRingCat.{u}} {q : f ⟶ g}
    {P : Presentation f} {P' : Presentation g} (h : PresentationMap q P P') where
  map : complex P ⟶ (restrictComplex q.right).obj (complex P')
  conormal_formula : ∀ (x : P.ring) (hx : P.augmentation x = 0)
    (hx' : P'.augmentation (h.map x) = 0),
    (conormalIso P').hom (map.f (-1) ((conormalIso P).inv (kernelClass P ⟨x, hx⟩))) =
      kernelClass P' ⟨h.map x, hx'⟩
  tensor_formula : ∀ (b : f.right) (x : P.ring),
    (differentialsIso P').hom
      (map.f 0 ((differentialsIso P).inv (tensorGenerator P b x))) =
      tensorGenerator P' (q.right b) (h.map x)

/-- The complete comparison assertion, with the canonical projection characterized
on every lift of the standard presentation. Its factorization uses good truncation:
the term in degree minus one is the cokernel of the incoming differential.
Source: Stacks, Tags 08RB and 08UP, and Algebra, Tags 00S1 and 00S7
(blueprint: lem-trf-lci-naive-cotangent-model). -/
structure Comparison
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (C : Coherence.{u}) where
  naiveMap : ∀ {f g : Arrow CommRingCat.{u}} {q : f ⟶ g}
    {P : Presentation f} {P' : Presentation g} (h : PresentationMap q P P'), NaiveMap h
  lift_exists : ∀ {f : Arrow CommRingCat.{u}} (P : Presentation f),
    IsLocalizedPolynomial P → Nonempty (PresentationMap (𝟙 f) (standardPresentation C f) P)
  projection : ∀ {f : Arrow CommRingCat.{u}} (P : Presentation f)
    (_hP : IsLocalizedPolynomial P)
    (_a : PresentationMap (𝟙 f) (standardPresentation C f) P),
    differentialComplex (C.differentials (C.standard f)) ⟶ complex P
  projection_zero : ∀ {f : Arrow CommRingCat.{u}} (P : Presentation f)
    (hP : IsLocalizedPolynomial P)
    (a : PresentationMap (𝟙 f) (standardPresentation C f) P)
    (b : f.right) (x : (C.standard f).algebra.obj (op ⦋0⦌)),
    (differentialsIso P).hom
      ((projection P hP a).f 0
        (complexGenerator (C.differentials (C.standard f)) 0 b x)) =
      tensorGenerator P b (a.map x)
  projection_neg_one : ∀ {f : Arrow CommRingCat.{u}} (P : Presentation f)
    (hP : IsLocalizedPolynomial P)
    (a : PresentationMap (𝟙 f) (standardPresentation C f) P)
    (b : f.right) (x : (C.standard f).algebra.obj (op ⦋1⦌))
    (hx : P.augmentation
      (a.map ((C.standard f).algebra.δ (0 : Fin 2) x -
        (C.standard f).algebra.δ (1 : Fin 2) x)) = 0),
    (conormalIso P).hom
      ((projection P hP a).f (-1)
        (complexGenerator (C.differentials (C.standard f)) 1 b x)) =
      b • kernelClass P
        ⟨a.map ((C.standard f).algebra.δ (0 : Fin 2) x -
          (C.standard f).algebra.δ (1 : Fin 2) x), hx⟩
  comparison : ∀ {f : Arrow CommRingCat.{u}} (P : Presentation f)
    (_hP : IsLocalizedPolynomial P), cotangentComplex C f ⟶ DerivedCategory.Q.obj (complex P)
  comparison_formula : ∀ {f : Arrow CommRingCat.{u}} (P : Presentation f)
    (hP : IsLocalizedPolynomial P)
    (a : PresentationMap (𝟙 f) (standardPresentation C f) P),
    comparison P hP = DerivedCategory.Q.map (projection P hP a)
  truncation : ∀ {f : Arrow CommRingCat.{u}} (P : Presentation f)
    (_hP : IsLocalizedPolynomial P),
    DerivedCategory.Q.obj
      ((differentialComplex (C.differentials (C.standard f))).truncGE (-1)) ≅
      DerivedCategory.Q.obj (complex P)
  factorization : ∀ {f : Arrow CommRingCat.{u}} (P : Presentation f)
    (hP : IsLocalizedPolynomial P),
    DerivedCategory.Q.map
      ((differentialComplex (C.differentials (C.standard f))).πTruncGE (-1)) ≫
      (truncation P hP).hom = comparison P hP
  naturality : ∀ {f g : Arrow CommRingCat.{u}} {q : f ⟶ g}
    {P : Presentation f} {P' : Presentation g}
    (hP : IsLocalizedPolynomial P) (hP' : IsLocalizedPolynomial P')
    (h : PresentationMap q P P'),
    comparison P hP ≫ DerivedCategory.Q.map (naiveMap h).map ≫
      (ModuleCat.restrictScalars q.right.hom).mapDerivedCategoryFactors.inv.app (complex P') =
    cotangentMap C q ≫
      (ModuleCat.restrictScalars q.right.hom).mapDerivedCategory.map (comparison P' hP')

/-- The canonical projection `L[B/A] → [J/J² → Ω¹[P/A] ⊗_P B]` identifies its good
truncation in degrees at least minus one with that two-term complex, naturally
under every compatible square of polynomial or localized polynomial presentations.
Source: Stacks, Cotangent Complex, Tags 08RB and 08UP; Algebra, Tags 00S1 and 00S7;
localization of the cotangent complex: Tag 08SF
(blueprint: lem-trf-lci-naive-cotangent-model).

Proof: (1) Use the standard resolution from lem-trf-cotangent-resolution-coherence.
Its first terms are `R = A[B]`, `Q₁ = A[R]`, `Q₂ = A[Q₁]`. The differential modules
are free on differentials of their polynomial variables, by
lem-weil-pbc-polynomial-ring-kahler-basis-any-variables.
(2) The difference of the two faces, modulo the square of the augmentation ideal,
is a derivation. The universal property of def-weil-pbc-kahler-differentials gives
ρ(b ⊗ df) = b[d₀f-d₁f]. This commutes with the differential and kills the image
from degree minus two, so it and the degree-zero identity form a chain map.
(3) Write t_p for the differential generator in the cokernel of that incoming
map. The degree-two relations give t_Xb = 0, t_(h+k) = t_h+t_k-t_0 for h,k in I,
and t_(hk) = t_0. For r in R they give t_(rh)-t_0 = ε(r)(t_h-t_0).
(4) Thus h ↦ t_h-t_0 factors through a B-linear map I/I² to that cokernel.
(5) It is inverse to ρ: on h in I the composite is h, and the relation for
Y_p-Y_Xεp gives t_p-t_(p-Xεp)+t_0 = 0. Hence the standard comparison induces the
asserted good-truncation isomorphism. All formulas commute with standard ring squares.
(6) A lift R → P exists by choosing a preimage for each b and applying
def-weil-pbc-mv-polynomial-ring. Maps of conormal modules send [h] to [a(h)];
maps of differential tensors send b ⊗ dx to β(b) ⊗ d(a(x)).
(7) For two lifts a,a', their difference modulo J² is a derivation. It defines
a homotopy H with C(a)-C(a') = dH+Hd on both kinds of generators. The same
calculation works for maps into P/J² and under changes of base rings.
(8) For polynomial presentations use lem-weil-pbc-nl-presentations-homotopy-equivalent.
For a localization P = W⁻¹A[E], lift E into R/I², and use
lem-weil-pbc-localization-square-zero-lifting to obtain P → R/I². Its conormal
map and descended universal derivation define the reverse chain map.
(9) Step (7) makes both composites homotopic to the identity. Consequently every
lift induces the same derived comparison, and it is an isomorphism after good
truncation. Compose the standard projection with a lift to obtain the formulas above.
(10) In an arbitrary ring square compare the two composites R → P': their
reductions to B' agree. Step (7) and standard-resolution functoriality give the
naturality equation, with the target restricted along B → B'. No assertion about
cohomology below minus one or finite generation occurs. -/
theorem exists_comparison
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (C : Coherence.{u}) : Nonempty (Comparison C) := by
  sorry

end Algebra.CotangentResolution.Naive
