/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.RingTheory.SquareZeroAlgebraExtension
public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Sheaf.RingTheory.NaiveCotangentComparison
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Algebra.Homology.TwoTermDerivedHomBoundary
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-! # Classification of square-zero algebra extensions

Source: Stacks Project, Deformation Theory, Tags 0GPT, 0GPU, 0GPV and 0GPW;
Cotangent Complex, Tag 08RB
(blueprint: lem-sfb-ring-square-zero-extension-classification).

Surjectivity and equality precisely on isomorphic extensions express the bijection
on isomorphism classes without choosing representatives or a small quotient.
The presentation formula fixes the canonical class, including its sign.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open Algebra.CotangentResolution

namespace Algebra.SquareZero

variable [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]

/-- Derived `Ext¹` of the full standard cotangent complex, with the module in degree zero.
Source: Stacks, Tags 0GPT and 08RB
(blueprint: lem-sfb-ring-square-zero-extension-classification). -/
abbrev E1 (C : Coherence.{u}) (a : Arrow CommRingCat.{u}) (M : ModuleCat.{u} a.right) :=
  cotangentComplex C a ⟶ ((DerivedCategory.singleFunctor (ModuleCat a.right) 0).obj M)⟦(1 : ℤ)⟧

/-- The coefficient map is postcomposition with the shifted single-complex map.
Source: Stacks, Tag 0GPV
(blueprint: lem-sfb-ring-square-zero-extension-classification). -/
def coefficientMap (C : Coherence.{u}) {a : Arrow CommRingCat.{u}}
    {M N : ModuleCat.{u} a.right} (u : M ⟶ N) (ξ : E1 C a M) : E1 C a N :=
  ξ ≫ ((DerivedCategory.singleFunctor (ModuleCat a.right) 0).map u)⟦(1 : ℤ)⟧'

/-- Restriction followed by precomposition with the specified standard cotangent map.
The final two maps are the canonical shift and single-object comparisons for restriction.
Source: Stacks, Tag 0GPV
(blueprint: lem-sfb-ring-square-zero-extension-classification). -/
def pullbackClass (C : Coherence.{u}) {a b : Arrow CommRingCat.{u}} (q : a ⟶ b)
    {N : ModuleCat.{u} b.right} (ξ : E1 C b N) :
    E1 C a ((ModuleCat.restrictScalars q.right.hom).obj N) :=
  cotangentMap C q ≫ (ModuleCat.restrictScalars q.right.hom).mapDerivedCategory.map ξ ≫
    ((ModuleCat.restrictScalars q.right.hom).mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app
      ((DerivedCategory.singleFunctor (ModuleCat b.right) 0).obj N) ≫
    (((ModuleCat.restrictScalars q.right.hom).mapDerivedCategorySingleFunctor 0).hom.app
      N)⟦(1 : ℤ)⟧'

/-- The commutative ring square associated to a map over the fixed base ring.
Source: Stacks, Tag 0GPV
(blueprint: lem-sfb-ring-square-zero-extension-classification). -/
def baseSquare {R A B : CommRingCat.{u}} (a : R ⟶ A) (b : R ⟶ B)
    (f : A ⟶ B) (hf : a ≫ f = b) : Arrow.mk a ⟶ Arrow.mk b :=
  Arrow.homMk (𝟙 R) f ((Category.id_comp b).trans hf.symm)

/-- The canonical class formula of 0GPU: choose a polynomial lift, take its map on
`J/J²`, form the positive projection to `M[1]`, and precompose the normalized full
cotangent comparison. Every displayed datum is constrained by its actual formula.
Source: Stacks, Tags 0GPU and 08RB
(blueprint: lem-sfb-ring-square-zero-extension-classification). -/
def HasPresentationFormula (C : Coherence.{u}) (D : Naive.Comparison C)
    (cl : ∀ (a : Arrow CommRingCat.{u}) (M : ModuleCat.{u} a.right),
      Extension a M → E1 C a M) : Prop :=
  ∀ (a : Arrow CommRingCat.{u}) (M : ModuleCat.{u} a.right) (E : Extension a M),
    ∃ (P : Naive.Presentation a) (hP : Naive.IsLocalizedPolynomial P)
      (t : P.ring ⟶ E.ring) (h : Naive.conormal P ⟶ M)
      (q : Naive.complex P ⟶ (CochainComplex.singleFunctor (ModuleCat a.right) (-1)).obj M),
      P.base ≫ t = E.base ∧ t ≫ E.projection = P.augmentation ∧
      (∀ j : RingHom.ker P.augmentation.hom,
        t j = E.injection (h (Naive.kernelClass P j))) ∧
      (Naive.conormalIso P).inv ≫ q.f (-1) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1) M).hom = h ∧
      cl a M E = D.comparison P hP ≫ DerivedCategory.Q.map q ≫
        ((DerivedCategory.singleFunctors (ModuleCat a.right)).shiftIso
          1 (-1) 0 (by decide)).inv.app M

/-- The complete classification assertion, including existence of coefficient pushouts
and Baer sums, so their compatibility statements are not conditional on missing objects.
Source: Stacks, Tags 0GPT, 0GPU, 0GPV and 0GPW
(blueprint: lem-sfb-ring-square-zero-extension-classification). -/
def Classification (C : Coherence.{u}) (D : Naive.Comparison C)
    (cl : ∀ (a : Arrow CommRingCat.{u}) (M : ModuleCat.{u} a.right),
      Extension a M → E1 C a M) : Prop :=
  HasPresentationFormula C D cl ∧
  (∀ (a : Arrow CommRingCat.{u}) (M : ModuleCat.{u} a.right),
    Function.Surjective (cl a M) ∧
    (∀ E F : Extension a M, cl a M E = cl a M F ↔ IsIsomorphic E F) ∧
    (∃ E : Extension a M, IsSplit E) ∧
    (∀ E : Extension a M, IsSplit E → cl a M E = 0)) ∧
  (∀ (R A : CommRingCat.{u}) (a : R ⟶ A) (M N : ModuleCat.{u} A)
    (u : M ⟶ N) (E : Extension (Arrow.mk a) M),
    (∃ F : Extension (Arrow.mk a) N, IsPushout u E F) ∧
    ∀ F : Extension (Arrow.mk a) N, IsPushout u E F →
      cl (Arrow.mk a) N F = coefficientMap C u (cl (Arrow.mk a) M E)) ∧
  (∀ (R A : CommRingCat.{u}) (a : R ⟶ A) (M : ModuleCat.{u} A)
    (E F : Extension (Arrow.mk a) M),
    (∃ G : Extension (Arrow.mk a) M, IsBaerSum E F G) ∧
    ∀ G : Extension (Arrow.mk a) M, IsBaerSum E F G →
      cl (Arrow.mk a) M G = cl (Arrow.mk a) M E + cl (Arrow.mk a) M F) ∧
  (∀ (R A B : CommRingCat.{u}) (a : R ⟶ A) (b : R ⟶ B)
    (f : A ⟶ B) (hf : a ≫ f = b) (M : ModuleCat.{u} A) (N : ModuleCat.{u} B)
    (u : M ⟶ (ModuleCat.restrictScalars f.hom).obj N)
    (E : Extension (Arrow.mk a) M) (F : Extension (Arrow.mk b) N),
    Nonempty (Hom E F f u.hom.toAddMonoidHom) ↔
      coefficientMap C u (cl (Arrow.mk a) M E) =
        pullbackClass C (baseSquare a b f hf)
          (cl (Arrow.mk b) N F))

/-- The actual coefficient and cotangent class maps preserve identity and composition.
Base maps here are over one fixed ring; `HEq` only compares the canonically identical
iterated restriction module with restriction along the composite.
Source: Stacks, Tag 0GPW
(blueprint: lem-sfb-ring-square-zero-extension-classification). -/
def ClassMapsFunctorial (C : Coherence.{u}) : Prop :=
  (∀ (a : Arrow CommRingCat.{u}) (M : ModuleCat.{u} a.right) (ξ : E1 C a M),
    coefficientMap C (𝟙 M) ξ = ξ) ∧
  (∀ (a : Arrow CommRingCat.{u}) (M N P : ModuleCat.{u} a.right)
    (u : M ⟶ N) (v : N ⟶ P) (ξ : E1 C a M),
    coefficientMap C (u ≫ v) ξ = coefficientMap C v (coefficientMap C u ξ)) ∧
  (∀ (a : Arrow CommRingCat.{u}) (M : ModuleCat.{u} a.right) (ξ : E1 C a M),
    HEq (pullbackClass C (𝟙 a) ξ) ξ) ∧
  (∀ (R A B T : CommRingCat.{u}) (a : R ⟶ A) (b : R ⟶ B) (c : R ⟶ T)
    (f : A ⟶ B) (g : B ⟶ T) (hf : a ≫ f = b) (hg : b ≫ g = c)
    (N : ModuleCat.{u} T) (ξ : E1 C (Arrow.mk c) N),
    HEq (pullbackClass C
      (baseSquare a c (f ≫ g) ((Category.assoc a f g).symm.trans
        ((congrArg (fun k : R ⟶ B ↦ k ≫ g) hf).trans hg))) ξ)
      (pullbackClass C (baseSquare a b f hf)
        (pullbackClass C (baseSquare b c g hg) ξ))) ∧
  (∀ (a b : Arrow CommRingCat.{u}) (q : a ⟶ b) (N N' : ModuleCat.{u} b.right)
    (v : N ⟶ N') (ξ : E1 C b N),
    pullbackClass C q (coefficientMap C v ξ) =
      coefficientMap C ((ModuleCat.restrictScalars q.right.hom).map v)
        (pullbackClass C q ξ))

/-- Square-zero extensions are canonically classified by derived Ext of the full
standard cotangent complex, with the stated coefficient, Baer-sum and map compatibilities.
Source: Stacks, Tags 0GPT--0GPW and 08RB
(blueprint: lem-sfb-ring-square-zero-extension-classification).

Proof: (1) Use the standard polynomial presentation and identify its differential
module with the free module on the variables (Kahler differentials).
(2) The comparison of lem-trf-lci-naive-cotangent-model identifies the good truncation
in degrees at least -1. Orthogonality and the truncation triangle show precomposition
induces a bijection on Hom into M[1]; lower cohomology of L need not vanish.
(3) Apply lem-sfb-two-term-derived-hom-boundary and projective Ext vanishing to identify
this Hom group with the cokernel of Hom(V,M) → Hom(J/J²,M).
(4) Lift the polynomial generators to an extension. Its restriction to J defines h.
Changing lifts changes h by a derivation, hence by a map through V; the boundary kills
that difference, so the displayed presentation formula is independent of all choices.
(5) For h form (P ⊕ M)/{(j,-h([j]))}. The antidiagonal is an ideal; the kernel is M,
its square is zero and its quotient is A. This proves surjectivity.
(6) Evaluation plus kernel inclusion identifies every extension with this quotient.
Equal classes differ by a derivation; adjust the polynomial lifts by that derivation
to obtain an isomorphism fixing M and A. The split extension has zero conormal map.
(7) The quotient (E ⊕ N)/{(i(m),-u(m))} is the coefficient pushout and its conormal
map is uh, proving coefficient naturality.
(8) Paired lifts in E ×_A F have conormal map (h_E,h_F). Pushout by addition gives
h_E+h_F, and the boundary is additive, proving the Baer identity.
(9) For f:A → B, the fibre product A ×_B F has the conormal map obtained by
precomposing with x_a ↦ x_f(a). Comparison naturality identifies this with restriction
followed by the specified full cotangent map, giving f*cl(F).
(10) A compatible E → F is equivalent to an isomorphism from its coefficient pushout
to that fibre product: [(e,n)] ↦ (p(e),H(e)+i_F(n)). The inverse implication uses the
canonical maps out of E and into F. Injectivity of classification gives exactly the iff.
(11) Standard polynomial maps preserve identities and composition strictly. Coherence
and canonical localization, shift and single-object comparisons transfer these equations
to class maps; coefficient functoriality follows from postcomposition. The presentation
formula forces uniqueness. All constructions allow arbitrary rings and modules. -/
theorem exists_unique_extension_classification (C : Coherence.{u}) (D : Naive.Comparison C) :
    (∃! cl : ∀ (a : Arrow CommRingCat.{u}) (M : ModuleCat.{u} a.right),
      Extension a M → E1 C a M, Classification C D cl) ∧ ClassMapsFunctorial C := by
  sorry

end Algebra.SquareZero
