/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecTraceFormula.SurjectiveTwoTermDeterminantCalculus
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Module.Projective

/-! # Good two-term surjective diagrams

Source: Stacks Project, More on Algebra, Tag 0FJM
(blueprint: lem-trf-good-two-term-surjective-diagrams).

The definitions below use the recorded two-term complex and map encodings.  A good
complex has finite projective terms, and the fibre-product construction is made
termwise by kernels of the two comparison maps.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory

namespace Module

/-- The finite-projective condition on the two terms of a two-term complex.
Source: Stacks Project, More on Algebra, Tag 0FJM
(blueprint: lem-trf-good-two-term-surjective-diagrams). -/
def IsGoodTwoTermComplex {R : Type u} [CommRing R]
    (P : TwoTermComplex.{u, v} R) : Prop :=
  Module.Finite R P.neg ∧ Module.Projective R P.neg ∧
    Module.Finite R P.zero ∧ Module.Projective R P.zero

/-- The contractible-summand complex `[P⁻¹ ⊕ F → P⁰ ⊕ F]`.
Source: Stacks Project, More on Algebra, Tag 0FJM
(blueprint: lem-trf-good-two-term-surjective-diagrams). -/
def TwoTermComplex.contractibleSummand {R : Type u} [CommRing R]
    (P : TwoTermComplex.{u, v} R) (F : Type v) [AddCommGroup F] [Module R F] :
    TwoTermComplex.{u, v} R where
  neg := ModuleCat.of R ((↑P.neg : Type v) × F)
  zero := ModuleCat.of R ((↑P.zero : Type v) × F)
  differential := ModuleCat.ofHom
    ((ModuleCat.Hom.hom P.differential).prodMap (LinearMap.id : F →ₗ[R] F))

/-- Well-definedness of `TwoTermComplex.contractibleProjection`: the projections commute
with the differentials.
Source: Stacks Project, More on Algebra, Tag 0FJM
(blueprint: lem-trf-good-two-term-surjective-diagrams). -/
theorem contractibleProjection_commutes {R : Type u} [CommRing R]
    {P : TwoTermComplex.{u, v} R} (F : Type v) [AddCommGroup F] [Module R F] :
    (ModuleCat.Hom.hom P.differential).comp
        (LinearMap.fst R (↑P.neg : Type v) F) =
      (LinearMap.fst R (↑P.zero : Type v) F).comp
        (ModuleCat.Hom.hom (P.contractibleSummand F).differential) := by
  sorry

/-- The projection `b` from the contractible-summand complex to `P`.
Source: Stacks Project, More on Algebra, Tag 0FJM
(blueprint: lem-trf-good-two-term-surjective-diagrams). -/
def TwoTermComplex.contractibleProjection {R : Type u} [CommRing R]
    {P : TwoTermComplex.{u, v} R} (F : Type v) [AddCommGroup F] [Module R F] :
    TwoTermMap (P.contractibleSummand F) P where
  neg := ModuleCat.ofHom (LinearMap.fst R (↑P.neg : Type v) F)
  zero := ModuleCat.ofHom (LinearMap.fst R (↑P.zero : Type v) F)
  commutes := contractibleProjection_commutes F

/-- Well-definedness of `TwoTermComplex.contractibleComparison`: the chain-map equation.
Source: Stacks Project, More on Algebra, Tag 0FJM
(blueprint: lem-trf-good-two-term-surjective-diagrams). -/
theorem contractibleComparison_commutes {R : Type u} [CommRing R]
    {P Q : TwoTermComplex.{u, v} R} (a : TwoTermMap P Q)
    (F : Type v) [AddCommGroup F] [Module R F]
    (p : F →ₗ[R] (↑Q.neg : Type v)) :
    (ModuleCat.Hom.hom Q.differential).comp
        ((ModuleCat.Hom.hom a.neg).comp
          (LinearMap.fst R (↑P.neg : Type v) F) +
          p.comp (LinearMap.snd R (↑P.neg : Type v) F)) =
      ((ModuleCat.Hom.hom a.zero).comp
          (LinearMap.fst R (↑P.zero : Type v) F) +
          ((ModuleCat.Hom.hom Q.differential).comp p).comp
            (LinearMap.snd R (↑P.zero : Type v) F)).comp
        (ModuleCat.Hom.hom (P.contractibleSummand F).differential) := by
  sorry

/-- The right leg `c` in the explicit good diagram: `c⁻¹(x,f) = a⁻¹(x) + p(f)` and
`c⁰(x,f) = a⁰(x) + d_Q(p(f))`.
Source: Stacks Project, More on Algebra, Tag 0FJM
(blueprint: lem-trf-good-two-term-surjective-diagrams). -/
def TwoTermComplex.contractibleComparison {R : Type u} [CommRing R]
    {P Q : TwoTermComplex.{u, v} R} (a : TwoTermMap P Q)
    (F : Type v) [AddCommGroup F] [Module R F]
    (p : F →ₗ[R] (↑Q.neg : Type v)) :
    TwoTermMap (P.contractibleSummand F) Q where
  neg := ModuleCat.ofHom
    ((ModuleCat.Hom.hom a.neg).comp
      (LinearMap.fst R (↑P.neg : Type v) F) +
      p.comp (LinearMap.snd R (↑P.neg : Type v) F))
  zero := ModuleCat.ofHom
    ((ModuleCat.Hom.hom a.zero).comp
      (LinearMap.fst R (↑P.zero : Type v) F) +
      ((ModuleCat.Hom.hom Q.differential).comp p).comp
        (LinearMap.snd R (↑P.zero : Type v) F))
  commutes := contractibleComparison_commutes a F p

/-- A good diagram consists of degreewise-surjective quasi-isomorphism legs and
the specified chain homotopy between the right leg and the composite.
Source: Stacks Project, More on Algebra, Tag 0FJM
(blueprint: lem-trf-good-two-term-surjective-diagrams). -/
structure GoodTwoTermSurjectiveDiagram {R : Type u} [CommRing R]
    (P Q : TwoTermComplex.{u, v} R) (a : TwoTermMap P Q)
    (M : TwoTermComplex.{u, v} R) where
  middle_good : IsGoodTwoTermComplex M
  left : TwoTermMap M P
  right : TwoTermMap M Q
  left_surjective : left.DegreewiseSurjective
  left_quasiIso : left.QuasiIso
  right_surjective : right.DegreewiseSurjective
  right_quasiIso : right.QuasiIso
  homotopy : ∃ h : (M.zero : Type v) →ₗ[R] (Q.neg : Type v),
    ModuleCat.Hom.hom right.neg -
          ModuleCat.Hom.hom (TwoTermMap.comp a left).neg =
        h.comp (ModuleCat.Hom.hom M.differential) ∧
      ModuleCat.Hom.hom right.zero -
          ModuleCat.Hom.hom (TwoTermMap.comp a left).zero =
        (ModuleCat.Hom.hom Q.differential).comp h

/-- The negative term of the termwise fibre product of two maps to `Q`.
Source: Stacks Project, More on Algebra, Tag 0FJM
(blueprint: lem-trf-good-two-term-surjective-diagrams). -/
def fiberNeg {R : Type u} [CommRing R]
    {M N Q : TwoTermComplex.{u, v} R}
    (u : TwoTermMap M Q) (v : TwoTermMap N Q) :
    Submodule R ((↑M.neg : Type v) × (↑N.neg : Type v)) :=
  LinearMap.ker
    ((ModuleCat.Hom.hom u.neg).comp (LinearMap.fst R _ _) -
      (ModuleCat.Hom.hom v.neg).comp (LinearMap.snd R _ _))

/-- The degree-zero term of the termwise fibre product.
Source: Stacks Project, More on Algebra, Tag 0FJM
(blueprint: lem-trf-good-two-term-surjective-diagrams). -/
def fiberZero {R : Type u} [CommRing R]
    {M N Q : TwoTermComplex.{u, v} R}
    (u : TwoTermMap M Q) (v : TwoTermMap N Q) :
    Submodule R ((↑M.zero : Type v) × (↑N.zero : Type v)) :=
  LinearMap.ker
    ((ModuleCat.Hom.hom u.zero).comp (LinearMap.fst R _ _) -
      (ModuleCat.Hom.hom v.zero).comp (LinearMap.snd R _ _))

/-- Well-definedness of `fiberDifferential`: `d_M × d_N` preserves the fibre product.
Source: Stacks Project, More on Algebra, Tag 0FJM
(blueprint: lem-trf-good-two-term-surjective-diagrams). -/
theorem fiberDifferential_mem {R : Type u} [CommRing R]
    {M N Q : TwoTermComplex.{u, v} R}
    (u : TwoTermMap M Q) (v : TwoTermMap N Q) :
    ∀ x : fiberNeg u v,
      ((ModuleCat.Hom.hom M.differential).prodMap
        (ModuleCat.Hom.hom N.differential)) x ∈ fiberZero u v := by
  sorry

/-- The differential on the termwise fibre product, restricted from `d_M × d_N`.
Source: Stacks Project, More on Algebra, Tag 0FJM
(blueprint: lem-trf-good-two-term-surjective-diagrams). -/
def fiberDifferential {R : Type u} [CommRing R]
    {M N Q : TwoTermComplex.{u, v} R}
    (u : TwoTermMap M Q) (v : TwoTermMap N Q) :
    (fiberNeg u v : Type v) →ₗ[R] (fiberZero u v : Type v) :=
  LinearMap.codRestrict (fiberZero u v)
    (((ModuleCat.Hom.hom M.differential).prodMap
      (ModuleCat.Hom.hom N.differential)).domRestrict (fiberNeg u v))
    (fiberDifferential_mem u v)

/-- The termwise fibre product two-term complex.
Source: Stacks Project, More on Algebra, Tag 0FJM
(blueprint: lem-trf-good-two-term-surjective-diagrams). -/
def fiberProduct {R : Type u} [CommRing R]
    {M N Q : TwoTermComplex.{u, v} R}
    (u : TwoTermMap M Q) (v : TwoTermMap N Q) : TwoTermComplex.{u, v} R where
  neg := ModuleCat.of R (fiberNeg u v : Type v)
  zero := ModuleCat.of R (fiberZero u v : Type v)
  differential := ModuleCat.ofHom (fiberDifferential u v)

/-- Well-definedness of `fiberProjectionLeft`: the chain-map equation.
Source: Stacks Project, More on Algebra, Tag 0FJM
(blueprint: lem-trf-good-two-term-surjective-diagrams). -/
theorem fiberProjectionLeft_commutes {R : Type u} [CommRing R]
    {M N Q : TwoTermComplex.{u, v} R}
    (u : TwoTermMap M Q) (v : TwoTermMap N Q) :
    (ModuleCat.Hom.hom M.differential).comp
        ((LinearMap.fst R (↑M.neg : Type v) (↑N.neg : Type v)).domRestrict
          (fiberNeg u v)) =
      ((LinearMap.fst R (↑M.zero : Type v) (↑N.zero : Type v)).domRestrict
        (fiberZero u v)).comp (fiberDifferential u v) := by
  sorry

/-- The first projection from the termwise fibre product.
Source: Stacks Project, More on Algebra, Tag 0FJM
(blueprint: lem-trf-good-two-term-surjective-diagrams). -/
def fiberProjectionLeft {R : Type u} [CommRing R]
    {M N Q : TwoTermComplex.{u, v} R}
    (u : TwoTermMap M Q) (v : TwoTermMap N Q) :
    TwoTermMap (fiberProduct u v) M where
  neg := ModuleCat.ofHom
    ((LinearMap.fst R (M.neg : Type v) (N.neg : Type v)).domRestrict (fiberNeg u v))
  zero := ModuleCat.ofHom
    ((LinearMap.fst R (M.zero : Type v) (N.zero : Type v)).domRestrict (fiberZero u v))
  commutes := fiberProjectionLeft_commutes u v

/-- Well-definedness of `fiberProjectionRight`: the chain-map equation.
Source: Stacks Project, More on Algebra, Tag 0FJM
(blueprint: lem-trf-good-two-term-surjective-diagrams). -/
theorem fiberProjectionRight_commutes {R : Type u} [CommRing R]
    {M N Q : TwoTermComplex.{u, v} R}
    (u : TwoTermMap M Q) (v : TwoTermMap N Q) :
    (ModuleCat.Hom.hom N.differential).comp
        ((LinearMap.snd R (↑M.neg : Type v) (↑N.neg : Type v)).domRestrict
          (fiberNeg u v)) =
      ((LinearMap.snd R (↑M.zero : Type v) (↑N.zero : Type v)).domRestrict
        (fiberZero u v)).comp (fiberDifferential u v) := by
  sorry

/-- The second projection from the termwise fibre product.
Source: Stacks Project, More on Algebra, Tag 0FJM
(blueprint: lem-trf-good-two-term-surjective-diagrams). -/
def fiberProjectionRight {R : Type u} [CommRing R]
    {M N Q : TwoTermComplex.{u, v} R}
    (u : TwoTermMap M Q) (v : TwoTermMap N Q) :
    TwoTermMap (fiberProduct u v) N where
  neg := ModuleCat.ofHom
    ((LinearMap.snd R (M.neg : Type v) (N.neg : Type v)).domRestrict (fiberNeg u v))
  zero := ModuleCat.ofHom
    ((LinearMap.snd R (M.zero : Type v) (N.zero : Type v)).domRestrict (fiberZero u v))
  commutes := fiberProjectionRight_commutes u v

/-- Good diagrams exist for the explicit contractible-summand construction; termwise
fibre products preserve goodness and both surjective quasi-isomorphism legs; and
fibre-product composition gives a good diagram for a composite.
Source: Stacks Project, More on Algebra, Tag 0FJM
(blueprint: lem-trf-good-two-term-surjective-diagrams).

Proof.
1. Each `Pⁱ × F` is a summand of a finite free module, so `M` is good; `b` is surjective,
   its degree `-1` cycles are `(x,0)` with `d_P x = 0` and `im d_M = im d_P × F`, so
   `b` is a quasi-isomorphism.
2. `c` is a chain map; `h⁰(x,f) = p(f)` gives `c - a b = d h + h d`, so by homotopy
   invariance of cohomology `H(c) = H(a) H(b)` and `c` is a quasi-isomorphism.
3. `c⁻¹` is surjective since `p` is; for `y ∈ Q⁰` write `y = a⁰ x + d_Q z` by
   surjectivity of `H⁰(a)` and lift `z` along `p`, so `c⁰` is surjective.
4. For `u, v`, the fibre product is preserved by `d_M × d_N` and both projections are
   surjective; a section `s` of `v` (projectivity of `Q`) identifies the fibre product
   with `M × ker v`, a summand of a finite free module.
5. The differential `ker v⁻¹ → ker v⁰` is bijective, using that `v` is a
   quasi-isomorphism and there are no degree `-1` boundaries.
6. Hence the left projection is bijective on `H⁻¹` and `H⁰`; symmetrically for the
   right projection.
7. For good diagrams `(b₁₂, c₁₂)`, `(b₂₃, c₂₃)` take the fibre product over `c₁₂, b₂₃`;
   the legs `b₁₂ π₁₂` and `c₂₃ π₂₃` are surjective quasi-isomorphisms and
   `H = h' π₂₃ + a' h π₁₂` is the required homotopy. -/
theorem good_two_term_surjective_diagrams {R : Type u} [CommRing R]
    {P Q : TwoTermComplex.{u, v} R}
    [Module.Finite R P.neg] [Module.Projective R P.neg]
    [Module.Finite R P.zero] [Module.Projective R P.zero]
    [Module.Finite R Q.neg] [Module.Projective R Q.neg]
    [Module.Finite R Q.zero] [Module.Projective R Q.zero]
    (a : TwoTermMap P Q) (ha : a.QuasiIso) :
    (∀ (F : Type v) [AddCommGroup F] [Module R F]
      [Module.Finite R F] [Module.Free R F]
    (p : F →ₗ[R] (↑Q.neg : Type v)), Function.Surjective p →
      ∃ d : GoodTwoTermSurjectiveDiagram P Q a (P.contractibleSummand F),
        d.left = P.contractibleProjection F ∧
          d.right = P.contractibleComparison a F p) ∧
    (∀ {M N : TwoTermComplex.{u, v} R} (u : TwoTermMap M Q)
      (v : TwoTermMap N Q),
      IsGoodTwoTermComplex M → IsGoodTwoTermComplex N →
      u.DegreewiseSurjective → u.QuasiIso →
      v.DegreewiseSurjective → v.QuasiIso →
      IsGoodTwoTermComplex (fiberProduct u v) ∧
        (fiberProjectionLeft u v).DegreewiseSurjective ∧
        (fiberProjectionLeft u v).QuasiIso ∧
        (fiberProjectionRight u v).DegreewiseSurjective ∧
        (fiberProjectionRight u v).QuasiIso) ∧
    (∀ {S : TwoTermComplex.{u, v} R} (a' : TwoTermMap Q S)
      {M N : TwoTermComplex.{u, v} R}
      (d : GoodTwoTermSurjectiveDiagram P Q a M)
      (d' : GoodTwoTermSurjectiveDiagram Q S a' N),
      ∃ e : GoodTwoTermSurjectiveDiagram P S (TwoTermMap.comp a' a)
          (fiberProduct d.right d'.left),
        e.left = TwoTermMap.comp d.left (fiberProjectionLeft d.right d'.left) ∧
          e.right = TwoTermMap.comp d'.right (fiberProjectionRight d.right d'.left)) := by
  sorry

end Module
