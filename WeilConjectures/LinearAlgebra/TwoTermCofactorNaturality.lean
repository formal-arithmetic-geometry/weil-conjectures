/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecTraceFormula.SurjectiveTwoTermDeterminantCalculus
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.LinearAlgebra.TensorProduct.Associator
import WeilConjectures.TraceFormula.TwoTermPerfectDeterminant
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover
import WeilConjectures.LinearAlgebra.GenericExteriorPowerLocalization
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.RingTheory.CoverModuleExact
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # Naturality of the two-term cofactor map

Source: Stacks Project, duality.tex, Tag 0E9Y, and more-algebra.tex, Tag 0FJM,
with the kernel-first determinant normalization preceding that lemma.
(blueprint: lem-sfb-two-term-cofactor-naturality)

The exterior formula is stated by contraction against every top wedge. On a free
chart contraction against a basis wedge gives exactly the displayed formula in 0E9Y.
Good diagrams characterize both the determinant comparison and the map on cokernels;
they range over every isomorphism in the derived category, not only chain isomorphisms.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open CategoryTheory
open scoped TensorProduct

namespace Module

/-- The actual complex in degrees minus one and zero.
Source: Stacks Project, Tag 0FJM
(blueprint: lem-sfb-two-term-cofactor-naturality). -/
noncomputable def TwoTermComplex.cofactorComplex {R : Type u} [CommRing R]
    (E : TwoTermComplex.{u, v} R) : CochainComplex (ModuleCat.{v} R) ℤ :=
  HomologicalComplex.double E.differential
    (c := ComplexShape.up ℤ) (i₀ := -1) (i₁ := 0) (by decide)

/-- The cokernel used for zeroth cohomology; no injectivity of the differential is imposed.
Source: Stacks Project, Tags 0E9Y and 0FJM
(blueprint: lem-sfb-two-term-cofactor-naturality). -/
abbrev TwoTermComplex.cofactorCokernel {R : Type u} [CommRing R]
    (E : TwoTermComplex.{u, v} R) :=
  E.zero ⧸ LinearMap.range E.differential.hom

/-- The determinant in the dual-first order of the statement, with its specified ranks.
Source: Stacks Project, Tag 0E9Y
(blueprint: lem-sfb-two-term-cofactor-naturality). -/
abbrev TwoTermComplex.cofactorLine {R : Type u} [CommRing R]
    (E : TwoTermComplex.{u, v} R) (c : ℕ) :=
  Dual R (⋀[R]^c E.neg) ⊗[R] (⋀[R]^(c + 1) E.zero)

/-- Evaluate the dual factor against a top wedge, leaving the positive exterior factor.
Source: Stacks Project, Tag 0E9Y, wedge formula
(blueprint: lem-sfb-two-term-cofactor-naturality). -/
noncomputable def TwoTermComplex.cofactorContraction {R : Type u} [CommRing R]
    (E : TwoTermComplex.{u, v} R) (c : ℕ) (x : ⋀[R]^c E.neg) :
    E.cofactorLine c →ₗ[R] (⋀[R]^(c + 1) E.zero) :=
  (TensorProduct.lid R _).toLinearMap.comp
    (TensorProduct.map (Dual.eval R _ x) LinearMap.id)

/-- A cofactor map together with the canonical identifications between the already
recorded socle determinants and the specified top exterior powers. The equations on the
inclusions make the identifications unique. The final equation is the basis-free form
of the local formula, for every top wedge and every lift of a cokernel element.
Source: Stacks Project, Tags 0E9Y and 0FJM
(blueprint: lem-sfb-two-term-cofactor-naturality). -/
structure TwoTermCofactorPresentation {R : Type u} [CommRing R]
    (E : TwoTermComplex.{u, v} R) (c : ℕ) where
  /-- Identification in degree minus one, preserving the exterior-algebra inclusion. -/
  negIso : determinantModule R E.neg ≃ₗ[R] (⋀[R]^c E.neg)
  /-- Inclusion normalization in degree minus one. -/
  neg_formula : ∀ x, (negIso x).val = x.val
  /-- Identification in degree zero, preserving the exterior-algebra inclusion. -/
  zeroIso : determinantModule R E.zero ≃ₗ[R] (⋀[R]^(c + 1) E.zero)
  /-- Inclusion normalization in degree zero. -/
  zero_formula : ∀ x, (zeroIso x).val = x.val
  /-- The linear cofactor map on the actual cokernel. -/
  map : E.cofactorCokernel →ₗ[R] E.cofactorLine c
  /-- Contraction expresses the local wedge formula without choosing a basis or cover. -/
  formula : ∀ (x : ⋀[R]^c E.neg) (v : E.zero),
    (E.cofactorContraction c x (map ((LinearMap.range E.differential.hom).mkQ v))).val =
      ExteriorAlgebra.map E.differential.hom x.val * ExteriorAlgebra.ι R v

/-- Ordinary tensor symmetry transports the recorded target-first determinant to the
specified dual-first exterior formula. In particular no graded sign is introduced.
Source: Stacks Project, Tag 0FJM
(blueprint: lem-sfb-two-term-cofactor-naturality). -/
noncomputable def TwoTermCofactorPresentation.lineIso {R : Type u} [CommRing R]
    {E : TwoTermComplex.{u, v} R} {c : ℕ} (C : TwoTermCofactorPresentation E c) :
    twoTermDeterminant E ≃ₗ[R] E.cofactorLine c :=
  (TensorProduct.congr C.zeroIso C.negIso.symm.dualMap).trans
    (TensorProduct.comm R _ _)

/-- A chain morphism realizes a two-term map when its two nonzero components are those
of that map, under the canonical identifications of the double complex.
Source: Stacks Project, Tag 0FJM
(blueprint: lem-sfb-two-term-cofactor-naturality). -/
def TwoTermMap.IsCofactorRealization {R : Type u} [CommRing R]
    {E F : TwoTermComplex.{u, v} R} (b : TwoTermMap E F)
    (f : E.cofactorComplex ⟶ F.cofactorComplex) : Prop :=
  f.f (-1) ≫ (HomologicalComplex.doubleXIso₀ F.differential
      (by decide : (ComplexShape.up ℤ).Rel (-1) 0)).hom =
    (HomologicalComplex.doubleXIso₀ E.differential
      (by decide : (ComplexShape.up ℤ).Rel (-1) 0)).hom ≫ b.neg ∧
  f.f 0 ≫ (HomologicalComplex.doubleXIso₁ F.differential
      (by decide : (ComplexShape.up ℤ).Rel (-1) 0) (by decide)).hom =
    (HomologicalComplex.doubleXIso₁ E.differential
      (by decide : (ComplexShape.up ℤ).Rel (-1) 0) (by decide)).hom ≫ b.zero

/-- A good diagram for a specified derived isomorphism. Both legs are degreewise
surjective quasi-isomorphisms of finite projective two-term complexes, and their images
have precisely the required derived relation. No representative of the isomorphism is
assumed given. Source: Stacks Project, Tag 0FJM, good diagrams
(blueprint: lem-sfb-two-term-cofactor-naturality). -/
structure TwoTermCofactorGoodDiagram {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (E F : TwoTermComplex.{u, v} R)
    (a : DerivedCategory.Q.obj E.cofactorComplex ≅
      DerivedCategory.Q.obj F.cofactorComplex) where
  /-- The middle good complex, whose ranks need not be constant. -/
  middle : TwoTermComplex.{u, v} R
  /-- Finiteness in degree minus one. -/
  [neg_finite : Module.Finite R middle.neg]
  /-- Projectivity in degree minus one. -/
  [neg_projective : Module.Projective R middle.neg]
  /-- Finiteness in degree zero. -/
  [zero_finite : Module.Finite R middle.zero]
  /-- Projectivity in degree zero. -/
  [zero_projective : Module.Projective R middle.zero]
  /-- The left leg. -/
  left : TwoTermMap middle E
  /-- The right leg. -/
  right : TwoTermMap middle F
  /-- Surjectivity of the left leg in both degrees. -/
  left_surjective : left.DegreewiseSurjective
  /-- The left leg is a quasi-isomorphism. -/
  left_quasiIso : left.QuasiIso
  /-- Surjectivity of the right leg in both degrees. -/
  right_surjective : right.DegreewiseSurjective
  /-- The right leg is a quasi-isomorphism. -/
  right_quasiIso : right.QuasiIso
  /-- The actual left chain map. -/
  leftChain : middle.cofactorComplex ⟶ E.cofactorComplex
  /-- Its components are the left leg. -/
  left_realizes : left.IsCofactorRealization leftChain
  /-- The actual right chain map. -/
  rightChain : middle.cofactorComplex ⟶ F.cofactorComplex
  /-- Its components are the right leg. -/
  right_realizes : right.IsCofactorRealization rightChain
  /-- The diagram represents exactly the prescribed derived isomorphism. -/
  relation : DerivedCategory.Q.map leftChain ≫ a.hom = DerivedCategory.Q.map rightChain

/-- The determinant of a good diagram, transported to the displayed exterior lines.
Both legs use the recorded kernel-first comparison, including differential
trivialization of the acyclic kernel. Source: Stacks Project, Tag 0FJM
(blueprint: lem-sfb-two-term-cofactor-naturality). -/
noncomputable def TwoTermCofactorGoodDiagram.determinant {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    {E F : TwoTermComplex.{u, v} R}
    [Module.Finite R E.neg] [Module.Projective R E.neg]
    [Module.Finite R E.zero] [Module.Projective R E.zero]
    [Module.Finite R F.neg] [Module.Projective R F.neg]
    [Module.Finite R F.zero] [Module.Projective R F.zero]
    {c c' : ℕ} (C : TwoTermCofactorPresentation E c)
    (C' : TwoTermCofactorPresentation F c')
    {a : DerivedCategory.Q.obj E.cofactorComplex ≅
      DerivedCategory.Q.obj F.cofactorComplex} (d : TwoTermCofactorGoodDiagram E F a) :
    E.cofactorLine c ≃ₗ[R] F.cofactorLine c' :=
  letI := d.neg_finite
  letI := d.neg_projective
  letI := d.zero_finite
  letI := d.zero_projective
  ((C.lineIso.symm.trans
    (kernelNormalizedDeterminantMap d.left d.left_surjective d.left_quasiIso).symm).trans
    (kernelNormalizedDeterminantMap d.right d.right_surjective d.right_quasiIso)).trans
      C'.lineIso

/-- Existence and uniqueness of the map specified by the local cofactor formula,
including its canonical top-exterior identifications.
Source: Stacks Project, Tag 0E9Y, displayed formula; Tag 0FJM, determinant convention
(blueprint: lem-sfb-two-term-cofactor-naturality).

Proof: choose a finite standard cover trivializing both finite projective terms.
Exterior powers and tensors localize. A finite projective dual localizes by writing the
module as the image of an idempotent and using the transpose idempotent on the dual.
On each chart define the value of a lift v to be the dual basis wedge tensored with
u(p_1) wedge ... wedge u(p_c) wedge v. Adding u(x) to the lift gives zero by alternation.
Changing basis multiplies the positive wedge by det(g) and the dual generator by its
inverse, so the factors cancel over any ring. The finite-standard-cover exactness theorem
glues these local values uniquely. Uniqueness proves linearity and annihilation of u(P),
hence descent to the cokernel and independence of the cover. The same exterior-basis
calculation identifies the socle determinant with the top exterior power; the inclusion
equations determine the identifications uniquely. Contraction against all top wedges is
exactly the chart formula and determines the map. Empty wedges give c=0; over the zero
ring every module involved is zero and the same uniqueness statements apply. -/
theorem existsUnique_twoTermCofactorPresentation {R : Type u} [CommRing R]
    (E : TwoTermComplex.{u, v} R) (c : ℕ)
    [Module.Finite R E.neg] [Module.Projective R E.neg]
    [Module.Finite R E.zero] [Module.Projective R E.zero]
    (hneg : ∀ p : PrimeSpectrum R, Module.rankAtStalk E.neg p = c)
    (hzero : ∀ p : PrimeSpectrum R, Module.rankAtStalk E.zero p = c + 1) :
    Nonempty (Unique (TwoTermCofactorPresentation E c)) := by
  sorry

/-- The canonical cofactor presentation, selected from a theorem determining all of
its data uniquely, including the map and the exterior-inclusion normalizations.
Source: Stacks Project, Tags 0E9Y and 0FJM
(blueprint: lem-sfb-two-term-cofactor-naturality). -/
noncomputable def TwoTermComplex.cofactorPresentation {R : Type u} [CommRing R]
    (E : TwoTermComplex.{u, v} R) (c : ℕ)
    [Module.Finite R E.neg] [Module.Projective R E.neg]
    [Module.Finite R E.zero] [Module.Projective R E.zero]
    (hneg : ∀ p : PrimeSpectrum R, Module.rankAtStalk E.neg p = c)
    (hzero : ∀ p : PrimeSpectrum R, Module.rankAtStalk E.zero p = c + 1) :
    TwoTermCofactorPresentation E c :=
  (Classical.choice (existsUnique_twoTermCofactorPresentation E c hneg hzero)).default

/-- Cofactor naturality for every derived isomorphism, with both comparison maps
uniquely specified by all good diagrams. The first component is D(a); the second is
H^0(a) under H^0(E)=coker(u). The good-diagram clause supplies representatives rather
than assuming a lift or an arbitrary determinant map.
Source: Stacks Project, Tag 0E9Y and Tag 0FJM, kernel-first construction and good diagrams;
Perfect Complexes, Tags 0FJX and 0FJY
(blueprint: lem-sfb-two-term-cofactor-naturality).

Proof: construct the two cofactor maps by the preceding local formula. For a surjective
quasi-isomorphism the kernel is finite projective and its differential is an isomorphism,
by the recorded surjective determinant calculus. Locally choose kernel-first bases of
both terms and identify the positive kernel basis with the differential of the negative
one. Lift bases of the quotient terms. In the cofactor wedge, every correction from a
kernel-valued change of lift repeats a kernel wedge factor, hence vanishes. The remaining
coefficient is unchanged by the normalized determinant comparison. Empty kernel blocks
and rank-zero negative quotient blocks obey the same computation. Equality on the finite
standard cover detects global equality. For an arbitrary derived isomorphism use bounded
projective K-projectivity and the K-projective Hom bijection to represent it by a chain
quasi-isomorphism f. Choose a finite free surjection pi:F0 -> F.neg and enlarge E by the
contractible summand [F0 --id--> F0]. The left projection b is a surjective quasi-isomorphism;
the right leg t has components f.neg+pi and f.zero+u' pi. Its homotopy to f b is pi on the
contractible summand. Surjectivity in degree zero follows from surjectivity of H^0(f),
and degree minus one from pi. Thus this is a good diagram. The stipulated determinant
functor identifies D(a) with D(t)D(b)^{-1}, independently of the good diagram. The induced
cokernel comparison is characterized by H^0(a)H^0(b)=H^0(t). Apply the surjective case
to b and t and cancel the invertible H^0(b), obtaining the asserted naturality equation.
Every comparison is determined by a good diagram, proving uniqueness. No injectivity,
regularity, reducedness, or restriction on the characteristic has been used. -/
theorem twoTermCofactor_naturality {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (E F : TwoTermComplex.{u, v} R) (c c' : ℕ)
    [Module.Finite R E.neg] [Module.Projective R E.neg]
    [Module.Finite R E.zero] [Module.Projective R E.zero]
    [Module.Finite R F.neg] [Module.Projective R F.neg]
    [Module.Finite R F.zero] [Module.Projective R F.zero]
    (hneg : ∀ p : PrimeSpectrum R, Module.rankAtStalk E.neg p = c)
    (hzero : ∀ p : PrimeSpectrum R, Module.rankAtStalk E.zero p = c + 1)
    (hneg' : ∀ p : PrimeSpectrum R, Module.rankAtStalk F.neg p = c')
    (hzero' : ∀ p : PrimeSpectrum R, Module.rankAtStalk F.zero p = c' + 1)
    (C : TwoTermCofactorPresentation E c) (C' : TwoTermCofactorPresentation F c')
    (a : DerivedCategory.Q.obj E.cofactorComplex ≅
      DerivedCategory.Q.obj F.cofactorComplex) :
    Nonempty (TwoTermCofactorGoodDiagram E F a) ∧
      ∃! p : (E.cofactorLine c ≃ₗ[R] F.cofactorLine c') ×
          (E.cofactorCokernel ≃ₗ[R] F.cofactorCokernel),
        (∀ d : TwoTermCofactorGoodDiagram E F a, p.1 = d.determinant C C') ∧
        (∀ (d : TwoTermCofactorGoodDiagram E F a) (x : d.middle.zero),
          p.2 ((LinearMap.range E.differential.hom).mkQ (d.left.zero.hom x)) =
            (LinearMap.range F.differential.hom).mkQ (d.right.zero.hom x)) ∧
        p.1.toLinearMap.comp C.map = C'.map.comp p.2.toLinearMap := by
  sorry

end Module
