/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import WeilConjectures.Blowup.Affine.ChartAlgebra
public import WeilConjectures.Mathlib.Algebra.Module.Torsion
import Sheaf.RingTheory.PresentationFittingIdeal
import WeilConjectures.Blowup.Affine.Principalization
import Sheaf.Paper.AffineGenericLocalizationIntersection
import Sheaf.RingTheory.AffineGeometricallyIntegralProjective
import Sheaf.RingTheory.AffinePrincipalFittingGenerators

/-!
# Constant generic rank affine module becomes free on blow-up charts

Source: `literature/stacks-project/flat.tex`, Tag 0810, `lemma-helper-blowup-affine-space`
(blueprint: lem-trf-affine-generic-rank-blowup).

The auxiliary declarations construct the prescribed chart algebra and strict-transform
module. No arbitrary map or module is chosen.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace AlgebraicGeometry

/-- Base change of the given algebra to `R[I/a]`.
Source: Stacks Project, Tag 0810, `lemma-helper-blowup-affine-space`
(blueprint: lem-trf-affine-generic-rank-blowup). -/
noncomputable abbrev affineGenericRankChartAlgebra
    (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    (I : Ideal R) (a : R) : Type max u v :=
  B ⊗[R] (AffineBlowup.chartRing I a : Type u)

/-- The pullback module on the chart, with the exceptional-generator power torsion removed.
The extension `C ⊗[B] N` is canonically `N ⊗[R] R[I/a]`, with its full `C`-action.
Source: Stacks Project, Tag 0810, `lemma-helper-blowup-affine-space`
(blueprint: lem-trf-affine-generic-rank-blowup). -/
noncomputable def affineGenericRankChartModule
    (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    (N : ModuleCat.{w} B) (I : Ideal R) (a : R) :
    ModuleCat.{max u v w} (affineGenericRankChartAlgebra R B I a) :=
  let C := affineGenericRankChartAlgebra R B I a
  let P := (ModuleCat.extendScalars (algebraMap B C)).obj N
  ModuleCat.of C (P ⧸ Submodule.powTorsion C P (algebraMap R C a))

/-- A finite module of constant generic rank becomes rank-`r` free on a fibrewise nonempty
principal open of every chart of a blow-up whose centre has vanishing set `V(h)`.
The fibre-generic prime is specified by the kernel of the canonical map `B → p.Fiber B`.
The conclusion uses `g ∉ p'C`, exactly the source's formulation: flatness makes
`C/p'C → C ⊗[R[I/a]] κ(p')` injective, so this is equivalent to nonzero fibre image.

Source: Stacks Project, `flat.tex`, Tag 0810, `lemma-helper-blowup-affine-space`
(blueprint: lem-trf-affine-generic-rank-blowup).

Proof:
1. Choose a finite free surjection onto N. The finite-presentation hypothesis on N_h
   gives finitely many kernel generators after inverting h: lift both presentations and
   use the columns of zA and 1-zu. Clear denominators to obtain a finitely presented M
   surjecting onto N and agreeing with it after inverting h
   [def-sc-finitely-presented-module].
2. Split B into a free R-module using [lem-trf-affine-geometrically-integral-projective].
   Let J be the rth Fitting ideal of M [lem-trf-fitting-ideal-independence-base-change].
   Its finitely many generators have finitely many coordinates; let C be their coordinate
   ideal in R and put I=hC. Multiplication by elements of B, followed by the split maps,
   shows these coordinates generate those of every element of J.
3. Flatness injects B/pB into the domain fibre, so the generic prime is pB. Where h avoids
   p, the rank-r hypothesis gives J localized at pB equal to the unit ideal. A generator
   has a coordinate outside p, so C is not contained in p. This proves V(I)=V(h).
4. On R*=R[I/a], write a=hc. The chart generator is regular
   [lemma-nagata-chart-generator-regular], and IR*=(a)
   [lemma-nagata-chart-extended-ideal-principal]. Cancel h to obtain CR*=(c).
   Flatness preserves regularity of a and c on B*=B tensor R*.
5. Divide all split coordinates by c and apply the retraction to get j_l=cu_l. Cancelling
   c shows the divided coordinates generate the unit ideal. At every base prime one u_l
   avoids its fibre-generic prime. Thus J localized there equals (c).
6. Apply [lem-trf-affine-principal-fitting-generators] to the base-changed M localized at
   this prime. Its quotient by the kernel of c has at most r generators; the power-torsion
   quotient is a further quotient because a=hc. Clearing denominators shows power torsion
   commutes with this localization.
7. Spread r generators using the finite cokernel of the chosen r-generator map. A product
   of annihilators outside the prime gives g outside the prime and a surjection on D(g).
   When r=0 this already proves the conclusion.
8. For r>0 the lower Fitting ideal vanishes on B_h: it vanishes in all fibre-generic stalks,
   and [lem-trf-affine-generic-localization-intersection] detects this vanishing.
9. The chart localization at a equals R_a, where h is invertible with inverse c/a. The lower
   Fitting ideal of the power-torsion quotient therefore vanishes after inverting a. Since
   a is regular on B*, it vanishes before localization. In the r-generator surjection on
   D(g), its minors are the entries of kernel vectors, hence all relations vanish
   [lem-trf-fitting-ideal-independence-base-change]. The surjection is an isomorphism.
10. The power-torsion quotients of M and N are isomorphic: their surjection becomes an
    isomorphism after inverting a, and its kernel is power torsion in a power-torsion-free
    module. Transfer the free open to N. The fibre injection from step 3 identifies avoiding
    the fibre-generic prime with a nonzero fibre image.
-/
theorem exists_affine_generic_rank_blowup
    (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    (N : ModuleCat.{w} B) (hflat : RingHom.Flat (algebraMap R B))
    [Algebra.FinitePresentation R B] [Module.Finite B N] (h : R) (r : ℕ)
    (hfp : Module.FinitePresentation (Localization.Away (algebraMap R B h))
      (LocalizedModule.Away (algebraMap R B h) N))
    (hgeom : ∀ (p : PrimeSpectrum R) (K : Type (max u v w)) [Field K]
      [Algebra (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) K]
      [Algebra R K] [IsScalarTower R
        (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) K],
      IsDomain (B ⊗[R] K))
    (hfree : ∀ (p : PrimeSpectrum R) (q : PrimeSpectrum B),
      q.asIdeal = RingHom.ker
        (Algebra.TensorProduct.includeRight : B →ₐ[R] p.asIdeal.Fiber B).toRingHom →
      h ∉ p.asIdeal → Nonempty (LocalizedModule.AtPrime q.asIdeal N
        ≃ₗ[Localization.AtPrime q.asIdeal] (Fin r → Localization.AtPrime q.asIdeal))) :
    ∃ I : Ideal R, I.FG ∧ I.radical = (Ideal.span {h}).radical ∧
      ∀ (a : R), a ∈ I → ∀ p' : PrimeSpectrum (AffineBlowup.chartRing I a : Type u),
        ∃ g : affineGenericRankChartAlgebra R B I a,
          g ∉ p'.asIdeal.map (Algebra.TensorProduct.includeRight (R := R) (A := B)
            (B := (AffineBlowup.chartRing I a : Type u))).toRingHom ∧
          Nonempty (LocalizedModule.Away g (affineGenericRankChartModule R B N I a)
            ≃ₗ[Localization.Away g] (Fin r → Localization.Away g)) := by
  sorry

end AlgebraicGeometry
