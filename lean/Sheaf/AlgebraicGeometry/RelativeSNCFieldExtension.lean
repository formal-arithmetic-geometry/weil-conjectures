/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Sheaf.AlgebraicGeometry.SmoothStrictNormalCrossingsDivisor
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import Mathlib.Algebra.Algebra.Defs
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.DimensionLocallyAlgebraic
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Relative smooth strict normal crossings pairs after field extension

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose X, definition after
Theorem 2.1, p.149, and 2.3 Step 2, pp.150--151; Stacks 01VB, 02FY, 056T, 02OO
(blueprint: lem-sfb-relative-snc-field-extension).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Arbitrary extension of the ground field preserves a smooth finite-type SNC pair.
The given integral components split into finite disjoint clopen integral pieces. Their
union is the pulled-back divisor, and their inverse images in that divisor are exactly
its irreducible components. All intersections are smooth of the expected pure codimension;
choosing two pieces over the same original component gives the empty subscheme.

Source: ILO Expose X, definition after Theorem 2.1, p.149, and 2.3 Step 2, pp.150--151;
Stacks 01VB, 02FY, 056T, 02OO (blueprint: lem-sfb-relative-snc-field-extension).

Proof:
1. Every original component intersection is smooth by the SNC definition and finite type
   as a closed subscheme of X. Smooth and finite-type base change preserve these properties.
   Finite type over a field is Noetherian. Smooth geometric normality and the normal
   decomposition give finite disjoint clopen integral components after extension.
2. On Spec R the scalar extension is Spec (R tensor_F L), faithfully flat over Spec R.
   Flat pullback preserves effective Cartier ideals: a local nonzerodivisor stays one.
3. Tensor the kernel sequence for R -> direct sum R/I_a with L. Flat tensor exactness gives
   (intersection I_a)R_L = intersection (I_a R_L). Each factor quotient is reduced by step 1,
   so the injection of the divisor quotient into their direct sum proves reducedness.
4. Work inside an integral clopen component U of X and a component V of an original
   intersection Y_J. At its generic point the local ring of Y_J is a field. The SNC height
   hypothesis and the finite-type dimension formula give dim U = dim V + card J.
   Dimension constancy on irreducible locally algebraic schemes gives this at every point.
5. Fibre-dimension invariance under field extension preserves that dimension difference.
   Apply the dimension formula over L and cancel the common residue transcendence degree.
   At generic points of the pulled-back intersection its local ring is a field; thus every
   minimal prime of its ideal on an ambient affine chart has height card J.
6. Distinct pieces over the same a are disjoint. Otherwise the selected original indices
   are distinct; pull their clopen inclusions back to the original intersection after
   extension. Their intersection is clopen there, hence smooth, with step 5's codimension.
7. Pieces over different a cannot contain one another: at a generic point containment
   would give ambient local dimension both one and two, by steps 5--6. The finite union
   from step 3 and this noncontainment identify exactly the irreducible components.
8. These are all clauses of the existing SNC definition. The empty selected intersection
   is X_L, with minimal primes of height zero. The unit ideal and empty component family
   cover the empty divisor; an empty X is allowed throughout. No separability is used. -/
theorem relative_snc_field_extension
    {F L : Type u} [Field F] [Field L] [Algebra F L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of F)) [Smooth f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (D : X.IdealSheafData) (hD : D.IsSmoothStrictNormalCrossingsDivisor f)
    (n : ℕ) (C : Fin n → X.IdealSheafData)
    (hunion : D = ⨅ a, C a)
    (hintegral : ∀ a, IsIntegral (C a).subscheme)
    (hdistinct : ∀ a b, (C a).support ≤ (C b).support → a = b) :
    Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap F L)))) ∧
    (D.comap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap F L))))).IsInvertible ∧
    IsReduced (D.comap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap F L))))).subscheme ∧
    (D.comap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap F
      L))))).IsSmoothStrictNormalCrossingsDivisor
        ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap F L))))) ∧
    ∃ (m : Fin n → ℕ)
      (B : (Σ a, Fin (m a)) →
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap F L)))).IdealSheafData),
      (∀ a, Smooth (((C a).comap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap F
        L))))).subschemeι ≫
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap F L)))))) ∧
      (∀ a, (C a).comap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap F L)))) = ⨅ b, B
        ⟨a, b⟩) ∧
      (∀ b, IsIntegral (B b).subscheme) ∧
      (∀ a b, ∃ h : (C a).comap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap F L)))) ≤ B
        ⟨a, b⟩,
        IsOpenImmersion (Scheme.IdealSheafData.inclusion h) ∧
          IsClosedImmersion (Scheme.IdealSheafData.inclusion h)) ∧
      (∀ a b c, b ≠ c → Disjoint (B ⟨a, b⟩).support (B ⟨a, c⟩).support) ∧
      (D.comap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap F L)))) = ⨅ b, B b) ∧
      (∀ b c, (B b).support ≤ (B c).support → b = c) ∧
      (Set.range (fun b : Σ a, Fin (m a) ↦
        (((B b).comap (D.comap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap F
          L))))).subschemeι).support :
            Set (D.comap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap F
              L))))).subscheme)) =
        irreducibleComponents (D.comap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap F
          L))))).subscheme) ∧
      (∀ s : Finset (Σ a, Fin (m a)),
        Smooth ((s.sup B).subschemeι ≫
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap F L))))) ∧
        (∀ (U : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap F L)))).affineOpens)
          (p : Ideal Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap F L)))), U.1)),
          p ∈ ((s.sup B).ideal U).minimalPrimes → p.height = (s.card : ℕ∞)) ∧
        ((¬ Set.InjOn (fun b : Σ a, Fin (m a) ↦ b.1) (s : Set (Σ a, Fin (m a)))) →
          s.sup B = ⊤) ∧
        (Set.InjOn (fun b : Σ a, Fin (m a) ↦ b.1) (s : Set (Σ a, Fin (m a))) →
          ∃ h : ((s.image (fun b ↦ b.1)).sup C).comap (pullback.fst f (Spec.map (CommRingCat.ofHom
            (algebraMap F L)))) ≤ s.sup B,
            IsOpenImmersion (Scheme.IdealSheafData.inclusion h) ∧
              IsClosedImmersion (Scheme.IdealSheafData.inclusion h))) := by
  sorry

end AlgebraicGeometry
