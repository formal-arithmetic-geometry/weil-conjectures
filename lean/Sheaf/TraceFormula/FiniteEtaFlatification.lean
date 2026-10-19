/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Sober
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Sheaf.TraceFormula.SchematicallyDenseOpen

/-! # Finite generic flatification after a birational base modification

Source: Temkin, *Stable modification of relative curves*, Theorem 3.5.5, Step 0,
printed pp. 21--22; Raynaud--Gruson, Théorème 5.2.2
(blueprint: lem-trf-finite-eta-flatification).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A dominant finitely presented morphism admits a proper integral base modification and
finite generic modification whose source is flat and finitely presented.

The generic fibre of the source is schematically dense, while the isomorphism open is asserted
only in the source of the finite map. No density assertion is made for the possibly nonflat
base-change target.

Source: Temkin, *Stable modification of relative curves*, Theorem 3.5.5, Step 0,
printed pp. 21--22; Raynaud--Gruson, Théorème 5.2.2
(blueprint: lem-trf-finite-eta-flatification).

Proof plan:
1. Apply generic flatness to the dominant finitely presented map over the integral base and
   choose a nonempty affine open containing the generic point.
2. Apply flattening by an admissible blowup to obtain an integral proper surjective base
   modification and a flat finitely presented strict transform.
3. Use properness and the finite-type centre to identify the base modification with the
   original base over an open containing the generic point; the generic fibre is therefore
   `Spec S.functionField`.
4. The strict transform is a finite closed subscheme of the base change and is an isomorphism
   over the preserved open.
5. Flatness over the integral base gives scheme-theoretic density of the generic fibre in the
   source. The inverse image of the preserved open is schematically dense in the source by
   this generic-density calculation.
-/
theorem exists_finite_eta_flatification
    {S X : Scheme.{u}} [IsIntegral S] [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [IsDominant f] [LocallyOfFinitePresentation f] [QuasiCompact f]
    [QuasiSeparated f] :
    ∃ (S₁ : Scheme.{u}) (b : S₁ ⟶ S),
      IsIntegral S₁ ∧ IsProper b ∧ Surjective b ∧
      IsIso (pullback.snd b S.fromSpecFunctionField) ∧
      ∃ (X₁ : Scheme.{u}) (a : X₁ ⟶ pullback f b),
        IsFinite a ∧
        IsIso
          (pullback.map
            (a ≫ pullback.snd f b ≫ b) S.fromSpecFunctionField
            (pullback.snd f b ≫ b) S.fromSpecFunctionField
            a (𝟙 _) (𝟙 _) (by simp) (by simp)) ∧
        ∃ (U₁ : (pullback f b).Opens),
          IsIso (a ∣_ U₁) ∧ SchematicallyDenseOpen (a ⁻¹ᵁ U₁) ∧
          Flat (a ≫ pullback.snd f b) ∧
          LocallyOfFinitePresentation (a ≫ pullback.snd f b) ∧
          IsSchemeTheoreticallyDominant
            (pullback.fst
              (a ≫ pullback.snd f b ≫ b) S.fromSpecFunctionField) := by
  sorry

end AlgebraicGeometry
