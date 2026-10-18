/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.LogRegularPair
public import Sheaf.AlgebraicGeometry.NormalCrossingsDivisor
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Desingularization of a log regular pair

Source: Illusie--Laszlo--Orgogozo, *Travaux de Gabber*, Exposé VIII,
3.4.6(i), 3.4.8--3.4.9, 4.1.1, printed pp. 110--112, 117; Exposé VI,
1.7, printed p. 70 (blueprint: lem-trf-log-regular-desingularization).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/--
Source: Illusie--Laszlo--Orgogozo, *Travaux de Gabber*, Exposé VIII,
3.4.6(i), 3.4.8--3.4.9, 4.1.1, printed pp. 110--112, 117; Exposé VI,
1.7, printed p. 70 (blueprint: lem-trf-log-regular-desingularization).

Proof:
1. The divisorial log structure of `hlog` is fine saturated and log regular, with
   dense triviality locus `j`; finite type over the field supplies the required
   local Noetherian hypotheses.
2. The characteristic monoids are sharp saturated monoids, hence their group
   completions are torsion-free. The saturated monoidal resolution tower therefore
   ends with free characteristic monoids.
3. On an integral scheme, every nonzero finite-type blowup chart is a domain, and
   normalization inside the common function field remains integral.
4. Inductively, normalized log blowups preserve log regularity, integrality,
   finite type, properness, and the isomorphism over the triviality locus.
5. At the final free-characteristic stage, the free-characteristic criterion gives
   a regular finite-type scheme and identifies the reduced inverse boundary with
   an effective Cartier normal-crossings divisor. The zero-length tower is the
   identity case, and the inverse image of the dense triviality locus remains dense.
-/
theorem exists_log_regular_desingularization
    (F : Type u) [Field F] [IsAlgClosed F]
    (V : Scheme.{u}) (f : V ⟶ Spec (.of F))
    [IsIntegral V] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsLocallyNoetherian V]
    (Z : TopologicalSpace.Closeds V) (U : Scheme.{u}) (j : U ⟶ V)
    [IsOpenImmersion j]
    (hU : DenseRange j)
    (hZU : (Set.range j : Set V) = (Z : Set V)ᶜ)
    (hlog : IsDivisorialFineSaturatedLogRegularPair V U j hU) :
    ∃ (V₁ : Scheme.{u}) (f₁ : V₁ ⟶ Spec (.of F)) (p : V₁ ⟶ V),
      IsIntegral V₁ ∧
        LocallyOfFiniteType f₁ ∧
        QuasiCompact f₁ ∧
        p ≫ f = f₁ ∧
        (∀ x : V₁, ∃ W : V₁.affineOpens,
          x ∈ W.1 ∧ IsRegularRing Γ(V₁, W)) ∧
        IsProper p ∧
        IsIso (pullback.snd p j) ∧
        DenseRange (pullback.fst p j) ∧
        (((Scheme.IdealSheafData.vanishingIdeal Z).comap p).radical).IsNormalCrossingsDivisor := by
  sorry

end AlgebraicGeometry
