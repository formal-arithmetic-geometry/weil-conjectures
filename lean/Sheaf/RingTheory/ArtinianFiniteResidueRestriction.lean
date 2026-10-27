/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65
-/
module

public import Mathlib.RingTheory.LocalRing.Pullback
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.HopkinsLevitzki
import Sheaf.RingTheory.SemilocalRestrictionLength
import Mathlib.RingTheory.Length

/-!
# Artinian local rings after restricting a finite residue extension

Source: Stacks Project, Formal Deformation Theory, Tag 07W8, comparison functor and
its verification (blueprint: lem-sfb-artinian-finite-residue-restriction).

The ring is Mathlib's `RingHom.pullback`, with its coordinatewise operations.
The auxiliary map below sends `(b', t)` to `(q b', t)`.
-/

@[expose] public section

universe u v w w'

namespace RingHom

/-- The canonical map on residue-restriction pullbacks, sending `(b', t)` to `(q b', t)`.
The source residue map is `ρ.comp q`, so the residue-field map is the identity.

Source: Stacks Project, Formal Deformation Theory, Tag 07W8, comparison functor
(blueprint: lem-sfb-artinian-finite-residue-restriction). -/
def finiteResidueRestrictionMap
    {k : Type u} {l : Type v} {B : Type w} {B' : Type w'}
    [CommRing k] [CommRing l] [CommRing B] [CommRing B']
    (ρ : B →+* l) (ρ' : B' →+* l) (ι : k →+* l) (q : B' →+* B)
    (hρ : ρ' = ρ.comp q) :
    ρ'.pullback ι →+* ρ.pullback ι :=
  (q.prodMap (RingHom.id k)).restrict (ρ'.pullback ι) (ρ.pullback ι)
    (fun x hx ↦ by simpa [hρ] using hx)

/-- Restricting the residue field along a finite field extension preserves Artinian
local rings and surjections, with the specified residue field and its identity map.
A surjection from a local ring to a field is its residue map with that field identified.

Source: Stacks Project, Formal Deformation Theory, Tag 07W8 (`situation-change-of-fields`)
and the verification following `equation-comparison`
(blueprint: lem-sfb-artinian-finite-residue-restriction).

Proof:
1. For `C = B ×_l k`, the first projection is injective since the field embedding is
   injective. The second projection is surjective by lifting elements along `ρ`.
   Its kernel is the pairs `(b, 0)` with `ρ b = 0`. A pair with nonzero second coordinate
   has inverse `(b⁻¹, t⁻¹)`, since `b` is outside the unique maximal ideal of `B`.
   Hence this kernel is the unique maximal ideal, and the quotient is the specified `k`.
2. By `lem-weil-pbc-artinian-ring-self-finite-length` (Stacks 00JB), `B` has finite
   length over itself. Apply `lem-exc-semilocal-restriction-length` (Stacks 02M0) to
   `C → B` and the module `B`. The unique maximal ideal contracts to the kernel just
   described, and the induced residue extension is precisely the finite extension `l/k`.
   Therefore `B` has finite length over `C`.
3. By `def-weil-pbc-module-length` (Stacks 02LY), strict chains of `C`-submodules of `B`
   have bounded length. Injectivity of `C → B` embeds ideals of `C` as such submodules,
   preserving and reflecting strict inclusions. Descending ideal chains consequently
   stabilize, so `C` is Artinian.
4. Given a surjection `q : B' → B`, identify the source residue map with `ρ.comp q`.
   A lift `b'` of `b` makes `(b', t)` a lift of every `(b, t)` in the target pullback.
   Thus `finiteResidueRestrictionMap` is surjective. Its unchanged second coordinate
   says that the induced map on the specified residue field `k` is the identity.
   Applying steps 1–3 to `B'` also gives its Artinian local residue-restriction ring. -/
theorem artinian_finite_residue_restriction
    (k : Type u) (l : Type v) [Field k] [Field l]
    [Algebra k l] [FiniteDimensional k l]
    (B : Type w) [CommRing B] [IsArtinianRing B] [IsLocalRing B]
    (ρ : B →+* l) (hρ : Function.Surjective ρ) :
    IsArtinianRing (ρ.pullback (algebraMap k l)) ∧
      ∃ hC : IsLocalRing (ρ.pullback (algebraMap k l)),
        Function.Surjective (ρ.pullbackSnd (algebraMap k l)) ∧
        RingHom.ker (ρ.pullbackSnd (algebraMap k l)) =
          @IsLocalRing.maximalIdeal (ρ.pullback (algebraMap k l)) _ hC ∧
        Function.Injective (ρ.pullbackFst (algebraMap k l)) ∧
        ∀ (B' : Type w') [CommRing B'] [IsArtinianRing B'] [IsLocalRing B']
          (ρ' : B' →+* l) (hρ' : Function.Surjective ρ')
          (q : B' →+* B) (hρq : ρ' = ρ.comp q), Function.Surjective q →
          Function.Surjective
            (finiteResidueRestrictionMap ρ ρ' (algebraMap k l) q hρq) ∧
          (ρ.pullbackSnd (algebraMap k l)).comp
              (finiteResidueRestrictionMap ρ ρ' (algebraMap k l) q hρq) =
            ρ'.pullbackSnd (algebraMap k l) := by
  sorry

end RingHom
