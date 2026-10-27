/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Sheaf.AlgebraicGeometry.ClosedPointField
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import Sheaf.DeligneLaumon.BertiniSections
import Sheaf.FieldTheory.FieldExtensionGeometricallyIrreducible
import Sheaf.AlgebraicGeometry.GenericPointGeometricIrreducibility
import Sheaf.AlgebraicGeometry.BertiniIrreducibleMember
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme
import Sheaf.AlgebraicGeometry.PureDimension
import Sheaf.AlgebraicGeometry.EffectiveCartierPureDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# An integral dimension cut through prescribed closed points

Source: Charles–Poonen, Bertini irreducibility theorems over finite fields,
Theorem 1.8, printed p. 4, specialized to an algebraically closed field and reduced
induced structures (blueprint: lem-sfb-bertini-prescribed-point-dimension-cut).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An integral separated variety of dimension at least two admits an integral closed
subvariety of dimension one less containing any prescribed finite set of closed points.
The structure morphism of the subvariety is the composite of its immersion with that of `X`.

Source: Charles–Poonen, Theorem 1.8, printed p. 4.
(blueprint: lem-sfb-bertini-prescribed-point-dimension-cut).

Proof:
1. Use `lem-sfb-integral-chow-envelope-compactification` to obtain a proper birational
   surjection `P → X`, with `P` dense open in an integral projective closure `Z`.
   The dimension-of-opens lemma gives `dim Z = dim P = dim X = m`; finite type over
   a Noetherian base makes these schemes Noetherian.
2. Lift each point of `F` to a closed point of its nonempty fibre in `P`, using the
   Jacobson and residue-field lemmas. Its residue field is `k`, so the closed-point
   criterion makes it closed in `Z` too. Add a closed point over the birational
   isomorphism open. The resulting finite nonempty set `S` works even when `F` is empty.
3. Give `S` its reduced induced structure. For a sufficiently high ample twist `M`,
   `lem-zl-bertini-sections` says the sections vanishing on `S` generate `M` and
   define an immersion away from `S`. Proper coherent finiteness makes this space
   finite-dimensional. `lem-sfb-immersive-finite-base-bertini-conditions` supplies
   the codimension-two witness and base-locus bound for irreducible Bertini.
4. Algebraic closedness in the function field and the generic-point criterion make
   `Z` geometrically irreducible. Apply `lem-zl-bertini-irreducible-member` and
   intersect its coefficient open with the nonzero-section open. The Jacobson and
   residue-field lemmas supply a `k`-point of this nonempty open, hence a nonzero
   section with geometrically irreducible zero scheme `H` containing `S`.
5. On integral `Z` that section is locally a non-zero-divisor. The zero-scheme
   properties give an effective Cartier divisor. Cartier purity gives dimension
   `m - 1`; its reduced induced structure `D` is integral and still contains `S`.
6. The nonempty open `E = D ∩ P` is integral of dimension `m - 1`. Its map to `X`
   is proper (closed immersion followed by the Chow map), so its image is closed
   and irreducible. Give this image its reduced induced structure `Y`; it contains `F`.
7. Over the isomorphism open the reduced induced structures of `E` and `Y` agree,
   by uniqueness of the radical ideal on each affine open. This open is nonempty
   by the extra point chosen in step 2, so dimension-of-opens gives `dim Y = m - 1`.
   The closed immersion into separated finite-type `X` gives separatedness and
   finite type of `Y` over `k`.
-/
theorem exists_integral_closedSubscheme_dimension_cut_through_finite_closedPoints
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsIntegral X]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (m : ℕ) (hm : 2 ≤ m) (hX : topologicalKrullDim X = (m : WithBot ℕ∞))
    (F : Set X) (hF : F.Finite) (hclosed : ∀ x ∈ F, IsClosed ({x} : Set X)) :
    ∃ (Y : Scheme.{u}) (i : Y ⟶ X),
      IsIntegral Y ∧ IsSeparated (i ≫ (X ↘ Spec (.of k))) ∧
      LocallyOfFiniteType (i ≫ (X ↘ Spec (.of k))) ∧
      QuasiCompact (i ≫ (X ↘ Spec (.of k))) ∧
      topologicalKrullDim Y = ((m - 1 : ℕ) : WithBot ℕ∞) ∧
      IsClosedImmersion i ∧ F ⊆ Set.range i := by
  sorry

end AlgebraicGeometry
