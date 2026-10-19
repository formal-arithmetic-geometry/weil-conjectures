/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.RingTheory.ValuationRingNormal
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.SubsetGeometricIrreducibility
import WeilConjectures.FieldTheory.FieldTensorUniqueMinimalPrime
import Sheaf.AlgebraicGeometry.GeometricReducednessFromGenericStalks
import Sheaf.AlgebraicGeometry.ProductIrreducibleComponentsBijection
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# Geometric components over valuation residue fields

Source: Stacks Project, Varieties, Tags 020J, 038H and 04KS; Étale Cohomology,
Tag 09Z9 (2); Algebra, Tag 00IC
(blueprint: lem-trf-sepclosed-valuation-geometric-components).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Residue fields of valuations of separably closed fields are separably closed, and
geometrically reduced finite type schemes over them have geometrically integral components.
Source: Stacks Project, Tags 020J, 038H, 04KS, 09Z9 (2) and 00IC.
(blueprint: lem-trf-sepclosed-valuation-geometric-components)

Here `p` is a point of `Spec V`, equivalently a prime ideal. Its scheme residue field is
canonically `Frac(V / p)`. For a closed component `T`, `vanishingIdeal T` supplies its
reduced induced structure. The iterated pullback `T ×[Z] Z_L` is canonically `T_L`.
The last equality of ideal sheaves says that the base-changed component has exactly the
reduced induced closed structure on its inverse-image component, not just the same support.

Proof, following the seven steps of the node:
1. The stalks of `Spec V` are the localizations `V_q`, with fraction field `K`.
   The element-or-inverse condition persists in these localizations; valuation-ring
   normality (lem-weil-pbc-valuation-ring-normal) makes every stalk normal.
2. Apply sbc-lem-etale-over-normal, clause (2), to the integral normal scheme `Spec V`.
   Its function field is separably closed, so every stalk is strictly henselian.
   Its residue field, canonically `Frac(V / p)`, is therefore separably closed.
3. For a component `T`, apply lem-sbc-subset-geometric-irreducibility with the identity
   extension of the residue field. Every inverse image of `T` is irreducible and nonempty.
   Closed-immersion base change and the affine quotient tensor formula identify it with
   the support of `T_L`.
4. On an affine chart meeting `T`, its generic point corresponds to a minimal prime `q`.
   Reducedness of `Z` makes `A_q` a field, with `q A_q = 0`. Thus the generic stalks of
   the reduced component and of `Z` agree, including their scalar maps.
5. After tensoring with any field extension `L`, that generic stalk is a localization
   of the reduced ring `A tensor L`, hence is reduced (localization-tensor-over-base).
6. Apply lem-pur-geometric-reducedness-from-generic-stalks to the reduced component.
   It remains reduced after every extension; step 3 gives irreducibility, hence integrality.
7. The spectrum of an algebraic closure is geometrically irreducible by the field-tensor
   theorem. Apply lem-sc-product-irreducible-components-bijection. Its inverse is preimage:
   maximality identifies the corresponding component with the preimage of `T`.
   Step 6 and uniqueness in lem-weil-pbc-reduced-induced-closed-subscheme identify the
   reduced induced structures, equivalently their ideal sheaves. No height hypothesis is used.
-/
theorem sepClosed_valuation_geometric_components
    (K : Type u) [Field K] [IsSepClosed K] (V : Subring K) [IsFractionRing V K]
    (hV : ∀ a : K, a ≠ 0 → a ∈ V ∨ a⁻¹ ∈ V)
    (p : Spec (CommRingCat.of V)) :
    IsSepClosed ((Spec (CommRingCat.of V)).residueField p) ∧
      ∀ (Z : Scheme.{u}) (f : Z ⟶ Spec ((Spec (CommRingCat.of V)).residueField p))
        [LocallyOfFiniteType f] [QuasiCompact f] [GeometricallyReduced f],
        (∀ T : TopologicalSpace.Closeds Z, (T : Set Z) ∈ irreducibleComponents Z →
          ∀ (L : Type u) [Field L]
            [Algebra ((Spec (CommRingCat.of V)).residueField p) L],
            IsIntegral (pullback (Scheme.IdealSheafData.vanishingIdeal T).subschemeι
              (pullback.fst f (Spec.map (CommRingCat.ofHom
                (algebraMap ((Spec (CommRingCat.of V)).residueField p) L)))))) ∧
        ∀ (Ω : Type u) [Field Ω]
          [Algebra ((Spec (CommRingCat.of V)).residueField p) Ω]
          [IsAlgClosure ((Spec (CommRingCat.of V)).residueField p) Ω],
          Set.BijOn
            (Set.preimage (pullback.fst f (Spec.map (CommRingCat.ofHom
              (algebraMap ((Spec (CommRingCat.of V)).residueField p) Ω)))))
            (irreducibleComponents Z)
            (irreducibleComponents ↥(pullback f (Spec.map (CommRingCat.ofHom
              (algebraMap ((Spec (CommRingCat.of V)).residueField p) Ω))))) ∧
          ∀ T : TopologicalSpace.Closeds Z, (T : Set Z) ∈ irreducibleComponents Z →
            ∀ D : TopologicalSpace.Closeds ↥(pullback f (Spec.map (CommRingCat.ofHom
              (algebraMap ((Spec (CommRingCat.of V)).residueField p) Ω)))),
              (D : Set _) = (pullback.fst f (Spec.map (CommRingCat.ofHom
                (algebraMap ((Spec (CommRingCat.of V)).residueField p) Ω)))) ⁻¹' (T : Set Z) →
              (pullback.snd (Scheme.IdealSheafData.vanishingIdeal T).subschemeι
                (pullback.fst f (Spec.map (CommRingCat.ofHom
                  (algebraMap ((Spec (CommRingCat.of V)).residueField p) Ω))))).ker =
                Scheme.IdealSheafData.vanishingIdeal D := by
  sorry

end AlgebraicGeometry
