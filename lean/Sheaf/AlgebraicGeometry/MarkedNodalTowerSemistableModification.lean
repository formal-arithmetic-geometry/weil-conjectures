/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q144
-/
module

public import Sheaf.AlgebraicGeometry.MarkedSplitNodalTower
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.AlgebraicGeometry.RegularLogSmoothMonomialChart
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.RingTheory.CompleteLocalExcellent
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Semistable modification of a marked split nodal tower

Source: ILO, Travaux de Gabber, Expose X, Lemma 2.5, proof, p.153,
using Vidal 2004b, Proposition 4.4.4 and its following remark
(blueprint: lem-per-marked-nodal-tower-semistable-modification).

The base action need not be trivial. Semistable charts use the already constructed
monomial quotient with exponents one on the first `r` variables and zero elsewhere.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Equivariant projective birational semistable modification with strict boundary.
Source: ILO X 2.5, proof, p.153; Vidal 2004b, Proposition 4.4.4 and following remark
(blueprint: lem-per-marked-nodal-tower-semistable-modification).

Proof plan, the six DAG steps:
1. The complete local DVR is excellent by lem-per-complete-local-excellence. Induct on
   tower height, starting with the trait, its identity, and its closed-point boundary.
   Maintain an integral regular projective equivariant model with G-strict strict boundary,
   branch-fixing stabilizers, and compatible squarefree semistable boundary charts.
2. Pull the next nodal curve back to that model. Projectivity follows from
   lem-pc-projective-base-change. Tensoring preserves flatness and finite presentations;
   the lifting criterion preserves smoothness. Fibres and disjoint smooth sections pull
   back, and the curve is smooth outside the previous boundary.
3. Flatness embeds local rings into the integral generic fibre, proving integrality of
   the pullback. The inverse image of the previous dense isomorphism open proves that
   the projection to the original next stage is birational. New stabilizers are subgroups
   of old ones, so their graph action is trivial.
4. Apply lem-per-split-nodal-relative-resolution-charts. The regular model is finite type
   and Noetherian by lem-kun-projective-implies-proper, def-weil-proper-morphism and
   lem-weil-pbc-finite-type-over-noetherian. That relative lemma gives a regular integral
   equivariant projective birational model with strict boundary. Its inverse boundary
   equals the recursive inverse image of the original tower boundary.
5. Compose the relative smooth or uv=t_j chart with the previous trait chart. For a
   vertical t_j replace it by uv in the product defining pi; for a horizontal t_j the
   equation defining pi is unchanged. Thus all vertical exponents remain one, and the
   boundary is a product of distinct parameters. Etale base change and composition use
   lem-trf-space-chartwise-etale-permanence, in its scheme case.
6. Compose projective maps using lem-trf-h-projective-composition, and intersect dense
   isomorphism opens to compose birational maps. At height d this gives the claimed
   model, squarefree semistable charts and the global strict normal crossings boundary.
-/
theorem exists_markedNodalTower_semistableModification
    (R : CommRingCat.{u}) [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [IsStrictlyHenselianLocalRing R] [CharZero (FractionRing R)]
    (hchar : ∃ p : ℕ, p.Prime ∧ CharP (IsLocalRing.ResidueField R) p)
    (G : Type v) [Group G] [Finite G] (d : ℕ) (hd : 1 ≤ d)
    (N : MarkedSplitNodalTower (Spec R) {IsLocalRing.closedPoint R} G d) :
    ∃ (Z : Scheme.{u}) (h : Z ⟶ N.Y (Fin.last d)) (ρ : G →* Aut Z),
      IsIntegral Z ∧ IsRegularScheme Z ∧ IsHProjective h ∧
      IsHProjective (h ≫ N.toBase (Fin.last d)) ∧
      (∀ g : G, (ρ g).hom ≫ h = h ≫ (N.action (Fin.last d) g).hom) ∧
      (∃ U : (N.Y (Fin.last d)).Opens, Dense (U : Set (N.Y (Fin.last d))) ∧
        IsIso (h ∣_ U)) ∧
      (∃ π : R, Irreducible π ∧
        ∀ z : Z, ∃ (n r : ℕ) (_ : 1 ≤ r) (_ : r ≤ n)
          (V : Z.Etale)
          (c : V.left ⟶ Spec (.of
            (monomialTraitAlgebra R π n (fun i ↦ if i.val < r then 1 else 0)))),
          z ∈ Set.range V.hom ∧ Etale c ∧
          c ≫ Spec.map (CommRingCat.ofHom
            (monomialTraitAlgebraMap R π n (fun i ↦ if i.val < r then 1 else 0))) =
            V.hom ≫ h ≫ N.toBase (Fin.last d)) ∧
      ∃ E : Z.IdealSheafData, IsStrictNormalCrossingsBoundary E ∧
        (E.support : Set Z) = h ⁻¹' (N.boundary (Fin.last d) : Set (N.Y (Fin.last d))) := by
  sorry

end AlgebraicGeometry
