/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q157
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Sheaf.AlgebraicGeometry.GeometricRegularitySmoothFieldCriterion
import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition

/-!
# The boundary of fibrewise nonempty opens in good curves

Source: Stacks Project, More on Etale Cohomology, Tag 0GKX,
lemma-constant-shriek-rel-dim-1, the second boundary Zprime, using Tag 0GK7
(blueprint: lem-weil-pbc-good-curves-boundary-quasifinite).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The canonical map to the base from the reduced closed complement of the open union
of the `O i` in the coproduct of the `C i`. The open union is the supremum of the open
images of `u i` followed by the coprojections. Its complement carries the reduced
induced closed structure given by the existing vanishing-ideal construction.
Source: Stacks Project, Tag 0GKX, second boundary Zprime; Tags 01J3 and 01J4
(blueprint: lem-weil-pbc-good-curves-boundary-quasifinite). -/
noncomputable def goodCurvesBoundaryMap
    {I : Type u} (B : Scheme.{u}) (T C O : I → Scheme.{u})
    (t : ∀ i, T i ⟶ B) (b : ∀ i, C i ⟶ T i) (u : ∀ i, O i ⟶ C i)
    [∀ i, IsOpenImmersion (u i)] :
    (Scheme.IdealSheafData.vanishingIdeal
      (⨆ i, (u i ≫ Sigma.ι C i).opensRange).compl).subscheme ⟶ B :=
  (Scheme.IdealSheafData.vanishingIdeal
    (⨆ i, (u i ≫ Sigma.ι C i).opensRange).compl).subschemeι ≫
      Sigma.desc (fun i ↦ b i ≫ t i)

/-- Source: Stacks Project, Tag 0GKX, the assertion that the second boundary Zprime
is quasi-finite, with the good-curves hypotheses of Tag 0GK7 made explicit
(blueprint: lem-weil-pbc-good-curves-boundary-quasifinite).

Proof plan:
1. Each finite `t i` is proper (lem-weil-pbc-finite-proper), so `b i ≫ t i` is
   proper (lem-weil-pbc-proper-composition).
2. Their finite coproduct is proper: finite type follows by combining finite affine
   covers; separatedness is checked on the pieces `C i ×[B] C j` of the diagonal,
   empty off the equal-index pieces; universal closedness follows from a finite union
   of closed images after any base change (lem-weil-pbc-scheme-coproduct-family).
3. The reduced complement is a closed immersion
   (lem-weil-pbc-reduced-induced-closed-subscheme), hence its map to `B` is proper
   (lem-weil-pbc-closed-immersion-proper). It is separated and of finite type.
   Over the locally Noetherian base it is locally of finite presentation
   (pqf-lem-lft-fp-locnoeth); properness also gives quasi-compactness and a
   quasi-compact diagonal, hence quasi-separatedness.
4. Each fibre of `b i` is proper and smooth over its residue field
   (lem-weil-pbc-proper-base-change, sbc-lem-smooth-criterion). It is Noetherian
   (lem-weil-pbc-finite-type-over-noetherian), and regular by the smooth-field
   criterion applied to the identity field extension
   (lem-weil-pbc-geometric-regularity-smooth-field-criterion). Geometric connectedness
   gives connectedness; nonemptiness and regularity give irreducibility
   (rem-pc-regular-normal). No perfection of the residue field is needed.
5. The open fibre is nonempty. On an irreducible scheme of dimension at most one,
   every point outside it is closed (lem-sc-scheme-sober,
   lem-sc-dim-one-point-outside-open-closed). Its closed complement is finite
   by Noetherianity (lem-sc-noetherian-closed-points-finite). In dimension zero
   the complement is empty.
6. For any point of `B`, each `t i` has a finite fibre (pqf-lem-finite-qf,
   pqf-lem-qf-finitefibres). The boundary fibre is the disjoint union of the finite
   complements from step 5 over these points and over the finite set `I`.
   The fibre homeomorphism (def-pc-scheme-fibre) and the image of the reduced
   closed immersion justify this set-level decomposition; reduction need not commute
   with base change.
7. Finite type and finite fibres imply quasi-finiteness (pqf-lem-qf-finitefibres).
   The other conclusions were obtained in step 3. Empty `I`, `B` or `T i`
   contribute no points and are permitted throughout. -/
theorem good_curves_boundary_quasiFinite
    {I : Type u} [Finite I] (B : Scheme.{u}) [IsLocallyNoetherian B] [CompactSpace B]
    (T C O : I → Scheme.{u})
    (t : ∀ i, T i ⟶ B) (b : ∀ i, C i ⟶ T i) (u : ∀ i, O i ⟶ C i)
    [∀ i, IsFinite (t i)] [∀ i, Etale (t i)]
    [∀ i, Smooth (b i)] [∀ i, IsProper (b i)]
    [∀ i, IsOpenImmersion (u i)]
    (hC : ∀ (i : I) (s : T i), Nonempty ((b i).fiber s) ∧
      GeometricallyConnected ((b i).fiberToSpecResidueField s) ∧
      topologicalKrullDim ((b i).fiber s) ≤ 1)
    (hO : ∀ (i : I) (s : T i), Nonempty ((u i ≫ b i).fiber s)) :
    IsSeparated (goodCurvesBoundaryMap B T C O t b u) ∧
    Scheme.Hom.IsQuasiFinite (goodCurvesBoundaryMap B T C O t b u) ∧
    LocallyOfFinitePresentation (goodCurvesBoundaryMap B T C O t b u) ∧
    QuasiCompact (goodCurvesBoundaryMap B T C O t b u) ∧
    QuasiSeparated (goodCurvesBoundaryMap B T C O t b u) := by
  sorry

end AlgebraicGeometry
