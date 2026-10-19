/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.KrullDimension
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.ConormalSequenceSmoothImmersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Topology.NoetherianSpace
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.AlgebraicGeometry.FiniteTypeFibreImageDimensionBounds
import Sheaf.AlgebraicGeometry.HypersurfaceNonzeroRelativeDifferential

/-!
# Dimension bound for the singular locus in a Bertini family

Source: Stacks Project, Varieties, Situation 0FD3 and Lemma 0FD6, universal-family proof
(blueprint: lem-zl-bertini-singular-locus-dimension).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

/-- The universal section `∑ xᵢ pr₂* sᵢ` on coefficient affine space times `Y`.
The coordinates are the polynomial variables under the canonical global-sections isomorphism.
Source: Stacks Project, Situation 0FD3 (blueprint: lem-zl-bertini-singular-locus-dimension). -/
def bertiniUniversalSection {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) :
    Γ((Scheme.Modules.tensorPullback
      (pullback.snd (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k)))
        f)).obj L, ⊤) :=
  ∑ i, (pullback.fst
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))) f).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial I k))).inv (MvPolynomial.X i)) •
    Scheme.Modules.tensorSectionsUnit
      (pullback.snd (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k)))
        f) L (s i)

/-- The ideal sheaf of the universal zero scheme, constructed using the recorded zero scheme.
Source: Stacks Project, Situation 0FD3 (blueprint: lem-zl-bertini-singular-locus-dimension). -/
def bertiniUniversalIdeal {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) :
    (pullback
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))) f).IdealSheafData :=
  (Scheme.Modules.homOfGlobalSection _ (bertiniUniversalSection f L s)).zeroLocus

/-- The projection `q : H_univ ⟶ A^I_k` from the universal zero scheme.
Source: Stacks Project, Tag 0FD6 (blueprint: lem-zl-bertini-singular-locus-dimension). -/
def bertiniUniversalProjection {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) :
    (bertiniUniversalIdeal f L s).subscheme ⟶ Spec (CommRingCat.of (MvPolynomial I k)) :=
  (bertiniUniversalIdeal f L s).subschemeι ≫
    pullback.fst
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial I k))) f

/-- The non-smooth locus of the universal projection: points with no smooth open neighbourhood.
Source: Stacks Project, Tag 0FD6 (blueprint: lem-zl-bertini-singular-locus-dimension). -/
def bertiniUniversalSingularLocus {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) (L : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(L, ⊤)) :
    Set (bertiniUniversalIdeal f L s).subscheme :=
  {h | ¬ ∃ W : (bertiniUniversalIdeal f L s).subscheme.Opens,
    h ∈ W ∧ Smooth (W.ι ≫ bertiniUniversalProjection f L s)}

/-- The non-smooth locus of the universal Bertini family has dimension less than `r`,
and its image lies in a proper closed subset of coefficient affine space. The additive map
`ψ` and its scalar equation express exactly linearity for the canonical action through `f`.
The basis indexed by `ULift (Fin r)` expresses finite dimensionality and dimension `r`.

Source: Stacks Project, Tag 0FD6, universal-family proof
(blueprint: lem-zl-bertini-singular-locus-dimension).

Proof:
1. If `Y` is empty, the singular locus is empty and take `B` empty. If `r = 0`, generation
   forces the invertible sheaf's stalks to vanish, so `Y` is empty as well
   (`def-sc-invertible-module`, `def-weil-pbc-generating-sections`).
2. The projective immersion places `Y` in a Noetherian space, so it is quasi-compact;
   smoothness then makes it finite type. Affine trivializations show that the universal
   zero scheme is finite type. Its non-smooth locus is closed by openness of smoothness,
   hence its reduced induced scheme is finite type too. Use
   `lem-wf-affine-noetherian-components`, `lem-kun-finite-union-noetherian`,
   `lem-sfb-noetherian-space-compact-subsets`, `def-weil-closed-immersion`,
   `def-sbc-smooth-morphisms`, `def-weil-finite-type-morphism`, `def-pc-zero-scheme`.
3. On finitely many affine charts trivializing a generating section and the differential
   sheaf of rank `d`, the immersion and conormal sequence imply that the differentials of
   the section ratios span the cotangent fibres. Thus the value-and-differential matrix
   sends the `r` coordinates onto a vector space of dimension `d + 1`. Use
   `lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension`,
   `lem-pur-conormal-sequence-smooth-immersion`, `def-sc-relative-differential-sheaf`,
   and `def-weil-pbc-morphism-to-projective-space-by-sections`.
4. Write `F = ∑ xⱼ fⱼ` locally. The ambient projection is smooth by smooth base change.
   The hypersurface nonzero-relative-differential criterion puts the non-smooth locus
   inside the closed locus `F = dF = 0`. This uses only containment, including at the zero
   parameter; it makes no false flatness inference there. Use
   `lem-pc-proper-base-change` (smoothness clause),
   `lem-zl-hypersurface-nonzero-relative-differential`,
   `def-sc-relative-differential-sheaf`, and `def-pc-zero-scheme`.
5. Each residue-field fibre of this linear kernel is affine space of dimension `r-d-1`,
   by the rank computation. The polynomial dimension formula and the finite-type fibre
   bound give dimension at most `r-1` on each chart, hence on its closed singular subspace.
   Use `lem-sf-noetherian-polynomial-dimension`,
   `lem-weil-pbc-spec-topological-krull-dimension-ring`, and
   `lem-zl-finite-type-fibre-image-dimension-bounds`.
6. Every chain of irreducible closed subsets can be restricted to a chart meeting its
   smallest member without losing strictness. Thus the singular locus has dimension
   at most `r-1 < r`. The finite-type image-dimension bound shows that the closure of its
   image has dimension less than `r`; affine coefficient space has dimension `r`, so
   that closure is the required proper closed subset. Use
   `lem-zl-finite-type-fibre-image-dimension-bounds`,
   `lem-sf-noetherian-polynomial-dimension`, and
   `lem-weil-pbc-spec-topological-krull-dimension-ring`. -/
theorem bertini_singularLocus_dimension_lt
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [Smooth f]
    (L : Y.Modules) [L.IsInvertible]
    {V : Type v} [AddCommGroup V] [Module k V]
    (r : ℕ) (b : Module.Basis (ULift.{u} (Fin r)) k V)
    (ψ : V →+ Γ(L, ⊤))
    (_hlinear : ∀ (c : k) (v : V),
      ψ (c • v) = f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) • ψ v)
    (hgen : Epi (L.freeHomEquiv.symm (fun i : ULift.{u} (Fin r) ↦
      (SheafOfModules.unitHomEquiv L) (Scheme.Modules.homOfGlobalSection L (ψ (b i))))))
    [IsImmersion (ProjectiveSpace.homOfGeneratingSections (ULift.{u} (Fin r)) f L
      (fun i ↦ (SheafOfModules.unitHomEquiv L)
        (Scheme.Modules.homOfGlobalSection L (ψ (b i)))) hgen)] :
    topologicalKrullDim (bertiniUniversalSingularLocus f L (fun i ↦ ψ (b i))) <
        (r : WithBot ℕ∞) ∧
      ∃ B : Set (Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin r)) k))),
        IsClosed B ∧ B ≠ Set.univ ∧
          (bertiniUniversalProjection f L (fun i ↦ ψ (b i))) ''
            bertiniUniversalSingularLocus f L (fun i ↦ ψ (b i)) ⊆ B := by
  sorry

end

end AlgebraicGeometry
