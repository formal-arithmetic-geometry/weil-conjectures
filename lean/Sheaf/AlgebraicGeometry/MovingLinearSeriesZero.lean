/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.ProjectiveSpace.MRegularConsequences
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.ResidueFiber
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
import Sheaf.AlgebraicGeometry.RegularCurveDivisorCalculus
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import WeilConjectures.AlgebraicGeometry.Curve
import Mathlib.GroupTheory.CosetCover
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Moving zeros of a restricted linear series

Source: Stacks Project, Varieties, Tag 0B40, with the normalization and
fixed-divisor corollary in the DAG; Franciosi--Tenni, Lemma 3.3 Step 1, p.236.
(blueprint: lem-sfb-moving-linear-series-zero)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- The image of a restricted linear series, written as the span of its actual tensor
pullbacks. The section-normalized adjunction sends a section to `1 ⊗ s`; since this
map is k-linear, this span is exactly its image.
Source: Stacks, Tag 0B40, restriction of sections in the moving-zero corollary.
(blueprint: lem-sfb-moving-linear-series-zero) -/
def restrictedLinearSeriesImage (k : Type u) [Field k]
    {X C : Scheme.{u}} [X.Over (Spec (.of k))] [C.Over (Spec (.of k))]
    (i : C ⟶ X) [i.IsOver (Spec (.of k))] (L : X.Modules)
    (V : Submodule k (ProjectiveSpace.fieldSections k L)) :
    Submodule k (ProjectiveSpace.fieldSections k ((tensorPullback i).obj L)) :=
  Submodule.span k (Set.range fun s : V ↦
    ((tensorPullbackSectionAdjunction i).unit.app L).app ⊤ s.val)

/-- A general section whose restrictions span at least two dimensions has a zero on
that reduced component outside a prescribed zero-dimensional closed subscheme.
The good set is nonempty and Zariski open in every choice of affine coordinates:
its coordinate points are the inverse image of an open of the polynomial spectrum.

Source: Stacks Project, Varieties, Tag 0B40, normalization/fixed-divisor corollary
in the DAG; Franciosi--Tenni, Lemma 3.3 Step 1, printed p.236.
(blueprint: lem-sfb-moving-linear-series-zero)

Proof:
1. The reduced component C is integral of dimension one. Its closed immersion into
   the projective X makes it projective and proper (lem-pc-projective-proper and
   lem-weil-pbc-closed-immersion-comp). Normalize C, using
   lem-sc-normalization-properties: over the algebraically closed, hence perfect, k
   its normalization is a smooth proper integral curve.
2. Restrict V and pull it to the normalization. Pullback of sections is injective:
   a section zero at the generic point is zero on every affine trivialization in
   the integral C. Thus the image U still has dimension at least two. By
   lem-pc-zero-dimensional-closed-subscheme-finite and
   lem-weil-pbc-finite-closed-map-finite-fibres, the inverse image T of |Z| is finite.
3. Apply lem-sc-smooth-connected-curve-local-rings and
   lem-pc-regular-curve-divisor-calculus. A nonzero section of the normalized line
   bundle gives an effective divisor of its fixed degree d (def-sc-pic0). There are
   only finitely many degree-d effective divisors supported on T.
4. Sections with the same divisor differ by a nowhere-vanishing rational function;
   divisor calculus identifies it and its inverse as regular global functions.
   By lem-sc-global-functions the ratio is in k*, so these sections form one line.
5. Take inverse images of the finitely many realized lines, the kernel of restriction
   and pullback, and the zero subspace. All are proper since dim U >= 2. A section
   outside them has a divisor with a closed point y outside T.
6. Its image x in X is closed, lies on C and outside |Z|. In a local frame the
   coefficient maps to zero in kappa(y). The injection kappa(x) -> kappa(y) forces
   its value in kappa(x) to be zero: this is residueValue = 0
   (def-weil-pbc-module-residue-fiber).
7. In any basis every linear subspace is cut out by linear polynomials. The finite
   union is closed, giving the stated open of the affine polynomial spectrum.
   Algebraically closed k is infinite; lem-pc-finite-linear-avoidance gives a point
   of the complement. This also excludes the zero section. -/
theorem exists_moving_linear_series_zero (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [Nonempty X] [IsReduced X]
    [IsHProjective (X ↘ Spec (.of k))] (hdim : X.IsPureDimension 1)
    (L : X.Modules) [L.IsInvertible]
    (V : Submodule k (ProjectiveSpace.fieldSections k L)) [FiniteDimensional k V]
    (C : Scheme.{u}) [C.Over (Spec (.of k))] [IsReduced C]
    (i : C ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (hC : Set.range i ∈ irreducibleComponents X)
    (hV : 2 ≤ Module.finrank k (restrictedLinearSeriesImage k i L V))
    (Z : Scheme.{u}) (j : Z ⟶ X) [IsClosedImmersion j]
    (hZ : topologicalKrullDim Z ≤ 0) :
    ∃ S : Finset (Submodule k V),
      (⊥ : Submodule k V) ∈ S ∧
      (∀ W ∈ S, W ≠ ⊤) ∧
      (∀ s : V, (∀ W ∈ S, s ∉ W) →
        ∃ x : X, IsClosed ({x} : Set X) ∧ x ∈ Set.range i ∧ x ∉ Set.range j ∧
          residueValue (M := L) (U := ⊤) s.val x trivial = 0) ∧
      (∃ s : V, ∀ W ∈ S, s ∉ W) ∧
      (∀ (n : ℕ) (b : Module.Basis (Fin n) k V),
        ∃ U : TopologicalSpace.Opens (PrimeSpectrum (MvPolynomial (Fin n) k)),
          ∀ s : V, (∀ W ∈ S, s ∉ W) ↔
            PrimeSpectrum.comap (MvPolynomial.eval (fun a ↦ b.repr s a))
              (IsLocalRing.closedPoint k) ∈ U) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
