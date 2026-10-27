module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Connected.Basic
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier

/-! # Invariant quasi-projective open neighborhoods

Source: Sumihiro, Equivariant completion (1974), Theorem 1 and Lemma 8;
Brion, Algebraic group actions on normal varieties, arXiv:1703.09506v3,
Introduction and Theorem 1, with the finite disjoint normal-component extension
specified in the DAG. Supporting input to Milne, Algebraic Groups (2017), Section 7e
and Lemma 13.46, rather than a theorem attributed to Milne.
(blueprint: lem-sfb-sumihiro-invariant-quasiprojective-open)

Internal module objects encode scheme-level actions, and their morphisms encode
scheme-level equivariance. Projective space is the Proj of the polynomial ring
with its total-degree grading, via `Proj.projectiveSpaceOverAffine`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every point has an invariant normal quasi-projective open neighborhood.

Source: Sumihiro (1974), Theorem 1 and Lemma 8; Brion, arXiv:1703.09506v3,
Introduction, Theorem 1 and Section 3.2. The DAG extends the variety case to normal
separated finite-type schemes with finitely many disjoint normal components.
(blueprint: lem-sfb-sumihiro-invariant-quasiprojective-open)

Proof, following the accepted five-step split:
1. The empty scheme has no points. Choose an affine open U containing the given x,
   using lem-weil-pbc-affine-opens-basis. Apply
   lem-sfb-affine-saturation-cartier-boundary to obtain its saturation W under G(k),
   a restricted scheme-level action, and an effective Cartier divisor D with
   complement U. That lemma also supplies normality, separatedness, finite type and
   quasi-compactness of W. The identity shows x belongs to W, for any schematic x.
2. The Cartier ideal I_D is invertible by lemma-nagata-effective-cartier-is-invertible.
   Its dual L = O_W(D), as in def-pc-divisor-line-bundle, is invertible by the local
   rank-one calculation and def-sc-invertible-module. The inclusion I_D -> O_W is
   a section s of L. In a frame I_D = f O_W, its coefficient is the non-zero-divisor
   f, so the nonvanishing open of s is exactly U.
3. By lem-sfb-normal-line-bundle-power-linearization some positive tensor power
   M = L^m is G-linearized. The section t = s^m has nonvanishing open U, since f^m
   is nonzero in a residue field exactly when f is. Translate t using the action
   of g inverse and its linearization isomorphism. Its nonvanishing open is gU,
   including at nonclosed points.
4. These opens gU cover W and are affine, via the action automorphisms. The
   quasi-compactness of W and these sections with exponent one give ampleness
   directly by def-weil-pbc-ample-invertible-module.
5. Apply lem-weil-pbc-ample-very-ample-immersion-affine-base over k to obtain an
   immersion into a finite-dimensional projective space. This gives exactly the
   required quasi-projectivity together with the properties from step 1. No
   integrality, smoothness, projectivity or faithfulness of X was assumed; the
   argument is independent of the characteristic. -/
theorem exists_sumihiro_invariant_quasiprojective_open
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : Grp (Over (Spec (.of k))))
    [Smooth G.X.hom] [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [ConnectedSpace G.X.left]
    (X : CategoryTheory.Mod (Over (Spec (.of k))) G.X)
    [IsSeparated X.X.hom] [LocallyOfFiniteType X.X.hom] [QuasiCompact X.X.hom]
    (hnormal : ∀ p : X.X.left,
      IsDomain (X.X.left.presheaf.stalk p) ∧
        IsIntegrallyClosed (X.X.left.presheaf.stalk p))
    (x : X.X.left) :
    ∃ (W : CategoryTheory.Mod (Over (Spec (.of k))) G.X) (i : W ⟶ X),
      IsOpenImmersion i.hom.left ∧ x ∈ Set.range i.hom.left ∧
      (∀ p : W.X.left, IsDomain (W.X.left.presheaf.stalk p) ∧
        IsIntegrallyClosed (W.X.left.presheaf.stalk p)) ∧
      IsSeparated W.X.hom ∧ LocallyOfFiniteType W.X.hom ∧ QuasiCompact W.X.hom ∧
      ∃ (n : ℕ)
        (j : W.X.left ⟶ Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (n + 1))) k),
        IsImmersion j ∧
          j ≫ Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (n + 1))) k =
            W.X.hom := by
  sorry

end AlgebraicGeometry
