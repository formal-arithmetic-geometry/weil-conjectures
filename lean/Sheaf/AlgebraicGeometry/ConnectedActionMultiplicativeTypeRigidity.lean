module

public import Sheaf.AlgebraicGeometry.DiagonalizableGroup
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Topology.Connected.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Connected actions on groups of multiplicative type

Source: Milne, Algebraic Groups (2017), Corollary 12.37, printed p.244,
following Theorem 12.36, pp.243--244
(blueprint: lem-sfb-connected-action-multiplicative-type-rigidity).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CartesianMonoidalCategory MonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A smooth connected affine group acts trivially by group automorphisms on an affine
finite-type group isomorphic to D(M) for a finitely generated abelian group M.
There is no smoothness or connectedness assumption on the group being acted on.
Source: Milne, Algebraic Groups (2017), Corollary 12.37, printed p.244
(blueprint: lem-sfb-connected-action-multiplicative-type-rigidity).

Proof:
1. Transport the action through the group-scheme isomorphism D ≅ D(M). Write
   G = Spec B using affineness. The affine product formula
   (lem-weil-pbc-fibre-product-affine-spectra) and the tensor-product universal property
   (lem-weil-pbc-algebra-tensor-pushout-universal-property) identify its coordinate map
   with α : F[M] → B[M], sending a character e_m to a finite sum ∑ b_v e_v.
2. The homomorphism hypothesis, evaluated on the universal G-point and the two universal
   D-points over B[M] ⊗_B B[M], gives Δ(α(e_m)) = α(e_m) ⊗ α(e_m). Evaluating at the
   identity D-point gives ε(α(e_m)) = 1. These are identities of functions, including
   nilpotents, rather than identities only on field-valued points.
3. Comparing the coefficients in the basis e_v ⊗ e_w gives b_v² = b_v,
   b_v b_w = 0 for v ≠ w, and ∑ b_v = 1. This applies to all torsion in M.
4. By lem-weil-pbc-spec-clopen-idempotent and connectedness of G, every b_v is 0 or 1.
   The identity section gives B → F, so B is nonzero. The sum and orthogonality show that
   exactly one coefficient is 1. Thus α(e_m) = e_ν(m) for a unique ν(m).
5. The action unit law gives (η ⊗ 1)α(e_m) = e_m. Independence of the group-algebra
   basis implies ν(m) = m. Hence α is the coordinate map of the second projection.
   The affine spectrum correspondence (def-weil-affine-spectrum) and transport back
   through D ≅ D(M) give the required equality, and therefore its evaluation on every
   commutative F-algebra. No reducedness assumption on D was used. -/
theorem connected_action_multiplicativeType_rigidity
    (F : Type u) [Field F] [IsAlgClosed F]
    (G D : Grp (Over (Spec (.of F))))
    [IsAffine G.X.left] [IsAffine D.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [LocallyOfFiniteType D.X.hom] [QuasiCompact D.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hD : ∃ (M : Type u) (_ : AddCommGroup M) (_ : AddGroup.FG M),
      Nonempty (D ≅ diagonalizableGroup F M))
    (a : ModObj G.X D.X)
    (hAut : ∀ (A : Type u) [CommRing A] [Algebra F A]
      (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F A))) ⟶ G.X),
      ∃ e :
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F A))) ⟶ D.X) ≃*
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F A))) ⟶ D.X),
        ∀ d : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F A))) ⟶ D.X,
          e d = lift g d ≫ a.smul) :
    a.smul = snd G.X D.X := by
  sorry

end AlgebraicGeometry
