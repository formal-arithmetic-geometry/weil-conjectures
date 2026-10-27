module

public import Sheaf.AlgebraicGeometry.GeometricPicardQuotient
public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Local rational lifting of generic semiabelian Picard classes

Source: Raynaud, Faisceaux amples, XI Theorem 1.13, Picard-class supporting input;
Moret-Bailly, Pinceaux de varietes abeliennes, II 3.6, via diagonal pullback.
The quotient formulation is agent-written, not a transcription of Raynaud's theorem.
(blueprint: lem-sfb-semiabelian-generic-picard-class-lifting)

Multiplication in the Picard quotient denotes tensor product. The factorization
through the open is constrained to be the canonical generic-point map; it is unique
because an open immersion is a monomorphism. The positive-multiple conclusion is
also the elementwise meaning of torsion cokernel for the union of local images.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

/-- Every geometric generic Picard class has a positive multiple represented by an
invertible module on the restriction to an affine neighbourhood of any base point.
No symmetry or positivity is assumed, and equality holds only in the quotient.

Source: Raynaud XI 1.13 (supporting input, agent quotient formulation), and
Moret-Bailly II 3.6; proof assembled from the DAG's two biextension inputs.
(blueprint: lem-sfb-semiabelian-generic-picard-class-lifting)

Proof plan:
1. Represent the class by L and rigidify its identity fibre with a basis. By
   lem-sfb-semiabelian-second-difference-diagonal, its second difference is a
   biextension D whose diagonal class is twice the given class. The generic
   fibre satisfies the geometric hypothesis. Smooth base change
   (lem-pc-proper-base-change), separated base change
   (lem-weil-pbc-separated-base-change), and finite-presentation base change
   (lem-weil-pbc-qcqs-morphism-permanence) give the required field hypotheses.
2. Apply lem-sfb-normal-semiabelian-biextension-extension to (G,G), extending D
   to a biextension E on G times G with its laws and generic isomorphism.
3. Pull E back along the diagonal. By lem-weil-pbc-invertible-pullback-tensor,
   the result N is invertible and its generic restriction is the diagonal
   pullback of D. Restrict N to an affine neighbourhood W of s and use n = 2.
   The union of the local images is a subgroup: restrict two lines to a common
   affine neighbourhood inside the intersection, tensor them, and use duals
   for inverses. Every cokernel class is killed by 2, hence the cokernel is
   torsion. Conversely, torsion says that every class has a positive multiple
   in one of those images. -/
theorem semiabelian_generic_picard_class_lifting
    {S : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (G : Grp (Over S)) [IsCommMonObj G.X]
    [Smooth G.X.hom] [IsSeparated G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    (hG : HasSemiabelianGeometricFibres G) (s : S)
    (α : Scheme.Pic.GeometricQuotient
      (Over.mk (pullback.snd G.X.hom (S.fromSpecResidueField (genericPoint S))))) :
    ∃ W : S.Opens, s ∈ W ∧ IsAffineOpen W ∧
      ∃ (a : Spec (S.residueField (genericPoint S)) ⟶ W.toScheme)
        (ha : a ≫ W.ι = S.fromSpecResidueField (genericPoint S))
        (n : ℕ), 0 < n ∧
        ∃ (M : (pullback G.X.hom W.ι).Modules) (hM : M.IsInvertible),
          Scheme.Pic.geometricClass
            (Over.mk (pullback.snd G.X.hom (S.fromSpecResidueField (genericPoint S))))
            (Scheme.Pic.map (baseChangeMap G.X.hom
              (Over.homMk (U := Over.mk (S.fromSpecResidueField (genericPoint S)))
                (V := Over.mk W.ι) a ha))
              (@Scheme.Pic.ofIsInvertible _ M hM)) = α ^ n := by
  sorry

end AlgebraicGeometry
