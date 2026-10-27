module

public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

import WeilConjectures.AlgebraicGeometry.AmplePositiveTensorPower
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor

/-! # Raynaud prolongation of a symmetrized generic ample module

Source: Raynaud, Faisceaux amples, XI Theorem 1.13; Moret-Bailly,
Pinceaux de varietes abeliennes, II 3.3.3, printed p.53, opening paragraph.
The DAG records an agent-formulated power version; the Raynaud original is WANTED.
(blueprint: lem-sfb-raynaud-generic-ample-symmetrization)

The generic fibre is taken over the residue field of the canonical generic point.
Its map to each nonempty base restriction is specified by its composite with the
open immersion to G; this condition determines that map uniquely.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory MonObj

namespace AlgebraicGeometry

/-- A positive power of the symmetrization of a generic ample invertible module
extends to a relatively ample invertible module on an affine base open covering.
Normality is the integrally closed domain condition on every local ring. Separatedness
supplies quasi-separatedness, so local finite presentation and quasi-compactness
express finite presentation. No properness or extension of L itself is assumed.

Source: Raynaud, Faisceaux amples, XI Theorem 1.13; Moret-Bailly II 3.3.3,
printed p.53, opening paragraph; agent-formulated power version, original WANTED.
(blueprint: lem-sfb-raynaud-generic-ample-symmetrization)

Proof plan, following the four steps of the node:
1. For every s, apply lem-sfb-semiabelian-generic-picard-class-lifting to the class
   of L modulo geometric algebraic equivalence. It gives an affine neighbourhood W,
   n >= 1 and an invertible M on G_W with T = M_eta tensor (L^n)-dual geometrically
   algebraically trivial. These nonempty W cover S and contain its generic point.
2. By lem-sc-ample-positive-tensor-power, L^n is ample. Clause (ii) of
   lem-sfb-semiabelian-algebraic-equivalence-norm implies that M_eta = L^n tensor T
   is ample. The displayed isomorphism follows from tensor evaluation.
3. Set Q = M tensor inverse-pullback M. The invertibility and tensor/pullback rules
   are lem-weil-pbc-invertible-pullback-tensor. Inversion commutes with generic
   restriction. Reorder the generic factors to separate L^n tensor inverse-pullback
   L^n from T tensor inverse-pullback T. Clause (i) of
   lem-sfb-semiabelian-algebraic-equivalence-norm trivializes the latter. Distributing
   pullback over tensor powers identifies Q_eta with (L tensor inverse-pullback L)^n.
4. Apply lem-sfb-semiabelian-supplied-norm-ampleness to M on G_W, using the generic
   ampleness from step 2. It gives ampleness over every affine open of W. Take
   a = n and the comparison of step 3 for every member of the covering. -/
theorem raynaudGenericAmpleSymmetrization
    {S : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S]
    (hS : ∀ s : S, IsDomain (S.presheaf.stalk s) ∧
      IsIntegrallyClosed (S.presheaf.stalk s))
    (G : Grp (Over S)) [IsCommMonObj G.X]
    [Smooth G.X.hom] [IsSeparated G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom]
    (hG : HasSemiabelianGeometricFibres G)
    (L : ((Over.pullback (S.fromSpecResidueField (genericPoint S))).mapGrp.obj G).X.left.Modules)
    [L.IsInvertible]
    (hL : Scheme.Modules.IsAmple _ L) :
    ∃ (I : Type u) (W : I → S.Opens), (⨆ i, W i) = ⊤ ∧
      (∀ i, IsAffineOpen (W i)) ∧
      ∀ i, Nonempty (W i) →
        ∃ (a : ℕ), 1 ≤ a ∧
          ∃ (Q : (pullback G.X.hom (W i).ι).Modules), Q.IsInvertible ∧
            (∃ jη :
              ((Over.pullback (S.fromSpecResidueField (genericPoint S))).mapGrp.obj G).X.left ⟶
                pullback G.X.hom (W i).ι,
              jη ≫ pullback.fst G.X.hom (W i).ι =
                pullback.fst G.X.hom (S.fromSpecResidueField (genericPoint S)) ∧
              Nonempty ((Scheme.Modules.tensorPullback jη).obj Q ≅
                (L ⊗ (Scheme.Modules.tensorPullback
                  ι[((Over.pullback (S.fromSpecResidueField (genericPoint S))).mapGrp.obj
                    G).X].left).obj L).tensorPow a)) ∧
            ∀ V : (W i).toScheme.Opens, IsAffineOpen V →
              ∃ h : ((Scheme.Modules.tensorPullback
                ((pullback.snd G.X.hom (W i).ι) ⁻¹ᵁ V).ι).obj Q).IsInvertible,
                @Scheme.Modules.IsAmple
                  ((pullback.snd G.X.hom (W i).ι) ⁻¹ᵁ V).toScheme
                  ((Scheme.Modules.tensorPullback
                    ((pullback.snd G.X.hom (W i).ι) ⁻¹ᵁ V).ι).obj Q) h := by
  sorry

end AlgebraicGeometry
