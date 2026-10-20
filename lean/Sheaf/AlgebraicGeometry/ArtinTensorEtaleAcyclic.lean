/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.AlgebraicGeometry.EtaleAcyclic
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.RingTheory.TensorProduct.Basic
public import WeilConjectures.RingTheory.ProEtale.IndEtale
import Sheaf.AlgebraicGeometry.ArtinHenselianTensorResidueDichotomy
import Sheaf.AlgebraicGeometry.KInjectiveResolutions
import Sheaf.RingTheory.IndEtaleUniverseTransport
import Sheaf.TraceFormula.AffineEtaleCoverComponentCriterion
import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# Artin tensor étale acyclicity

Source: Hübner–Schmidt, Definition 7.8, Proposition 7.9 and Theorem 7.10, étale case
(blueprint: lem-trf-artin-tensor-etale-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped TensorProduct

/-- The tensor product of two ind-étale algebras whose spectra are étale-acyclic is
étale-acyclic for torsion abelian sheaves.
Source: Hübner–Schmidt, Definition 7.8, Proposition 7.9 and Theorem 7.10, étale case
(blueprint: lem-trf-artin-tensor-etale-acyclic).

Proof (from the node):
1. By `lem-trf-affine-etale-cover-component-criterion`, the split-cover hypothesis makes
   every component ring `B_j / I_Z` strictly henselian local. Every maximal residue field
   `B_j / n` is separably closed: `n` lies on a component `Z`, `I_Z ⊆ n`, and `n / I_Z` is the
   maximal ideal of the local ring `B_j / I_Z`, with residue field `B_j / n`.
2. Put `B = B₁ ⊗[R] B₂`. By `lem-trf-artin-henselian-tensor-residue-dichotomy` (Hübner–Schmidt
   Theorem 6.4) every component ring of `B` is henselian local, and for each maximal `m ⊂ B`
   either `B / m` is separably closed or it is a separable algebraic extension of some
   `B_j / n` with `n` maximal.
3. In the second case `B_j / n` is separably closed by step 1, so the separable algebraic
   extension `B / m` equals it. Hence every maximal residue field of `B` is separably closed,
   every component ring of `B` is strictly henselian, and by
   `lem-trf-affine-etale-cover-component-criterion` every étale covering of `T = Spec B` has
   a section after disjoint union.
4. `Γ(T, -)` is exact: given an epimorphism `G → H` and `h ∈ H(T)`, lift `h` locally on an
   étale covering `{U_a → T}` (`lem-weil-pbc-abelian-sheaf-epi-locally-surjective`), pull the
   lifts back along a section `s` of `∐ U_a → T` to the disjoint clopen pieces
   `T_a = s⁻¹(U_a)`, and glue them by the sheaf condition; kernels are computed sectionwise.
5. For a K-injective resolution `F → I•`, `H^q(T_et, F) = H^q(Γ(T, I•)) ≅ Γ(T, H^q(I•)) = 0`
   for `q > 0` by `lem-weil-pbc-exact-functor-complex-cohomology`. Torsion is not used; the
   case `B = 0` (empty `T`) is included. -/
theorem artin_tensor_etale_acyclic
    (R B₁ B₂ : Type u)
    [CommRing R] [CommRing B₁] [CommRing B₂]
    [Algebra R B₁] [Algebra R B₂]
    [Algebra.IndEtale R B₁] [Algebra.IndEtale R B₂]
    (h₁ : Scheme.IsEtaleAcyclic (Spec (.of B₁)))
    (h₂ : Scheme.IsEtaleAcyclic (Spec (.of B₂))) :
    ∀ (F : Sheaf
        (Scheme.smallEtaleTopology (Spec (.of (B₁ ⊗[R] B₂))))
        AddCommGrpCat.{u + 1}),
      AlgebraicGeometry.Scheme.IsTorsionAbelianSheaf F →
      ∀ (q : ℤ), 0 < q →
        IsZero
          ((AlgebraicGeometry.Etale.cohomology AddCommGrpCat.{u + 1}
            (Spec (.of (B₁ ⊗[R] B₂))) q).obj
            ((DerivedCategory.singleFunctor
              (Sheaf (Scheme.smallEtaleTopology
                (Spec (.of (B₁ ⊗[R] B₂)))) AddCommGrpCat.{u + 1}) 0).obj F)) := by
  sorry
