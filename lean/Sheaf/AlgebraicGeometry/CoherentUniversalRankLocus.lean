/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.FittingIdealGenerateLocally
import Sheaf.AlgebraicGeometry.FittingIdealSheaf
import Sheaf.RingTheory.PresentationFittingIdeal
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.FinitePresentationOfFiniteLocallyNoetherian
import Mathlib.RingTheory.LocalRing.Module

/-! # The universal fixed-rank stratum of a coherent sheaf

Source: Stacks Project, Divisors, Tags 05P8(2),(3), 0C3F; More on Algebra,
Tags 07ZC and 07ZD (blueprint: lem-sfb-coherent-universal-rank-locus).

The test schemes are arbitrary, including non-Noetherian and nonreduced schemes.
The ideal sheaf's canonical subscheme supplies the closed immersion into the open locus.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The fibre-dimension bound is open, and within that open a closed subscheme
universally represents rank-`r` local freeness of arbitrary ordinary pullbacks.
Both inclusions into `S` are of finite presentation in the full Stacks 01TP sense.
Source: Stacks Project, Divisors, Tags 05P8(2),(3), 0C3F; More on Algebra,
Tags 07ZC and 07ZD (blueprint: lem-sfb-coherent-universal-rank-locus).

Proof plan (the nine steps of the node):
1. By pqf-lem-coherent-ft-locnoeth, F is quasi-coherent of finite type.
   Its stalks are finite. Nakayama (lem-weil-pbc-nakayama-local-generators)
   identifies the residue-dimension bound with generation by at most r elements.
   By lem-trf-fitting-ideal-generate-locally(2), this is precisely the complement W
   of the support of the r-th Fitting ideal, hence is open.
2. For r > 0 restrict Fit_{r-1}(F) to W; for r = 0 use the zero ideal.
   This quasi-coherent ideal has the canonical closed subscheme C by
   lem-weil-pbc-quasi-coherent-ideal-closed-subscheme. Its affine charts are
   Spec(A/I(U)). For r = 0, F restricted to W is zero and C = W.
3. On affine charts of W choose r generators, padding with zeros. By
   lem-weil-pbc-quasi-coherent-finite-type-affine and the affine tilde adjunction,
   they give A^r onto M. For an arbitrary map Spec B to this chart, the tilde
   pullback/base-change theorem identifies the pulled-back module with B tensor M.
   Presentation Fitting-ideal base change identifies Fit_{r-1} with I(U)B.
4. If this pullback is free of rank r, compute its Fitting ideal using the identity
   presentation of B^r. Its kernel is zero, so its 1-minors vanish. Presentation
   independence shows I(U)B = 0. This is local on the source.
5. Conversely, if I(U)B = 0, every coordinate of every element of the kernel of
   B^r onto B tensor M is a vanishing 1-minor. Thus the kernel is zero and the
   quotient is free of rank r. The rank-zero case follows from F restricted to W = 0.
6. For arbitrary g, local freeness first forces the unique factorization through W
   by lem-trf-fitting-ideal-generate-locally and open-immersion monomorphy.
   Steps 4-5 and lem-weil-pbc-closed-immersion-lift-ideal-kills-sections give the
   factorization through C. Quotient ring maps uniquely determine its affine lifts,
   which glue. Conversely such a lift kills the ideal, so step 5 applies.
7. Noetherian opens are quasi-compact. Hence W to S is quasi-compact, of finite
   type, and locally of finite presentation over the locally Noetherian S.
   Its diagonal is an isomorphism since it is a monomorphism, so it is quasi-separated.
8. C to W is finite and W is locally Noetherian, so pqf-lem-finite-fp-locnoeth
   gives finite presentation. Composition gives local finite presentation of C to S.
   Its inverse images of affine opens are closed in the quasi-compact opens from
   step 7, so it is quasi-compact. It is a monomorphism, so is quasi-separated.
9. If all fibre dimensions are bounded by r, W is the whole of S and the
   composite C to S is a closed immersion. All steps include empty schemes,
   the zero module, and arbitrary nonflat, non-Noetherian test schemes.
-/
theorem exists_coherentUniversalRankLocus (S : Scheme.{u})
    [IsLocallyNoetherian S] [CompactSpace S] (F : S.Modules)
    (hF : RingedSpace.IsCoherent S.toRingedSpace F) (r : ℕ) :
    ∃ W : S.Opens,
      (∀ s : S, s ∈ W ↔
        Module.finrank (S.residueField s)
          ((ModuleCat.extendScalars (S.residue s).hom).obj
            ((RingedSpace.moduleStalkFunctor S.toRingedSpace s).obj F)) ≤ r) ∧
      ∃ I : W.toScheme.IdealSheafData,
        (∀ (T : Scheme.{u}) (g : T ⟶ S),
          ((tensorPullback g).obj F).IsFiniteLocallyFreeOfRank r ↔
            ∃! h : T ⟶ I.subscheme, h ≫ I.subschemeι ≫ W.ι = g) ∧
        LocallyOfFinitePresentation W.ι ∧ QuasiCompact W.ι ∧ QuasiSeparated W.ι ∧
        LocallyOfFinitePresentation (I.subschemeι ≫ W.ι) ∧
        QuasiCompact (I.subschemeι ≫ W.ι) ∧ QuasiSeparated (I.subschemeι ≫ W.ι) ∧
        ((∀ s : S, Module.finrank (S.residueField s)
          ((ModuleCat.extendScalars (S.residue s).hom).obj
            ((RingedSpace.moduleStalkFunctor S.toRingedSpace s).obj F)) ≤ r) →
          IsClosedImmersion (I.subschemeι ≫ W.ι)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
