/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q130
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Defs.Filter
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Cohomology.QuasicoherentExtension
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.AlgebraicGeometry.AffinePushforwardResolutionQuasiIso

/-! # Quasi-coherent complex models on quasi-compact separated schemes

Source: Stacks Project, perfect.tex, Tag 08DB
(proposition-quasi-compact-affine-diagonal), specialized to separated schemes;
Tag 0BQR (lemma-nonzero-some-cohomology), first paragraph of proof.
(blueprint: lem-sfb-qc-separated-quasicoherent-complex-model)
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry

/-- Every unbounded derived object with quasi-coherent cohomology on a quasi-compact
separated scheme has a representative whose terms are quasi-coherent.
Source: Stacks Project, perfect.tex, Tag 08DB, essential surjectivity, and Tag 0BQR,
first paragraph of proof.
(blueprint: lem-sfb-qc-separated-quasicoherent-complex-model)

Proof:
1. For every scheme T, the full category of quasi-coherent modules is abelian with
   exact inclusion: use lem-weil-pbc-quasi-coherent-module-kernel,
   lem-weil-pbc-quasi-coherent-module-cokernel-image, and
   lem-weil-pbc-quasi-coherent-module-direct-sum. Its zero is the associated zero
   module (lem-weil-pbc-spec-module-tilde-sections). Cohomology is computed by the
   same kernels and cokernels, so lem-weil-pbc-exact-functor-derived-factorization
   gives I_T : D(QCoh(T)) → D_QCoh(O_T), identifying localized complexes with their
   underlying sheaf complexes (def-weil-sheaf-of-modules-category).
2. The diagonal is a closed immersion. The quotient-ring description of
   def-weil-closed-immersion and spectrum compactness
   (lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact) make it quasi-compact;
   thus X is quasi-separated (def-weil-quasi-separated-morphism). Each affine open
   inclusion j : U → X is affine by
   lem-weil-pbc-affine-source-separated-target-affine-morphism.
3. For such j, lem-pc-affine-morphism-hi gives quasi-coherence of j_*A. On an affine
   open V of X its inverse image W is affine (pqf-def-affine-morphism). The affine
   section clause of lem-weil-pbc-quasi-coherent-module-cokernel-image gives
   exactness of sections on W, hence exactness of j_* on QCoh. By
   lem-weil-pbc-exact-functor-derived-functor its unbounded right derived functor
   Phi_j is the termwise functor, with invertible unit.
4. Choose a functorial ambient K-injective resolution s : F → J using
   prop-pur-kinjective-resolutions-exist. By
   lem-pc-affine-pushforward-resolution-quasi-iso, j_*s is a quasi-isomorphism for
   every complex F of quasi-coherent modules. The left side represents I_X Phi_j(QF);
   the right side represents Rj_* I_U(QF) by
   def-pc-ringed-spaces-derived-direct-image. Compose the termwise identification
   with Q(j_*s). This is the natural invertible derived comparison, and its
   composite with I_X of the unit is the canonical map Q(j_*F) → Rj_*(QF).
5. Apply lem-sfb-affine-open-derived-qcoh-criterion, using quasi-compactness,
   quasi-separatedness and the three hypotheses verified in steps 3 and 4. Thus
   I_X is an equivalence. Lift K along I_X and represent that lift by an arbitrary
   integer-indexed complex in QCoh(X) (def-weil-abstract-derived-category).
   The underlying sheaf complex F has quasi-coherent terms, and the factorization
   in step 1 gives Q(F) ≅ K. No construction imposes a boundedness condition. -/
theorem exists_quasicoherent_complex_of_compactSpace_of_isSeparated
    (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K) :
    ∃ F : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
      (∀ i : ℤ, (F.X i).IsQuasicoherent) ∧ Nonempty (DerivedCategory.Q.obj F ≅ K) := by
  sorry

end AlgebraicGeometry
