/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Algebra.Homology.DerivedTensor
import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage
import Sheaf.CategoryTheory.RingedSiteModules
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.ConstructibleSheaf.Refinement
import Sheaf.Paper.LocallyConstantTensor
import Sheaf.Paper.RingedTopoiCanonicalTensorPullback
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.Paper.ProEtaleConstructibleSheaf

/-!
# Constructible cohomology of finite-coefficient derived tensors

Source: Stacks Project, Pro-etale Cohomology, Tag 09BQ, lemma-tensor-c
(blueprint: lem-pur-finite-tensor-constructible-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Every cohomology sheaf of the derived tensor of bounded constructible
finite-torsion inputs is constructible. The tensor is computed on arbitrary
representatives by the recorded K-flat resolution; no lower bound is asserted.

Source: Stacks Project, Pro-etale Cohomology, Tag 09BQ, lemma-tensor-c
(blueprint: lem-pur-finite-tensor-constructible-cohomology).

Proof:
1. The spectral absolute value is nonarchimedean, the integer ring is a DVR
with finite residue field, and the chosen uniformizer generates the maximal ideal
(lem-weil-l-adic-extension-absolute-value, lem-weil-l-adic-extension-integers-dvr).
The finite quotient lemma (lem-weil-valued-dvr-finite-quotients) makes the coefficient
ring finite and Noetherian. Finite type modules over it have finite underlying sets.
2. The two inputs have only finitely many nonzero cohomology sheaves. Refine their
finite constructible stratifications by successive intersections
(lem-weil-pbc-constructible-stratification-intersection). Inverse image preserves
constant local models and pulls back their covers (def-weil-proetale-inverse-image).
The resulting one finite partition trivializes all input cohomology sheaves.
For zero inputs use the trivial partition; on the empty scheme keep its empty stratum.
3. Restriction to each stratum with the canonical constant-coefficient identification
is exact (lem-weil-pbc-site-pullback-abelian-exact and
 def-weil-sheaf-of-modules-category). It commutes with cohomology and derived tensor
(lem-weil-pbc-ringed-topoi-derived-tensor-pullback), using the small-site universe
convention of def-weil-pbc-proetale-site and def-weil-pbc-proetale-operations.
4. Apply lem-weil-pbc-locally-constant-tensor on every stratum to the bounded-above
restricted inputs over the Noetherian coefficient ring. Each output cohomology
sheaf is locally constant of finite type and thus has finite stalks.
5. For each integer i, the same finite partition now witnesses constructibility
of the tensor's i-th cohomology by def-weil-proetale-constructible-sheaf.
There is no finite Tor dimension assumption and no lower cohomological bound.
-/
theorem finiteTensor_constructible_cohomology
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.residueField x)]
    (K L P : CochainComplex (proEtaleRingModules T
      (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n))) ℤ)
    (f : P ⟶ K) (hf : QuasiIso f)
    (hP : CochainComplex.IsKFlat
      (R := proEtaleConstantRing T (Padic.coefficientExtensionRing l E n)) P)
    (hK : intrinsicFiniteTorsionConstructible l E n hn T (DerivedCategory.Q.obj K))
    (hL : intrinsicFiniteTorsionConstructible l E n hn T (DerivedCategory.Q.obj L))
    (i : ℤ) :
    @IsConstructibleProEtaleModuleSheaf T (Padic.coefficientExtensionRing l E n) _
      (Padic.finite_coefficientExtensionRing l E n hn)
      ((DerivedCategory.homologyFunctor (proEtaleRingModules T
        (proEtaleConstantRing T (Padic.coefficientExtensionRing l E n))) i).obj
          (derivedTensor T (Padic.coefficientExtensionRing l E n) K L P f hf hP)) := by
  sorry

end AlgebraicGeometry.Scheme
