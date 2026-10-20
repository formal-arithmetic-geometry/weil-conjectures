/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.AlgebraicGeometry.SfFullCohomologicalDimension
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.EtaleDirectImageVanishing
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.Paper.FiniteLevelProEtaleBaseChange
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.Paper.RingedEtaleOriginWitness
import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness

/-!
# Uniform higher-direct-image vanishing for sheaves of etale origin

Source: Weil blueprint, sec-six-functors-basics/sk-prop-sf-fullcd-etale-origin,
main-20261015, with the reviewed arbitrary-base-change repair in the DAG;
Stacks Project, Tags 095T, 099V and 04JC (blueprint: thm-sf-fullcd-etale-origin).

Both clauses concern the specified sheaf on the original source. The second clause
allows every scheme over the target, without finite-type or dimension conditions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Higher direct images vanish above twice the dimension of the original source,
for the given etale-origin sheaf and all of its scheme pullbacks. The origin witness
uses the canonical fixed-scalar realization over the intrinsic constant ring sheaf.
Source: Weil blueprint, main-20261015, sk-prop-sf-fullcd-etale-origin, and its
reviewed DAG proof; Stacks Tags 095T, 099V and 04JC
(blueprint: thm-sf-fullcd-etale-origin).

Proof:
1. The coefficient quotient is finite by def-weil-l-adic-coefficient-extension.
The extended absolute value gives |l| = 1/l < 1, so l lies in the maximal ideal
and l^n kills A. Since l differs from the characteristic, l^n is invertible in k.
Properness gives finite type and separatedness, hence qcqs by
lem-pc-separated-quasi-separated.
2. Apply lem-sf-etale-direct-image-vanishing to G on the original finite-type
schemes, obtaining the bound 2d. Apply prop-weil-pbc-comparison-direct-image to
G[0] and p. By lem-sf-comparison-pullback-exact, comparison inverse image is exact
and commutes with cohomology. The given isomorphism identifies its image with F,
so the absolute clause follows. No constructibility condition is needed.
3. For arbitrary v:V -> Y, lem-weil-pbc-comparison-pullback identifies the
pullback of F with the comparison pullback of the etale inverse image of G.
The pair (G[0], inverse of the given isomorphism in degree zero) is the witness
of def-weil-pbc-etale-origin-witness. Apply thm-weil-pbc-finite-level-proetale
to p and the canonical cartesian square. This gives v* Rp_* F isomorphic to
R(p_V)_* g_V* F. Constant-coefficient inverse image is exact by
prop-weil-pbc-proetale-constant-exact; apply
lem-weil-pbc-exact-functor-complex-cohomology and the absolute vanishing.
Thus every degree above 2d vanishes after this base change. This argument does
not bound the dimension of V or of the base-changed source.
4. Specialize the second clause to every pro-etale site object, or every etale
Y-scheme. Together with the first clause this is precisely the two clauses of
def-weil-full-cohomological-dimension restricted to original-source sheaves
of etale origin; it makes no assertion about arbitrary pro-etale sheaves. -/
theorem sfFullcdEtaleOrigin
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (_hn : 1 ≤ n) (d : ℕ)
    (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (p : X ⟶ Y) [p.IsOver (Spec (CommRingCat.of D.k))] [IsProper p]
    (F : proEtaleRingModules X (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n)))
    (G : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))))
    (_e : F ≅ (ProEtale.finiteCoefficientIntrinsicComparison X
      (Padic.coefficientExtensionRing l E n)).obj G) :
    (∀ (r : ℤ), (2 * d : ℤ) < r →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj
        ((proEtaleConstantDerivedDirectImage p (Padic.coefficientExtensionRing l E n)).obj
          ((DerivedCategory.singleFunctor _ 0).obj F)))) ∧
    ∀ (V : Scheme.{u}) (v : V ⟶ Y) (r : ℤ), (2 * d : ℤ) < r →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj
        ((proEtaleConstantDerivedDirectImage (pullback.snd p v)
          (Padic.coefficientExtensionRing l E n)).obj
            ((DerivedCategory.singleFunctor _ 0).obj
              (proEtaleConstantModulePullback (pullback.fst p v)
                (Padic.coefficientExtensionRing l E n) F)))) := by
  sorry

end AlgebraicGeometry.Scheme
