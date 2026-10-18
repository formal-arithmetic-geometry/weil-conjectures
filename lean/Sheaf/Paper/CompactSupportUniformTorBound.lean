/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Paper.SmoothPurityTowerShriekLevels
public import Sheaf.Paper.ProjectionCompactification
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.ConstantModelTorAmplitude
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.AlgebraicGeometry.EtaleCompactSupportAmplitude
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Sheaf.AlgebraicGeometry.ProperBoundedConstructible
import Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula
import Sheaf.AlgebraicGeometry.GeometricStalkAsPullback
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.Paper.SmoothPurityCoefficientTowers
import WeilConjectures.Compactification.NagataCompactification
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Uniform Tor bounds for compact supports

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower-bound,
`sk-lem-sp-tower-bound-uniform.md`; Stacks Project, Tag 0F10
(blueprint: det-sp-tower-bound-uniform).

Finite coefficients use the recorded ordinary ringed pro-etale derived category.
The second clause uses the existing strict semilinear sequence-site presentation of
coefficient towers. Its natural index n denotes the positive exponent n+1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Compact support preserves finite-Tor constructibility and enlarges the upper Tor
bound by twice the dimension of the original geometric fibres, uniformly in coefficients.
The tower assertion concerns every ordinary derived tower with the stated common interval;
its operations are the normalized geometric operations of det-sp-tower-shriek-levels.
It does not assume that the tower is normalized.

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower-bound,
`sk-lem-sp-tower-bound-uniform.md`; Stacks Project, Tag 0F10
(blueprint: det-sp-tower-bound-uniform).

Proof, following the node's seven steps:
1. A finite ring is Noetherian. Apply det-pe-finite-tor-comparison-noetherian to obtain
an etale bounded constructible representative with the same Tor interval. The schemes
are Noetherian and quasi-separated by lem-weil-pbc-finite-type-over-noetherian and
lem-weil-pbc-locally-noetherian-quasi-separated. Choose the Nagata compactification;
its proper middle scheme is finite type over k, and its open immersion is quasi-compact
by lemma-nagata-open-immersion-qc-over-separated-target. Use the compact-support candidate
of def-amb-etale-compact-support.
2. Exact extension by zero preserves constructibility (lem-weil-pbc-extension-by-zero-exact,
lem-fin-extension-by-zero). Proper bounded constructible direct image
(lem-fin-proper-bounded-constructible) and lem-amb-etale-compact-comparisons therefore
make the compact-support output bounded constructible, independently of the numerical bound.
3. By lem-sf-etale-flat-model choose a flat representative supported in [a,b]; it is
K-flat by lem-pc-bounded-above-flat-kflat-site. For ANY degree-zero module N on Y,
exact inverse image places its pullback in degree zero. The K-flat definition of tensor
(def-kun-derived-tensor) puts the tensor with this representative in [a,b].
4. The open projection comparison is an isomorphism on geometric stalks: it is the
identity on the open and zero off it (lem-kun-stalk-as-pullback,
lem-cbc-extension-zero-base-change, lem-pod-etale-stalk-tensor-scalar,
lemma-weil-pbc-geometric-stalk-conservative). Extend this identity to the bounded flat
representative by finite signed totalization. Exact open extension and exact restriction
show that its extension is K-flat. Apply lem-kun-0f0g to the proper factor and arbitrary
N to identify H(M) tensor^L N with H(M tensor^L f^-1 N), for H = Rp_* j_!.
5. lem-dg-compact-support-amplitude bounds H of ANY sheaf above by 2d. Negative degrees
vanish using lem-weil-pbc-dplus-injective-representative. The finite good-truncation
triangles from def-sbc-standard-tstructure-derived-category, exact/derived triangulatedness
and lem-sf-derived-homology-long-exact then put H of a complex with cohomology in [a,b]
in [a,b+2d]. Apply this to the tensor in step 3 and use step 4. Since N was arbitrary,
this is the asserted Tor bound. Only the original fibres, not compactified fibres, enter d.
6. lem-cbc-proetale-extension-zero-comparison and prop-weil-pbc-comparison-direct-image
identify the pro-etale compact-support output with the comparison of the etale output.
The latter is bounded below, as required. Transport bounded constructibility and the exact
Tor interval back by det-pe-finite-tor-comparison-noetherian. No geometric-stalk test on
arbitrary pro-etale sheaves is used.
7. Write ell = unit times uniformizer^e using def-weil-l-adic-coefficient-extension.
Then O_E/ell^n is the finite positive coefficient quotient A_(E,en), killed by ell^n.
Apply the finite-ring assertion at every positive level with the SAME a,b,d.
Levelwise kernels and cokernels (sk-def-sp-coefficient-towers) show that the input tower
is bounded below. Clause (1) of det-sp-tower-shriek-levels identifies its output levels
with these finite compact-support images. Testing Tor amplitude with the coefficient
ring itself yields cohomology vanishing outside [a,b+2d]. No compatibility of newly
chosen projection maps is claimed. -/
theorem compactSupport_uniform_tor_bound
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] (k : Type u) [Field k] [CharP k p]
    (_hlp : l ≠ p)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) [QuasiCompact c.i] (d : ℕ)
    (_hd : ∀ y : Y, topologicalKrullDim
      (↑(pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y))) ≤ (d : WithBot ℕ∞))
    (a b : ℤ) (_hab : a ≤ b) :
    (∀ (A : Type u) [CommRing A] [Finite A],
      (∃ r : ℕ, 0 < r ∧ (l : A) ^ r = 0) →
      ∀ M : proEtaleDerivedCategory X A,
        spFiniteConstructibleTor X A M → HasProEtaleTorAmplitude X A M a b →
        spFiniteConstructibleTor Y A
          ((proEtaleRingCompactSupportImage c
            (proEtaleConstantRing Y A) (proEtaleConstantRing c.Z A)
            (proEtaleConstantRing X A) (proEtaleConstantRingComparison c.g A)
            (proEtaleConstantRingComparison c.i A)).obj M) ∧
        HasProEtaleTorAmplitude Y A
          ((proEtaleRingCompactSupportImage c
            (proEtaleConstantRing Y A) (proEtaleConstantRing c.Z A)
            (proEtaleConstantRing X A) (proEtaleConstantRingComparison c.g A)
            (proEtaleConstantRingComparison c.i A)).obj M) a (b + 2 * (d : ℤ))) ∧
    (∀ (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
      (base : SpTowerShriek.Base l E) (ops : SpTowerShriek.Operations l E base)
      (C : SpTowerShriek.D l E X),
      (∀ n : ℕ, spFiniteConstructibleTor X (SpTowerShriek.R l E n)
        ((SpTowerShriek.Ev l E X n).obj C) ∧
        HasProEtaleTorAmplitude X (SpTowerShriek.R l E n)
          ((SpTowerShriek.Ev l E X n).obj C) a b) →
      ∀ n : ℕ,
        HasProEtaleTorAmplitude Y (SpTowerShriek.R l E n)
          ((SpTowerShriek.Ev l E Y n).obj ((SpTowerShriek.F l E base ops c).obj C))
          a (b + 2 * (d : ℤ)) ∧
        ∀ q : ℤ, (q < a ∨ b + 2 * (d : ℤ) < q) →
          IsZero ((@DerivedCategory.homologyFunctor
            (proEtaleRingModules Y (proEtaleConstantRing Y (SpTowerShriek.R l E n)))
            _ _ (HasDerivedCategory.standard _) q).obj
            ((SpTowerShriek.Ev l E Y n).obj ((SpTowerShriek.F l E base ops c).obj C)))) := by
  sorry

end AlgebraicGeometry.ProEtale
