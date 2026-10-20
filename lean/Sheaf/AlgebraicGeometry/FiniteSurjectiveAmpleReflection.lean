/-
Copyright (c) 2026 The SHEAF contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor

import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact
import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.AffinePushforwardIdealProduct
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import Sheaf.AlgebraicGeometry.CoherentPropertyDevissageIntegralSubschemes
import Sheaf.AlgebraicGeometry.CoherentSerreVanishing
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import Sheaf.Paper.FiniteSurjectiveCoherentGenericSupport
import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.AmplePullback
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.AlgebraicGeometry.PQFCohomology
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.TraceFormula.IdealTwistVanishingImpliesAmple

/-! # Finite surjective reflection of ampleness

Source: Stacks Project, `coherent.tex`, Tag 0B5V, `lemma-surjective-finite-morphism-ample`
(blueprint: lem-trf-finite-surjective-ample-reflection).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Ampleness of an invertible module is equivalent to ampleness after finite surjective
pullback between proper schemes over a Noetherian ring.

Source: Stacks Project, `coherent.tex`, Tag 0B5V, `lemma-surjective-finite-morphism-ample`.
(blueprint: lem-trf-finite-surjective-ample-reflection).

Proof (the DAG proof, in seven steps):

1. A finite morphism is affine by [def-weil-finite-integral-morphism]. Hence if $\mathcal L$ is
ample, [lem-weil-pbc-pullback-ample-invertible] applied to $f$ proves that $f^*\mathcal L$ is
ample. Pullback preserves the rank-one local trivializations: on $f^{-1}U$ a trivialization
$\mathcal L|_U\cong\mathcal O_U$ pulls back to $\mathcal O_{f^{-1}U}$ by the tensor-pullback
definition [def-pc-module-pullback]. Thus $f^*\mathcal L$ is invertible
[def-sc-invertible-module]. For the remaining steps assume it is ample.

2. Both $X$ and $Y$ are Noetherian. Indeed $\operatorname{Spec}R$ is locally Noetherian by its
single affine chart with ring $R$ [pqf-def-locnoeth], and is quasi-compact by
[lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact](iii). Properness includes finite type
[def-weil-proper-morphism], so [lem-weil-pbc-finite-type-over-noetherian] applies to each
structure morphism. In particular both schemes are locally Noetherian, as required by the
coherence and devissage statements below.

3. For a coherent module $\mathcal E$ on $X$, define $\mathcal P(\mathcal E)$ by eventual
vanishing of $H^p(X,\mathcal E\otimes\mathcal L^{\otimes n})$ for every $p>0$, with one bound
$n_0\ge0$ for all $p$. Cohomology is derived global sections [pqf-def-cohomology]; the module
category has enough injectives [lem-sc-ringed-space-module-sheaves-enough-injectives] and global
sections is additive and left exact [lem-sc-global-sections-left-exact]. Thus
[lem-weil-pbc-right-derived-universal-delta-functor] gives additive cohomology functors and long
exact sequences. The zero module has $\mathcal P$. Tensoring a short exact sequence by $\mathcal
L^{\otimes n}$ is exact: on a rank-one trivializing cover [def-sc-invertible-module] the tensor
functor [def-pur-sheaf-tensor-product] is the identity, so its stalk sequences are exact and
[lem-weil-pbc-module-stalk-exact](5) gives sheaf exactness. If the end terms have $\mathcal P$,
the segment $H^p(\mathcal E_1\otimes\mathcal L^{\otimes n})\to H^p(\mathcal E\otimes\mathcal
L^{\otimes n})\to H^p(\mathcal E_2\otimes\mathcal L^{\otimes n})$ gives vanishing after the
maximum of their two bounds. Finite sums are coherent
[lem-weil-pbc-coherent-modules-kernel-cokernel-sum](3). For $r\ge1$, $\mathcal E$ is a retract of
$\mathcal E^{\oplus r}$ using the first inclusion and projection; tensor and additive cohomology
preserve that retraction, so $\mathcal P(\mathcal E^{\oplus r})$ implies $\mathcal P(\mathcal E)$.
These are clauses (0), (1), (2) of devissage.

4. For an integral closed subscheme $i:Z\hookrightarrow X$ with generic point $\xi$,
[lem-weil-pbc-finite-surjective-coherent-generic-support] gives a coherent $\mathcal F$ on $Y$
such that $\mathcal G=f_*\mathcal F$ has support $i(Z)$ and $\mathfrak m_\xi\mathcal G_\xi=0$. The
finite-pushforward theorem [lem-weil-pbc-finite-pushforward-coherent] makes $\mathcal G$ coherent
on the locally Noetherian $X$. Let $\mathcal J\subseteq\mathcal O_X$ be quasi-coherent with
$\mathcal J_\xi=\mathcal O_{X,\xi}$. Coherent modules on locally Noetherian schemes are
quasi-coherent [pqf-lem-coherent-ft-locnoeth]. Apply
[lem-weil-pbc-affine-pushforward-ideal-product] to the affine $f$, $\mathcal F$, and $\mathcal J$.
Its clause (1) says that $\mathcal H:=f^{-1}\mathcal J\cdot\mathcal F$ is a quasi-coherent
submodule of $\mathcal F$, and its clause (2) gives the equality $\mathcal J\mathcal G=f_*\mathcal
H$ as submodules of $\mathcal G$. Since $Y$ is locally Noetherian,
[lem-weil-pbc-coherent-kernel-cokernel-locnoeth](2) gives coherence of $\mathcal H$; finite
coherent pushforward then gives coherence of $\mathcal J\mathcal G=f_*\mathcal H$. Thus both the
identity and coherence on $Y$ used below are supplied by cited statements.

5. For $n\ge0$ put $\mathcal N=\mathcal L^{\otimes n}$ (with $\mathcal N=\mathcal O_X$ for $n=0$).
It is invertible by its rank-one trivializations [def-sc-invertible-module]. The affine morphism
$f$ is quasi-compact and quasi-separated by [lem-weil-pbc-affine-morphism-permanence](3), so the
invertible-module clause of [lem-pc-projection-formula] applies to $E=\mathcal H[0]$ and $\mathcal
N$. Tensoring by $\mathcal N$ and by $f^*\mathcal N$ is exact by the same local identity argument
as Step 3, so the derived tensors here are ordinary tensors. The quasi-coherent tensor-product
theorem [lem-weil-pbc-quasi-coherent-tensor-product-affine-sections] applies to $\mathcal H$ and
$f^*\mathcal N$. Affine higher-direct-image vanishing
[lem-weil-pbc-affine-morphism-cohomology-edge] for $\mathcal H$ and $\mathcal H\otimes f^*\mathcal
N$ therefore turns the derived projection isomorphism, in degree zero, into $f_*\mathcal
H\otimes\mathcal N\cong f_*(\mathcal H\otimes f^*\mathcal N)$. Concretely this is the ordinary
projection map: on any open $U$ trivializing $\mathcal N$, both sides are $(f_*\mathcal H)|_U$ and
the map is the identity. This also proves compatibility on overlaps, since the projection map is
defined by multiplication by the pulled-back local section. By the tensor-pullback definition
[def-pc-module-pullback], $f^*(\mathcal L^{\otimes n})\cong(f^*\mathcal L)^{\otimes n}$: both are
trivial on $f^{-1}U$ and have the same pulled-back $n$-th-power transition functions.

6. Apply [lem-weil-pbc-affine-morphism-cohomology-edge] to the quasi-coherent $\mathcal
H\otimes(f^*\mathcal L)^{\otimes n}$ (quasi-coherence was checked in Step 5). Steps 4-5 give for
every $p,n\ge0$ the isomorphisms $H^p(X,\mathcal J\mathcal G\otimes\mathcal L^{\otimes n})\cong
H^p(X,f_*(\mathcal H\otimes(f^*\mathcal L)^{\otimes n}))\cong H^p(Y,\mathcal H\otimes(f^*\mathcal
L)^{\otimes n})$. The sheaf $\mathcal H$ is coherent by Step 4, $Y$ is proper over the Noetherian
ring $R$, and $f^*\mathcal L$ is invertible and ample. Consequently
[lem-weil-pbc-coherent-serre-vanishing] gives one $n_0$ for which the right side vanishes for all
$p>0$ and $n\ge n_0$. Hence $\mathcal P(\mathcal J\mathcal G)$ holds. By
[lem-weil-pbc-ideal-module-product-stalk](2), $(\mathcal J\mathcal G)_\xi=\mathcal J_\xi\mathcal
G_\xi=\mathcal G_\xi$, with the equality through its inclusion into $\mathcal G_\xi$. The coherent
submodule $\mathcal G'=\mathcal J\mathcal G$ thus verifies devissage clause (3)(c), while Step 4
verified (3)(a) and (3)(b).

7. The property $\mathcal P$ satisfies every hypothesis of
[lem-weil-pbc-coherent-property-devissage-integral-subschemes]: $X$ is Noetherian by Step 2,
clauses (0)-(2) hold by Step 3, and the coherent $\mathcal G$ and $\mathcal G'$ required by (3)
were verified in Steps 4-6. Hence $\mathcal P$ holds for every coherent module on $X$. In
particular it holds for every quasi-coherent ideal $\mathcal I\subseteq\mathcal O_X$: $\mathcal
O_X$ is quasi-coherent of finite type, hence coherent by [pqf-lem-coherent-ft-locnoeth], and
[lem-weil-pbc-coherent-kernel-cokernel-locnoeth](2) makes $\mathcal I$ coherent. Choose
$n\ge\max(1,n_0)$ for its bound; then $H^1(X,\mathcal I\otimes\mathcal L^{\otimes n})=0$. The
exact ideal-twist vanishing hypothesis of [lem-trf-ideal-twist-vanishing-implies-ample] is now
satisfied, so $\mathcal L$ is ample. Together with Step 1 this proves the stated equivalence.
-/
theorem isAmple_iff_tensorPullback_of_isFinite_surjective
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (X Y : Scheme.{u}) [X.Over (Spec (CommRingCat.of R))]
    [Y.Over (Spec (CommRingCat.of R))]
    [IsProper (X ↘ Spec (CommRingCat.of R))]
    [IsProper (Y ↘ Spec (CommRingCat.of R))]
    (f : Y ⟶ X) [f.IsOver (Spec (CommRingCat.of R))]
    [IsFinite f] [Surjective f]
    (L : X.Modules) [L.IsInvertible] :
    Scheme.Modules.IsAmple X L ↔
      @Scheme.Modules.IsAmple Y ((Scheme.Modules.tensorPullback f).obj L)
        ((Scheme.Modules.invertible_pullback_tensor f).1 L |>.2) := by
  sorry

end AlgebraicGeometry
