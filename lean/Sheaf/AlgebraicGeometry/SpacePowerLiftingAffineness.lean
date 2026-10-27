/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q81
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.StackQcqsMorphism
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentAlgebra
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Types.Basic
import Sheaf.AlgebraicGeometry.AlgebraicSpaceHigherDirectImageQuasiCoherent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineChartCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.ClosedSubsetQcIdeal
import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra
import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
import WeilConjectures.AlgebraicGeometry.QcqsCohomologyDirectSum
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Topology.Separation.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

/-! # Global power lifting detects affine algebraic spaces

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
Lemma 4.1.8(3) implies (2), printed pp. 502-504, and Theorem 4.3.1,
printed pp. 505-506 (blueprint: lem-sfb-space-power-lifting-affineness).

Global sections are compatible families over the small etale site. Surjectivity
means local surjectivity of the underlying ring sheaves. The base is an arbitrary
commutative ring, and the representing affine scheme retains its map to the base.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A qcqs algebraic space with positive-power lifts for every quotient of
quasi-coherent commutative algebra sheaves is represented by an affine scheme.
Source: Alper, Lemma 4.1.8(3) implies (2) and Theorem 4.3.1, printed pp. 502-506
(blueprint: lem-sfb-space-power-lifting-affineness).

Proof (the six steps of the DAG node):
1. Choose a finite surjective finitely presented scheme cover $p:Y\to Z$. Its source is qcqs by
   the cited finite-presentation source lemma. Given a surjection $\mathcal
   B\twoheadrightarrow\mathcal C$ of quasi-coherent algebras on $Y$, both $p_*\mathcal B$ and
   $p_*\mathcal C$ are quasi-coherent, by the degree-zero case of the higher-direct-image lemma.
   This pushforward is still surjective: on every affine etale chart $V\to Z$, the scheme
   $W=Y\times_ZV$ is affine by finiteness, and affine-chart sections compute cokernels, so
   $\mathcal B(W)\to\mathcal C(W)$ is surjective. The direct-image chart-limit definition
   identifies its value on $V$ with sections over $W$: a compatible family on all etale charts
   of $W$ is exactly a section by the sheaf gluing axiom. The same definition identifies global
   sections of $p_*\mathcal B$ and $p_*\mathcal C$ with those of $\mathcal B$ and $\mathcal C$.
   Apply the assumed property on $Z$ to these pushed-forward algebras. Thus $Y$ has the same
   global positive-power-lifting property.
   Uses: lem-sfb-qcqs-space-finite-scheme-cover, lem-sfb-space-fp-qcqs-source,
   lem-sfb-space-higher-direct-image-quasi-coherent, lem-sfb-space-qcoh-affine-chart-calculus,
   def-trf-space-etale-module-functors.

2. Use the Zariski-etale quasi-coherent equivalence to work on the scheme $Y$ with Zariski
   quasi-coherent algebras; restriction preserves global sections and the tensor-pullback
   description identifies algebra structures. Surjectivity is detected on affine charts, so the
   lifting property just obtained applies to these algebras. Put $A=\Gamma(Y,\mathcal O_Y)$. For
   a closed point $q\in Y$, choose an affine open $U$ containing $q$. Choose quasi-coherent
   ideals $\mathcal I,\mathcal J\subseteq\mathcal O_Y$ cutting out $Y\setminus U$ and $\{q\}$,
   respectively. Their vanishing sets are disjoint, so $\mathcal I+\mathcal J=\mathcal O_Y$: at
   every stalk one ideal is the unit ideal. Consequently the composite $\mathcal
   I\hookrightarrow\mathcal O_Y\twoheadrightarrow\mathcal O_Y/\mathcal J$ is surjective. Its
   target is quasi-coherent by affine-chart cokernel calculus. The induced map
   $\operatorname{Sym}(\mathcal I)\twoheadrightarrow\operatorname{Sym}(\mathcal O_Y/\mathcal J)$
   is a surjection of quasi-coherent algebras. Let $t$ be the global degree-one section given by
   $1$ modulo $\mathcal J$. Power lifting supplies $N>0$ and
   $s\in\Gamma(Y,\operatorname{Sym}(\mathcal I))$ mapping to $t^N$.
   Uses: lem-trf-scheme-zariski-etale-quasi-coherent-equivalence,
   lem-sfb-space-qcoh-affine-chart-calculus, lem-sc-closed-subset-qc-ideal,
   lem-weil-pbc-quasi-coherent-symmetric-algebra,
   lem-trf-symmetric-sheaf-map-degreewise-surjective.

3. Take the degree-$N$ component $s_N$ of $s$. This is a global section: on every affine open
   the symmetric algebra has its cited direct-sum grading, and the degree projections commute
   with restrictions, since restrictions send degree-one generators to degree-one generators.
   The same generator calculation shows that the symmetric-algebra map preserves degrees, hence
   $s_N$ maps to $t^N$. Evaluate $\operatorname{Sym}(\mathcal I)\to\mathcal O_Y$ via the
   inclusion of $\mathcal I$, and let $f$ be the image of $s_N$. Locally it is a sum of products
   of $N$ elements of $\mathcal I$, so $f\in\mathcal I^N\subseteq\mathcal I$ since $N>0$. Modulo
   $\mathcal J$, evaluation agrees with the map $\operatorname{Sym}(\mathcal O_Y/\mathcal
   J)\to\mathcal O_Y/\mathcal J$ sending its degree-one section $t$ to $1$, by the
   symmetric-algebra universal property. Thus $f\equiv1\pmod{\mathcal J}$. Therefore $q\in
   Y_f\subseteq U$, and $Y_f=D_U(f|_U)$ is affine by the affine principal-open lemma.
   Uses: lem-weil-pbc-quasi-coherent-symmetric-algebra, lem-weil-pbc-symmetric-algebra-graded,
   lem-weil-pbc-affine-open-section-vanishing-prime.

4. The opens $Y_f$ so obtained cover all closed points, hence all of $Y$. Indeed, the complement
   of their union is a closed subset of the quasi-compact space $Y$; if nonempty it has a point
   closed in $Y$ by the cited Kolmogorov-space lemma, contradicting the construction. The
   underlying space of a scheme is Kolmogorov directly from its affine charts: two distinct
   points either have an open containing only one, or both lie in one affine open and distinct
   prime ideals are distinguished by a principal open. Quasi-compactness now gives finitely many
   such sections $f_1,\ldots,f_m\in A$ with affine $Y_{f_i}$ covering $Y$. If $Y$ is empty it is
   $\operatorname{Spec}(0)$ and the conclusion follows immediately, so in the remaining argument
   choose $m>0$.
   Uses: lem-sc-quasi-compact-kolmogorov-closed-point.

5. Consider the map of quasi-coherent polynomial algebra sheaves $\alpha:\mathcal
   O_Y[T_1,\ldots,T_m]\to\mathcal O_Y[x]$ defined by $T_i\mapsto f_i x$. These algebras are the
   symmetric algebras of the corresponding finite free modules. On $Y_{f_i}$ the image contains
   $x$ because $f_i$ is a unit, so $\alpha$ is surjective as a sheaf. Global sections of these
   polynomial sheaves are $A[T_1,\ldots,T_m]$ and $A[x]$: their underlying modules are direct
   sums of copies of $\mathcal O_Y$ indexed by monomials, and the degree-zero case of the cited
   coproduct-cohomology lemma commutes these sums with $\Gamma$. The free-module
   symmetric-algebra identification makes these identifications multiplicative and sends each
   variable to the same variable. Apply positive-power lifting to $x$. There are $L>0$ and $g\in
   A[T_1,\ldots,T_m]$ with $g(f_1x,\ldots,f_mx)=x^L$. Writing $g=\sum_\nu a_\nu T^\nu$,
   comparison of the coefficient of $x^L$ gives $1=\sum_{|\nu|=L}a_\nu\prod_i f_i^{\nu_i}$. Each
   term belongs to $(f_1,\ldots,f_m)$ because $L>0$. Thus this ideal is the unit ideal.
   Uses: lem-weil-pbc-quasi-coherent-symmetric-algebra,
   lem-weil-pbc-symmetric-algebra-free-module-polynomial, lem-weil-pbc-basic-open-function,
   lem-weil-pbc-qcqs-cohomology-direct-sum.

6. The finite family $f_i$ generates the unit ideal in $A$ and all $Y_{f_i}$ are affine, so the
   cited unit-ideal principal-open criterion makes $Y$ affine. Apply Chevalley affineness
   descent for algebraic spaces to the finite surjective morphism $p:Y\to Z$. It gives that $Z$
   is represented by an affine scheme. Every preceding step allowed arbitrary commutative rings
   and used neither Noetherianity nor finite type of $Z$ over $R$.
   Uses: lem-weil-pbc-affine-unit-ideal-basic-opens,
   lem-sfb-finite-surjective-affine-space-target.
-/
theorem exists_affine_scheme_of_global_power_lifting
    (R : Type u) [CommRing R] (Z : AlgebraicSpace (Spec (CommRingCat.of R)))
    (_hqc : IsQuasiCompact Z.obj)
    (_hqs : MapIsQuasiCompact (prod.lift (𝟙 Z.obj.obj) (𝟙 Z.obj.obj)))
    (_hlift : ∀ (B C : Z.QCAlg) (q : B ⟶ C),
      Presheaf.IsLocallySurjective Z.etaleTopology q.hom.right.hom →
        ∀ c : (C.obj.right.obj ⋙ forget CommRingCat).sections,
          ∃ N : ℕ, 0 < N ∧
            ∃ b : (B.obj.right.obj ⋙ forget CommRingCat).sections,
              ∀ U : Z.EtaleSiteᵒᵖ, (q.hom.right.hom.app U) (b.val U) = (c.val U) ^ N) :
    ∃ U : Over (Spec (CommRingCat.of R)),
      IsAffine U.left ∧ Nonempty (yoneda.obj U ≅ Z.obj.obj) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
