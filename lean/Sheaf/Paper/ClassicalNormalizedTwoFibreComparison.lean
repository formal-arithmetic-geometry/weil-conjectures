/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.Paper.ClassicalTwoFibreCommonData
public import Sheaf.Paper.ClassicalTwoFibreScalarData
/-! # The two normalized fibres of a classical lisse adic system

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4), Proposition 6.8.14(2),
Remark 6.8.15; blueprint real-mixed-by-curves, proof paragraph 1
(blueprint: lem-zl-classical-normalized-two-fibre-comparison).

## Main definitions and statements

* `normalized_two_fibre_comparison`: simultaneous existence of all comparison data.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
attribute [-instance] AlgebraicGeometry.Scheme.pbcRationalHasShift
open scoped TensorProduct
namespace WeilConjectures.ClassicalTwoFibre
open AlgebraicGeometry.Scheme.ContinuousRational
open AlgebraicGeometry.Scheme.AdicFibreComparison

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [hl : Fact (l ≠ D.p)]
  (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]


/-- The normalized sf and PBC fibres of every realized classical lisse system agree.
All realization and comparison data below are conclusions supplied simultaneously;
they impose no further hypotheses on the scheme, coefficients, system or object.
`AtStage.model` is the required derived realization isomorphism for each specified lattice.
`AtStage.fractions` and the natural isomorphisms apply to all realized maps, so two
fractional presentations of the same map give the same inverse-limit map.
The existing lattice predicate permits rank zero and varying finite clopen ranks.

Source: BS Proposition 6.8.4(1),(4), Proposition 6.8.14(2), Remark 6.8.15;
blueprint real-mixed-by-curves, proof paragraph 1
(blueprint: lem-zl-classical-normalized-two-fibre-comparison).

Proof (the seven steps of the DAG node):
1. First check the schemes needed by the comparisons. By [lem-pod-separated-finite-type-base-
change], $Y=Y_0\times_{k_0}k$ is separated and of finite type over $k$. A field is noetherian, so
[pqf-lem-locnoeth-lft] applied to the finite-type structure map makes $Y$ locally noetherian;
finite type includes quasi-compactness, hence $Y$ is noetherian. It has finite dimension by [lem-
kun-dimension-finite-type], and $\ell$ is invertible since $\ell\ne p$. These assertions also hold
for $s$. The equivalence [lem-fd-rational-coefficient-category-comparison] is the identity on the
common integral objects and on $u\otimes e$. The nonpositive and nonnegative classes in [def-weil-
constructible-standard-tstructure] and [prop-weil-localized-tstructure] are the isomorphism
closures of precisely the same integral cohomological classes. Thus $J_{Y,E}$ identifies their
intersections, namely the two hearts. By [lem-per-continuous-rational-derived-realization] its
continuous realization on an integral representative $C$ is $E_Y\otimes^L_{B_Y}C$, with
$B_Y=\varprojlim_n(A/\varpi^n)_Y$. This is also the functor defining [lem-tw-lisse-rational-
realization], including its arrow formula. The specified realization of $K$ therefore gives the
claimed isomorphism $\operatorname{Real}(J_{Y,E}K)\cong\widehat N[1/\varpi][0]$ in the ambient
derived category.

2. By [lem-per-lisse-completed-system-comparison], $\widehat N$ is a lisse $B_Y$-module with
reduction system exactly $(N_n)$. The given normalized realization therefore supplies an actual
integral lisse lattice of the continuous sheaf representing $J_{Y,E}K$. Apply [lem-per-adic-
normalized-fibre-exactness] on any affine etale neighbourhood of $\bar y$, taking this lattice
restricted to that neighbourhood. Its normalization identifies $\omega_{\bar y,E}(J_{Y,E}K)$ with
$M_{\bar y}\otimes_AE$, where $M_{\bar y}=\varprojlim_n(N_n)_{\bar y}$, and asserts that $M_{\bar
y}$ is finite free. The chart-independent identification of that lemma applies to this chosen
global lattice, so this gives the right-hand comparison without choosing a different lattice or a
path between points.

3. Pull the system $(N_n)$ to $s$ along $\bar y$. Put $P=\varprojlim_n\nu_s^*(\bar y^{-1}N_n)$.
The pullback compatibility in [lem-per-lisse-completed-system-comparison] identifies $P$ with the
ordinary module pullback of $\widehat N$. At finite level [lem-weil-pbc-inverse-image-stalk-germ]
identifies the pulled fibre with $(N_n)_{\bar y}$, sending every pulled germ to the original germ
and commuting with each transition and each $f_n$. Since $k$ is algebraically closed its absolute
Galois group is trivial. The equivalence [lem-exc-etale-sheaves-gsets-point], applied also to the
module structure maps, identifies the pulled etale sheaf with the constant module of its fibre.
That fibre is finite free over $A/\varpi^n$. Inverse image to the pro-etale site preserves
constant coefficient sheaves and finite sums, so a basis identifies its pro-etale pullback with a
finite sum of $(A/\varpi^n)_s$. By [lem-pur-proetale-finite-constant-sections] the sections of
each coefficient summand at $s$ are $A/\varpi^n$, with the constant-section normalization. Hence
its sections are canonically $(N_n)_{\bar y}$; changing bases changes both sides by the same
matrix. The inverse-limit construction [def-pur-sheaf-inverse-limit] is sectionwise. Consequently
$\Gamma(s,P)=M_{\bar y}$, and a pulled system map has sections map exactly
$\varprojlim_n(f_n)_{\bar y}$. This calculation pulls the normalized system first; it does not
commute an arbitrary geometric stalk with an infinite limit.

4. The pullback and point normalization of [lem-tw-lisse-rational-realization] carries $L\bar
y^*K$ to $P[1/\varpi][0]$. Here $P[0]$ belongs to the common integral constructible category by
[lem-weil-pbc-integral-stratified-perfect-characterization]: its lisse local model is a finite
free module in degree zero. Realization also carries the rationalized integral lattice $P[0]$ to
that same sheaf. Full faithfulness lifts this specified identification to an isomorphism of the
two rationalized objects: lift the sheaf isomorphism and its inverse, and their composites are
identities by faithfulness. The point functor [def-weil-finite-coefficient-point], applied to
$P[0]$, is $\Gamma(s,P)\otimes_AE$ in degree zero; exact sections [lem-weil-point-proetale-
sections-exact] justifies this use on the derived category. The preceding computation gives
$\operatorname{Fib}_s(L\bar y^*K)\cong(M_{\bar y}\otimes_AE)[0]$. This is the left-hand
comparison, with vector spaces in the displayed statement understood in degree zero. It is
normalized by the same quotient projections as the right-hand comparison.

5. For $f/\varpi^t$, step 3 gives the integral point map $\varprojlim_n(f_n)_{\bar y}$. The
localized arrow prescription in [def-weil-finite-coefficient-point] multiplies it by
$\varpi^{-t}$; the normalized prescription in [lem-per-adic-normalized-fibre-exactness] gives
exactly the same formula on the right. The equivalence [lem-fd-rational-coefficient-category-
comparison] changes neither the integral map nor this scalar. Hence both squares commute. If
$f/\varpi^t=h/\varpi^u$, equality in a localized Hom module means that
$\varpi^b(\varpi^uf-\varpi^th)=0$ for some $b$. Apply each finite-level fibre map and then take
the limit: the same equality holds for limit maps, and inversion of $\varpi$ makes the rational
maps equal. Finally [lem-per-lisse-completed-system-comparison] is fully faithful after raw
localization. Therefore every map between the realized sheaves with the specified lattices is
represented by such a fraction. The formulas prove naturality for every map between the realized
objects, not merely maps for which an integral representative was initially supplied.

6. For $E\subset E'$, use the scalar system of [def-pod-lisse-l-adic-sheaves]: its level $m$ is
$N_{n(m)}\otimes_{A/\varpi^{n(m)}}A'/\varpi'^m$, where $n(m)=\lceil m/e\rceil$ and $e$ is the
ramification index. The pullback and scalar comparisons of [lem-per-lisse-completed-system-
comparison] are induced by these quotient maps. The scalar comparison of [lem-per-adic-normalized-
fibre-comparisons] identifies its rational limit fibre with $M_{\bar y}\otimes_AE'$, using those
same finite integral maps. On the sf side [lem-tw-lisse-rational-realization] respects finite
coefficient extension with its specified normalization, and [lem-fd-rational-coefficient-category-
comparison] identifies the sf and PBC scalar functors with their associators. Thus the comparison
constructed above commutes with extension to $E'$: on every quotient the two routes send a pulled
germ tensored with a scalar to that same germ tensored with that scalar. Equality after every
quotient gives equality into the inverse limit, and localization gives the required rational
square. For successive extensions both routes multiply the scalars, so these squares respect the
associators. Passing to the common finite-stage description gives the comparison after scalar
extension to $\Omega$, including naturality in common-stage maps.

7. All formulas use the actual normalized lattice, its quotient projections and its map on germs.
On a clopen component of rank $r$ they compute $M_{\bar y}\cong A^r$ and $V_{\bar y}(N)\cong E^r$.
For $r=0$ these are zero modules and the same formulas are their unique maps. Restriction to any
of the finitely many clopen rank components leaves every construction and displayed formula
unchanged. The empty scheme has no geometric points, so its fibre assertions are vacuous. Thus no
nonzero-rank or connectedness assumption has been inserted.
-/
theorem normalized_two_fibre_comparison :
    ∃ (a : LisseRealization.Family D l hl.out) (R : ContinuousRational.Family.{u} l)
      (C : FdCoefficientComparison l Ω (D.geometricFiber Y₀).left)
      (ω : Fibres (k := D.k) l R) (c : AllComparisons l R ω)
      (V : CommonAssertions l R Ω ω)
      (S : ∀ E, AtStage D l Ω Y₀ E a R C ω),
      (∀ E : Padic.FiniteCoefficientFields l Ω,
        Nonempty (LisseRealization.PointNormalized D l hl.out (pbcFiniteField.{u} l Ω E)
          (a.realization _ (LisseRealization.point D l hl.out)) (a.point _))) ∧
      (∀ (E : Padic.FiniteCoefficientFields l Ω)
        (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left),
        Nonempty (LisseRealization.PullNormalized D l hl.out (pbcFiniteField.{u} l Ω E) x
          (a.realization _ (LisseRealization.point D l hl.out))
          (a.realization _ (zlRealizationBase D l hl.out Y₀))
          (a.along _ (X := LisseRealization.point D l hl.out)
            (Y := zlRealizationBase D l hl.out Y₀) x))) ∧
      (∀ (E L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L),
        Nonempty (LisseRealization.FieldNormalized D l hl.out (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h)
          (zlRealizationBase D l hl.out Y₀) (a.realization _ _)
          (a.realization _ _) (a.fieldChange _ _ (pbcFiniteFieldInclusion l Ω h) _))) ∧
      Nonempty (Coherence l R ω c) ∧ Nonempty (UnitNormalization l R ω c) ∧
      Nonempty (Descent l R Ω ω c V) ∧ Nonempty (LocalLimits l R ω c) ∧
      Nonempty (Scalars D l Ω Y₀ a R C ω c S) ∧
      Nonempty (Common D l Ω Y₀ a R C ω V S) := by
  sorry

end WeilConjectures.ClassicalTwoFibre
