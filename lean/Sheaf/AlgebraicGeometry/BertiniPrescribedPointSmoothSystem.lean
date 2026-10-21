/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import WeilConjectures.AlgebraicGeometry.InvertibleStalkLinearEquiv
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import Sheaf.DeligneLaumon.BertiniSections
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ClosedImmersionIdealTensorSections
import WeilConjectures.AlgebraicGeometry.CoherentSerreVanishing
import WeilConjectures.AlgebraicGeometry.PQFCohomology
import Sheaf.RingTheory.SmoothOverFieldRegularLocal
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.RingTheory.SmoothAtPrimeDifferentialsDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.MaximalIdealDifferentialCotangentDimension
public import Sheaf.AlgebraicGeometry.BertiniSmoothMember
import Sheaf.AlgebraicGeometry.HypersurfaceNonzeroRelativeDifferential
import WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import Sheaf.AlgebraicGeometry.EffectiveCartierDimensionDrop
import Sheaf.AlgebraicGeometry.AmpleOfAffineGeneratingLoci

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Baire.Lemmas
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.Topology.NoetherianSpace

/-!
# High-degree systems through prescribed points with smooth members

Source: blueprint main-20261015, proof of lem-zl-bertini-finite-cover-curve, paragraph 2;
Stacks Project, Varieties, Tags 0FD5 and 0FD6; Coherent, Tag 0B5T.
(blueprint: lem-zl-bertini-prescribed-point-smooth-system).

The kernel is presented by a finite basis: every section vanishing on the reduced finite
set has a unique coefficient tuple. Thus its affine parameter space is literally the affine
space in these coordinates. First-order values use the canonical model
`(m / m²) ⊗[O_x] L_x`. Since `m` annihilates `m / m²`, this is canonically
`(m / m²) ⊗[κ(x)] (L_x ⊗[O_x] κ(x))`, and at a closed point over the algebraically
closed field it is the tensor product over `k` displayed in the source.
-/

@[expose] public section

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules

noncomputable section

/-- The restricted projective twist `O_Y(n)`.
Source: blueprint, finite-cover-curve proof, paragraph 2.
(blueprint: lem-zl-bertini-prescribed-point-smooth-system). -/
abbrev prescribedPointTwist {k : Type u} [Field k] {N : ℕ} {Y : Scheme.{u}}
    (c : Y ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k))) (n : ℕ) : Y.Modules :=
  (tensorPullback c).obj (ProjectiveSpace.twist _ _ (n : ℤ))

/-- The section with the given coefficients in a finite family, with scalars supplied by
its specified structure morphism. Source: blueprint, finite-cover-curve proof, paragraph 2.
(blueprint: lem-zl-bertini-prescribed-point-smooth-system). -/
def prescribedPointCombination {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (M : Y.Modules) {I : Type u} [Fintype I]
    (s : I → Γ(M, ⊤)) (a : I → k) : Γ(M, ⊤) :=
  ∑ i, f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (a i)) • s i

/-- Vanishing on a reduced finite set, tested in the residue-field fibres.
Source: blueprint, finite-cover-curve proof, paragraph 2, definition of `V_n`.
(blueprint: lem-zl-bertini-prescribed-point-smooth-system). -/
def prescribedPointVanishes {X : Scheme.{u}} (M : X.Modules) (S : Finset X)
    (v : Γ(M, ⊤)) : Prop :=
  ∀ x ∈ S, M.presheaf.germ ⊤ x trivial v ∈
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
      (⊤ : Submodule (X.presheaf.stalk x) (M.presheaf.stalk x))

/-- A concrete canonical model of the first-order target at a prescribed point.
Source: blueprint, finite-cover-curve proof, paragraph 2, displayed jet map.
(blueprint: lem-zl-bertini-prescribed-point-smooth-system). -/
abbrev PrescribedPointJet {X : Scheme.{u}} (M : X.Modules) (x : X) : Type u :=
  TensorProduct (X.presheaf.stalk x) (IsLocalRing.CotangentSpace (X.presheaf.stalk x))
    (M.presheaf.stalk x)

/-- First-order value of a section vanishing at `x`. In a stalk frame `e`, write its germ
as `a * e⁻¹(1)` and take `[a] ⊗ e⁻¹(1)`. Changing the frame cancels between the two
factors. The value off the vanishing subspace is set to zero and is never used below.
Source: blueprint, finite-cover-curve proof, paragraph 2, displayed jet map.
(blueprint: lem-zl-bertini-prescribed-point-smooth-system). -/
def prescribedPointJet {X : Scheme.{u}} (M : X.Modules) [M.IsInvertible]
    (x : X) (v : Γ(M, ⊤)) : PrescribedPointJet M x := by
  classical
  let e := Classical.choice (invertible_stalk_linearEquiv X M x)
  let a := e (M.presheaf.germ ⊤ x trivial v)
  exact if h : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) then
    TensorProduct.tmul (X.presheaf.stalk x)
      ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).toCotangent ⟨a, h⟩) (e.symm 1)
    else 0

/-- Restrict a family of sections to an open, using the canonical tensor-pullback unit,
and convert it to the compatible-section encoding used by the projective morphism.
Source: Stacks Project, Tag 0FD5, restriction of the kernel linear system.
(blueprint: lem-zl-bertini-prescribed-point-smooth-system). -/
def prescribedPointRestrictedFamily {Y : Scheme.{u}} (M : Y.Modules)
    {X : Scheme.{u}} (j : X ⟶ Y) (U : X.Opens) {I : Type u}
    (s : I → Γ(M, ⊤)) : I → ((tensorPullback (U.ι ≫ j)).obj M).sections :=
  bertiniSectionFamily _ (fun i ↦ tensorSectionsUnit (U.ι ≫ j) M (s i))

/-- The actual zero scheme of the restricted section with coefficient tuple `a`.
Source: blueprint, finite-cover-curve proof, paragraph 2, `H_v = Z(v|_X)`.
(blueprint: lem-zl-bertini-prescribed-point-smooth-system). -/
def prescribedPointMember {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (j : X ⟶ Y) (M : Y.Modules)
    {I : Type u} [Fintype I] (s : I → Γ(M, ⊤)) (a : I → k) : X.IdealSheafData :=
  (homOfGlobalSection ((tensorPullback j).obj M)
    (tensorSectionsUnit j M (prescribedPointCombination f M s a))).zeroLocus

/-- High-degree prescribed-point systems generate and immerse off the base points,
separate simultaneous first-order values, and have a nonempty open of smooth members.

Source: blueprint main-20261015, finite-cover-curve proof, paragraph 2;
Stacks Project, Tags 0FD5, 0FD6 and 0B5T.
(blueprint: lem-zl-bertini-prescribed-point-smooth-system).

Proof:
1. Put $Y=\overline X$ and $L=\mathcal O_Y(1)$. The given closed immersion into projective space
makes $Y$ projective, hence proper over $k$, and makes $L$ invertible and ample in the absolute
sense, with the nonvanishing loci $Y_{s_k}$ of the coordinate sections $s_k\in\Gamma(Y,L)$ forming
an affine open cover of $Y$. Since $Y$ is proper over $k$, the affine-loci criterion (with $n=1$
and these sections) makes $L$ ample also in the very-ample-power sense used by the sections-
vanishing theorem of step 2. Properness includes finite type; since $k$ is Noetherian, $Y$ is
Noetherian. The same finite-type-over-Noetherian theorem applies to the given finite-type
$k$-scheme $X$, so $X$ is Noetherian as well. An invertible sheaf and each of its tensor powers
are coherent: locally they are free of rank one. Proper coherent cohomology therefore makes
$\Gamma(Y,L^{\otimes n})$ finite-dimensional for every $n\ge0$, and its subspace $V_n$ is finite-
dimensional.
Uses: lem-pc-projective-proper, lem-weil-pbc-projective-ample-invertible, lem-pc-ample-affine-
loci-criterion, lem-weil-pbc-finite-type-over-noetherian, pqf-lem-coherent-ft-locnoeth, lem-pc-
coherent-hi.
2. Apply the sections-vanishing theorem to $(Y,L,S)$. There is $a$ such that for every $n\ge a$,
$V_n$ generates $L^{\otimes n}$ on $Y\setminus S$ and gives an immersion there. Restricting the
sections and the morphism to the open subscheme $X\setminus S$ preserves generation, and the
morphism remains an immersion by composition with the open immersion $X\setminus S\hookrightarrow
Y\setminus S$. This proves the first two requested clauses.
Uses: lem-zl-bertini-sections, lem-weil-pbc-proper-fp-permanence.
3. Let $\mathcal I$ be the ideal sheaf of $S$ in $Y$. It is quasi-coherent, and so is its square
$\mathcal I^2$, computed by squaring the ideal on each affine chart. Both are coherent, since they
are quasi-coherent submodules of the coherent module $\mathcal O_Y$ on the Noetherian scheme $Y$.
The quotient $\mathcal I/\mathcal I^2$ is coherent as well. For every $n$, tensoring the inclusion
and quotient sequence with $L^{\otimes n}$ gives the short exact sequence $0\to\mathcal I^2\otimes
L^{\otimes n}\to\mathcal I\otimes L^{\otimes n}\to(\mathcal I/\mathcal I^2)\otimes L^{\otimes
n}\to0$: in a frame of the invertible sheaf it is the original exact sequence. The ideal-tensor-
sections theorem identifies $\Gamma(Y,\mathcal I\otimes L^{\otimes n})$ with exactly $V_n$, with
its given inclusion into $\Gamma(Y,L^{\otimes n})$.
Uses: def-sbc-closed-immersion-ideal-sheaf, def-sbc-ideal-sheaf-powers, lem-weil-pbc-coherent-
kernel-cokernel-locnoeth, lem-sc-closed-immersion-ideal-tensor-sections.
4. The sheaf $Q_n=(\mathcal I/\mathcal I^2)\otimes L^{\otimes n}$ is supported on the finite set
$S$ and is annihilated by $\mathcal I$. Its stalk at $s$ is $(\mathfrak m_s/\mathfrak
m_s^2)\otimes_k L_n(s)$, since $X$ is open in $Y$ and $\kappa(s)=k$. Consequently $\Gamma(Y,Q_n)$
is the direct sum of these stalks. Explicitly, take a representative of a germ near $s$ on an open
excluding the other points of $S$; it glues with zero on $Y\setminus\{s\}$, because the overlap
has zero sheaf. These extensions are unique and their sum gives the asserted inverse to the stalk
map. Under this identification the quotient map from the preceding exact sequence sends a section
vanishing on $S$ to its first-order parts. Thus the map in the statement is exactly the map on
global sections induced by that sequence.
Uses: def-sbc-closed-immersion-ideal-sheaf, def-sbc-ideal-sheaf-powers.
5. Apply coherent Serre vanishing on the proper scheme $Y$ with ample $L$ to the fixed coherent
sheaf $\mathcal I^2$. For all $n\ge b$ it gives $H^1(Y,\mathcal I^2\otimes L^{\otimes n})=0$. The
long exact sequence for the short exact sequence of step 3 then contains $\Gamma(Y,\mathcal
I\otimes L^{\otimes n})\to\Gamma(Y,Q_n)\to H^1(Y,\mathcal I^2\otimes L^{\otimes n})=0$. By
exactness the first arrow is surjective. Step 4 identifies it with the required simultaneous
first-order map from $V_n$. This is the source's infinitesimal-neighbourhood argument, using the
ideal $\mathcal I^2$ of the union of the first neighbourhoods.
Uses: lem-weil-pbc-coherent-serre-vanishing, pqf-def-cohomology.
6. Fix $n\ge\max(a,b,0)$. Smoothness gives regular local rings on $X$, so connectedness and
nonemptiness (which follows from $S\ne\varnothing$) make $X$ integral. At a closed point $s\in S$,
smoothness identifies the dimension of the differential fibre with the topological dimension at
$s$; that dimension is $d$, because every nonempty open of the integral finite-type scheme $X$ has
dimension $d$. The closed-point cotangent-dimension comparison then gives $\dim_k(\mathfrak
m_s/\mathfrak m_s^2)=d>0$. Each summand of the first-order target is therefore nonzero, since
$L_n(s)$ is a one-dimensional $k$-vector space.
Uses: lem-weil-pbc-smooth-over-field-regular-local, lem-sc-regular-connected-integral, lem-weil-
pbc-smooth-over-field-dimension-differentials, lem-sc-integral-locally-algebraic-opens-dimension,
lem-weil-pbc-maximal-ideal-differential-cotangent-dimension.
7. For $s\in S$ let $j_s:V_n\to(\mathfrak m_s/\mathfrak m_s^2)\otimes_k L_n(s)$ be its first-order
evaluation. Its zero fibre is a linear closed subspace of $\mathbf A(V_n)$ (in bases, it is
defined by the linear coordinate equations of $j_s$). Hence $W=\bigcap_{s\in S}(\mathbf
A(V_n)\setminus\ker j_s)$ is open. Choose a nonzero vector in every nonzero summand of the target.
Surjectivity in step 5 lifts the resulting tuple to a vector of $V_n$ lying in $W(k)$. Thus $W$ is
nonempty, and its $k$-points have nonzero first-order part at every prescribed point.
8. Apply Bertini smoothness to the smooth $k$-scheme $X\setminus S$, the restriction of $L_n$, and
the linear restriction map $V_n\to\Gamma(X\setminus S,L_n)$. The vector space is finite-
dimensional by step 1; its image generates and its associated map is an immersion by step 2. It
yields a nonempty Zariski open $O\subseteq\mathbf A(V_n)$ on which the zero schemes restricted to
$X\setminus S$ are smooth. Notice that injectivity of this linear restriction map is not a
hypothesis of the cited Bertini theorem.
Uses: lem-zl-bertini-smooth-member.
9. The coordinate ring of $\mathbf A(V_n)$ is a polynomial ring over $k$, hence a domain. Its
nilradical is zero and prime, so its spectrum is irreducible. Every nonempty open in an
irreducible space is dense: otherwise it and the complement of its closure would be disjoint
nonempty opens, whose complements would be two proper closed subsets covering the space. Thus the
two nonempty opens $O$ and $W$ are dense, and $U_{\rm sm}=O\cap W$ is a nonempty open by finite
intersection of dense opens.
Uses: lem-weil-pbc-polynomial-ring-domain, lem-zl-spectrum-irreducible-nilradical-prime, lem-trf-
finite-dense-open-intersection.
10. Let $v\in U_{\rm sm}(k)$. It vanishes on $S$. Its zero scheme is smooth off $S$ by step 8. At
$s\in S$, in a local frame write $v=f$ with $f\in\mathfrak m_s$. The map $\mathfrak m_s/\mathfrak
m_s^2\to\Omega^1_{X/k}(s)$ sends $f$ to $df(s)$ and is an isomorphism: its inverse sends $da$ to
$a-a(s)$ modulo $\mathfrak m_s^2$; the identity $ab-a(s)b(s)\equiv a(s)(b-b(s))+b(s)(a-a(s))$
verifies the derivation rule. Thus the nonzero first-order part provided by $v\in W(k)$ gives
$df(s)\ne0$. The nonzero-relative-differential criterion makes $H_v$ smooth in a neighbourhood of
$s$. These neighbourhoods and $H_v\setminus S$ cover $H_v$, proving smoothness everywhere.
Uses: lem-zl-hypersurface-nonzero-relative-differential.
11. The zero-scheme properties make $H_v$ a locally principal closed subscheme of $X$, containing
$S$ scheme-theoretically because $v$ restricts to zero on $S$. A closed immersion is affine, so
$H_v$ is affine since $X$ is affine. The nonzero first-order part at any $s\in S$ shows that $v$
is a nonzero section on the integral scheme $X$. Its value at the generic point is nonzero: in
each nonempty trivializing affine open the coordinate ring is a domain and embeds in its fraction
field, so a section zero generically would be zero on every such open. Thus every local defining
function is a nonzero element of a domain, hence a nonzerodivisor. The zero scheme is a nonempty
effective Cartier divisor on $X$.
Uses: lem-pc-zero-scheme-properties, lem-weil-pbc-closed-immersion-integral-separated-uc, def-
nagata-effective-cartier-ideal.
12. To check purity, fix any irreducible component $D$ of $H_v$, with its reduced induced scheme
structure. There are only finitely many components, because $H_v$ is closed in the Noetherian
scheme $X$. Remove all the other components from $X$ and call the remaining open $A$. The
intersection $D\cap A$ is nonempty: otherwise the irreducible component $D$ would lie in one of
the finitely many other components. The divisor $E=H_v\cap A$ and $D\cap A$ therefore have the
same underlying topological space; no equality of their scheme structures is needed. By the open-
dimension theorem, $A$ is integral of dimension $d$. It is finite type over $k$: since $X$ is
Noetherian, $A$ is quasi-compact, hence covered by finitely many distinguished affine opens from
finite-type affine charts of $X$, whose coordinate rings are finitely generated over $k$. The
local nonzerodivisor equations of step 11 restrict to $A$, so $E$ is a nonempty effective Cartier
divisor on $A$. The Cartier dimension-drop theorem gives $\dim E=d-1$, hence $\dim(D\cap A)=d-1$.
Finally $D$ is integral and locally of finite type over $k$ (its affine charts are reduced prime
quotients of finite-type affine charts of $H_v$). Applying the open-dimension theorem to its
nonempty open $D\cap A$ gives $\dim D=d-1$. This holds for every component. The bounds $a$ and $b$
are uniform in $n$, so all conclusions hold for every sufficiently large $n$.
Uses: lem-sc-noetherian-closed-subset-finite-components, lem-sc-integral-locally-algebraic-opens-
dimension, lem-sc-effective-cartier-dimension-drop.
-/
theorem exists_eventual_prescribedPoint_smoothSystem
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsAffine X] [ConnectedSpace X]
    [Smooth (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (d : ℕ) (hd : 2 ≤ d) (hdim : X.IsPureDimension d)
    (S : Finset X) (hS : S.Nonempty) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (N : ℕ) (Y : Scheme.{u}) [IsReduced Y]
    (c : Y ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k))) [IsClosedImmersion c]
    (j : X ⟶ Y) [IsOpenImmersion j] (hdense : DenseRange j)
    (hchart : Set.range j = c ⁻¹' (ProjectiveSpace.standardOpen
      (ULift.{u} (Fin (N + 1))) (Spec (.of k)) ⟨0⟩ : Set _))
    (hover : j ≫ c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)) =
      X ↘ Spec (.of k)) :
    ∃ (n₀ : ℕ) (U : X.Opens),
      (∀ x : X, x ∈ U ↔ x ∉ S) ∧
      ∀ n : ℕ, n₀ ≤ n →
        ∃ (I : Type u) (_ : Fintype I) (s : I → Γ(prescribedPointTwist c n, ⊤)),
          (∀ v : Γ(prescribedPointTwist c n, ⊤),
            prescribedPointVanishes ((tensorPullback j).obj (prescribedPointTwist c n)) S
                (tensorSectionsUnit j (prescribedPointTwist c n) v) ↔
              ∃! a : I → k, prescribedPointCombination
                (c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)))
                (prescribedPointTwist c n) s a = v) ∧
          (∃ ht : Epi ((((tensorPullback (U.ι ≫ j)).obj
              (prescribedPointTwist c n)).freeHomEquiv).symm
                (prescribedPointRestrictedFamily (prescribedPointTwist c n) j U s)),
            IsImmersion (@ProjectiveSpace.homOfGeneratingSections I inferInstance
              U.toScheme (Spec (.of k)) (U.ι ≫ (X ↘ Spec (.of k)))
              ((tensorPullback (U.ι ≫ j)).obj (prescribedPointTwist c n))
              ((@id (∀ L : Y.Modules, L.IsInvertible → _)
                (invertible_pullback_tensor (U.ι ≫ j)).1) (prescribedPointTwist c n)
                ((invertible_pullback_tensor c).1 (ProjectiveSpace.twist _ _ (n : ℤ))).2).2
              (prescribedPointRestrictedFamily (prescribedPointTwist c n) j U s) ht)) ∧
          Function.Surjective (fun a : I → k ↦ fun x : S ↦
            @prescribedPointJet X ((tensorPullback j).obj (prescribedPointTwist c n))
              ((@id (∀ L : Y.Modules, L.IsInvertible → _)
                (invertible_pullback_tensor j).1) (prescribedPointTwist c n)
                ((invertible_pullback_tensor c).1 (ProjectiveSpace.twist _ _ (n : ℤ))).2).2
              x.val
              (tensorSectionsUnit j (prescribedPointTwist c n)
                (prescribedPointCombination
                  (c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)))
                  (prescribedPointTwist c n) s a))) ∧
          ∃ O : (Spec (CommRingCat.of (MvPolynomial I k))).Opens,
            (O : Set (Spec (CommRingCat.of (MvPolynomial I k)))).Nonempty ∧
            ∀ a : I → k, Set.range (bertiniCoefficientPoint (k := k) a) ⊆ (O : Set _) →
              Smooth ((prescribedPointMember
                (c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)))
                j (prescribedPointTwist c n) s a).subschemeι ≫ (X ↘ Spec (.of k))) ∧
              IsAffine (prescribedPointMember
                (c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)))
                j (prescribedPointTwist c n) s a).subscheme ∧
              (prescribedPointMember
                (c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)))
                j (prescribedPointTwist c n) s a).subscheme.IsPureDimension (d - 1) ∧
              (∀ x ∈ S, x ∈ (prescribedPointMember
                (c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)))
                j (prescribedPointTwist c n) s a).support) ∧
              ∀ x ∈ S, @prescribedPointJet X
                ((tensorPullback j).obj (prescribedPointTwist c n))
                ((@id (∀ L : Y.Modules, L.IsInvertible → _)
                (invertible_pullback_tensor j).1) (prescribedPointTwist c n)
                  ((invertible_pullback_tensor c).1 (ProjectiveSpace.twist _ _ (n : ℤ))).2).2 x
                (tensorSectionsUnit j (prescribedPointTwist c n)
                  (prescribedPointCombination
                    (c ≫ (ℙ(ULift.{u} (Fin (N + 1)); Spec (.of k)) ↘ Spec (.of k)))
                    (prescribedPointTwist c n) s a)) ≠ 0 := by
  sorry

end

end AlgebraicGeometry
