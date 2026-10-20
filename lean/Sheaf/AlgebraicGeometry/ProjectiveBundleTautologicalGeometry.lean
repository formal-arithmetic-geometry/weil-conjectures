/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalData
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
public import Sheaf.AlgebraicGeometry.RelativeProjectiveSpace
public import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra
import Sheaf.AlgebraicGeometry.ProjectiveBundleBaseChangeCoherence
import Sheaf.AlgebraicGeometry.ProjectiveBundleCoordinateGeometry
import Sheaf.AlgebraicGeometry.ProjectiveBundleRankZero

/-! # Finite locally free projective bundles and tautological geometry

Source: Stacks Project, Tags 01OB, 01O3, 01OE
(blueprint: lem-pur-projective-bundle-tautological-geometry).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback
  projectiveBundleTensorPullbackIso projectiveBundlePullbackId projectiveBundlePullbackComp
  projectiveBundlePullbackCongr projectiveBundlePullbackAdjunction projectiveBundlePullbackUnitIso
  projectiveBundlePullbackSection

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A coherent family of the projective-bundle constructions. Module isomorphisms to a
pullback are included in the indexing to make the identity and composition equations typed
without pretending that iterated pullbacks are definitionally equal.
Source: Stacks, Tags 01OB, 01O3, 01OE
(blueprint: lem-pur-projective-bundle-tautological-geometry). -/
structure ProjectiveBundleTautologicalSystem (n : ℕ) where
  bundle : ∀ (B : Scheme.{u}) (F : B.Modules)
    (_hF : projectiveBundleRank B n F), ProjectiveBundleRealization B F
  invertible : ∀ (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F),
    (bundle B F hF).L.IsInvertible
  proper : ∀ (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F),
    IsProper (bundle B F hF).A.data.relProjHom
  frame : ∀ (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F)
    (U : B.Opens) (e : B.ModuleFrame F U (n + 1)),
      ProjectiveBundleFrameChart (bundle B F hF) n U e
  pullback_rank : ∀ (B B' : Scheme.{u}) (F : B.Modules)
    (_hF : projectiveBundleRank B n F) (g : B' ⟶ B),
      projectiveBundleRank B' n ((Scheme.Modules.tensorPullback g).obj F)
  baseChange : ∀ {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    (hF : projectiveBundleRank B n F) (hF' : projectiveBundleRank B' n F')
    (g : B' ⟶ B) (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F),
      ProjectiveBundleBaseChangeDatum (bundle B F hF) (bundle B' F' hF') g e
  baseChange_id : ∀ (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F),
    (baseChange hF hF (𝟙 B) ((projectiveBundlePullbackId B).app F).symm).map =
      𝟙 (bundle B F hF).A.data.relProj
  baseChange_theta_id : ∀ (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F),
    (baseChange hF hF (𝟙 B) ((projectiveBundlePullbackId B).app F).symm).theta =
      (projectiveBundlePullbackCongr (baseChange_id B F hF)).app (bundle B F hF).L ≪≫
        (projectiveBundlePullbackId (bundle B F hF).A.data.relProj).app (bundle B F hF).L
  baseChange_comp : ∀ {B₀ B₁ B₂ : Scheme.{u}} {F₀ : B₀.Modules} {F₁ : B₁.Modules}
    {F₂ : B₂.Modules} (h₀ : projectiveBundleRank B₀ n F₀)
    (h₁ : projectiveBundleRank B₁ n F₁) (h₂ : projectiveBundleRank B₂ n F₂)
    (g : B₁ ⟶ B₀) (h : B₂ ⟶ B₁)
    (e : F₁ ≅ (Scheme.Modules.tensorPullback g).obj F₀)
    (e' : F₂ ≅ (Scheme.Modules.tensorPullback h).obj F₁),
      (baseChange h₀ h₂ (h ≫ g) (e' ≪≫ (Scheme.Modules.tensorPullback h).mapIso e ≪≫
        (projectiveBundlePullbackComp h g).app F₀)).map =
      (baseChange h₁ h₂ h e').map ≫
        (baseChange h₀ h₁ g e).map
  baseChange_theta_comp : ∀ {B₀ B₁ B₂ : Scheme.{u}} {F₀ : B₀.Modules} {F₁ : B₁.Modules}
    {F₂ : B₂.Modules} (h₀ : projectiveBundleRank B₀ n F₀)
    (h₁ : projectiveBundleRank B₁ n F₁) (h₂ : projectiveBundleRank B₂ n F₂)
    (g : B₁ ⟶ B₀) (h : B₂ ⟶ B₁)
    (e : F₁ ≅ (Scheme.Modules.tensorPullback g).obj F₀)
    (e' : F₂ ≅ (Scheme.Modules.tensorPullback h).obj F₁),
      (baseChange h₀ h₂ (h ≫ g) (e' ≪≫ (Scheme.Modules.tensorPullback h).mapIso e ≪≫
        (projectiveBundlePullbackComp h g).app F₀)).theta =
      (projectiveBundlePullbackCongr (baseChange_comp h₀ h₁ h₂ g h e e')).app (bundle B₀ F₀ h₀).L ≪≫
        ((projectiveBundlePullbackComp (baseChange h₁ h₂ h e').map
          (baseChange h₀ h₁ g e).map).app (bundle B₀ F₀ h₀).L).symm ≪≫
        (Scheme.Modules.tensorPullback (baseChange h₁ h₂ h e').map).mapIso
          (baseChange h₀ h₁ g e).theta ≪≫ (baseChange h₁ h₂ h e').theta
  coordinate : ∀ (K : Type u) [Field K], ProjectiveBundleCoordinateGeometry K n
  rank_zero : ∀ (B : Scheme.{u}) (F : B.Modules) (hF : projectiveBundleRank B n F)
    (_hzero : n = 0), ∃ _e : (bundle B F hF).L ≅
      (Scheme.Modules.tensorPullback (bundle B F hF).A.data.relProjHom).obj F,
      IsIso (bundle B F hF).A.data.relProjHom

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The natural projective-bundle geometry, specializing the coherent construction to
`B` and `F`. The system records identities and composition for the same chosen maps.
Source: Stacks, Tags 01OB, 01O3, 01OE
(blueprint: lem-pur-projective-bundle-tautological-geometry). -/
structure ProjectiveBundleTautologicalGeometry (B : Scheme.{u}) (n : ℕ) (F : B.Modules)
    [hF : F.IsFiniteLocallyFreeOfRank (n + 1)] where
  system : ProjectiveBundleTautologicalSystem.{u} n
  realization : ProjectiveBundleRealization B F
  selected : realization = system.bundle B F hF

private theorem projectiveBundle_pullback_rank
    (B B' : Scheme.{u}) (n : ℕ) (F : B.Modules)
    (hF : projectiveBundleRank B n F) (g : B' ⟶ B) :
    projectiveBundleRank B' n ((Scheme.Modules.tensorPullback g).obj F) := by
  let : F.IsFiniteLocallyFreeOfRank (n + 1) := hF
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
    ((projectiveBundleTensorPullbackIso g).app F).symm

private theorem projectiveBundle_proper_of_frame
    {B : Scheme.{u}} {n : ℕ} {F : B.Modules}
    [F.IsFiniteLocallyFreeOfRank (n + 1)] (D : ProjectiveBundleRealization B F)
    (frame : ∀ (U : B.Opens) (e : B.ModuleFrame F U (n + 1)),
      ProjectiveBundleFrameChart D n U e) : IsProper D.A.data.relProjHom := by
  obtain ⟨I, U, hU, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free F (r := n + 1)
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) U hU
  intro i
  let e' : B.ModuleFrame F (U i) (n + 1) :=
    (projectiveBundleTensorPullbackIso (U i).ι).app F ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app F).symm ≪≫ (e i).some
  let C := frame (U i) e'
  rw [← C.relativeChart_over, ← C.polynomialChart_over]
  infer_instance

private theorem projectiveBundle_invertible_of_frame
    {B : Scheme.{u}} {n : ℕ} {F : B.Modules}
    [F.IsFiniteLocallyFreeOfRank (n + 1)] (D : ProjectiveBundleRealization B F)
    (frame : ∀ (U : B.Opens) (e : B.ModuleFrame F U (n + 1)),
      ProjectiveBundleFrameChart D n U e) : D.L.IsInvertible := by
  obtain ⟨I, U, hU, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free F (r := n + 1)
  have hlocal (i : I) :
      ((Scheme.Modules.pullback
        (D.A.data.relProjHom ⁻¹ᵁ U i).ι).obj D.L).IsFiniteLocallyFreeOfRank 1 := by
    let e' : B.ModuleFrame F (U i) (n + 1) :=
      (projectiveBundleTensorPullbackIso (U i).ι).app F ≪≫
        ((Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app F).symm ≪≫ (e i).some
    let C := frame (U i) e'
    have ht : ((Scheme.Modules.tensorPullback
        (C.relativeChart.hom ≫ C.polynomialChart.hom)).obj
        (ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) (U i).toScheme 1)).IsInvertible :=
      Scheme.Modules.IsInvertible.of_iso
        ((projectiveBundleTensorPullbackIso _).app _).symm
    have hi : ((Scheme.Modules.tensorPullback
        (D.A.data.relProjHom ⁻¹ᵁ U i).ι).obj D.L).IsInvertible :=
      Scheme.Modules.IsInvertible.of_iso C.twist
    have hi' : ((Scheme.Modules.pullback
        (D.A.data.relProjHom ⁻¹ᵁ U i).ι).obj D.L).IsInvertible :=
      Scheme.Modules.IsInvertible.of_iso ((projectiveBundleTensorPullbackIso _).app _)
    let : ((Scheme.Modules.pullback (D.A.data.relProjHom ⁻¹ᵁ U i).ι).obj D.L).IsInvertible := hi'
    have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
      ((Scheme.Modules.pullback (D.A.data.relProjHom ⁻¹ᵁ U i).ι).obj D.L)
    exact (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one
      ((Scheme.Modules.pullback (D.A.data.relProjHom ⁻¹ᵁ U i).ι).obj D.L)).mp inferInstance
  have : D.L.IsFiniteLocallyFreeOfRank 1 :=
    Scheme.Modules.isFiniteLocallyFreeOfRank_of_isOpenImmersion D.L
      (fun i ↦ (D.A.data.relProjHom ⁻¹ᵁ U i).ι)
      (by
        simp only [Scheme.Opens.opensRange_ι]
        rw [← Scheme.Hom.preimage_iSup, hU]
        rfl) hlocal
  have := (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one D.L).mpr
    (inferInstance : D.L.IsFiniteLocallyFreeOfRank 1)
  exact Scheme.Modules.IsInvertible.of_sheafOfModules D.L

/-- Finite locally free projective bundles and their tautological geometry.
Source: Stacks, Tags 01OB, 01O3, 01OE
(blueprint: lem-pur-projective-bundle-tautological-geometry).

Proof plan from the node:

1. Choose a Zariski cover trivializing $F$ and refine it by affine opens $V=\operatorname{Spec}R$,
using [def-amb-finite-locally-free-module]. In a chosen frame $v_0,\ldots,v_n$, [lem-weil-pbc-
quasi-coherent-symmetric-algebra] identifies the affine sections of $\operatorname{Sym}F$ with
$\operatorname{Sym}_R(R^{n+1})$. By [lem-weil-pbc-symmetric-algebra-free-module-polynomial], the
map sending $v_i$ to $T_i$ is an algebra isomorphism with $R[T_0,\ldots,T_n]$. It is graded: [lem-
weil-pbc-symmetric-algebra-graded] describes degree $d$ as the span of products of $d$ degree-one
generators, and the map and its inverse send each such product to a product of the same length.
The same construction works for a frame on any open $U$, since its affine restrictions agree on
their degree-one generators and hence agree as maps of symmetric algebra sheaves.

2. Apply the graded-equivalence clause of [prop-nagata-relative-proj-functoriality] to the frame
isomorphism in step 1. Relative Proj and its affine restriction data [def-nagata-relative-proj]
then identify $P|_U$ with $\operatorname{Proj}_U\operatorname{Sym}(\mathcal O_U^{n+1})=\mathbf
P^n_U$ [def-nagata-relative-projective-space]. On an affine base piece, $D_+(T_i)$ has structure
ring $H_i=(R[T_0,\ldots,T_n])_{(T_i),0}$, and these opens cover, by [prop-nagata-proj-standard-
open], since the variables generate the positive-degree ideal. This proves the scheme part of the
assertion about every frame, not just about the frames in the initial covering.

3. Here is the compatibility needed to glue the affine twists. For a degree-preserving algebra
isomorphism $\alpha:A\to C$, the map on the degree-one localization modules is
$a/f^m\mapsto\alpha(a)/\alpha(f)^m$, with $\deg a=m\deg f+1$; its inverse is the same formula for
$\alpha^{-1}$. The fraction relation is preserved by a ring map, and the formula commutes with the
localization restriction maps in [def-weil-pbc-proj-twisting-sheaf]. For restriction on the base,
use that same formula with the coefficient restriction map on a principal affine refinement, as in
the overlap data of [def-nagata-relative-proj]. For a principal base restriction $R\to R_s$, on a
frame chart both restrictions are the free module $H_i[1/s]T_i$: multiplication by $T_i$
identifies the degree-one fractions with the degree-zero ring, with inverse division by $T_i$.
Thus restrictions and frame changes induce compatible isomorphisms of the local twisting modules.
The identity and triple-overlap equations follow by applying the composite algebra map to the
numerator and denominator. Apply [lem-weil-pbc-site-module-sheaf-gluing] on the Zariski open site
of $P$ to these overlap isomorphisms to obtain the global module $L$. Its affine identifications
are precisely $\widetilde{(\operatorname{Sym}F)(1)}$; thus $L$ is the twisting module $\mathcal
O_P(1)$ specified in the statement. No intersection of affine base opens is assumed affine: the
formulas are checked on principal refinements inside affine pieces, and then on an affine covering
of each overlap.

4. On a frame chart $D_+(T_i)$, the definition of the shift in [def-weil-pbc-proj-twisting-sheaf]
gives $L=(A_{T_i})_1$, where $A=R[T_0,\ldots,T_n]$. Multiplication by $T_i$ gives an $H_i$-linear
isomorphism $H_i\to(A_{T_i})_1$, with inverse $a/T_i^m\mapsto a/T_i^{m+1}$; the two composites are
the identity by multiplication of fractions. On an overlap the generators satisfy
$T_i=(T_i/T_j)T_j$. Hence $L$ is locally free of rank one, so invertible by [def-sc-invertible-
module], and these trivializations identify it with [def-pc-projective-space-twist] by $e_i\mapsto
T_i$. The maps agree on overlaps by the displayed identity; they and their inverses glue by
applying the sheaf axiom to local sections. Together with step 2 this proves the asserted
identification of pairs in every frame.

5. To use properness for the precise projective-space interface, apply [lemma-nagata-relative-
proj-base-change-arbitrary] to $\mathcal O_{\operatorname{Spec}\mathbf Z}[T_0,\ldots,T_n]$ and
$U\to\operatorname{Spec}\mathbf Z$. The pullback algebra is $\mathcal O_U[T_0,\ldots,T_n]$: on
each affine piece this is [lem-weil-pbc-symmetric-algebra-base-change] applied to the free module,
with the polynomial identification of step 1. Thus $\mathbf P^n_U$ of step 2 is canonically
$\mathbf P(\{0,\ldots,n\};U)$ of [def-nagata-projective-space-base-change], over $U$. This latter
structural morphism is proper by [lemma-nagata-projective-space-base-change-proper]. Therefore $p$
is proper over every member of the frame cover, and [lemma-nagata-projective-target-local] gives
properness over $B$. These results require no Noetherian, finite-type-base, or separated-base
hypothesis.

6. Let $g:B'\to B$ be arbitrary. The pullback of $F$ is quasi-coherent by [lem-weil-pbc-module-
pullback-quasi-coherent], and its affine sections on $W=\operatorname{Spec}S\subseteq
g^{-1}(\operatorname{Spec}R)$ are $S\otimes_R F(\operatorname{Spec}R)$ by [lem-weil-pbc-module-
pullback-affine-sections] (interchanging the tensor factors). Apply [lem-weil-pbc-symmetric-
algebra-base-change] to obtain an isomorphism $$S\otimes_R\operatorname{Sym}_R
F(\operatorname{Spec}R)\xrightarrow{\sim}\operatorname{Sym}_S(S\otimes_R
F(\operatorname{Spec}R)).$$ It sends $s\otimes\iota(v)$ to $s\iota(1\otimes v)$. It and its
inverse preserve degree, since the homogeneous pieces are the spans of products of degree-one
generators [lem-weil-pbc-symmetric-algebra-graded]. These maps agree under restriction: both
restriction composites agree on coefficients and on every $\iota(v)$, hence on all products and
sums. By the sheaf axiom they give a canonical graded algebra isomorphism
$g^*\operatorname{Sym}F\cong\operatorname{Sym}(g^*F)$. The affine-section identifications here are
those of [lem-weil-pbc-quasi-coherent-symmetric-algebra].

7. Apply [lemma-nagata-relative-proj-base-change-arbitrary] to $\operatorname{Sym}F$ and the
graded-equivalence clause of [prop-nagata-relative-proj-functoriality] to step 6. This constructs
the asserted isomorphism $\mathbf P_{B'}(g^*F)\cong B'\times_B P$. To fix its map, use [lem-
nagata-affine-proj-scalar-extension] on the affine pieces in step 6. If $\beta$ is that graded
scalar-extension isomorphism and $\psi(a)=\beta(1\otimes a)$, the map to $P$ has inverse image
$D_+(\psi(f))$ of $D_+(f)$ and ring map $a/f^m\mapsto\psi(a)/\psi(f)^m$. These formulas determine
the map uniquely on the covering by the pulled-back frame charts; in particular this is the
canonical coefficient-pullback comparison, with no flatness condition on $g$.

8. Let $r:\mathbf P_{B'}(g^*F)\to P$ be the projection just constructed. On a pulled-back frame
chart the modules in $r^*L\to L'$ are free of rank one by step 4; define the map by $r^*T_i\mapsto
T'_i=\psi(T_i)$. In affine module coordinates this is an isomorphism: pullback of $H_iT_i$ is
$H'_i\otimes_{H_i}H_iT_i\cong H'_iT'_i$, by [lem-weil-pbc-module-pullback-affine-sections]. The
ring map of step 7 sends $T_i/T_j$ to $T'_i/T'_j$, so these maps agree on overlaps of standard
charts. Across changes of base frame, they too agree: on a degree-one fraction both formulas send
$a/f^m$ to $\psi(a)/\psi(f)^m$, using step 3 and the map on generators in step 6. Thus maps and
inverses glue by the sheaf axiom. This proves the canonical isomorphism $r^*\mathcal
O_P(1)\cong\mathcal O_{\mathbf P_{B'}(g^*F)}(1)$; it gives exactly the degree-one part of the
twist comparison, rather than assuming that part from the scheme-only base-change node. The
meaning of pullback is [def-pc-module-pullback], and the fraction description is [def-weil-pbc-
proj-twisting-sheaf].

9. For the identity base map the maps in steps 6--8 fix coefficients, degree-one generators, and
all fractions. For $B''\xrightarrow{h}B'\xrightarrow{g}B$, identify the iterated module pullbacks
by [def-pc-module-pullback]. On affine pieces with coefficient maps $R\to S\to T$, both symmetric-
algebra maps send $t\otimes(s\otimes\iota(v))$ to $t\,\overline{s}\,\iota(1\otimes v)$; the
corresponding maps on every Proj chart send $a/f^m$ to its image over $T$. By the uniqueness of
the chart-described morphism in [lem-nagata-affine-proj-scalar-extension] and [lem-weil-pbc-
scheme-morphism-gluing], the comparison scheme maps coincide. Their maps into the fibre products
coincide by the two projections [def-pc-fibre-product]. On the line modules both composites carry
the pulled-back generator $T_i$ to the same generator over $T$, so they coincide as well. This
proves identity and composition compatibility for both the scheme and twist isomorphisms.

10. Now let $K$ be any field and $n\geq1$. The quotient $K[T_0,\ldots,T_n]\twoheadrightarrow
K[T_1,\ldots,T_n]$, setting $T_0=0$, is graded and surjective. The closed-immersion clause of
[prop-nagata-relative-proj-functoriality] gives $\mathbf P^{n-1}_K\hookrightarrow\mathbf P^n_K$,
using [def-nagata-relative-projective-space] over the affine base. On $D_+(T_j)$ for $j\ne0$, the
map on dehomogenized rings sets $T_0/T_j$ equal to zero and fixes all other coordinates [lem-weil-
pbc-dehomogenization-polynomial-ring]. Its kernel is $(T_0/T_j)$: expand a polynomial in that one
variable as its constant term plus that variable times a polynomial. The source has no $D_+(T_0)$
chart. Thus this immersion is scheme-theoretically the subscheme $T_0=0$, not just a bijection on
points. Its twist restricts to the lower-dimensional twist, since the local generators $T_j$ and
ratios $T_j/T_k$ restrict to the identically named ones, as in step 4.

11. The complement of $T_0=0$ is $D_+(T_0)$: in its local trivialization the section $T_0$
vanishes exactly where its coefficient is in the point's maximal ideal. By [lem-weil-pbc-
projective-space-standard-charts], its non-vanishing locus is the standard open, and that chart
has coordinate algebra $K[t_1,\ldots,t_n]$, $t_i=T_i/T_0$. By [def-sbc-affine-space], this chart
is $\mathbf A^n_K$. The base-change model used by that chart theorem is the same one identified
with relative Proj in step 5, with the same generators by steps 4 and 8.

12. For any $i$, the equation of $D_i=\{T_i=0\}$ on $U_j=D_+(T_j)$ is $q_j=T_i/T_j$, by [lem-weil-
pbc-projective-space-standard-charts]. For $j=i$ this is $1$; for $j\ne i$ it is one polynomial
variable, a nonzerodivisor because multiplying by it shifts the monomial coefficients injectively.
Hence the ideal is an effective Cartier ideal [def-nagata-effective-cartier-ideal]. Its associated
line bundle is the dual ideal [def-pc-divisor-line-bundle]. Let $h_j$ be the dual generator with
$h_j(q_j)=1$. On $U_j\cap U_k$ one has $q_k=(T_j/T_k)q_j$, hence $h_j=(T_j/T_k)h_k$. These are
exactly the transitions for $\mathcal O(1)$ in [def-pc-projective-space-twist], so $e_j\mapsto
h_j$ glues to $\mathcal O(1)\cong\mathcal O(D_i)$. This also checks the sign of the twist: it is
$+1$.

13. The scheme-theoretic intersection $T_1=\cdots=T_n=0$ has empty intersection with $D_+(T_i)$
for $i\geq1$, because there the defining ideal contains $T_i/T_i=1$. By the covering and
coordinate-ring clauses of [lem-weil-pbc-projective-space-standard-charts], it is therefore
entirely in $D_+(T_0)=\mathbf A^n_K$, where its coordinate ring is
$K[t_1,\ldots,t_n]/(t_1,\ldots,t_n)\cong K$ (evaluation at zero, with inverse the constants). This
is a reduced point, with coordinates $t_1=\cdots=t_n=0$, hence the homogeneous point
$[1:0:\cdots:0]$. In particular no nilpotent thickening is hidden in the assertion about the
intersection.

14. Finally take $n=0$. Over any framed affine base open, the positive-degree ideal of $R[T]$ is
generated by $T$, so its entire Proj is $D_+(T)$ by [prop-nagata-proj-standard-open]. By [lem-
weil-pbc-dehomogenization-polynomial-ring] its degree-zero localization is the polynomial ring on
zero variables, namely $R$, with structure map the identity. Thus $p$ is locally an isomorphism to
the base; the local inverses agree because each is an inverse to $p$ on its open, and glue by
[lem-weil-pbc-scheme-morphism-gluing]. Moreover, step 4 identifies the twist with the free module
generated by $T$. The local isomorphism $F\to L$ over this base identification sends the frame $v$
to $T$. If $v'=uv$ for a unit $u$, then $T'=uT$ by the degree-one symmetric algebra map, so this
isomorphism is independent of the frame and glues. Hence $\mathcal O_P(1)$ corresponds to $F$,
including when $F$ is a nontrivial line bundle. All covering arguments also apply to the empty
base.
-/
theorem exists_projectiveBundleTautologicalGeometry
    (B : Scheme.{u}) (n : ℕ) (F : B.Modules)
    [F.IsFiniteLocallyFreeOfRank (n + 1)] :
    Nonempty (ProjectiveBundleTautologicalGeometry B n F) := by
  classical
  obtain ⟨M⟩ := exists_projectiveBundleFrameModels.{u} n
  obtain ⟨C⟩ := exists_projectiveBundleBaseChangeCoherence M
  let system : ProjectiveBundleTautologicalSystem.{u} n :=
    { bundle := M.bundle
      invertible := fun B F hF ↦ by
        let : F.IsFiniteLocallyFreeOfRank (n + 1) := hF
        exact projectiveBundle_invertible_of_frame (M.bundle B F hF) (M.frame B F hF)
      proper := fun B F hF ↦ by
        let : F.IsFiniteLocallyFreeOfRank (n + 1) := hF
        exact projectiveBundle_proper_of_frame (M.bundle B F hF) (M.frame B F hF)
      frame := M.frame
      pullback_rank := fun B B' F hF g ↦ projectiveBundle_pullback_rank B B' n F hF g
      baseChange := C.baseChange
      baseChange_id := C.baseChange_id
      baseChange_theta_id := C.baseChange_theta_id
      baseChange_comp := C.baseChange_comp
      baseChange_theta_comp := C.baseChange_theta_comp
      coordinate := fun K _ ↦ Classical.choice (exists_projectiveBundleCoordinateGeometry K n)
      rank_zero := fun B F hF hn ↦ by
        subst n
        let : F.IsFiniteLocallyFreeOfRank (0 + 1) := hF
        obtain ⟨qiso, hqiso⟩ := exists_projectiveBundleRankZero
          (M.bundle B F hF) (M.frame B F hF)
        exact ⟨qiso, hqiso⟩ }
  have hF : projectiveBundleRank B n F := by
    change F.IsFiniteLocallyFreeOfRank (n + 1)
    infer_instance
  exact ⟨{ system := system, realization := system.bundle B F hF, selected := rfl }⟩

end AlgebraicGeometry
