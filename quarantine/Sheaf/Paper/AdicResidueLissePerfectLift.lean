/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.CategoryTheory.ConstantCoefficientScalarExtension
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.RingedDerivedRestriction
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison
public import Sheaf.CategoryTheory.SiteConstantModuleHom
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Mathlib.RingTheory.Finiteness.Defs
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses

import Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore
import Sheaf.Paper.ConstantModuleSectionProperties
import WeilConjectures.AlgebraicGeometry.MLSetsTowerLimitNonempty
import Sheaf.Paper.NilpotentReductionLissity
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Sheaf.Algebra.Homology.KFlatCoefficientUniverse
import Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationExact
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import Sheaf.Paper.PbcActualScalarPullback
import Sheaf.RingTheory.RlimPerfectComplete
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Algebra.Homology.DerivedChangeOfRings
import Sheaf.Paper.TorsionLimitSheafCompleteness
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.AdicConstructibleFiniteReductions
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.WContractibleConstantReductionsML
import Sheaf.SixFunctors.ConnectedEtalePerfectConstant
/-!
# Local perfect lifting from lisse residue complexes

Source: Stacks Project, `proetale.tex`, Tag 09C6; Bhatt--Scholze, Lemma 6.6.8
(blueprint: lem-sfb-adic-residue-lisse-perfect-lift).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme


/-- The algebraic lift of comparison, specified on all operations and constants.
Source: Stacks Tags 00YV and 03D2
(blueprint: lem-sfb-adic-residue-lisse-perfect-lift). -/
def adicResidueComparisonData (X : Scheme.{u}) :=
  Classical.choice (CategoryTheory.ConstantCompletion.inverseImageData_exists
    (smallModelComparisonPullback.{u, v} X)
    (smallModelComparisonPushforward.{u, v} X) (smallModelProEtaleComparison.{u, v} X))

/-- Derived comparison with its canonical constant coefficient map.
Source: Stacks Tags 06YY and 099R
(blueprint: lem-sfb-adic-residue-lisse-perfect-lift). -/
def adicResidueComparison (X : Scheme.{u}) (R : Type (max v (u + 1))) [CommRing R] :=
  (CategoryTheory.ConstantCompletion.derivedPull (adicResidueComparisonData.{u, v} X)
    (smallModelComparisonPushforward.{u, v} X) (smallModelProEtaleComparison.{u, v} X)
    (CategoryTheory.ConstantCompletion.constantMap (adicResidueComparisonData.{u, v} X) R)).functor

/-- Completed constant realization of a complex of coefficient modules, termwise.
Source: Stacks Tag 09C6 (blueprint: lem-sfb-adic-residue-lisse-perfect-lift). -/
def adicResidueConstantPerfect (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) :
    CategoryTheory.ConstantCompletion.D
      (CategoryTheory.ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, v} X) A
        J) :=
  let F := SheafOfModules.strictPerfectConstantSheaf (coefficientProEtaleModelTopology.{u, v} X) A ⋙
    SheafOfModules.restrictScalars
      (CategoryTheory.constantModuleHomRingIso (coefficientProEtaleModelTopology.{u, v} X) A).inv ⋙
    CategoryTheory.ConstantCompletion.change
      (CategoryTheory.ConstantCompletion.coefficientMap (coefficientProEtaleModelTopology.{u, v}
        X) A J)
  (CategoryTheory.ConstantCompletion.Q
    (CategoryTheory.ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, v} X) A
      J)).obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)

/-- Cohomology in the standard localization used by the coefficient package.
Source: Stacks Tag 05RU (blueprint: lem-sfb-adic-residue-lisse-perfect-lift). -/
abbrev adicResidueCohomology {D : Type w} [SmallCategory D]
    {T : GrothendieckTopology D} (R : Sheaf T CommRingCat.{w}) (q : ℤ) :
    CategoryTheory.ConstantCompletion.D R ⥤ CategoryTheory.ConstantCompletion.Mod R :=
  @DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) q

/-- Exact restriction to the actual localized site, at the same standard localization.
Source: Stacks Tag 03DJ (blueprint: lem-sfb-adic-residue-lisse-perfect-lift). -/
def adicResidueRestriction {D : Type w} [SmallCategory D]
    {T : GrothendieckTopology D} (R : Sheaf T CommRingCat.{w}) (U : D) :
    CategoryTheory.ConstantCompletion.D R ⥤ CategoryTheory.ConstantCompletion.D (R.over U) :=
  letI := HasDerivedCategory.standard (CategoryTheory.ConstantCompletion.Mod R)
  letI := HasDerivedCategory.standard (CategoryTheory.ConstantCompletion.Mod (R.over U))
  CategoryTheory.ringedDerivedRestriction R U

/-- Cohomology of the existing total tensor with a module in degree zero.
With a K-flat first factor this is precisely the derived Tor test.
Source: Stacks Tags 06YS and 09C6
(blueprint: lem-sfb-adic-residue-lisse-perfect-lift). -/
def adicResidueTensorCohomology {D : Type w} [SmallCategory D]
    {T : GrothendieckTopology D} (R : Sheaf T CommRingCat.{w})
    (P : CategoryTheory.ConstantCompletion.Cx R)
    (N : CategoryTheory.ConstantCompletion.Mod R) (q : ℤ) :
    CategoryTheory.ConstantCompletion.Mod R :=
  (((CategoryTheory.ringedKoszulTensor R).obj P).obj
    ((HomologicalComplex.single (CategoryTheory.ConstantCompletion.Mod R)
      (ComplexShape.up ℤ) 0).obj N)).homology q

/-- A complete completed-coefficient complex with bounded lisse finite-Tor residue has
bounded finite-projective constant local models. The residue is an etale complex; its
comparison is taken only after derived reduction. The Tor test is written on every
K-flat representative, using the existing total tensor with degree-zero module sheaves.
The covering sieve is on the transported final object. The termwise completed model
uses the canonical constant-ring comparison and ordinary scalar extension.

Source: Stacks Project, proetale.tex, Tag 09C6 and Section 099L; Bhatt--Scholze,
Lemma 6.6.8 and Proposition 6.6.11
(blueprint: lem-sfb-adic-residue-lisse-perfect-lift).

Proof (deferred):
1. Choose generators of $J$, possible since $A$ is Noetherian, and put
$N=\operatorname{Res}_{\underline A}M$. The constant/completed coefficient equivalence applies
on $X_{\mathrm{proét}}$: its completed ring is exactly $B_X$, its completeness notion is the
local one in the statement, and it identifies the reductions of $N$ and $M$ compatibly with all
quotient maps. The residue complex $C$ is constructible, using the single stratum $X$ for each
of its finitely many nonzero locally constant cohomology sheaves. Apply the finite-reduction
structure lemma to $N,C,[a,b]$. Write $A_n=A/J^n$, $M_n=M\otimes^L_{B_X}\underline{A_n}$, and
obtain étale $C_n$ with bounded constructible cohomology and Tor amplitude $[a,b]$, and
compatible $\alpha_n,\beta_n$. In particular $M$ is the derived limit of this specified quotient
tower after restricting scalars. No perfectness of $A_n$ over $A$ was invoked.
Uses: lem-weil-pbc-constant-completion-equivalence,
lem-sfb-adic-constructible-finite-reductions.
2. Work on a connected clopen component $Y$ of an affine Noetherian chart of $X$. These form an
open covering. Indeed the underlying affine space is Noetherian by the cited lemma; Noetherian
induction on closed subsets gives finitely many irreducible components (a minimal counterexample
would be reducible into two smaller closed subsets). Grouping those finitely many components by
chains of nonempty intersections gives finitely many connected components; each group and its
complement are finite unions of closed components, hence clopen. Slice restriction is identified
with the pro-étale site of $Y$ by the localization lemma. It is sectionwise restriction, so
preserves products and kernels, and it preserves epimorphisms because their locally lifting
sections lift over the same covering in the slice. It is therefore exact. It preserves constant
sheaves and their inverse limits. Countable products are exact and represent derived products;
consequently restriction takes the quotient Roos triangle, including its completion unit, to the
same triangle on $Y$. Thus $M|_Y$ and $N|_Y$ remain complete and have the restricted compatible
quotient tower. Restriction also commutes with the total tensor calculation on K-flat
resolutions. Apply the finite-reduction structure lemma on $Y$, choosing these restricted
markings, and henceforth replace $X$ by nonempty connected affine $Y$.
Uses: lem-sc-affine-noetherian-underlying-space, lem-weil-proetale-weakly-etale-localization,
lem-weil-proetale-countable-products-exact, lem-weil-derived-countable-products-core,
lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-weil-pbc-constant-completion-equivalence,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-sfb-adic-constructible-finite-reductions.
3. For each $n$, apply nilpotent-reduction lissity on the étale site with coefficient ring
$A_n$, ideal $J/J^n$, and bounded complex $C_n$. The ideal is nilpotent, $A_n$ is Noetherian
(ideals correspond to ideals of $A$ containing $J^n$), and the normalized reduction of $C_n$
modulo $J/J^n$ is $C_1=C$. Thus all cohomology sheaves of $C_n$ are étale locally constant of
finite type. The connected étale perfect-constancy lemma now applies: the Tor bound and
boundedness were provided in step 1. Fix one geometric point $\bar x$ of $Y$ and put
$E_n=(C_n)_{\bar x}$. It gives a perfect $E_n$ and one étale local constant value $E_n$ for
$C_n$. Take the exact stalk of $\beta_n$. The tensor-pullback comparison gives normalizations
$E_{n+1}\otimes^L_{A_{n+1}}A_n\simeq E_n$. Define the transition $E_{n+1}\to E_n$ as the
scalar-extension unit followed by this normalization, considered first in $D(A_{n+1})$ and then
in $D(A)$. On K-flat representatives the unit is $p\mapsto p\otimes1$ and reassociation is
$(p\otimes u)\otimes v\mapsto p\otimes uv$; hence the stalk normalizations have the same
quotient cocycles as the $\beta_n$.
Uses: lem-weil-pbc-nilpotent-reduction-lissity, lem-sfb-connected-etale-perfect-constant,
prop-weil-pbc-geometric-stalks-exact, lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
lem-pur-derived-change-of-rings.
4. Apply algebraic perfect inverse-limit reconstruction to the tower $E_n$ with those
transitions. Its ring hypothesis is the given $A\simeq\varprojlim A/J^n$, and $E_1$ is perfect
by step 3. Obtain a perfect $P\in D(A)$ and projection-induced isomorphisms $P\otimes_A^L
A_n\simeq E_n$ compatible with all transitions. Choose a bounded finite-projective
representative $P^\bullet$. Next take an affine weakly contractible pro-étale covering $\{W_t\to
Y\}$. The weakly contractible clause of the connected perfect-constancy lemma gives, for each
$n$ and each $W=W_t$, an isomorphism
$M_n|_W\simeq\underline{E_n}|_W\simeq\underline{P^\bullet\otimes_A A_n}|_W$. These isomorphisms
need not be compatible, and no such compatibility is presumed in the next step. For every such
$W$, the localization lemma identifies $Y_{\mathrm{proét}}/W$ with $W_{\mathrm{proét}}$.
Restriction is exact, preserves sectionwise products and the finite Koszul tensor complexes, and
therefore preserves their Roos completion unit, since countable products are exact. Hence $M|_W$
is locally derived complete, and restriction of the completed coefficient ring is
$B_Y|_W=\varprojlim_n\underline{A_n}|_W$; this justifies the completion calculation on $W$
below.
Uses: lem-weil-pbc-rlim-perfect-complete, def-pc-perfect-ring-complex,
lem-weil-pbc-proetale-affine-wcontractible-covering-family,
lem-sfb-connected-etale-perfect-constant, lem-weil-proetale-weakly-etale-localization,
lem-weil-proetale-countable-products-exact, lem-weil-derived-countable-products-core,
lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-weil-pbc-constant-completion-equivalence.
5. Fix $W$ and write $B=B_X|_W$, $T=B\otimes_A P^\bullet$, and
$T_n=\underline{P^\bullet\otimes_A A_n}|_W$. Every term of $T$ is the image of an idempotent on
a finite power of $B$. In fact it is the inverse limit of the corresponding idempotent summands
of $\underline{A_n}^{\,r}$, since an image of an idempotent is the equalizer of that idempotent
and the identity. These summands are killed by $J^n$. The torsion-limit completeness theorem
makes $T$ complete after restriction to $\underline A$, and the constant/completed equivalence
makes it complete over $B$. Put $P^\vee=\operatorname{Hom}_A^\bullet(P^\bullet,A)$, with degree
$i$ term $\operatorname{Hom}_A(P^{-i},A)$ and differential $(-1)^{i+1}$ times precomposition by
$d_P$. Set $H=(B\otimes_A P^\vee)\otimes_B^L M|_W$. A finite-projective term is a retract of a
finite free term, so its tensor is exact; a bounded such complex is K-flat. Its tensor with a
product is the product of its tensors: each total degree has only finitely many summands, and
for an idempotent $e$ on a finite free module, its image commutes with products because
$\operatorname{im}(e)=\ker(1-e)$ and products commute with kernels and finite powers. Thus
tensoring the quotient-completion Roos triangle of $M|_W$ with this bounded dual identifies
$H\simeq R\lim_n H_n$, where $H_n=T_n^\vee\otimes_{\underline{A_n}}^L M_n|_W$ are its canonical
reductions. The coefficient-completion lemma identifies this quotient-limit unit with the local
completeness unit, so $H$ is locally complete. By step 4 every $H_n$ is a constant complex with
value $(P^\vee\otimes_A A_n)\otimes_{A_n}(P^\bullet\otimes_A A_n)$. This is perfect, in
particular at $n=1$.
Uses: lem-weil-pbc-torsion-limit-sheaf-completeness,
lem-weil-pbc-constant-completion-equivalence, lem-pc-kflat-closure,
lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-pur-derived-change-of-rings.
6. For clarity the degree-zero cohomology groups $G_n=H^0(W,H_n)$ are precisely
$\operatorname{Hom}_{D(W_{\mathrm{proét}},A_n)}(T_n,M_n|_W)$. Evaluation on $W$ is exact. The
sheaf $\underline{A_n}$ is therefore projective in the slice module category, since its Hom
functor is evaluation; each term of $T_n$ is a finite direct summand of such free sheaves and is
projective too. Bounded-above projective complexes are K-projective, so the derived-Hom
bijection identifies these morphisms with chain maps modulo chain homotopy. Termwise
finite-projective duality identifies their Hom complex with $T_n^\vee\otimes M_n|_W$: on a
summand of $A_n^r$ the map is $\lambda\otimes m\mapsto(p\mapsto\lambda(p)m)$; for complexes use
the displayed dual differential and the usual tensor sign. Over $B$, exact evaluation gives
$\operatorname{Hom}_B(B,F)=F(W)$, so the finite direct summands of finite free $B$-sheaves in
$T$ are projective. The two cited K-projective statements then identify
$\operatorname{Hom}_{D(B)}(T,M|_W)$ with $H^0$ of the global Hom complex. Evaluation
$\lambda\otimes m\mapsto(p\mapsto\lambda(p)m)$, with the dual differential of step 5, identifies
that complex with the sections of a representative of $H$; exact evaluation identifies its
cohomology with $H^0(W,H)$. These identifications commute with quotient reduction because the
evaluation formula and both differentials commute with the coefficient map $A_{n+1}\to A_n$.
Apply the weakly contractible ML lemma to $\operatorname{Res}H$. Its reductions are the $H_n$ by
coefficient comparison, it is complete by step 5, and its first constant value is perfect.
Therefore the tower $G_n$ has eventually stable images. Each $G_n$ contains an isomorphism by
step 4.
Uses: lem-weil-pbc-proetale-weakly-contractible-evaluation-exact,
lem-sc-bounded-above-projective-kprojective, lem-coef-kprojective-derived-hom-bijection,
lem-sfb-wcontractible-constant-reductions-ml, lem-weil-pbc-constant-completion-equivalence.
7. Let $S_n=\bigcap_{k\geq n}\operatorname{im}(G_k\to G_n)$. The ML property says that this
intersection is an eventual image. The maps $S_{n+1}\to S_n$ are surjective: for fixed $n$,
choose $k$ beyond stabilization at both $n$ and $n+1$ and lift an element of $S_n$ from $G_k$.
Choose $k$ beyond stabilization at $1$ and an isomorphism in $G_k$; its reduction $g_1\in S_1$
is an isomorphism. Repeatedly lift along the surjections $S_{n+1}\to S_n$ to obtain a compatible
sequence $(g_n)$ beginning with $g_1$. Equivalently apply the nonempty-ML-limit lemma to the
fibers over $g_1$ in the stable systems. Apply the sheaf Milnor sequence to the strict quotient
tower $H_n$. The Roos model is a derived limit by exact countable products. Exact evaluation at
$W$ preserves the resulting epimorphism $H^0(H)\twoheadrightarrow\lim_nH^0(H_n)$, and evaluation
commutes with the limit sectionwise. Thus $(g_n)$ lifts to a class in $H^0(W,H)$, hence by step
6 to an actual morphism $g:T\to M|_W$ of $B$-complexes. Its derived reduction modulo $J$ is
$g_1$, an isomorphism. This constructs the compatible map; it does not take a nonfunctorial
limit of independently chosen isomorphisms.
Uses: lem-sfb-wcontractible-constant-reductions-ml, lem-weil-pbc-ml-sets-tower-limit-nonempty,
det-pe-milnor-sequence, lem-weil-proetale-countable-products-exact,
lem-weil-derived-countable-products-core, lem-weil-pbc-ringed-strict-tower-homotopy-limit,
lem-weil-pbc-proetale-weakly-contractible-evaluation-exact.
8. Let $Q=\operatorname{Cone}(g)$. Local completeness is closed under cones: the
Koszul-completion unit in the constant/completed lemma is a natural map between exact functors
(finite Koszul tensor and the exact derived-limit functor); its cone vanishes at the third
vertex whenever it vanishes at the other two, by the long exact cohomology sequence. Since both
$T$ and $M|_W$ are complete, $Q$ is complete. Its first reduction is zero. All its reductions
are zero: the exact constant sequence $0\to J^n/J^{n+1}\to A/J^{n+1}\to A/J^n\to0$ gives after
derived tensor with $\operatorname{Res}Q$ a triangle whose first term is
$(Q\otimes_B^L\underline{A/J})\otimes_{\underline{A/J}}^L\underline{J^n/J^{n+1}}=0$. Induction
from $n=1$ proves the claim. Constant realization is exact; derived scalar extension preserves
this triangle, and reassociation is the balancing map already written in step 3. Completeness
therefore gives $Q\simeq R\lim_n0=0$. The long exact cohomology sequence shows $g$ is an
isomorphism. On each $W_t$ we have proved exactly $M|_{W_t}\simeq (B_X|_{W_t})\otimes_A
P^\bullet$. The tensor is computed termwise because the finite-projective terms are flat and the
complex is bounded. Assemble the covers over all connected affine components of the original
$X$. If $X$ is empty take the empty cover. All coefficient rings remain the original $A$ and its
quotients; neither finiteness as sets nor quotient perfectness was used.
Uses: lem-weil-pbc-constant-completion-equivalence,
lem-weil-pbc-ringed-strict-tower-homotopy-limit, lem-sf-derived-homology-long-exact,
lem-weil-pbc-constant-module-section-properties, lem-pur-derived-change-of-rings,
lem-pc-kflat-closure.
-/
theorem adicResidueLissePerfectLift
    (X : Scheme.{u}) [IsNoetherian X]
    {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) [IsAdicComplete J A]
    (M : CategoryTheory.ConstantCompletion.D
      (CategoryTheory.ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, v} X) A J))
    (_hcomplete : CategoryTheory.ConstantCompletion.IsComplete
      (CategoryTheory.ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, v} X) A
        J 0) M)
    (C : CategoryTheory.ConstantCompletion.D
      (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A J 0))
    (_hbounded : ∃ c d : ℤ, ∀ q : ℤ, q < c ∨ d < q →
      IsZero ((adicResidueCohomology.{max v (u + 1)}
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0)
          q).obj C))
    (_hlisse : ∀ q : ℤ, SheafOfModules.IsLocallyConstantFiniteTypeModules
      (smallModelComparisonEtaleTopology.{u, v} X) (A ⧸ J ^ (0 + 1))
      ((adicResidueCohomology.{max v (u + 1)}
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0)
          q).obj C))
    (a b : ℤ) (_hab : a ≤ b)
    (_htor : ∀ P : CategoryTheory.ConstantCompletion.Cx
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0),
      CochainComplex.IsKFlatIndependentCoefficients
        (J := smallModelComparisonEtaleTopology.{u, v} X)
        (R := CategoryTheory.ConstantCompletion.finite
          (smallModelComparisonEtaleTopology.{u, v} X) A J 0) P →
      Nonempty ((CategoryTheory.ConstantCompletion.Q
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0)).obj P ≅ C) →
      ∀ (N : CategoryTheory.ConstantCompletion.Mod
        (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X) A
          J 0))
        (q : ℤ), q < a ∨ b < q →
        IsZero (adicResidueTensorCohomology.{max v (u + 1)}
          (CategoryTheory.ConstantCompletion.finite (smallModelComparisonEtaleTopology.{u, v} X)
            A J 0) P N q))
    (_hres : Nonempty
      ((CategoryTheory.ConstantCompletion.extend
        (CategoryTheory.ConstantCompletion.projection (coefficientProEtaleModelTopology.{u, v} X)
          A J 0)).obj M ≅
        (adicResidueComparison.{u, v} X (A ⧸ J ^ (0 + 1))).obj C)) :
    ∃ S : Sieve ((AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).obj (⊤_ X.ProEt)),
      S ∈ coefficientProEtaleModelTopology.{u, v} X _ ∧
      ∀ (U : coefficientProEtaleSiteModel.{u, v} X)
        (f : U ⟶ (AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).obj (⊤_
          X.ProEt)), S f →
        ∃ (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) (c d : ℤ),
          P.IsStrictlyGE c ∧ P.IsStrictlyLE d ∧
          (∀ q : ℤ, Module.Finite A (P.X q) ∧ Module.Projective A (P.X q)) ∧
          Nonempty
            ((adicResidueRestriction.{max v (u + 1)}
              (CategoryTheory.ConstantCompletion.completed (coefficientProEtaleModelTopology.{u,
                v} X) A J) U).obj M ≅
              (adicResidueRestriction.{max v (u + 1)}
                (CategoryTheory.ConstantCompletion.completed
                  (coefficientProEtaleModelTopology.{u, v} X) A J) U).obj
                    (adicResidueConstantPerfect.{u, v} X J P)) := by
  sorry

end AlgebraicGeometry.Scheme
