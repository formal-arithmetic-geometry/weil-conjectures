/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.CategoryTheory.ContinuousScalarRing
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Data.Fin.Tuple.Basic
import Sheaf.RepresentationTheory.TopologicalHomogeneousCochainCoordinates
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.CompactOpen
import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.Algebra.Homology.HomologySequence

/-! # Evaluation on the procyclic generator with continuous scalar coefficients

Source: Stacks Project, Tag 0DVG (the continuous cochain differential only), and the
agent-written scalar calculation supporting paragraph (3) of the main-20261015
six-functors direct-images proof. An exact analytic reference is WANTED.
(blueprint: lem-sfb-procyclic-scalar-cochain-evaluation).

The coordinates below specify the complexes up to their unique coordinate-preserving
isomorphisms. In particular they determine their data; they are not arbitrary complexes
or arbitrarily chosen comparison maps. Every function is continuous for the given norm
topology, and the quasi-isomorphism concerns ordinary sheaf images and kernels.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar Profinite.CondensedAction

namespace ContinuousCohomology

/-- The specified continuous scalar complexes and generator evaluation. Coordinates are
additive bijections onto all continuous functions, with the prescribed scalar action
and every parameter restriction. These conditions uniquely determine the objects and
arrows up to the coordinate-preserving isomorphism; no data is chosen from existence.
The ambient universe contains both the coefficient field and the profinite test sets.
Source: Stacks Tag 0DVG and the scalar input to blueprint direct-images paragraph (3)
(blueprint: lem-sfb-procyclic-scalar-cochain-evaluation). -/
structure ProcyclicScalarCochainEvaluation (ell : ℕ) [Fact ell.Prime]
    (F : Type u) [TopologicalSpace F] [CommRing F] [IsTopologicalRing F] where
  /-- The nonnegative continuous cochain complex, extended by zero to the integers. -/
  U : CochainComplex (Modules (continuousScalarRing F)) ℤ
  /-- The zero-differential complex in degrees zero and one. -/
  K : CochainComplex (Modules (continuousScalarRing F)) ℤ
  /-- Actual continuous-function coordinates in every nonnegative degree. -/
  uEval : ∀ (n : ℕ) (S : Profinite.{u}),
    sections (continuousScalarRing F) (U.X (n : ℤ)) S ≃+
      C(S × (Fin n → ℤ_[ell]), F)
  /-- The two nonzero terms have continuous-function coordinates. -/
  kEval : ∀ (n : ℕ) (_ : n ≤ 1) (S : Profinite.{u}),
    sections (continuousScalarRing F) (K.X (n : ℤ)) S ≃+ C(S, F)
  /-- The cochains vanish in negative degrees. -/
  uNegative : ∀ i : ℤ, i < 0 → IsZero (U.X i)
  /-- The target vanishes outside degrees zero and one. -/
  kOutside : ∀ i : ℤ, (i < 0 ∨ 1 < i) → IsZero (K.X i)
  /-- The degree-zero source differential is zero. -/
  uZero : U.d 0 1 = 0
  /-- All target differentials are zero. -/
  kZero : ∀ i j : ℤ, K.d i j = 0
  /-- Scalars act only through the profinite parameter. -/
  uScalar : ∀ (n : ℕ) (S : Profinite.{u})
    (a : sectionRing (continuousScalarRing F) S)
    (x : sections (continuousScalarRing F) (U.X (n : ℤ)) S)
    (s : S) (t : Fin n → ℤ_[ell]),
    uEval n S (a • x) (s, t) = a.down s * uEval n S x (s, t)
  /-- The target has the same pointwise scalar action. -/
  kScalar : ∀ (n : ℕ) (hn : n ≤ 1) (S : Profinite.{u})
    (a : sectionRing (continuousScalarRing F) S)
    (x : sections (continuousScalarRing F) (K.X (n : ℤ)) S) (s : S),
    kEval n hn S (a • x) s = a.down s * kEval n hn S x s
  /-- Source restrictions are precomposition, including empty profinite sets. -/
  uRestriction : ∀ (n : ℕ) (S T : Profinite.{u}) (v : T ⟶ S)
    (x : sections (continuousScalarRing F) (U.X (n : ℤ)) S)
    (s : T) (t : Fin n → ℤ_[ell]),
    uEval n T ((U.X (n : ℤ)).X.obj.map v.op x) (s, t) = uEval n S x (v s, t)
  /-- Target restrictions are precomposition. -/
  kRestriction : ∀ (n : ℕ) (hn : n ≤ 1) (S T : Profinite.{u}) (v : T ⟶ S)
    (x : sections (continuousScalarRing F) (K.X (n : ℤ)) S) (s : T),
    kEval n hn T ((K.X (n : ℤ)).X.obj.map v.op x) s = kEval n hn S x (v s)
  /-- The ordinary trivial-action inhomogeneous differential. The final contracted
  face drops the last coordinate; the other faces add adjacent coordinates. -/
  differential : ∀ (n : ℕ) (S : Profinite.{u})
    (x : sections (continuousScalarRing F) (U.X (n : ℤ)) S)
    (s : S) (t : Fin (n + 1) → ℤ_[ell]),
    uEval (n + 1) S (((U.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom.hom.app (op S)) x)
      (s, t) = uEval n S x (s, fun i ↦ t i.succ) +
        ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i.val + 1) •
          uEval n S x (s, Fin.contractNth i (· + ·) t)
  /-- Generator evaluation as an actual internal-module cochain map. -/
  epsilon : U ⟶ K
  /-- Degree zero is the identity, with the empty tuple identifying H^0 with a point. -/
  epsilonZero : ∀ (S : Profinite.{u})
    (x : sections (continuousScalarRing F) (U.X 0) S) (s : S),
    kEval 0 (by decide) S (((epsilon.f 0).hom.hom.app (op S)) x) s =
      uEval 0 S x (s, Fin.elim0)
  /-- Degree one evaluates at the additive generator 1. -/
  epsilonOne : ∀ (S : Profinite.{u})
    (x : sections (continuousScalarRing F) (U.X 1) S) (s : S),
    kEval 1 (by decide) S (((epsilon.f 1).hom.hom.app (op S)) x) s =
      uEval 1 S x (s, fun _ ↦ 1)
  /-- All other components are zero. -/
  epsilonOutside : ∀ i : ℤ, (i < 0 ∨ 1 < i) → epsilon.f i = 0

/-- Forget the scalar action while retaining the actual sheaf complex and all its maps.
Source: blueprint module objects and scalar-cochain compatibility
(blueprint: lem-sfb-procyclic-scalar-cochain-evaluation). -/
abbrev procyclicScalarUnderlying (F : Type u)
    [TopologicalSpace F] [CommRing F] [IsTopologicalRing F] :=
  (Mod.forget (D := Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    (continuousScalarRing F).X).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The ordinary derived localization in the standard larger universe. This is the
existing localization, with no additional size assumption or choice of a derived model.
Source: Stacks Tag 05RU, used by the scalar-cochain comparison
(blueprint: lem-sfb-procyclic-scalar-cochain-evaluation). -/
abbrev procyclicScalarLocalization (F : Type u)
    [TopologicalSpace F] [CommRing F] [IsTopologicalRing F] :=
  letI := HasDerivedCategory.standard (Modules (continuousScalarRing F))
  DerivedCategory.Q (C := Modules (continuousScalarRing F))

/-- Compatibility with a continuous scalar inclusion, characterized by postcomposition
on every cochain and on both target terms, with a commuting evaluation square.
Source: the scalar-cochain comparison, coefficient compatibility clause
(blueprint: lem-sfb-procyclic-scalar-cochain-evaluation). -/
structure ProcyclicScalarCoefficientCompatibility (ell : ℕ) [Fact ell.Prime]
    (E F : Type u) [TopologicalSpace E] [CommRing E] [IsTopologicalRing E]
    [TopologicalSpace F] [CommRing F] [IsTopologicalRing F]
    (iota : E →+* F)
    (D : ProcyclicScalarCochainEvaluation ell E)
    (D' : ProcyclicScalarCochainEvaluation ell F) where
  /-- The coefficient map on actual source sheaf complexes. -/
  uMap : (procyclicScalarUnderlying E).obj D.U ⟶
    (procyclicScalarUnderlying F).obj D'.U
  /-- The coefficient map on actual target sheaf complexes. -/
  kMap : (procyclicScalarUnderlying E).obj D.K ⟶
    (procyclicScalarUnderlying F).obj D'.K
  /-- Source coefficients are postcomposed with the inclusion. -/
  uFormula : ∀ (n : ℕ) (S : Profinite.{u})
    (x : sections (continuousScalarRing E) (D.U.X (n : ℤ)) S)
    (s : S) (t : Fin n → ℤ_[ell]),
    D'.uEval n S (((uMap.f (n : ℤ)).hom.app (op S)) x) (s, t) =
      iota (D.uEval n S x (s, t))
  /-- Target coefficients are postcomposed with the inclusion. -/
  kFormula : ∀ (n : ℕ) (hn : n ≤ 1) (S : Profinite.{u})
    (x : sections (continuousScalarRing E) (D.K.X (n : ℤ)) S) (s : S),
    D'.kEval n hn S (((kMap.f (n : ℤ)).hom.app (op S)) x) s =
      iota (D.kEval n hn S x s)
  /-- The coefficient square commutes already on cochain complexes. -/
  square : (procyclicScalarUnderlying E).map D.epsilon ≫ kMap =
    uMap ≫ (procyclicScalarUnderlying F).map D'.epsilon

/-- Evaluation on the generator is a quasi-isomorphism of the specified function-sheaf
complexes, for both a finite intermediate field and the norm-topological algebraic closure,
compatibly with their inclusion. The conclusion uses ordinary kernel/image cohomology
in the internal module category; no global primitive on each profinite set is asserted.
Source: Stacks Tag 0DVG supplies only the cochain convention; the proof below is the
agent-written analytic input to paragraph (3) of the main-20261015 direct-images proof.
(blueprint: lem-sfb-procyclic-scalar-cochain-evaluation).

Proof (DAG steps, retaining the noncomplete coefficients):

1. Each face in $d$ is precomposition by a continuous map, so it acts on all the indicated
continuous functions. Composing two faces in the two orders gives the same substitution, with
opposite alternating signs; hence $d^{q+1}d^q=0$. The convention $d^0=0$ is the trivial-action
degree-zero differential. Functions on $S\times H^q$ form a sheaf in $S$ by [def-sfb-continuous-
map-condensed-ring], applied to continuous functions and descent along the product with $H^q$.
Scalar multiplication through $S$ commutes with each face, and with restrictions. Thus these are
complexes of the internal modules defined in [sk-def-sfb-module-objects].

2. For $u:S'\to S$ one has $(f\circ(u\times1_H))(s';1)=f(u(s');1)$, and postcomposition by
$E\hookrightarrow\Omega$ commutes with evaluation and every finite sum. The identity in degree
zero and the zero maps in degrees at least two have the same naturality. Both sides of the
cochain-map identity in degree zero are zero because $d^0=0$; in degree one the target
differential and $\epsilon^2$ are zero, and higher degrees are zero as well. Evaluation is
$C(S,F)$-linear. This proves all the asserted map and compatibility clauses, including the empty
parameter.

3. In degree zero the cohomology is $C(S,F)$, and $\epsilon^0$ is its identity. A degree-one
cocycle satisfies $f(s;x+y)=f(s;x)+f(s;y)$. Put $a(s)=f(s;1)$. Additivity gives $f(s;m)=m a(s)$
for nonnegative integers $m$. Every basic congruence class of $H=\varprojlim_r\mathbf
Z/\ell^r\mathbf Z$ contains a nonnegative integer, so these integers are dense. The two continuous
functions $t\mapsto f(s;t)$ and $t\mapsto t a(s)$ agree on that dense subset and take values in
the Hausdorff norm field $F$, hence agree everywhere. Conversely $f(s;t)=t a(s)$ is jointly
continuous and a cocycle for each $a\in C(S,F)$. Since $d^0=0$ there are no degree-one boundaries.
Thus evaluation at $1$ is an isomorphism in degrees zero and one already on sections, for both
fields, without completeness.

4. For the higher degrees first let $B$ be either $E$ or $\widehat\Omega$. The first is complete
by [lem-weil-l-adic-extension-complete] and the second by [lem-sfb-normed-field-completion]. The
ultrametric inequality extends to the completion by taking limits in the inequality in $\Omega$;
the same applies to multiplication by $\mathbf Q_\ell$. For fixed $S$ set $V=C(S,B)$ with the
supremum norm. By [lem-sfb-compact-function-space-complete] this is a complete normed $\mathbf
Q_\ell$-vector space. Pointwise ultrametricity implies ultrametricity of its supremum norm, and
$\|a v\|=|a|_\ell\|v\|$ for $a\in\mathbf Z_\ell$. By [lem-coef-compact-open-currying], all the
function spaces in question can be curried as $C(H^q,V)$: the compact-open and supremum topologies
coincide here. In particular, continuous families remain continuous in the norm on $V$.

5. Put $R=C(H,V)$ and let $H$ act by $(t\cdot f)(x)=f(x+t)$. The action is jointly continuous: the
evaluation map on compact $H$ is continuous by [lem-coef-compact-open-currying], and currying the
continuous map $(t,f,x)\mapsto f(x+t)$ gives the action map. Set $\Delta f(x)=f(x+1)-f(x)$. It
commutes with this action. Its kernel is the constant functions, since invariance under $1$
implies invariance under the dense integer subgroup and then under all translations. By [lem-sfb-
banach-mahler-coordinates], if $\mathcal Mf=(a_0,a_1,\ldots)$ then $\mathcal M(\Delta
f)=(a_1,a_2,\ldots)$, directly from the forward-difference formula. Sending $(a_0,a_1,\ldots)$ to
$(0,a_0,a_1,\ldots)$ is a norm-one linear operator on $c_0$. Conjugating it by $\mathcal M$ gives
a continuous additive right inverse to $\Delta$. Hence $0\to
V\xrightarrow{\mathrm{const}}R\xrightarrow\Delta R\to0$ is exact and splits continuously as a
sequence of coefficient spaces. The splitting need not commute with the $H$-action.

6. Compute the cochains with coefficients in $R$ using [lem-sfb-topological-homogeneous-cochain-
coordinates], in additive notation. For a homogeneous equivariant cochain $F:H^{q+1}\to R$ put
$\phi(x_0,\ldots,x_q)=F(x_0,\ldots,x_q)(0)$. Equivariance is
$F(x_0+t,\ldots,x_q+t)(y)=F(x_0,\ldots,x_q)(y+t)$, so its inverse is
$F(x_0,\ldots,x_q)(y)=\phi(x_0+y,\ldots,x_q+y)$. Continuity in both directions follows from [lem-
coef-compact-open-currying]. The differential on $\phi\in C(H^{q+1},V)$ is alternating deletion.
For $q\geq1$ define $(h_q\phi)(x_0,\ldots,x_{q-1})=\phi(0,x_0,\ldots,x_{q-1})$. In
$h_{q+1}\delta\phi$, deletion of the prefixed zero gives $\phi$; every other deletion cancels its
counterpart in $\delta h_q\phi$ with the opposite sign. Thus $\delta h_q+h_{q+1}\delta=1$ in
positive degrees. These are actual continuous cochains. It follows that $H^q(C^\bullet(H,R))=0$
for $q\geq1$.

7. Apply continuous $q$-cochains to the coefficient sequence of step 5. Its continuous right
inverse makes $C(H^q,R)\xrightarrow\Delta C(H^q,R)$ surjective in every degree. Its kernel is
$C(H^q,V)$: the inverse to the constant inclusion is evaluation at $0$, which is continuous. The
equivariance of the coefficient maps makes this a degreewise short exact sequence of complexes of
abstract $\mathbf Q_\ell$-vector spaces. By [lem-weil-pbc-complex-ses-homology-long-exact], for
$n\geq2$ the segment $H^{n-1}(H,R)\to H^n(H,V)\to H^n(H,R)$ is exact. Both outside groups vanish
by step 6, so $H^n(H,V)=0$. Under the currying in step 4 this says that every closed element of
$C(S\times H^n,B)$ has an actual continuous primitive in $C(S\times H^{n-1},B)$, for $B=E$ and
$B=\widehat\Omega$.

8. For $F=E$, step 7 proves higher exactness on each parameter set. For $F=\Omega$, take any
$n\geq2$ and any closed $z\in C(S\times H^n,\Omega)$. Postcomposition with the isometric inclusion
$\iota:\Omega\hookrightarrow\widehat\Omega$ gives a continuous closed completed cochain. Step 7
with $B=\widehat\Omega$ provides its completed primitive. Now apply [lem-sfb-parameter-cochain-
completion-boundary-descent] with this $G=H$, the original $S$, and this $n$. Its hypotheses are
exactly the closedness and existence of a completed primitive just verified. It gives a finite
jointly surjective profinite cover $S_a\to S$ and genuine $\Omega$-valued continuous primitives
there. No Banach argument has been applied to $\Omega$ itself.

9. A section of the kernel sheaf in degree $n\geq2$ is locally in the image sheaf by step 8.
Images are always contained in kernels by $d^2=0$, so these sheaves are equal; this is ordinary
sheaf image, not its closure. In degrees zero and one the sectionwise inverse in step 3 is natural
in $S$ and therefore is an inverse on cohomology sheaves. Negative degrees are zero on both
complexes. The definition in [def-weil-abstract-derived-category] now makes $\epsilon$ a quasi-
isomorphism. The maps whose cohomology was computed are the explicit maps of step 2, so their
parameter and coefficient compatibility is the required compatibility. None of the argument
identifies these underived complexes with internal right derived invariants.
-/
theorem exists_procyclicScalarCochainEvaluation (ell : ℕ) [Fact ell.Prime]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ell] Ω] [IsAlgClosure ℚ_[ell] Ω]
    (E : IntermediateField ℚ_[ell] Ω) [FiniteDimensional ℚ_[ell] E] :
    ∃ (D : ProcyclicScalarCochainEvaluation ell E)
      (D' : ProcyclicScalarCochainEvaluation ell Ω),
      QuasiIso D.epsilon ∧ QuasiIso D'.epsilon ∧
        Nonempty {e : (procyclicScalarLocalization E).obj D.U ≅
          (procyclicScalarLocalization E).obj D.K //
            e.hom = (procyclicScalarLocalization E).map D.epsilon} ∧
        Nonempty {e : (procyclicScalarLocalization Ω).obj D'.U ≅
          (procyclicScalarLocalization Ω).obj D'.K //
            e.hom = (procyclicScalarLocalization Ω).map D'.epsilon} ∧
        Nonempty (ProcyclicScalarCoefficientCompatibility ell E Ω E.subtype D D') := by
  sorry

end ContinuousCohomology
