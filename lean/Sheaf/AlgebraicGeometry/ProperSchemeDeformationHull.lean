/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.ProperSchemeStalkTangentData
import Sheaf.AlgebraicGeometry.PointwiseFlatnessBaseChange
import Sheaf.AlgebraicGeometry.SchemeSquareZeroLiftTorsor
import Sheaf.AlgebraicGeometry.ProperSchemeCoherentExtFinite
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-! # Hull and tangent space of a proper scheme's deformation functor

Source: Stacks Project, examples-defos.tex, Tags 0DY9, 0DYA and 0ET5,
with coefficient ring Lambda = k
(blueprint: lem-sfb-proper-scheme-deformation-hull).

The hull and both tangent identifications are given simultaneously, including
restriction and continuous completed-local compatibility.
## Main statements

- `TangentVectorSpace` and `HullConclusion` package the explicit assertion.
- `exists_hull` states all clauses of the proper scheme hull theorem.

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option genSizeOfSpec false
set_option genInjectivity false
universe u v w
open CategoryTheory CategoryTheory.Limits
open Algebra.CotangentResolution
namespace AlgebraicGeometry.ProperSchemeDeformation
variable [hRing : ∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
  [∀ X : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  {k : Type u} [Field k] {X : Scheme.{u}}

/-- A vector-space identification retaining the operations it transports.
Source: Stacks 0DY9 and 06IG
(blueprint: lem-sfb-proper-scheme-deformation-hull). -/
structure TangentVectorSpace (C : Coherence.{u}) (D : TopCat.SheafCotangent.Comparison C)
    (f : X ⟶ Spec (.of k)) (V : Type v) where
  group : AddCommGroup V
  module : @Module k V _ group.toAddCommMonoid
  identify : @LinearEquiv k k _ _ (RingHom.id k) (RingHom.id k) _ _
    V (TangentExt C D f) group.toAddCommMonoid _ module (extModule C D f)

/-- All clauses of the hull theorem, with canonical maps fixed on representatives.
`finite` uses the structural k-action; `rigidity` concerns this very hull.
Source: Stacks 0DY9, 0DYA, 0ET5, 0DYW, 0DZM and 0DYV
(blueprint: lem-sfb-proper-scheme-deformation-hull). -/
structure HullConclusion (C : Coherence.{u}) (D : TopCat.SheafCotangent.Comparison C)
    (f : X ⟶ Spec (.of k)) where
  functor : ClassFunctor f
  hull : Hull f functor
  tangent : TangentNaturality C D f
  properTangent : Classes f (ArtinDeformation.squareZeroTest (R := k) (k := k) k) ≃
    SchemeDeformation.Classes f
      (SchemeDeformation.directionReduction k (ModuleCat.of k k))
  transport_exists : ∀ Y : Deformation f
    (ArtinDeformation.squareZeroTest (R := k) (k := k) k),
    ∃ Z : SchemeDeformation.Lift f
      (SchemeDeformation.directionReduction k (ModuleCat.of k k)),
      Nonempty (IsTangentTransport f Y Z)
  transport_class : ∀ (Y : Deformation f
    (ArtinDeformation.squareZeroTest (R := k) (k := k) k))
    (Z : SchemeDeformation.Lift f
      (SchemeDeformation.directionReduction k (ModuleCat.of k k))),
    Nonempty (IsTangentTransport f Y Z) → properTangent (classOf f Y) = Z.class
  properVector : TangentVectorSpace C D f
    (Classes f (ArtinDeformation.squareZeroTest (R := k) (k := k) k))
  proper_normalization : ∀ x : Classes f
    (ArtinDeformation.squareZeroTest (R := k) (k := k) k),
    properVector.identify x = tangent.global.identify (properTangent x)
  hullVector : TangentVectorSpace C D f (ArtinDeformation.LocalMap hull.algebra
    (ArtinDeformation.squareZeroTest (R := k) (k := k) k))
  hull_normalization : ∀ b : ArtinDeformation.LocalMap hull.algebra
    (ArtinDeformation.squareZeroTest (R := k) (k := k) k),
    hullVector.identify b = properVector.identify
      (hull.eta (ArtinDeformation.squareZeroTest (R := k) (k := k) k) b)
  finite : @Module.Finite k (TangentExt C D f) _ _ (extModule C D f)
  completion : ClosedCompletionCompatibility C D f tangent.global
  localNoetherian : ∀ x : X, IsNoetherianRing (localAlgebra f x)
  localPresentation : ∀ x : X, IsClosed ({x} : Set X) →
    ∃ P : Naive.Presentation (SchemeDeformation.affineArrow k (localAlgebra f x)),
      Naive.IsLocalizedPolynomial P ∧ CompletedSchemeTangent.IsFiniteLocalizedPolynomial P
  rigidity : (∀ d : (SheafOfModules.unit X.ringCatSheaf).val.Derivation'
    (Scheme.Modules.tensorPullbackRingMap f).hom,
    ∀ (V : X.Opens) (a : Γ(X, V)), d.d (X := Opposite.op V) a = 0) →
    ∀ A : ArtinDeformation.TestCategory k k, Function.Bijective (hull.eta A)

/-- A proper scheme has a hull; the canonical tangent spaces are finite-dimensional
cotangent Ext-one, compatible with opens and continuous completion. Vanishing of
all structural sheaf derivations makes the hull itself an isomorphism.
Source: Stacks 0DY9, 0DYA and 0ET5
(blueprint: lem-sfb-proper-scheme-deformation-hull).

Proof (the node's six steps):
1. For an Artinian local base $R$, its maximal ideal is nilpotent and $R$ is Noetherian. Hence
properness reflection identifies the groupoid $\mathcal D_X(R)$ of all marked flat scheme
deformations with that of proper flat ones: every such deformation has proper special fibre $X$.
Base change preserves flatness and properness, so these groupoids and their isomorphism classes
give the stated functor. Over $k$ a marked object has a unique marked isomorphism to $X$, so
$\mathcal D_X(k)$ is equivalent to a point.
Uses: lem-weil-pbc-artinian-local-noetherian-nilpotent,
lem-sfb-proper-nilpotent-base-change-reflection, lem-sfb-pointwise-flatness-base-change,
lem-weil-pbc-proper-base-change.

2. For $A_1\to A\leftarrow A_2$ with $A_2\twoheadrightarrow A$, put $B=A_1\times_AA_2$. The
infinitesimal affine-chart lemma identifies the base pushout with $\operatorname{Spec}B$. A pair
of deformations with a specified identification over $A$ has a scheme pushout $Z$ over this base,
recovering both deformations by that lemma. Each deformation is proper by step 1, and therefore
locally finitely presented over its Noetherian Artinian base. Flat patching makes $Z$ flat and
locally finitely presented; its canonical reconstruction map is invertible for every flat scheme.
A pair of compatible morphisms glues uniquely by the universal property of the pushout. These
identifications give inverse functors on objects and morphisms. The common marking over $k$ glues.
Properness reflection makes $Z$ proper, since $B$ is again in $\mathrm{Art}_k$: Noetherianity and
nilpotence make each $\mathfrak m_R^i/\mathfrak m_R^{i+1}$ finite-dimensional over $k$, so each
input ring is finite-dimensional. The subring $B\subset A_1\oplus A_2$ is finite-dimensional, and
its common residue map to $k$ has nilpotent kernel. Pairs of nonzero common residue are invertible
componentwise, hence this kernel is its unique maximal ideal. Thus $\mathcal D_X$ has the full
Rim-Schlessinger equivalence, including its specified gluing isomorphism.
Uses: lem-sfb-infinitesimal-pushout-affine-charts, lem-sfb-scheme-pushout-flat-patching,
pqf-lem-lft-fp-locnoeth, lem-weil-pbc-artinian-local-noetherian-nilpotent,
lem-sfb-proper-nilpotent-base-change-reflection.

3. Apply the square-zero lift torsor theorem to
$\operatorname{Spec}k\hookrightarrow\operatorname{Spec}k[\epsilon]/(\epsilon^2)$. Its ideal is
$k\epsilon$, and its pullback is $\mathcal O_X$ by $a\otimes c\epsilon\mapsto ca$. The trivial
lift supplies the origin. This gives $T F_X\cong\operatorname{Ext}^1_X(L_{X/k},\mathcal O_X)$,
with the asserted $k$-linear structure. For the trivial lift an automorphism on its structure
sheaf is $(a,b)\mapsto(a,b+D(a))$; multiplicativity is exactly $D(aa')=aD(a')+a'D(a)$ and the
$k$-algebra condition is $D|_k=0$. Conversely each such derivation gives this automorphism, and
composition adds derivations. Thus $\operatorname{Inf}(\mathcal D_X)=\operatorname{Der}_k(\mathcal
O_X,\mathcal O_X)$, without imposing any smoothness on $X$.
Uses: lem-sfb-scheme-square-zero-lift-torsor.

4. Every affine chart of $X$ has a finitely generated $k$-algebra of sections, so it is
Noetherian. The structure morphism is locally finitely presented because it is finite type over
the Noetherian field. The cotangent truncation theorem gives $N=\tau_{\geq-1}L_{X/k}$ with
coherent cohomology in degrees $-1,0$, coherent $\mathcal O_X$, and
$\operatorname{Ext}^1_X(N,\mathcal O_X)\cong\operatorname{Ext}^1_X(L_{X/k},\mathcal O_X)$. Apply
proper coherent Ext finiteness over $k$ to $K=N$ and $E=\mathcal O_X[0]$. All its bounds hold, so
this Ext group is a finite-dimensional $k$-vector space. This argument uses a coherent truncation
and makes no assertion that the full cotangent complex is bounded below.
Uses: lem-wf-affine-noetherian-components, pqf-lem-lft-fp-locnoeth,
lem-sfb-noetherian-scheme-cotangent-truncation, lem-sfb-proper-scheme-coherent-ext-finite.

5. The groupoid in step 2 and the finite tangent space in steps 3–4 satisfy the abstract
Schlessinger hull criterion with coefficient ring $k$. It supplies a complete Noetherian local
$k$-algebra $B$ and $h_B\to\pi_0\mathcal D_X=F_X$ with exactly the required surjective lifting map
and tangent isomorphism. Composing its tangent isomorphism with step 3 gives the claimed canonical
identification relative to the chosen hull. If all sheaf derivations vanish, the automorphism
formula of step 3 makes the infinitesimal automorphism group trivial; the rigidity clause of the
same criterion makes this hull itself an isomorphism on every Artinian base. This proves
prorepresentation, without claiming that a hull is unique with a chosen ring identification.
Uses: lem-sfb-schlessinger-groupoid-hull-criterion.

6. Restriction to an open $U\subseteq X$ takes the same first-order structure-sheaf extension and
trivial origin to their restrictions. The open-naturality clause of the lift torsor theorem
therefore makes the tangent square with $\operatorname{Ext}^1(L,\mathcal O)$ commute. For a closed
point $x$, choose an affine neighbourhood and localize its ring at $x$. The affine and
localization clause of that theorem represents the restricted class by the conormal complex $C$ of
a localized polynomial presentation. The completed-local comparison sends its class to
$\operatorname{Ext}^1_{\widehat{\mathcal O}_{X,x}}(C\otimes\widehat{\mathcal
O}_{X,x},\widehat{\mathcal O}_{X,x})$ and identifies it with the completed deformation. Its
complex uses continuous differentials. Thus the completion square commutes, independently of the
affine presentation, as claimed. The residue extension at $x$ need not be separable over $k$.
Uses: lem-sfb-scheme-square-zero-lift-torsor, lem-sfb-completed-local-deformation-tangent. -/
theorem exists_hull (C : Coherence.{u}) (D : TopCat.SheafCotangent.Comparison C)
    (f : X ⟶ Spec (.of k)) [IsProper f] : Nonempty (HullConclusion C D f) := by
  sorry

end AlgebraicGeometry.ProperSchemeDeformation
