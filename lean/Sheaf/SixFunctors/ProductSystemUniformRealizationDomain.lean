/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import Sheaf.SixFunctors.IntegralSystemExpressionDomain
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.CoefficientSystemDerivedComparison
public import Sheaf.Paper.StrictEtaleSystemInterfaces
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.NumberTheory.Padics.IntegersProfiniteTower
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.NoetherianSpace
import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import Sheaf.Paper.PullbackTorAmplitude
import Sheaf.Paper.FiniteCoefficientTensorCtf
import Sheaf.Paper.SystemNormalizedTensorClosure
import Sheaf.Paper.OpenExtensionFiniteTor
import Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage
public import Sheaf.Paper.FiniteRingConstructibleDerivedOrigin
import Sheaf.Paper.ProperEtaleOriginScalarIsomorphism
import Sheaf.AlgebraicGeometry.ComparisonTorInterval
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit

/-! # Uniform domains of product compactification systems

Source: Stacks 0941 (system/limit foundation), 09AL and 0F0G;
blueprint sec-six-functors/sk-thm-sf-kunneth-relative/lem-sf-kunneth-coherence.proof.md,
proper-reduction sentence
(blueprint: lem-sf-product-system-uniform-realization-domain).

The expression syntax and its actual operations are the published ones. Auxiliary
records specify the change of presentation needed to apply the published system
comparison, including every transition; they do not choose arbitrary endpoint maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Cache the existing sheafification at the explicit coefficient universe.
Source: small-site coefficient convention
(blueprint: lem-sf-product-system-uniform-realization-domain). -/
instance (priority := 6000) domainProEtaleRingSheafify (Z : Scheme.{u}) :
    HasSheafify (ProEt.topology Z) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u} Z


/-- The coefficient ring in the universe of the small sites; only a size lift.
Source: Zheng Construction 4.1
(blueprint: lem-sf-product-system-uniform-realization-domain). -/
abbrev domainIntegers := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)


/-- The same chosen uniformizer in the coefficient universe.
Source: blueprint coefficient convention
(blueprint: lem-sf-product-system-uniform-realization-domain). -/
abbrev domainUniformizer : domainIntegers l E := ⟨Padic.coefficientExtensionUniformizer l E⟩


/-- The canonical ring-sheaf map induced by a quotient presentation.
Source: Zheng Construction 4.1, scalar transport
(blueprint: lem-sf-product-system-uniform-realization-domain). -/
def domainQuotientMap (Z : Scheme.{u}) (n : ℕ)
    (r : ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)) ≃+*
      domainIntegers l E ⧸
        (Ideal.span ({domainUniformizer l E} : Set (domainIntegers l E))) ^ (n + 1)) :
    integralCoefficientSheaf.{u, u} l E Z n ⟶
      (sheafCompose (ProEt.topology Z) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (SheafOfModules.coefficientQuotientSheaf (J := ProEt.topology Z)
          (domainIntegers l E) (domainUniformizer l E) n) :=
  (sheafCompose (ProEt.topology Z) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    ((constantSheaf (ProEt.topology Z) CommRingCat.{u + 1}).map (CommRingCat.ofHom r.toRingHom))


/-- Standard localization for the strict pro-etale family presentation.
Source: Stacks 05RU (blueprint: lem-sf-product-system-uniform-realization-domain). -/
instance domainProSystemDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 2} (SheafOfModules.CoefficientSystem
      (J := ProEt.topology Z) (domainIntegers l E) (domainUniformizer l E)) :=
  HasDerivedCategory.standard _


/-- Standard localization at each positive pro-etale coefficient level.
Source: Stacks 05RU (blueprint: lem-sf-product-system-uniform-realization-domain). -/
instance domainProLevelDerived (Z : Scheme.{u}) (n : ℕ) :
    HasDerivedCategory.{u + 2} (SheafOfModules.coefficientLevelModules
      (J := ProEt.topology Z) (domainIntegers l E) (domainUniformizer l E) n) :=
  HasDerivedCategory.standard _


/-- Presentation of the very same strict systems as families. Quotient generators,
all module levels and the actual adjacent transitions specify the ordinary equivalence;
the factorization through Q specifies its derived localization.
Source: Zheng Construction 4.1; Stacks 0941
(blueprint: lem-sf-product-system-uniform-realization-domain). -/
structure DomainSystemPresentation (Z : Scheme.{u}) where
  quotient : ∀ n : ℕ,
    ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)) ≃+*
      domainIntegers l E ⧸
        (Ideal.span ({domainUniformizer l E} : Set (domainIntegers l E))) ^ (n + 1)
  quotient_mk : ∀ (n : ℕ) (x : Padic.coefficientExtensionIntegers l E),
    quotient n ⟨Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x⟩ =
      Ideal.Quotient.mk _ (ULift.up x)
  ordinary : coefficientSequenceModules.{u, u} l E Z ≌
    SheafOfModules.CoefficientSystem (J := ProEt.topology Z)
      (domainIntegers l E) (domainUniformizer l E)
  level : ∀ n : ℕ,
    ordinary.functor ⋙ SheafOfModules.coefficientEvaluation
        (J := ProEt.topology Z) (O := domainIntegers l E) (ell := domainUniformizer l E) n ⋙
      SheafOfModules.restrictScalars.{u + 1} (domainQuotientMap l E Z n (quotient n)) ≅
    coefficientSequenceEvaluation.{u, u} l E Z n
  sections : ∀ (N : coefficientSequenceModules.{u, u} l E Z) (n : ℕ)
      (U : Z.ProEtᵒᵖ), HEq (((level n).hom.app N).val.app U).hom.toAddMonoidHom
        (AddMonoidHom.id (((ordinary.functor.obj N).level n).val.obj U))
  transition : ∀ (N : coefficientSequenceModules.{u, u} l E Z) (n : ℕ)
      (U : Z.ProEtᵒᵖ),
    HEq (((ordinary.functor.obj N).transition n).val.app U).hom.toAddMonoidHom
      ((((coefficientSequenceTransition.{u, u} l E Z
        (Nat.le_succ n)).app N).val.app U).hom.toAddMonoidHom)
  derived : System l E Z ≌
    DerivedCategory (SheafOfModules.CoefficientSystem (J := ProEt.topology Z)
      (domainIntegers l E) (domainUniformizer l E))
  factors : DerivedCategory.Q ⋙ derived.functor ≅
    ordinary.functor.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q


/-- The simultaneous site comparison, in the recorded strict-family presentation.
The normalized predicate is transported along the transition-preserving presentation,
so its counit below is a map of the actual systems, not unrelated level maps.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 09AL
(blueprint: lem-sf-product-system-uniform-realization-domain). -/
structure DomainSiteComparison (Z : Scheme.{u}) where
  presentation : DomainSystemPresentation l E Z
  etaleEvaluation : SheafOfModules.CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2}
    (J := Z.smallEtaleTopology) (O := domainIntegers l E) (ell := domainUniformizer l E)
  proEvaluation : SheafOfModules.CoefficientEvaluationDerivedPackage.{u + 1, u, u + 1, u + 2}
    (J := ProEt.topology Z) (O := domainIntegers l E) (ell := domainUniformizer l E)
  ordinary : SheafOfModules.CoefficientSystemOrdinaryImage
    (J := Z.smallEtaleTopology) (K := ProEt.topology Z)
    (domainIntegers l E) (domainUniformizer l E) _ _ (Scheme.proEtaleSiteComparison Z)
  image : SheafOfModules.CoefficientSystemDerivedImage.{u + 1, u, u + 1, u, u + 1, u + 2}
    (J := Z.smallEtaleTopology) (K := ProEt.topology Z)
    (domainIntegers l E) (domainUniformizer l E) _ _ (Scheme.proEtaleSiteComparison Z)
    ordinary etaleEvaluation proEvaluation
  normalization : ∀ N : System l E Z,
    SheafOfModules.IsNormalizedCoefficientSystem (domainIntegers l E)
      (domainUniformizer l E) proEvaluation (presentation.derived.functor.obj N) ↔
        IsNormalizedCoefficientSequence l E Z N


/-- Descent by the actual system adjunction: invertibility of its specified counit,
bounded-below direct image, and normalization of that same direct image.
Source: Zheng Lemma 4.10; Stacks 09AL
(blueprint: lem-sf-product-system-uniform-realization-domain). -/
def DomainSiteComparison.descends {Z : Scheme.{u}} (C : DomainSiteComparison l E Z)
    (N : System l E Z) : Prop :=
  (∃ a : ℤ, N.IsGE a) ∧
    IsIso (C.image.system.adjunction.counit.app (C.presentation.derived.functor.obj N)) ∧
    (∃ a : ℤ, (C.image.system.direct.obj (C.presentation.derived.functor.obj N)).IsGE a) ∧
    SheafOfModules.IsNormalizedCoefficientSystem (domainIntegers l E)
      (domainUniformizer l E) C.etaleEvaluation
        (C.image.system.direct.obj (C.presentation.derived.functor.obj N))


/-- Vertices of the two- and three-factor product diagrams. A label is used at most
once; each factor is either the original scheme or its chosen compactification.
The base and all choices of product cones and associations are included.
Source: blueprint Kunneth-coherence proper reduction
(blueprint: lem-sf-product-system-uniform-realization-domain). -/
inductive ProductVertex {B : Scheme.{u}} (X : ULift.{u} (Fin 3) → Over B)
    (c : ∀ i : ULift.{u} (Fin 3), Compactification (X i).hom) :
    Finset (ULift.{u} (Fin 3)) → Over B → Prop where
  | base : ProductVertex X c ∅ (Over.mk (𝟙 B))
  | source (i : ULift.{u} (Fin 3)) : ProductVertex X c {i} (X i)
  | ambient (i : ULift.{u} (Fin 3)) : ProductVertex X c {i} (Over.mk (c i).g)
  | product {S T : Finset (ULift.{u} (Fin 3))} {U V P : Over B}
      (disjoint : Disjoint S T) (left : ProductVertex X c S U)
      (right : ProductVertex X c T V) (p : P ⟶ U) (q : P ⟶ V)
      (square : IsPullback p.left q.left U.hom V.hom) : ProductVertex X c (S ∪ T) P


/-- An expression uses only the actual product compactification vertices, including
its open intermediate in a compact-support constructor.
Source: blueprint Kunneth-coherence proper reduction
(blueprint: lem-sf-product-system-uniform-realization-domain). -/
def Expression.inProductDiagram {B : Scheme.{u}} {X : ULift.{u} (Fin 3) → Over B}
    (c : ∀ i : ULift.{u} (Fin 3), Compactification (X i).hom) :
    {W : Over B} → Expression B (ULift.{u} (Fin 3)) X W → Prop
  | W, e => (∃ S, ProductVertex X c S W) ∧
    match e with
    | .var _ => True
    | .pull _ e => e.inProductDiagram c
    | .push _ _ e => e.inProductDiagram c
    | .shriek _ _ _ e => e.inProductDiagram c
    | .compactSupport (V := V) _ t e => e.inProductDiagram c ∧
        ∃ S, ProductVertex X c S (Over.mk (t.g ≫ V.hom))
    | .tensor e f => e.inProductDiagram c ∧ f.inProductDiagram c


/-- Quantitative interval recursion. Pullback and open extension preserve the interval,
tensor adds endpoints, and proper image adds twice the fixed source dimension.
Source: blueprint finite-Tor operations and Stacks proper projection formula 0F0G
(blueprint: lem-sf-product-system-uniform-realization-domain). -/
def Expression.torBounds {B : Scheme.{u}} {X : ULift.{u} (Fin 3) → Over B}
    (a b : ULift.{u} (Fin 3) → ℤ) (d : Scheme.{u} → ℕ) :
    {W : Over B} → Expression B (ULift.{u} (Fin 3)) X W → ℤ × ℤ
  | _, .var i => (a i, b i)
  | _, .pull _ e => e.torBounds a b d
  | _, .push (U := U) _ _ e =>
      ((e.torBounds a b d).1, (e.torBounds a b d).2 + 2 * (d U.left : ℤ))
  | _, .shriek _ _ _ e => e.torBounds a b d
  | _, .compactSupport _ c e =>
      ((e.torBounds a b d).1, (e.torBounds a b d).2 + 2 * (d c.Z : ℤ))
  | _, .tensor e f =>
      ((e.torBounds a b d).1 + (f.torBounds a b d).1,
        (e.torBounds a b d).2 + (f.torBounds a b d).2)


/-- Actual intermediate systems with their recursively computed intervals. The list
includes the open intermediate of every compact-support constructor separately.
Source: blueprint Kunneth-coherence proper reduction
(blueprint: lem-sf-product-system-uniform-realization-domain). -/
def Expression.boundedSystems (o : Operations l E) {B : Scheme.{u}}
    {X : ULift.{u} (Fin 3) → Over B} (K : ∀ i, Integral l E (X i).left)
    (a b : ULift.{u} (Fin 3) → ℤ) (d : Scheme.{u} → ℕ) :
    {W : Over B} → Expression B (ULift.{u} (Fin 3)) X W →
      List ((Σ W : Over B, System l E W.left) × (ℤ × ℤ))
  | W, e => (⟨W, (e.evaluate (systemInterpretation l E o)).obj
      ((inputReduction l E X).obj K)⟩, e.torBounds a b d) ::
    match e with
    | .var _ => []
    | .pull _ e => e.boundedSystems o K a b d
    | .push _ _ e => e.boundedSystems o K a b d
    | .shriek _ _ _ e => e.boundedSystems o K a b d
    | .compactSupport (V := V) _ c e =>
        (⟨Over.mk (c.g ≫ V.hom), (Operations.shriek l E o c.i).obj
          ((e.evaluate (systemInterpretation l E o)).obj
            ((inputReduction l E X).obj K))⟩, e.torBounds a b d) ::
          e.boundedSystems o K a b d
    | .tensor e f => e.boundedSystems o K a b d ++ f.boundedSystems o K a b d


/-- The positive quotient is finite, with the recorded finiteness theorem as its proof.
Source: coefficient extension, clause 4
(blueprint: lem-sf-product-system-uniform-realization-domain). -/
instance domainFiniteQuotient (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

/-- The constructible levels, quantitative cohomological/Tor interval, and bounded
etale-origin witnesses. The latter have no transitions imposed at this stage.
Source: Stacks 09AL and finite-level finite-Tor closure
(blueprint: lem-sf-product-system-uniform-realization-domain). -/
def DomainInterval (Z : Scheme.{u}) (N : System l E Z) (a b : ℤ) : Prop :=
  a ≤ b ∧ ∀ n : ℕ,
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) Z
        ((coefficientSequenceDerivedEvaluation l E Z n).obj N) ∧
    proEtaleCohomologicalSupport ((coefficientSequenceDerivedEvaluation l E Z n).obj N) ⊆
      Set.Icc a b ∧
    HasProEtaleTorAmplitude Z (Padic.coefficientExtensionRing l E (n + 1))
      ((coefficientSequenceDerivedEvaluation l E Z n).obj N) a b ∧
    ∃ H : ProEtale.FiniteCoefficientEtaleDerivedCategory Z
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))),
      Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) Z H ∧
      Nonempty ((ProEtale.finiteCoefficientIntrinsicDerivedComparison Z
        (Padic.coefficientExtensionRing l E (n + 1))).obj H ≅
          (coefficientSequenceDerivedEvaluation l E Z n).obj N) ∧
      ∀ i : ℤ, (i < a ∨ b < i) → IsZero
        ((DerivedCategory.homologyFunctor
          (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1}
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))) i).obj H)


/-- Exact open extension preserves any supplied cohomological interval at all levels.
Source: blueprint open finite-Tor proof, exact extension by zero
(blueprint: lem-sf-product-system-uniform-realization-domain). -/
def OpenIntervalPreservation (o : Operations l E) {B : Scheme.{u}}
    (X : ULift.{u} (Fin 3) → Over B)
    (c : ∀ i : ULift.{u} (Fin 3), Compactification (X i).hom) : Prop :=
  ∀ {S T : Finset (ULift.{u} (Fin 3))} {U V : Over B},
    ProductVertex X c S U → ProductVertex X c T V →
    ∀ (j : U.left ⟶ V.left) [IsOpenImmersion j] (N : System l E U.left)
      (a b : ℤ),
      (∀ n : ℕ, proEtaleCohomologicalSupport
        ((coefficientSequenceDerivedEvaluation l E U.left n).obj N) ⊆ Set.Icc a b) →
      ∀ n : ℕ, proEtaleCohomologicalSupport
        ((coefficientSequenceDerivedEvaluation l E V.left n).obj
          ((Operations.shriek l E o j).obj N)) ⊆ Set.Icc a b


/-- Uniform domain bounds for the actual product compactification systems, including
all intermediate systems, quantitative intervals, and the actual comparison counit.
Source: Stacks 0941, 09AL, 0F0G; blueprint Kunneth-coherence proper-reduction sentence
(blueprint: lem-sf-product-system-uniform-realization-domain).

The coefficient completeness clause states that the actual reduction map to the
compatible families of positive quotients is bijective (Stacks 08ZY). The proper rule
holds for every dimension bound `d` on the diagram vertices; an empty vertex has
dimension `⊥`, so `d = 0` is allowed there.

Proof plan (the DAG proof, in order):

1. The local-field DVR theorem makes $R$ a principal ideal domain contained in $E$, and its
chosen uniformizer $t$ is nonzero. Thus multiplication by $t$ is injective. The PID theorem
gives Noetherianity. The valued-DVR quotient theorem gives finiteness of every $A_n$, and the
profinite-tower theorem identifies the actual reduction map $R\to\lim_nA_n$ as a ring
isomorphism. These establish the coefficient hypotheses, including regularity and completeness,
of the system comparison used below. Dependencies: lem-weil-l-adic-extension-integers-dvr, lem-
weil-pbc-pid-noetherian-normal, lem-weil-valued-dvr-finite-quotients, lem-sfb-integers-
profinite-tower.

2. For each compactification, its proper factor is finite type by the definition of properness;
its ambient scheme is finite type over $k$ by composition. Every two- or three-factor diagram
scheme is an iterated fibre product of these schemes and the original schemes over $B$. Finite-
type stability under base change and composition therefore makes each diagram scheme finite type
over $k$. The indicated proper arrows are base changes or composites of the proper factors, so
properness stability gives their properness. The inverse-image arrows used in the calculation
are the indicated separated finite-type projections and their composites. Apply finite-type-
over-Noetherian to their structure maps to $\operatorname{Spec}k$, a Noetherian affine scheme.
Dependencies: def-weil-compactifications-refinements, def-weil-proper-morphism, lem-sfb-finite-
type-composition-base-change, lem-weil-pbc-proper-base-change, lem-weil-pbc-proper-composition,
lem-weil-pbc-finite-type-over-noetherian.

3. Choose a finite Noetherian affine cover of each diagram scheme, using its local Noetherianity
and quasi-compactness. The underlying affine spaces are Noetherian, and the finite-union theorem
makes the entire underlying space Noetherian. The compact-subsets theorem now makes every
indicated open, and its intersection with any affine open of its target, quasi-compact; the
latter is precisely quasi-compactness of the open immersion. The finite-type dimension theorem
supplies a nonnegative integer $d_Z$ bounding each source dimension. If the source is empty
choose $d_Z=0$. These choices involve only the finite geometric diagram and never $n$.
Dependencies: lem-sc-affine-noetherian-underlying-space, lem-kun-finite-union-noetherian, lem-
sfb-noetherian-space-compact-subsets, lem-kun-dimension-finite-type.

4. Induct on the syntax tree of the finite expression. For a system $N$, the induction property
is: its actual transition-adjoints are invertible, its levels are constructible with a common
finite Tor interval $I_N=[u_N,v_N]$, and hence with that same cohomological interval. The
cohomological assertion follows by testing the Tor condition against the degree-zero coefficient
unit. For each input, the integral finite-Tor definition supplies $I_N$ independent of $n$, and
the derived-complete constructible definition supplies constructible reductions. The strict
reduction-system construction and successive scalar-association theorem identify the actual
adjoint transition as $$(K\otimes^L_{\widehat
R}A_m)\otimes^L_{A_m}A_n\xrightarrow{\sim}K\otimes^L_{\widehat R}A_n.$$ The theorem also
identifies the composite quotient units and their cocycles. Thus this is normalization of the
given strict reduction system, rather than a choice of unrelated level isomorphisms.
Dependencies: def-weil-finite-tor-amplitude, def-weil-derived-complete-integral-detailed, lem-
sfb-successive-derived-quotient-normalization, lem-coef-semilinear-derived-sections.

5. For an inverse-image constructor, apply pullback Tor-amplitude preservation at each finite
quotient. The interval stays $[u,v]$ and the levels remain constructible. For a tensor
constructor, apply finite-Tor tensor closure to its two inputs: the output is constructible with
interval $[u+u',v+v']$. The whole-system tensor/pullback closure theorem proves normalization
for these actual operations. In particular the tensor adjoint is scalar reassociation followed
by $\alpha^P_{m,n}\otimes\alpha^Q_{m,n}$, and the inverse-image adjoint is the inverse image of
the input adjoint under scalar association. Both are invertible and retain the actual quotient
cocycles. All hypotheses on the scheme arrows were established in steps 2 and 3. Dependencies:
lem-sf-pullback-tor-amplitude, lem-sf-tensor-ctf, lem-pur-system-normalized-tensor-closure.

6. For an open-extension constructor, finite-level open finite-Tor closure preserves
constructibility and the cohomological and Tor intervals. Apply the ringed open tensor
comparison to $B_X=(A_m)_X$, $M=N_m$ and the degree-zero $B_X$-module $(A_n)_X$. It identifies
$$(J_jN)_m\otimes^L_{A_m}A_n\cong j_!(N_m\otimes^L_{A_m}A_n).$$ Following this by
$j_!(\alpha^N_{m,n})$ is the actual output transition-adjoint: restriction to the open is the
input adjoint, and the open tensor comparison is normalized to the identity there. The whole-
system version of the same theorem and the evaluation calculus identify these maps with the
strict system transitions, including quotient composition. Hence this constructor preserves
normalization as well as the interval. Dependencies: lem-trf-open-ctf, lem-sf-open-tensor-
normalization, lem-coef-semilinear-derived-sections.

7. For a proper-image constructor $S_rN$, the evaluation calculus gives $e_nS_rN\cong
Rr_{*,n}N_n$. The pro-etale finite direct-image theorem applies to the separated finite-type
proper map with the fixed source bound $d$. It gives constructible output levels with Tor
interval $[u,v+2d]$, uniformly in $n$. Testing against the coefficient unit gives the same
cohomological interval. To check normalization, first choose bounded etale origins for $N_m$ and
$N_n$ by finite-ring constructible derived origin. That theorem preserves cohomological
intervals. The normalized input identifies $N_m\otimes^L_{A_m}A_n$ with $N_n$, so this scalar
extension is also bounded below, as required by the proper scalar comparison theorem.
Dependencies: lem-coef-semilinear-derived-sections, cor-sf-direct-image-ctf-proetale, lem-weil-
pbc-finite-ring-constructible-derived-origin.

8. More explicitly, for $m\ge n$ the actual proper-output transition-adjoint is $$ (Rr_{*,m}N_m)
\otimes^L_{A_m}A_n\xrightarrow{b_{m,n}}Rr_{*,n}(N_m\otimes^L_{A_m}A_n)\xrightarrow{Rr_{*,n}(\alp
ha^N_{m,n})}Rr_{*,n}N_n.$$ This is the transition formula in the semilinear evaluation calculus.
The first arrow is exactly its coefficient projection mate, so the proper etale-origin scalar-
isomorphism theorem makes it invertible; the second is invertible by the induction hypothesis.
The scalar theorem's etale hypothesis is valid: choose a bounded origin $E_e$ of $N_m$ and use
the comparison Tor-interval theorem to transfer its finite Tor interval to the etale site. Its
scalar extension by the degree-zero sheaf $A_n$ has cohomology in $[u,v]$, by that Tor
condition. Thus both etale objects required by the scalar theorem are bounded below. Properness
and finite coefficient rings are already established, and no flatness of $A_m\to A_n$ is
asserted. This proves normalization for the actual proper system. Dependencies: lem-coef-
semilinear-derived-sections, lem-fix-proper-etale-origin-scalar-isomorphism, lem-exc-comparison-
tor-interval.

9. The base and all constructors now prove the induction property for every subtree. At every
level of every intermediate system, finite-ring constructible derived origin supplies a bounded
constructible etale witness in the same cohomological interval. These witnesses have not been
given transitions. For any fixed finite collection of expressions, collect the finitely many
intervals attached recursively to all their subtrees. Their minimum lower endpoint and maximum
upper endpoint give common finite cohomological and Tor bounds, independent of $n$; each proper
contribution $2d_Z$ is fixed before the recursion. This includes all subtrees in the two- and
three-factor compactification calculation, with the open intermediate of every $S_pJ_j$ counted
separately. Dependencies: lem-weil-pbc-finite-ring-constructible-derived-origin, def-sf-
integral-system-expression-domain.

10. Fix an intermediate system $N$ on $Z$ with the common lower bound $c$. System cohomology is
levelwise, so $H^i(N)=0$ for $i<c$: every evaluation is zero in that degree. Hence $N\in
D^+(\mathscr S_A(Z_{\mathrm{proet}}))$. For every $n$, finite-ring site comparison is fully
faithful on $D^+$, and step 9 gives $N_n$ in its essential image. Apply the coefficient-system
derived comparison to $u=\nu_Z$, $O=R$, $\lambda=t$; step 1 checked regularity and completeness.
Its counit $$\nu_{A,Z}^*R\nu_{A,Z,*}N\longrightarrow N$$ is invertible, and $R\nu_{A,Z,*}N$ is
bounded below and normalized. Evaluation of this single etale system and its counit supplies
origins compatible with the actual quotient transitions. Thus no transition maps between the
independently chosen witnesses of step 9 have been assumed or lifted by a faithfulness
assertion. Dependencies: lem-coef-semilinear-derived-sections, thm-weil-pbc-site-comparison,
lem-pur-coefficient-system-derived-comparison.

11. The finite-expression domain requires normalization, common constructible cohomological and
Tor bounds, and compatible bounded-below etale origins for every intermediate system. Steps 4--9
supply the first conditions and step 10 supplies the compatible origins. Together with the
coefficient and geometric conditions of steps 1--3 these are precisely the intermediate-object
hypotheses stated in the integral compactification system-realization theorem. In particular
they apply to the actual open-product and compactification expressions. This proves the claimed
applicability without using realization to prove its own domain conditions. Dependencies: def-
sf-integral-system-expression-domain, lem-sf-integral-compactification-system-realization.
-/
theorem productSystemUniformRealizationDomain
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p) :
    IsNoetherianRing (Padic.coefficientExtensionIntegers l E) ∧
    (∀ x : Padic.coefficientExtensionIntegers l E,
      Padic.coefficientExtensionUniformizer l E * x = 0 → x = 0) ∧
    Function.Injective (fun (x : Padic.coefficientExtensionIntegers l E) (n : ℕ) ↦
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x) ∧
    (∀ y : ∀ n : ℕ, Padic.coefficientExtensionRing l E (n + 1),
      (∀ n : ℕ, Padic.coefficientExtensionTransition l E (n + 1) (y (n + 1)) = y n) →
      ∃ x : Padic.coefficientExtensionIntegers l E, ∀ n : ℕ,
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x = y n) ∧
    (∀ n : ℕ, Finite (Padic.coefficientExtensionRing l E (n + 1))) ∧
    ∀ o : Operations l E, ∃ C : ∀ Z : Scheme.{u}, DomainSiteComparison l E Z,
    ∀ (B : Over (Spec (CommRingCat.of D.k)))
      [IsSeparated B.hom] [LocallyOfFiniteType B.hom] [QuasiCompact B.hom]
      (X : ULift.{u} (Fin 3) → Over B.left)
      (_hX : ∀ i, IsSeparated (X i).hom ∧
        LocallyOfFiniteType (X i).hom ∧ QuasiCompact (X i).hom)
      (c : ∀ i : ULift.{u} (Fin 3), Compactification (X i).hom)
      (K : ∀ i, Integral l E (X i).left)
      (_hK : ∀ i, finiteTorConstructibleIntegral l E (X i).left (K i)),
      (∀ (S : Finset (ULift.{u} (Fin 3))) (W : Over B.left), ProductVertex X c S W →
        IsNoetherian W.left ∧ (∃ m : ℕ, topologicalKrullDim W.left ≤ (m : WithBot ℕ∞)) ∧
          ∀ U : W.left.Opens, IsCompact (U : Set W.left)) ∧
      (∀ {S T : Finset (ULift.{u} (Fin 3))} {V W : Over B.left},
        ProductVertex X c S V → ProductVertex X c T W →
        ∀ j : V.left ⟶ W.left, IsOpenImmersion j → QuasiCompact j) ∧
      OpenIntervalPreservation l E o X c ∧
      ∀ d : Scheme.{u} → ℕ,
        (∀ (S : Finset (ULift.{u} (Fin 3))) (W : Over B.left), ProductVertex X c S W →
          topologicalKrullDim W.left ≤ (d W.left : WithBot ℕ∞)) →
      ∀ a b : ULift.{u} (Fin 3) → ℤ,
        (∀ i, a i ≤ b i ∧ ∀ n : ℕ,
          HasProEtaleTorAmplitude (X i).left (Padic.coefficientExtensionRing l E (n + 1))
            ((scalarReductionDerivedExtension.{u, u} l E (X i).left n).obj (K i))
            (a i) (b i)) →
      ∀ es : List (Σ W : Over B.left, Expression B.left (ULift.{u} (Fin 3)) X W),
        (∀ e ∈ es, e.2.inProductDiagram c) →
        (∀ e ∈ es, e.2.geometric ∧ e.2.domain l E o K) ∧
        ∃ lower upper : ℤ, lower ≤ upper ∧
          ∀ z ∈ es.flatMap (fun e ↦ e.2.boundedSystems l E o K a b d),
            Good l E z.1.1.left z.1.2 ∧
            DomainInterval l E z.1.1.left z.1.2 z.2.1 z.2.2 ∧
            DomainInterval l E z.1.1.left z.1.2 lower upper ∧
            (C z.1.1.left).descends l E z.1.2 := by
  sorry

end WeilConjectures.IntegralSystemRealization
