/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.FinCategory.Basic
import Sheaf.AlgebraicGeometry.NagataFinitePresentationDescent
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.AlgebraicGeometry.RegularLCIGeometricCalculus
import Sheaf.AlgebraicGeometry.SNCBoundaryParameterCriterion
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.AlgebraicGeometry.LimitContainedInConstructible
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.NagataMorphismDescends
import Sheaf.AlgebraicGeometry.NagataMorphismEqEventually
import Sheaf.AlgebraicGeometry.NagataRelativeGluingAxiomsEventually
import Sheaf.AlgebraicGeometry.NagataRelativeGluingDatumDescends
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.LocalRing.Module

/-!
# Approximation of finite marked diagrams

Source: ILO, Travaux de Gabber, Expose III, section 2, Theorem 5.1, Corollary 5.4,
and Proposition 6.2, final paragraph, printed pp. 35--45
(blueprint: lem-per-marked-finite-diagram-approximation).

The ideal-sheaf markings specify all intersections and their canonical inclusions.
The arbitrary finite over-scheme diagram includes any additional objects and arrows.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Pull a model over a finite type subalgebra back along a ring map.
Source: ILO III, section 2 (blueprint: lem-per-marked-finite-diagram-approximation). -/
abbrev markedApproximationPullback {R T : Type u} [CommRing R] [CommRing T]
    (v : R →+* T) (Y : Over (Spec (.of R))) : Over (Spec (.of T)) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom v))).obj Y

/-- The canonical map from a specialized model to its original model.
Source: ILO III, section 2 (blueprint: lem-per-marked-finite-diagram-approximation). -/
abbrev markedApproximationProjection {R T : Type u} [CommRing R] [CommRing T]
    (v : R →+* T) (Y : Over (Spec (.of R))) :
    (markedApproximationPullback v Y).left ⟶ Y.left :=
  pullback.fst Y.hom (Spec.map (CommRingCat.ofHom v))

/-- The neighborhood conclusion, with all specified markings retained separately.
The ideal of the dominant union is the intersection of the vanishing ideals of precisely
those global irreducible components whose generic points map to the generic point of the base.
Thus its data is the reduced closed union, before restriction to the neighborhood.
Source: ILO III, Corollary 5.4 and Proposition 6.2, pp. 42--45
(blueprint: lem-per-marked-finite-diagram-approximation). -/
def MarkedApproximationNeighborhood (A : Type u) [CommRing A] [IsLocalRing A]
    (Z : Closeds (Spec (.of A))) (Y : Over (Spec (.of A)))
    (r : ℕ) (C : Fin r → Y.left.IdealSheafData) : Prop :=
  ∃ V : Y.left.Opens,
    (∀ y : Y.left, Y.hom y = IsLocalRing.closedPoint A → y ∈ V) ∧
    IsRegularScheme V.toScheme ∧
    IsStrictNormalCrossingsBoundary (⨅ j, (C j).comap V.ι) ∧
    (⨅ j, (C j).comap V.ι).support = Z.preimage (V.ι ≫ Y.hom).continuous ∧
    IsOpenImmersion
      (((⨅ (c : Closeds Y.left)
          (_ : (c : Set Y.left) ∈ irreducibleComponents Y.left)
          (_ : ∃ η : Y.left, IsGenericPoint η (c : Set Y.left) ∧
            IsGenericPoint (Y.hom η) Set.univ),
          Scheme.IdealSheafData.vanishingIdeal c).comap V.ι).subschemeι) ∧
    ∀ s : Finset (Fin r),
      IsRegularScheme (⨆ j ∈ s, (C j).comap V.ι).subscheme ∧
      ∀ z : (⨆ j ∈ s, (C j).comap V.ι).subscheme,
        ringKrullDim (V.toScheme.presheaf.stalk
            ((⨆ j ∈ s, (C j).comap V.ι).subschemeι z)) =
          ringKrullDim ((⨆ j ∈ s, (C j).comap V.ι).subscheme.presheaf.stalk z) +
            (s.card : ℕ)

/-- Finite marked diagrams descend to a finite type subalgebra of the completion,
and every sufficiently close specialization has the asserted regular SNC neighborhood.
Source: ILO III, section 2, Theorem 5.1, Corollary 5.4 and Proposition 6.2, pp. 35--45
(blueprint: lem-per-marked-finite-diagram-approximation).

Proof plan (the DAG proof, with its inputs):

1. List the finitely many reduced components $D_{ij}$ and all intersections $D_{iJ}$, including
$D_{i\varnothing}=X_i$. Add the objects and arrows of the requested extra finite diagram. By
[lem-weil-pbc-adic-completion-noetherian], $\widehat A$ is Noetherian; all these finite type
schemes are Noetherian by [lem-weil-pbc-finite-type-over-noetherian]. On finite affine covers,
[lem-weil-pbc-finite-type-noetherian-finite-presentation] gives finite presentations of the
coordinate algebras. Over a Noetherian affine base the overlaps are quasi-compact (every open of a
Noetherian space is quasi-compact), so the morphisms are of finite presentation. Thus the
finite-presentation descent statements apply to every object. Model an empty object by the empty
scheme.

2. For each object form the finite raw affine-chart and overlap datum of the Nagata descent
construction. Its base-change identifications are supplied by
[lemma-nagata-relative-gluing-datum-descends], and
[lemma-nagata-relative-gluing-axioms-eventually] supplies matching overlap opens, inverse maps and
cocycles at its selected valid stage. Gluing this valid datum gives the constructed model of
[def-nagata-finite-presentation-descent]; [lemma-nagata-finite-presentation-descends] asserts that
it is finitely presented and that its comparison with the original object is an isomorphism. Move
these finitely many models to one index. Descend each arrow by [lemma-nagata-morphism-descends]
and impose each of the finitely many diagram equations by [lemma-nagata-morphism-eq-eventually].
Increase the index so all marked inclusions are closed immersions by
[lemma-nagata-closed-immersion-stage-exists]. Define intersection models by the actual iterated
fibre products of the component inclusions. Their completed base changes are the original
scheme-theoretic intersections by the fibre-product universal property. If an intersection was
also specified as a separate object, descend its comparison isomorphism and its inverse, and
impose their inverse equations by the same two morphism lemmas. These operations give one finite
diagram at an index $\alpha_0$, together with its specified base-change identifications.

3. Let $W_{i,\alpha}=Z\times_S X_{i,\alpha}$ and let $H_{i,\alpha}$ be the closed union of the
component models. In $X_{i,\alpha_0}$ consider the constructible set $E_i$ where membership in
$|W_{i,\alpha_0}|$ and in $|H_{i,\alpha_0}|$ agrees. This is a Boolean combination of two closed
subsets of a Noetherian space. The image of the limit $X_i$ is contained in $E_i$ by the corrected
support hypothesis. Apply [lem-weil-pbc-limit-contained-in-constructible] to the system
$(X_{i,\alpha})_{\alpha\ge\alpha_0}$: its terms are qcqs and its transitions are affine, being
base changes of affine maps of spectra. After increasing $\alpha_0$, the two supports agree on
every later model. For every $u$ their inverse images agree as subsets of $X_{i,u}$. This proves
the required support equality for the union of the pulled-back component markings, regardless of
whether scheme-theoretic union commutes with this nonflat base change.

4. Apply [lem-per-gabber-graded-model-approximation] to each of the finitely many schemes $X_i$
and $D_{iJ}$ and their now fixed models. Take an upper bound for their stage thresholds and take
$N_0$ at least the maximum of their $n_0+1$ and $c+2$. Thus for every later $\alpha$, every $N\ge
N_0$, and every allowed $u$, each pair of corresponding schemes has isomorphic $G_a$ algebras and
isomorphic thickenings modulo $\mathfrak m^a$, with $a=N-c\ge2$ (the constants $c$ may vary with
the object). Quotient the graded algebra by its canonical degree $-1$ element, the class of $1$,
to obtain the ordinary associated graded algebra $\bigoplus_{q\ge0}I^q/I^{q+1}$: in degree $q$ the
image of multiplication by that element is $I^{q+1}/I^{q+a}$. Negative-degree quotients vanish.
The isomorphisms preserve that element because they are over $G_a(A)$. Restrict the thickening
isomorphism further modulo $\mathfrak m^2$. All closed fibres are identified by the original
congruence, not by independently chosen bijections of points.

5. Fix a point $x$ on the common closed fibre of one of these pairs and let $R$ and $T$ be its two
local rings. Taking stalks of the associated graded isomorphism gives
$\operatorname{gr}_I(R)\cong\operatorname{gr}_J(T)$, where $I=\mathfrak mR$ and $J=\mathfrak mT$;
formation of powers, quotients and direct sums commutes with localization. Since $x$ lies on the
closed fibre, $I$ and $J$ lie in the respective maximal ideals. Therefore
[lem-per-associated-graded-local-dimension] gives $\dim R=\dim T$. This applies both to the
ambient scheme and, at that same point, to every marked intersection through it.

6. The isomorphism modulo $\mathfrak m^2$ identifies the cotangent spaces of $R$ and $T$. Indeed
if $\mathfrak n$ is the maximal ideal of $R$, then $I^2\subseteq\mathfrak n^2$, so the
maximal-ideal cotangent space of $R/I^2$ is exactly $\mathfrak n/\mathfrak n^2$; the same
computation applies to $T/J^2$. Their residue fields are identified as well. Every original $X_i$
and $D_{iJ}$ is regular by [def-trf-strict-normal-crossings-boundary]. The equality of dimensions
in Step 5 and the cotangent criterion [lem-weil-pbc-regular-local-cotangent-dimension] therefore
make all pulled-back schemes regular at every closed-fibre point. Subtracting the two dimension
equalities gives, at every such point of $D_{iJ,u}$, $\dim\mathcal O_{X_{i,u},x}-\dim\mathcal
O_{D_{iJ,u},x}=|J|$, because that is the original boundary equality.

7. Each $X_{i,u}$ and each $D_{iJ,u}$ is of finite type over $A$. By
[lem-exc-finite-type-localization-excellent] its affine coordinate rings are excellent; their
regular loci are open by the J-2 clause in [def-exc-excellent-ring]. Start with the regular locus
of $X_{i,u}$ and remove the nonregular locus of every intersection. The latter locus is closed in
its intersection and hence closed in this ambient open because the intersection is closed. There
are only finitely many intersections, and none of these bad loci meets the closed fibre by Step 6.
The resulting open $W_{i,u}$ contains the entire closed fibre; both it and all its marked
intersections are regular Noetherian.

8. By [lem-per-regular-lci-geometric-calculus], every closed immersion $D_{iJ,u}\cap
W_{i,u}\hookrightarrow W_{i,u}$ is regular and its codimension is locally constant on its source.
In an affine neighborhood take the smooth factorization with smooth map the identity ($r=0$) in
that lemma. Its dimension formula says this codimension is $\dim\mathcal
O_{W_{i,u},x}-\dim\mathcal O_{D_{iJ,u},x}$. Hence it equals $|J|$ on the closed fibre by Step 6.
The locus where it differs from $|J|$ is open and closed in the intersection, and is therefore
closed in $W_{i,u}$. Remove all these finitely many wrong-codimension loci. The resulting open
$V_{i,u}$ still contains the entire closed fibre, and all its intersections are regular with the
stated dimension difference at every point.

9. At a point $x\in V_{i,u}$ write $B=\mathcal O_{V_{i,u},x}$, of dimension $d$, and list just the
$r$ component markings through $x$. Their ideals $K_j$ have regular quotients of dimension $d-1$.
By [lem-weil-pbc-regular-local-quotient-kernel-parameters] each $K_j$ is generated by an initial
part of a regular system of parameters; [lem-weil-pbc-regular-local-generators-regular-sequence]
computes the dimension of that quotient, so this part has length one. Write $K_j=(t_j)$. For
$K=\sum_jK_j$, the full intersection quotient is regular of dimension $d-r$. By
[lem-weil-pbc-regular-local-cotangent-dimension], the kernel $(K+\mathfrak n^2)/\mathfrak n^2$ of
the cotangent quotient has dimension $r$. It is spanned by the $r$ classes of the $t_j$, so those
classes are independent. Extend them to a basis of $\mathfrak n/\mathfrak n^2$ and lift the added
basis vectors. By [lem-weil-pbc-nakayama-local-generators] these $d$ lifts generate $\mathfrak n$,
giving a regular system of parameters containing all the $t_j$.

10. In this system of parameters the $t_j$ are pairwise nonassociated prime elements in a domain
by [lem-trf-regular-local-ufd-boundary-factorization]. Hence $\bigcap_j(t_j)=(\prod_jt_j)$: an
element divisible by each of finitely many distinct primes is divisible by their product. This
ideal is radical (if a power is divisible by each prime, so is the element), and its generator is
a nonzerodivisor. Thus the scheme-theoretic union $H_{i,u}$ of the component markings has at every
point the product equation from [lem-per-snc-boundary-parameter-criterion], which makes it a
strict normal crossings boundary. A marking may split into several components: by
[rem-pc-regular-normal] its regular Noetherian restriction is a finite disjoint union of integral
open and closed components. Different original markings cannot share one, since their common
intersection has codimension two by Step 8. Thus these are the boundary's reduced irreducible
components, with the same intersection conditions. Step 3 gives $|H_{i,u}|=|Z\times_SV_{i,u}|$. At
a point on no marking the product is $1$.

11. Finally [rem-pc-regular-normal] decomposes the regular Noetherian $V_{i,u}$ into finitely many
disjoint integral open and closed components. Each is the restriction of the unique global
irreducible component of $X_{i,u}$ containing its generic point. Select precisely those whose
global generic point maps to the generic point of $S$. Their finite union is open and closed. Its
reduced scheme structure agrees with the restriction of the reduced closed union of all global
dominant components, since a regular scheme is reduced and a reduced closed subscheme is
determined by its support. This proves the dominant-union assertion. The construction never
removed a closed-fibre point and used one common index and bound. An empty closed fibre allows the
empty neighborhood. Empty markings give the unit ideal and no codimension constraints; empty
intersections have no points to check. The extra finite diagram was included before choosing
thresholds, so every morphism and equation in it remains modeled simultaneously.
-/
theorem exists_marked_finite_diagram_approximation
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [HenselianLocalRing A] (hA : IsExcellent A)
    (Z : Closeds (Spec (.of A)))
    (J : Type u) [SmallCategory J] [FinCategory J]
    (F : J ⥤ Over (Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))))
    (hF : ∀ j, LocallyOfFiniteType (F.obj j).hom ∧ QuasiCompact (F.obj j).hom)
    (n : ℕ) (x : Fin n → J)
    (hX : ∀ i, IsNoetherian (F.obj (x i)).left ∧ IsRegularScheme (F.obj (x i)).left)
    (H : ∀ i : Fin n, (F.obj (x i)).left.IdealSheafData)
    (hH : ∀ i, IsStrictNormalCrossingsBoundary (H i))
    (hZ : ∀ i, (H i).support = Z.preimage
      ((F.obj (x i)).hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))).continuous)
    (r : Fin n → ℕ)
    (C : ∀ i : Fin n, Fin (r i) → (F.obj (x i)).left.IdealSheafData)
    (hCred : ∀ i j, (C i j).radical = C i j)
    (hCdistinct : ∀ i, Function.Injective (fun j ↦ (C i j).support))
    (hC : ∀ i, Set.range (fun j ↦ ((C i j).support : Set (F.obj (x i)).left)) =
      {c | ∃ d ∈ irreducibleComponents (H i).subscheme, c = (H i).subschemeι '' d}) :
    ∃ (B₀ : Subalgebra A (AdicCompletion (IsLocalRing.maximalIdeal A) A)), B₀.FG ∧
      ∃ (F₀ : J ⥤ Over (Spec (.of B₀)))
        (e : F₀ ⋙ Over.pullback (Spec.map (CommRingCat.ofHom B₀.val.toRingHom)) ≅ F)
        (C₀ : ∀ i : Fin n, Fin (r i) → (F₀.obj (x i)).left.IdealSheafData),
        (∀ j, LocallyOfFiniteType (F₀.obj j).hom ∧ QuasiCompact (F₀.obj j).hom) ∧
        (∀ i j, (C₀ i j).comap
          ((e.app (x i)).inv.left ≫ markedApproximationProjection B₀.val.toRingHom
            (F₀.obj (x i))) = C i j) ∧
        (∀ (i : Fin n) (s : Finset (Fin (r i))) (j : J) (a : j ⟶ x i),
          IsClosedImmersion (F.map a).left →
          (F.map a).left.ker = ⨆ k ∈ s, C i k →
          IsClosedImmersion (F₀.map a).left ∧
            (F₀.map a).left.ker = ⨆ k ∈ s, C₀ i k) ∧
        ∃ N₀ : ℕ, 1 ≤ N₀ ∧
          ∀ (B : Subalgebra A (AdicCompletion (IsLocalRing.maximalIdeal A) A)),
            B.FG → ∀ hB : B₀ ≤ B, ∀ N : ℕ, N₀ ≤ N → ∀ v : B →ₐ[A] A,
              (∀ b : B, algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)
                  (v b) - (b : AdicCompletion (IsLocalRing.maximalIdeal A) A) ∈
                (IsLocalRing.maximalIdeal A ^ N).map
                  (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))) →
              ∀ i : Fin n, MarkedApproximationNeighborhood A Z
                (markedApproximationPullback (v.comp (Subalgebra.inclusion hB)).toRingHom
                  (F₀.obj (x i))) (r i)
                (fun j ↦ (C₀ i j).comap (markedApproximationProjection
                  (v.comp (Subalgebra.inclusion hB)).toRingHom (F₀.obj (x i)))) := by
  sorry

end AlgebraicGeometry
