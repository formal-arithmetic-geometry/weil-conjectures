/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel

/-! # A common marked nodal model over a discrete valuation ring

Source: Stacks Project, resolve.tex, Tag 0C5S and models.tex, Tag 0CDE, with the
persistent-node, conductor and marking extension detailed in the DAG proof
(blueprint: lem-sfb-common-nodal-model).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Two projective marked nodal models of the same generic curve have a common projective
marked nodal model over the original DVR. The generic curve may itself be singular.
There are no positivity, completeness, excellence or residue-characteristic assumptions.
The finite sets lie in the special fibres, and the maps are isomorphisms off those sets.

Source: Stacks Project, resolve.tex, Tag 0C5S and models.tex, Tag 0CDE; the conductor
and marking extension is the ten-step argument below. These tags alone only provide the
regular-surface common resolution and the smooth-generic nodal regularization.
(blueprint: lem-sfb-common-nodal-model).

Proof plan from the DAG:
1. Apply persistent-node normalization to each $X_i$, obtaining $C_i$, $B_i\to N_i$ and
$X_i=C_i\amalg_{B_i}N_i$. The generic isomorphism $u$ identifies generic normalizations and
their conductor diagrams. It identifies $N_1$ with $N_2$ and $B_1$ with $B_2$: integral closures
of $R$ in the identified generic finite algebras coincide. Write these common finite etale
schemes as $N$ and $B$. The original markings lift to disjoint smooth sections of $C_i$,
disjoint from $B$, because normalization is an isomorphism there. The $C_i$ have smooth generic
fibres, possibly disconnected.
   Uses: lem-sfb-persistent-node-normalization.

2. Apply nodal regularization, obtaining $r_i:T_i\to C_i$, projective regular nodal families
unchanged generically and near $B$ and the markings. A regular scheme has disjoint irreducible
components; flatness excludes vertical components, so their finitely many connected components
are integral regular surfaces. The generic identification matches them. Apply common regular-
surface resolution componentwise over the Noetherian scheme $S$, and take the disjoint union.
This gives $W$ with two point-blowup projections. Every centre is in the special fibre: a closed
point of a proper $S$-surface has closed image in $S$. All generic identifications are
consequently preserved.
   Uses: lem-sfb-nodal-trait-regularization, lem-sfb-common-regular-surface-resolution.

3. Among point-blowup sequences $q_1:W\to T_1$ equipped with an $S$-map $q_2:W\to T_2$ inducing
the fixed generic identification, choose one of minimum length, summing lengths over components.
The preceding step gives nonemptiness. The second map is proper since $W$ is proper over $S$ and
$T_2$ is separated, and is birational on matched components. By the normal-modification theorem
it is an isomorphism above generic points of special-fibre components of $T_2$, whose local
rings are DVRs. Hence a component of $W$ of multiplicity greater than one, or an exceptional
$\mathbf P^1_l$ with $l/k$ inseparable, is contracted by $q_2$. If it dominated a component, it
would have its multiplicity and function field, contradicting the geometric reducedness of that
component of $T_2$.
   Uses: lem-sfb-point-blowup-fibre-defects, lem-weil-pbc-proper-to-separated, lem-sfb-normal-
modification-codimension-one, lem-kun-projective-implies-proper.

4. Call an exceptional component bad if its fibre coefficient exceeds one or it is $\mathbf
P^1_l$ with $l/k$ inseparable. The fibre-defect calculation says defects persist under strict
transform and any later blowup centred on a bad component creates another bad one. If there is a
bad creation, choose the last. Its curve $E$ has no later centre on it. Subsequent blowups are
away from $E$, so can be performed before this blowup: both orders are identical on the
complement of $E$ and glue with the unchanged neighbourhood of its centre. Thus $W$ is a single
point blowup of a regular $W^-$ whose sequence over $T_1$ is shorter by one. Both $q_1$ and
$q_2$ contract $E$. Point-blowdown factorization descends $q_2$ to $W^-$. Its structural map is
still over $S$ by uniqueness of factorization, and its generic identification is unchanged. This
contradicts minimality, so no bad component is ever created.
   Uses: lem-sfb-point-blowup-fibre-defects, lem-sfb-point-blowdown-factorization.

5. Induct along the minimal sequence from $T_1$. A node centre would create coefficient two; a
smooth centre with inseparable residue extension would create a non-geometrically-reduced
exceptional line. Both are excluded. Every centre is therefore a smooth point of the special
fibre with separable residue field. The good-centre clause proves inductively that all geometric
fibres remain reduced nodal curves and each blowup has geometrically connected fibres. The same
blowup theorem preserves projectivity, flatness and finite presentation. Thus $W$ is a
projective flat finitely presented regular nodal family, and $W\to C_1$ has nonempty
geometrically connected fibres: composition preserves this property by the closed-surjection
argument written in the final step.
   Uses: lem-sfb-point-blowup-fibre-defects, lem-sfb-nodal-trait-regularization.

6. Lift $B_K\to W_K$ locally at each closed point of $B$, using proper valuative extension on
its DVR local ring, with uniformizer $\pi$. This gives maps on neighbourhoods: in a finite
presentation of an affine target chart, choose denominators outside the maximal ideal for the
finitely many images of generators, then invert further denominators making the finitely many
relations zero. The resulting maps agree on overlaps because they agree generically and $W$ is
separated; the dense-open equality theorem applies since $B$ is flat over $R$. They glue to
$B\to W$. The markings lift directly from $\operatorname{Spec}R$ by the same valuative theorem.
Uniqueness gives the prescribed composites to $C_i$ and $T_i$. This argument uses local DVRs of
a semilocal finite etale algebra, and does not assume that algebra is a product of local rings.
   Uses: lemma-nagata-proper-separated-valuation-extension, lem-sfb-persistent-node-
normalization, def-sbc-locally-finite-presentation, lemma-nagata-ext-scheme-theoretically-
dominant-separated.

7. The branch and marking lifts are smooth. In the etale local nodal model the equation is
$xy=h$ over an etale DVR extension. Regularity of the total space forces a nonzero smoothing
parameter $h$ to have valuation one: valuation at least two leaves three independent maximal-
ideal generators in dimension two. The generic fibre is smooth, so $h\ne0$. A lifted branch,
being unramified over $R$, cannot pass through this node: it would give positive integral
$v(x),v(y)$ with sum $v(h)=1$. The lifts stay disjoint because their images in $C_1$ are
disjoint. The map $B\to W$ is a closed immersion by closed-immersion cancellation applied to
$B\to W\to C_1$: the composite is the given branch closed immersion and $W\to C_1$ is proper,
hence separated.
   Uses: lem-trf-nodal-family-etale-local-model, lem-sfb-dvr-nodal-chart-blowup-calculus, lem-
sfb-persistent-node-normalization, lem-weil-pbc-closed-immersion-cancellation.

8. Pinch $B\hookrightarrow W$ along $B\to N$, obtaining the projective flat finitely presented
nodal family $Y=W\amalg_BN$. The compatible maps $W\to C_i\to X_i$ and $N\to X_i$ induce
$p_i:Y\to X_i$. They are proper since $Y$ is proper over $S$ and $X_i$ is separated. The
markings give disjoint smooth sections $b_j$, since pinching changes nothing away from $B$.
Generically this pushout is the normalization-conductor square of $(X_i)_K$, whence $(p_1)_K$ is
an isomorphism and $(p_2)_K=u(p_1)_K$. The marking identities $p_1b_j=a_{1j}$ and
$p_2b_j=a_{2\sigma(j)}$ follow from construction and valuative uniqueness.
   Uses: lem-sfb-trait-etale-branch-pinching, lem-sfb-persistent-node-normalization, lem-weil-
pbc-proper-to-separated, lemma-nagata-proper-separated-valuation-extension, lem-kun-projective-
implies-proper.

9. For each $i$, take $Z_i$ to be the set of images in $X_i$ of the finitely many centres of
$T_i\to C_i$ and of the non-isomorphism locus of $W\to T_i$. For $q_1$ finiteness follows from
its finite blowup sequence. For $q_2$, the normal-modification theorem, clauses (1) and (2),
puts every codimension-zero point and every codimension-one point of the regular surface $T_2$
(whose local ring is then a DVR) into the maximal open over which $q_2$ is an isomorphism; its
closed complement has dimension zero and is finite in the Noetherian surface $T_2$. All these
points are closed special-fibre points. Put $V=X_i\setminus Z_i$. Then $W\to C_i$ is an
isomorphism over the inverse image $C_V$ of $V$, and it carries the lifted $B$ identically onto
$B_V$. By the open-restriction clauses of persistent-node normalization and of trait branch
pinching, $V$ is the pushout of $C_V\leftarrow B_V\to N_V$ and $p_i^{-1}(V)$ is the pushout of
the isomorphic diagram $W_V\leftarrow B_V\to N_V$, so $p_i^{-1}(V)\to V$ is an isomorphism. This
verifies the required isomorphism also along horizontal nodes, where normalization alone was not
an isomorphism.
   Uses: lem-sfb-normal-modification-codimension-one, lem-sfb-persistent-node-normalization,
lem-sfb-trait-etale-branch-pinching, lem-sfb-nodal-trait-regularization.

10. The geometric fibres of $Y$ are connected. The fibres of $W\to C_1$ are nonempty
geometrically connected, by regularization and good point blowups. Off $N$, the geometric fibres
of $Y\to X_1$ are these fibres. Over a point of $N$, the inverse image in $W$ is the union of
the two connected branch fibres; pinching identifies their chosen branch points and so makes the
fibre connected. Thus $Y_{\bar s}\to(X_1)_{\bar s}$ is a proper surjection with connected
fibres. If $Y_{\bar s}$ were disconnected, its two clopen pieces would have disjoint closed
images covering the connected $(X_1)_{\bar s}$, a contradiction. Nonemptiness is immediate from
surjectivity. This includes nonsplit nodes and disconnected intermediate normalizations. Empty
$B$ and $n=0$ require no alteration of the argument.
   Uses: lem-sfb-nodal-trait-regularization, lem-sfb-point-blowup-fibre-defects, lem-sfb-
persistent-node-normalization, lem-sfb-trait-etale-branch-pinching.
-/
theorem exists_common_marked_nodal_model
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (X₁ X₂ : Over (Spec (.of R)))
    [IsHProjective X₁.hom] [IsHProjective X₂.hom]
    [Flat X₁.hom] [Flat X₂.hom]
    [LocallyOfFinitePresentation X₁.hom] [LocallyOfFinitePresentation X₂.hom]
    (hnodal₁ : HasNodalGeometricFibres X₁.hom)
    (hnodal₂ : HasNodalGeometricFibres X₂.hom)
    (hgeometric₁ : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ Spec (.of R)),
      IsReduced (pullback X₁.hom t) ∧ (pullback X₁.hom t).IsPureDimension 1)
    (hgeometric₂ : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ Spec (.of R)),
      IsReduced (pullback X₂.hom t) ∧ (pullback X₂.hom t).IsPureDimension 1)
    (n : ℕ) (a₁ : Fin n → (Spec (.of R) ⟶ X₁.left))
    (a₂ : Fin n → (Spec (.of R) ⟶ X₂.left))
    (ha₁ : ∀ j : Fin n, a₁ j ≫ X₁.hom = 𝟙 (Spec (.of R)))
    (ha₂ : ∀ j : Fin n, a₂ j ≫ X₂.hom = 𝟙 (Spec (.of R)))
    (hdisjoint₁ : Pairwise (fun j k : Fin n ↦ Disjoint (Set.range (a₁ j)) (Set.range (a₁ k))))
    (hdisjoint₂ : Pairwise (fun j k : Fin n ↦ Disjoint (Set.range (a₂ j)) (Set.range (a₂ k))))
    (hsmooth₁ : ∀ (j : Fin n) (s : Spec (.of R)), a₁ j s ∈ X₁.hom.smoothLocus)
    (hsmooth₂ : ∀ (j : Fin n) (s : Spec (.of R)), a₂ j s ∈ X₂.hom.smoothLocus)
    (σ : Equiv.Perm (Fin n))
    (uK : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X₁ ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj X₂)
    (hmark : ∀ j : Fin n,
      sectionBaseChange X₁.hom (a₁ j) (ha₁ j)
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ≫ uK.hom.left =
        sectionBaseChange X₂.hom (a₂ (σ j)) (ha₂ (σ j))
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    ∃ (Y : Over (Spec (.of R))) (_ : IsHProjective Y.hom) (_ : Flat Y.hom)
      (hY : LocallyOfFinitePresentation Y.hom)
      (b : Fin n → (Spec (.of R) ⟶ Y.left)) (p₁ : Y ⟶ X₁) (p₂ : Y ⟶ X₂),
      @HasNodalGeometricFibres Y.left (Spec (.of R)) Y.hom hY ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of R)),
        IsReduced (pullback Y.hom t) ∧ (pullback Y.hom t).IsPureDimension 1) ∧
      (∀ j : Fin n, b j ≫ Y.hom = 𝟙 (Spec (.of R))) ∧
      Pairwise (fun j k : Fin n ↦ Disjoint (Set.range (b j)) (Set.range (b k))) ∧
      (∀ (j : Fin n) (s : Spec (.of R)), b j s ∈ Y.hom.smoothLocus) ∧
      IsProper p₁.left ∧ IsProper p₂.left ∧
      (∃ (Z₁ : Set X₁.left) (V₁ : X₁.left.Opens), Z₁.Finite ∧
        (∀ z ∈ Z₁, IsClosed ({z} : Set X₁.left) ∧
          X₁.hom z = IsLocalRing.closedPoint R) ∧
        (V₁ : Set X₁.left) = Z₁ᶜ ∧ IsIso (pullback.snd p₁.left V₁.ι)) ∧
      (∃ (Z₂ : Set X₂.left) (V₂ : X₂.left.Opens), Z₂.Finite ∧
        (∀ z ∈ Z₂, IsClosed ({z} : Set X₂.left) ∧
          X₂.hom z = IsLocalRing.closedPoint R) ∧
        (V₂ : Set X₂.left) = Z₂ᶜ ∧ IsIso (pullback.snd p₂.left V₂.ι)) ∧
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map p₂).left =
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map p₁).left ≫
          uK.hom.left ∧
      (∀ j : Fin n, b j ≫ p₁.left = a₁ j) ∧
      (∀ j : Fin n, b j ≫ p₂.left = a₂ (σ j)) ∧
      IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map p₁) ∧
      IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map p₂) := by
  sorry

end AlgebraicGeometry
