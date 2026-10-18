/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import Mathlib.CategoryTheory.Sites.Coherent.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Sheaf.AlgebraicGeometry.ProEtaleQcqsSubsite
public import Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite
public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.GeometricMorphism

import Sheaf.RingTheory.IndEtaleStability
import Sheaf.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import Sheaf.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresObjects
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Sheaves.Stalks

/-!
# The component-site projection of an affine scheme

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 2.2.8,
paragraph preceding Lemma 4.2.13, and Lemma 4.2.13(1), with the split-cover
qualification recorded in the DAG (blueprint: lem-zl-affine-component-site-projection).

## Main definitions

* `componentProfinite`: the component quotient of a qcqs scheme, as a profinite space.
* `componentObject`, `componentObjectMap`: the component object of a qcqs pro-etale
  object over the component quotient of the base, and its map on morphisms.
* `HasSplitFiniteQcqsCovers`: the split-cover condition on a qcqs pro-etale object.
* `ComponentSiteEvaluation`: the geometric morphism with its split-cover evaluation in one
  coefficient category.

## Main statements

* `affine_component_site_projection`: the component-site projection of an affine scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- Bundle the actual component quotient with its quotient topology. The structure proofs
come from the spectral-component theorem; there is no chosen replacement space.
Source: Bhatt--Scholze, Lemma 2.2.8
(blueprint: lem-zl-affine-component-site-projection). -/
def componentProfinite (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    Profinite.{u} := by
  letI : SpectralSpace X := {}
  exact @Profinite.of (ConnectedComponents X) _
    (spectralSpace_connectedComponents_profinite (T := X)).1
    (spectralSpace_connectedComponents_profinite (T := X)).2.1
    (spectralSpace_connectedComponents_profinite (T := X)).2.2

/-- The component object of a qcqs pro-etale object, over the component quotient of the base.
Source: Bhatt--Scholze, Lemma 2.2.8 and paragraph before Lemma 4.2.13
(blueprint: lem-zl-affine-component-site-projection). -/
def componentObject (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (W : Qcqs T) : Over (componentProfinite T) := by
  letI : CompactSpace W.obj.left := W.property.1
  letI : QuasiSeparatedSpace W.obj.left := W.property.2
  exact Over.mk (ConcreteCategory.ofHom
    ⟨W.obj.hom.continuous.connectedComponentsMap,
      W.obj.hom.continuous.connectedComponentsMap_continuous⟩ :
        componentProfinite W.obj.left ⟶ componentProfinite T)

/-- The map on actual component quotients induced by a map over the base.
Source: Bhatt--Scholze, Lemma 4.2.13(1), canonical factorization
(blueprint: lem-zl-affine-component-site-projection). -/
def componentObjectMap {T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    {V W : Qcqs T} (a : V ⟶ W) : componentObject T V ⟶ componentObject T W :=
  Over.homMk (ConcreteCategory.ofHom
    ⟨a.hom.left.continuous.connectedComponentsMap,
      a.hom.left.continuous.connectedComponentsMap_continuous⟩) (by
        ext z
        obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe z
        change ConnectedComponents.mk (W.obj.hom (a.hom.left x)) =
          ConnectedComponents.mk (V.obj.hom x)
        exact congrArg ConnectedComponents.mk
          (congrArg (fun f : V.obj.left ⟶ T ↦ f x) a.hom.w))

/-- Precisely the finite qcqs split-cover condition: the canonical coproduct map has a
scheme section. Since the coproduct map is over T, its section is automatically over T.
Finite index sets are represented by Fin n, including n = 0.
Source: the corrected split-cover form of Bhatt--Scholze, Lemma 4.2.13(1),
using Stacks Tags 00WB and 00WK (blueprint: lem-zl-affine-component-site-projection). -/
def HasSplitFiniteQcqsCovers {T : Scheme.{u}} (W : Qcqs T) : Prop :=
  ∀ (n : ℕ) (V : Fin n → Qcqs T) (a : ∀ i, (V i).obj ⟶ W.obj),
    Presieve.ofArrows (fun i ↦ (V i).obj) a ∈ precoverage T W.obj →
      ∃ σ : W.obj.left ⟶ ∐ (fun i ↦ (V i).obj.left),
        σ ≫ Sigma.desc (fun i ↦ (a i).left) = 𝟙 W.obj.left

/-- The evaluation assertion in a coefficient category. The direct image is identified
with actual restriction along U. Its adjunction unit and the component factorization b
normalize the evaluation isomorphisms, which are natural in both sheaves and eligible W.
Taking C to be sets, abelian groups, or rings retains all operations.
Source: Bhatt--Scholze, Lemma 4.2.13(1), with split-cover sheafification via
Stacks Tags 00WB/00WK (blueprint: lem-zl-affine-component-site-projection). -/
def ComponentSiteEvaluation (T : Scheme.{u}) [IsAffine T]
    (U : Over (componentProfinite T) ⥤ T.ProEt)
    (r : ∀ E : Over (componentProfinite T), C((U.obj E).left, E.left))
    (hU : U.IsContinuous ((coherentTopology Profinite.{u}).over (componentProfinite T))
      (topology T))
    (C : Type w) [Category.{v} C] : Prop :=
  ∃ g : GeometricMorphism (Sheaf (topology T) C)
      (Sheaf ((coherentTopology Profinite.{u}).over (componentProfinite T)) C),
    ∃ d : g.direct ≅ U.sheafPushforwardContinuous C
        ((coherentTopology Profinite.{u}).over (componentProfinite T)) (topology T),
      ∃ b : ∀ (W : Qcqs T) (E : Over (componentProfinite T)),
          (W.obj ⟶ U.obj E) → (componentObject T W ⟶ E),
        (∀ (W : Qcqs T) (E : Over (componentProfinite T))
          (a : W.obj ⟶ U.obj E) (x : W.obj.left),
          (b W E a).left (ConnectedComponents.mk x) = r E (a.left x)) ∧
        ∃ e : ∀ (F : Sheaf
            ((coherentTopology Profinite.{u}).over (componentProfinite T)) C)
            (W : Qcqs T) (_hW : HasSplitFiniteQcqsCovers W),
              (g.inverse.obj F).obj.obj (op W.obj) ≅ F.obj.obj (op (componentObject T W)),
          (∀ (F : Sheaf
              ((coherentTopology Profinite.{u}).over (componentProfinite T)) C)
            (W : Qcqs T) (hW : HasSplitFiniteQcqsCovers W)
            (E : Over (componentProfinite T)) (a : W.obj ⟶ U.obj E),
            ((g.adj.unit.app F ≫ d.hom.app (g.inverse.obj F)).hom.app (op E)) ≫
                (g.inverse.obj F).obj.map a.op ≫ (e F W hW).hom =
              F.obj.map (b W E a).op) ∧
          (∀ (F G : Sheaf
              ((coherentTopology Profinite.{u}).over (componentProfinite T)) C)
            (α : F ⟶ G) (V W : Qcqs T)
            (hV : HasSplitFiniteQcqsCovers V) (hW : HasSplitFiniteQcqsCovers W)
            (a : V ⟶ W),
            (g.inverse.obj F).obj.map a.hom.op ≫
                (g.inverse.map α).hom.app (op V.obj) ≫ (e G V hV).hom =
              (e F W hW).hom ≫ F.obj.map (componentObjectMap a).op ≫
                α.hom.app (op (componentObject T V)))

/-- The affine component functor, its geometric morphism, and its split-cover evaluation.
Source: Bhatt--Scholze, Lemma 2.2.8 and Lemma 4.2.13(1), with the corrected
split-cover hypothesis; Stacks Tags 00WB and 00WK
(blueprint: lem-zl-affine-component-site-projection).

Proof for stage 3 (the thirteen steps of the node):
1. Write $T=\operatorname{Spec}A$ and $q:|T|\to P$. By [lem-weil-pbc-qcqs-scheme-spectral] and
[lem-pe-spectral-components-profinite], $P$ is profinite. For a profinite $E$ put
$D=\operatorname{LC}(E,A)$. By [lem-weil-pbc-locally-constant-prime-spectrum],
$\operatorname{Spec}D=E\times|T|$, with the structure map to $T$ given by projection. Each
locally constant function has finite image on the compact space $E$ and factors through its
finite clopen partition into fibres. Two such presentations agree on their common refinement.
Thus $D$ is the filtered colimit of the finite products $A^{E_i}$. These are finite products of
the principal localization $A_1$, so $A\to D$ is ind-Zariski and ind-etale by
[def-weil-pbc-ind-etale-algebra].
2. The map $E\times|T|\to E\times P$, $(e,t)\mapsto(e,q(t))$, is a quotient map: it is a
continuous surjection from a quasi-compact space to a Hausdorff space and is closed, since each
closed subset of its source is quasi-compact. Its fibres are the connected components of $|T|$.
Conversely a connected subset has constant image in each of the totally disconnected spaces $E$
and $P$, so these fibres are exactly the connected components of $E\times|T|$. Consequently
$\pi_0(\operatorname{Spec}D)=E\times P$. For $f:E\to P$, its graph $G=\{(e,f(e)):e\in E\}$ is
closed. Put $Z=\{(e,t):q(t)=f(e)\}$, the inverse image of $G$. It is a closed union of
components of $\operatorname{Spec}D$.
3. Let $M$ be the multiplicative set of idempotents $a\in D$ such that $Z\subseteq D(a)$, and
define the actual algebra $B=M^{-1}D$ and $T_E=\operatorname{Spec}B$. Products stay in $M$, and
$1\in M$; if $Z=\varnothing$, $0\in M$ and $B=0$. By [lem-weil-pbc-spec-clopen-idempotent] and
[lem-weil-pbc-profinite-clopen-basis], the intersection of these clopen neighbourhoods is
exactly $Z$: a point outside $Z$ maps outside the closed subset $G$ of the profinite space
$E\times P$, so a clopen containing $G$ excludes it. By
[lem-weil-pbc-localization-spectrum-embedding], $\operatorname{Spec}B\to\operatorname{Spec}D$ is
a homeomorphism onto precisely this intersection. The localization $B$ is the filtered colimit
of $D_a$, $a\in M$, since finitely many denominators combine by multiplication. Therefore $D\to
B$ is ind-Zariski and ind-etale; [lem-weil-pbc-ind-etale-stability] makes $A\to B$ ind-etale.
This constructs the required affine object without choosing unspecified existence data.
4. At a point $(e,\mathfrak p)$ of $\operatorname{Spec}D$, evaluation identifies
$D_{(e,\mathfrak p)}$ with $A_{\mathfrak p}$. Indeed every locally constant function is constant
on a clopen neighbourhood of $e$; its characteristic idempotent is outside the prime and hence
becomes $1$ in this local ring. Thus every fraction is the fraction of its two values at $e$;
conversely constant functions define the inverse homomorphism. Further localization by $M$
leaves these local rings unchanged at points of $Z$, by the fraction formulas of
[def-weil-pbc-localization-at-prime]. Hence the structure morphism induces isomorphisms on all
stalks of the inverse-image structure sheaf from $T$. Applying
[lem-weil-pbc-sets-sheaf-iso-on-stalks] to the underlying sheaves identifies this structure
sheaf with $\mathcal O_{T_E}$; the inverse maps preserve ring operations because the original
maps do. The ringed space is therefore exactly $|T|\times_P E$ with the inverse-image sheaf
specified in the statement.
5. The projection $|T_E|\to E$ is surjective and has connected fibres $q^{-1}(f(e))$. A
connected subset has constant image in $E$, so these fibres are exactly the connected
components. The space $|T_E|$ is quasi-compact, and its projection to the Hausdorff space $E$ is
closed (closed subsets are quasi-compact). It is therefore a quotient map and induces the
canonical homeomorphism $\pi_0(|T_E|)\cong E$. For any scheme $W\to T$, a continuous lift
$|W|\to |T|\times_P E$ over $|T|$ gives a unique scheme map $W\to T_E$: pull back the given
structure-sheaf map of $W\to T$ through the identified inverse-image sheaf. It is local on
stalks because the stalks on the target are those of $T$. Conversely every scheme map gives that
lift. If $W$ is qcqs, such lifts are precisely continuous $P$-maps $\pi_0(|W|)\to E$, by the
quotient topology and total disconnectedness of $E$. This proves the mapping bijection,
including its naturality by composition.
6. A continuous $P$-map $E\to E'$ now gives the unique $T$-map $T_E\to T_{E'}$ inducing it;
uniqueness gives identities and composition. The same mapping description proves preservation of
finite limits: maps from any scheme $W\to T$ into a finite limiting cone correspond to
continuous lifts into the corresponding finite limit of profinite spaces over $P$, hence to one
unique map to its $T_E$. In particular $T_P=T$ and $T_{E_1\times_E
E_2}=T_{E_1}\times_{T_E}T_{E_2}$. For a finite jointly surjective family $E_i\to E$, every point
$(t,e)$ lifts to some $(t,e_i)$. Each induced arrow is ind-etale by the last algebra-map clause
of [lem-weil-pbc-ind-etale-stability], since both algebras are ind-etale over $A$. It is weakly
etale by that node. By [lem-weil-pbc-morphism-affine-schemes-affine], these arrows between
affine schemes are affine: over every affine open of the target, their inverse images are
affine. They remain jointly surjective over that open. Since the family is finite, these inverse
images give exactly the finite affine source opens required by [def-weil-pbc-proetale-site].
This proves preservation of coverings, also when all spaces are empty.
7. Take the small skeletons and the larger sheaf-value universe of [def-weil-size-convention].
The category of profinite spaces over $P$ has finite limits: they are the usual finite products
and closed equalizer subspaces in compact Hausdorff totally disconnected spaces, with terminal
object $P\to P$. Apply [lem-weil-pbc-left-exact-site-inverse-image-tensor] to $u:E\mapsto T_E$,
using step 6. This gives the geometric morphism $\pi_T$, whose inverse image is presheaf left
Kan extension followed by sheafification, and whose direct image is restriction along $u^{op}$.
This invocation supplies both the adjunction and left exactness; neither is inferred just from a
pointwise formula.
8. Let $F$ be a sheaf of sets on $\mathbf{Prof}/P$ and $W\to T$ be qcqs. In the Kan formula of
[lem-weil-pbc-presheaf-pullback-sets-left-exact], the index category before taking the opposite
consists of pairs $(E,W\to T_E)$. Step 5 gives its initial object $(\pi_0(|W|)\to P,W\to
T_{\pi_0(|W|)})$: the unique arrow to $(E,a)$ is the component map corresponding to $a$. Its
opposite is terminal. The colimit is therefore $F(\pi_0(|W|)\to P)$: every element represented
in $F(E)$ maps there by that unique arrow, and the universal cocone equations force precisely
these maps. Composition on $W$ and maps of $F$ preserve the component factorizations, so this
identification is natural in both variables. This computes the presheaf inverse image on all
qcqs objects, before sheafification.
9. Let $K$ be the presheaf Kan inverse image of step 8 and $\eta:K\to K^\#$ its sheafification
unit. By [lem-weil-pbc-proetale-qcqs-finite-family-geometry], finite disjoint unions of qcqs
objects are qcqs. Connected components commute with finite disjoint unions, directly from their
quotient topology. For such a union $V=\coprod_i V_i$, step 8 and the sheaf axiom of $F$ for the
clopen summand cover give $K(V)=F(\coprod_i\pi_0(V_i)\to P)=\prod_i K(V_i)$, by the restriction
maps. The same geometry node states $K^\#(V)=\prod_i K^\#(V_i)$ for the sheaf $K^\#$. These
identifications commute with $\eta$ by its naturality. This includes the empty family: both
presheaves have singleton value on the empty scheme.
10. Every covering of a qcqs $W$ has a finite affine refinement. Namely take a finite affine
open cover of $W$; on each affine target open the covering condition of
[def-weil-pbc-proetale-site] provides finitely many affine source opens mapping into it and
covering it. Their composites give the required refinement, and their sources are qcqs by
[lem-weil-pbc-proetale-qcqs-finite-family-geometry]. Hence every covering used to test local
equality or local representability of sections at $W$ can be replaced by a finite qcqs covering
$\{W_i\to W\}$. By the hypothesis in the corrected statement, $p:V=\coprod_iW_i\to W$ then has a
section $\sigma$. This hypothesis is imposed only here, after the general construction and Kan
calculation; it is not asserted for arbitrary qcqs schemes.
11. Suppose $a,b\in K(W)$ have the same image under $\eta_W$. By
[lem-weil-pbc-site-sheafification-sections-local], they agree after a covering of $W$. Refine as
in step 10 to a finite qcqs covering and write $p:V\to W$, $p\sigma=\operatorname{id}_W$. Their
pullbacks agree on each summand, so step 9 gives $p^*a=p^*b$ in $K(V)$. Pulling back by $\sigma$
gives $a=\sigma^*p^*a=\sigma^*p^*b=b$. Thus $\eta_W$ is injective. This uses injectivity of the
finite-product restriction of $K$; it does not assume that $K$ is already separated on arbitrary
objects.
12. Given $t\in K^\#(W)$, [lem-weil-pbc-site-sheafification-sections-local] supplies a cover and
local lifts. Refine it by step 10 to finite qcqs $W_i$, with lifts $a_i\in K(W_i)$ and split
$p:V=\coprod_iW_i\to W$. By step 9 there is a unique $a\in K(V)$ restricting to all $a_i$. The
two sections $\eta_V(a)$ and $p^*t$ of $K^\#(V)$ have the same restrictions on every summand;
the sheaf product formula in step 9 implies their equality. Consequently
$\eta_W(\sigma^*a)=\sigma^*\eta_V(a)=\sigma^*p^*t=t$. Thus $\eta_W$ is bijective. By step 7,
$K^\#=\pi_T^{-1}F$; compose $\eta_W^{-1}$ with step 8 to obtain the asserted formula. Naturality
follows from that of $\eta$ and step 8, for maps between eligible objects. The section $\sigma$
proves bijectivity only and does not enter this canonical identification.
13. For an abelian-group or ring sheaf, use [lem-weil-pbc-sheaf-algebraic-structures-objects] to
regard its operations as maps out of finite powers of its underlying sheaf of sets. The inverse
image preserves these powers by step 7. Naturality of the set-valued identification in step 12,
applied to addition, zero, negation, multiplication and one, identifies the induced operations
with those on $F(\pi_0(|W|)\to P)$. For example the addition square identifies the two maps from
$F(\pi_0(|W|))^2$ with the given addition on $F(\pi_0(|W|))$; the nullary maps similarly give
zero and one. The equations for the operations are preserved functorially. Thus the canonical
identification is one of abelian groups or rings, and is natural in their sheaves and in
eligible $W$.
-/
theorem affine_component_site_projection (T : Scheme.{u}) [IsAffine T] :
    ∃ (U : Over (componentProfinite T) ⥤ T.ProEt)
      (r : ∀ E : Over (componentProfinite T), C((U.obj E).left, E.left)),
      (∀ E : Over (componentProfinite T),
        IsAffine (U.obj E).left ∧
        RingHom.IndEtaleAcrossUniverses (U.obj E).hom.appTop.hom ∧
        (∀ x : (U.obj E).left, IsIso ((U.obj E).hom.stalkMap x)) ∧
        (∃ h : (U.obj E).left ≃ₜ
            {p : T × E.left | ConnectedComponents.mk p.1 = E.hom p.2},
          (∀ x, (h x).val.1 = (U.obj E).hom x) ∧
          (∀ x, (h x).val.2 = r E x)) ∧
        (∃ e : ConnectedComponents (U.obj E).left ≃ₜ E.left,
          ∀ x : (U.obj E).left, e (ConnectedComponents.mk x) = r E x)) ∧
      (∀ (E E' : Over (componentProfinite T)) (a : E ⟶ E')
        (x : (U.obj E).left), r E' ((U.map a).left x) = a.left (r E x)) ∧
      PreservesFiniteLimits U ∧
      (∀ (n : ℕ) (E : Fin n → Over (componentProfinite T))
        (B : Over (componentProfinite T)) (a : ∀ i, E i ⟶ B),
        (∀ x : B.left, ∃ (i : Fin n) (y : (E i).left), (a i).left y = x) →
          Presieve.ofArrows (fun i ↦ U.obj (E i)) (fun i ↦ U.map (a i)) ∈
            precoverage T (U.obj B)) ∧
      ∃ hU : U.IsContinuous
          ((coherentTopology Profinite.{u}).over (componentProfinite T)) (topology T),
        ComponentSiteEvaluation T U r hU (Type (u + 1)) ∧
        ComponentSiteEvaluation T U r hU AddCommGrpCat.{u + 1} ∧
        ComponentSiteEvaluation T U r hU CommRingCat.{u + 1} := by
  sorry

end AlgebraicGeometry.Scheme.ProEt
