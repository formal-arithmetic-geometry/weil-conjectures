/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.PbcQbarStandardCohomology
public import Sheaf.Paper.PbcQbarCategory
public import Sheaf.Paper.LocalizedTStructure
public import Sheaf.Paper.PbcScalarExtension
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.IntegralUniformCoefficient
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.FiniteTypeGeometryFibreBound
import Sheaf.Paper.IntegralTStructure
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Paper.FiniteFreeConstructibleScalarTransport
import Sheaf.CategoryTheory.Triangulated.TExactTruncationComparison
import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
import Sheaf.Paper.FiniteStagePairCategory
import Sheaf.Paper.CommonStageCalculus
import Sheaf.Paper.PbcVerdierAxioms

/-! # Ordinary truncations at common adic coefficient stages

Source: Bhatt--Scholze, Propositions 6.8.11(3) and 6.8.14;
BBD, Proposition 1.3.3 and §1.3.16
(blueprint: lem-per-adic-common-stage-truncations).

The package below states the entire assertion on the published completed PBC stages.
The finite stages use their published normalized shifts and integral-image triangles.
The Qbar category is the corresponding literal pair category, without a Karoubi envelope.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  {C : I → Type u} [∀ i : I, Category.{v} (C i)]
  [∀ i : I, Preadditive (C i)] [∀ i : I, HasZeroObject (C i)]
  [∀ i : I, HasShift (C i) ℤ]
  [∀ (i : I) (n : ℤ), (shiftFunctor (C i) n).Additive]
  [∀ i : I, Pretriangulated (C i)] [∀ i : I, IsTriangulated (C i)]
  (S : StageSystem C)
  [∀ {i j : I} (h : i ≤ j), (S.T h).Additive]
  [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]
  [HasShift S.PairCategory ℤ]
  [∀ n : ℤ, (shiftFunctor S.PairCategory n).Additive]
  [Pretriangulated S.PairCategory] [IsTriangulated S.PairCategory]
  [∀ i : I, (S.ι i).CommShift ℤ]

/-- The full common-stage truncation assertion, including its representative formulas.
This record packages equations for the existing stage-system and t-structure APIs.
The theorem below specializes it to the published PBC categories, scalar functors,
associators and shifts, and fixes the standard structures by their integral-image
classes. Comparison isomorphisms are normalized by the canonical units and counits.
Source: Bhatt--Scholze 6.8.11(3), 6.8.14; BBD 1.3.3, 1.3.16
(blueprint: lem-per-adic-common-stage-truncations). -/
structure AdicCommonStageTruncations where
  /-- Finite-stage standard structures, for the already fixed normalized shifts. -/
  finite : ∀ E : I,
    Triangulated.TStructure (C E)
  /-- Each localized standard structure is bounded. -/
  finite_bounded : ∀ E, (finite E).bounded = ⊤
  /-- Finite completed scalar extension is t-exact, with no Tor-compatibility assumption. -/
  scalar_tExact : ∀ {E F : I} (h : E ≤ F),
    (S.T h).IsTExact (finite E) (finite F)
  /-- Upper comparisons, oriented from scalar extension of truncation. -/
  upper : ∀ {E F : I} (h : E ≤ F) (n : ℤ),
    (finite E).truncLE n ⋙ S.T h ≅
      S.T h ⋙ (finite F).truncLE n
  /-- Lower comparisons, with the same orientation. -/
  lower : ∀ {E F : I} (h : E ≤ F) (n : ℤ),
    (finite E).truncGE n ⋙ S.T h ≅
      S.T h ⋙ (finite F).truncGE n
  /-- Normalization fixes the upper comparison uniquely. -/
  upper_counit : ∀ {E F : I} (h : E ≤ F) (n : ℤ)
    (K : C E),
    (upper h n).hom.app K ≫ ((finite F).truncLEι n).app
        ((S.T h).obj K) =
      (S.T h).map (((finite E).truncLEι n).app K)
  /-- Normalization fixes the lower comparison uniquely. -/
  lower_unit : ∀ {E F : I} (h : E ≤ F) (n : ℤ)
    (K : C E),
    (S.T h).map (((finite E).truncGEπ n).app K) ≫
        (lower h n).hom.app K =
      ((finite F).truncGEπ n).app ((S.T h).obj K)
  /-- The common-stage bounded standard t-structure. -/
  common : Triangulated.TStructure (S.PairCategory)
  /-- Boundedness on every pair object. -/
  common_bounded : common.bounded = ⊤
  /-- Both common-stage halves are isomorphism closures of the finite-stage halves. -/
  common_le : ∀ (n : ℤ) (Z : S.PairCategory), common.le n Z ↔
    ∃ (E : I) (K : C E),
      (finite E).le n K ∧
        Nonempty (Z ≅ (S.ι E).obj K)
  /-- The common-stage lower half, with its own finite-stage witness. -/
  common_ge : ∀ (n : ℤ) (Z : S.PairCategory), common.ge n Z ↔
    ∃ (E : I) (K : C E),
      (finite E).ge n K ∧
        Nonempty (Z ≅ (S.ι E).obj K)
  /-- The heart is the isomorphism closure of finite-stage hearts, with a single witness. -/
  common_heart : ∀ Z : S.PairCategory, common.heart Z ↔
    ∃ (E : I) (K : C E),
      (finite E).heart K ∧
        Nonempty (Z ≅ (S.ι E).obj K)
  /-- The representative-defined upper truncation functors. -/
  truncUpper : ℤ → S.PairCategory ⥤ S.PairCategory
  /-- The representative-defined lower truncation functors. -/
  truncLower : ℤ → S.PairCategory ⥤ S.PairCategory
  /-- Upper truncation is computed literally on the finite-stage object. -/
  truncUpper_obj : ∀ (n : ℤ) (Z : S.PairCategory),
    (truncUpper n).obj Z = ⟨Z.stage, ((finite Z.stage).truncLE n).obj Z.obj⟩
  /-- Lower truncation is computed literally on the finite-stage object. -/
  truncLower_obj : ∀ (n : ℤ) (Z : S.PairCategory),
    (truncLower n).obj Z = ⟨Z.stage, ((finite Z.stage).truncGE n).obj Z.obj⟩
  /-- Identity coefficient extensions have identity upper comparison. -/
  upper_id : ∀ (E : I) (n : ℤ)
    (K : C E),
    HEq ((upper (le_refl E) n).hom.app K) (𝟙 (((finite E).truncLE n).obj K))
  /-- The upper comparison satisfies composition with the specified scalar associator. -/
  upper_comp : ∀ {E F G : I}
    (h : E ≤ F) (k : F ≤ G) (n : ℤ) (K : C E),
    (S.assoc h k).hom.app
        (((finite E).truncLE n).obj K) ≫ (upper (h.trans k) n).hom.app K =
      (S.T k).map ((upper h n).hom.app K) ≫
        (upper k n).hom.app ((S.T h).obj K) ≫
          ((finite G).truncLE n).map
            ((S.assoc h k).hom.app K)
  /-- Identity coefficient extensions have identity lower comparison. -/
  lower_id : ∀ (E : I) (n : ℤ)
    (K : C E),
    HEq ((lower (le_refl E) n).hom.app K) (𝟙 (((finite E).truncGE n).obj K))
  /-- The lower comparison satisfies composition with the specified scalar associator. -/
  lower_comp : ∀ {E F G : I}
    (h : E ≤ F) (k : F ≤ G) (n : ℤ) (K : C E),
    (S.assoc h k).hom.app
        (((finite E).truncGE n).obj K) ≫ (lower (h.trans k) n).hom.app K =
      (S.T k).map ((lower h n).hom.app K) ≫
        (lower k n).hom.app ((S.T h).obj K) ≫
          ((finite G).truncGE n).map
            ((S.assoc h k).hom.app K)
  /-- Conjugation computes the upper truncation of every quotient representative. -/
  truncUpper_map : ∀ (n : ℤ) (Z W : S.PairCategory)
    (M : I) (hZ : Z.stage ≤ M) (hW : W.stage ≤ M)
    (f : Z.toStage hZ ⟶ W.toStage hW),
    HEq ((truncUpper n).map (StageSystem.PairCategory.mkHom M hZ hW f))
      (StageSystem.PairCategory.mkHom
        (S := S)
        (X := ⟨Z.stage, ((finite Z.stage).truncLE n).obj Z.obj⟩)
        (Y := ⟨W.stage, ((finite W.stage).truncLE n).obj W.obj⟩) M hZ hW
        ((upper hZ n).hom.app Z.obj ≫ ((finite M).truncLE n).map f ≫
          (upper hW n).inv.app W.obj))
  /-- The descended upper functor is the canonical common-stage truncation. -/
  canonicalUpper : ∀ n : ℤ, truncUpper n ≅ common.truncLE n
  /-- Conjugation computes the lower truncation of every quotient representative. -/
  truncLower_map : ∀ (n : ℤ) (Z W : S.PairCategory)
    (M : I) (hZ : Z.stage ≤ M) (hW : W.stage ≤ M)
    (f : Z.toStage hZ ⟶ W.toStage hW),
    HEq ((truncLower n).map (StageSystem.PairCategory.mkHom M hZ hW f))
      (StageSystem.PairCategory.mkHom
        (S := S)
        (X := ⟨Z.stage, ((finite Z.stage).truncGE n).obj Z.obj⟩)
        (Y := ⟨W.stage, ((finite W.stage).truncGE n).obj W.obj⟩) M hZ hW
        ((lower hZ n).hom.app Z.obj ≫ ((finite M).truncGE n).map f ≫
          (lower hW n).inv.app W.obj))
  /-- The descended lower functor is the canonical common-stage truncation. -/
  canonicalLower : ∀ n : ℤ, truncLower n ≅ common.truncGE n
  /-- The descended counit is the class of the finite-stage counit. -/
  canonicalUpper_counit : ∀ (n : ℤ) (Z : S.PairCategory),
    HEq ((canonicalUpper n).hom.app Z ≫ (common.truncLEι n).app Z)
      ((S.ι Z.stage).map
        (((finite Z.stage).truncLEι n).app Z.obj))
  /-- The descended unit is the class of the finite-stage unit. -/
  canonicalLower_unit : ∀ (n : ℤ) (Z : S.PairCategory),
    HEq ((common.truncGEπ n).app Z ≫ (canonicalLower n).inv.app Z)
      ((S.ι Z.stage).map
        (((finite Z.stage).truncGEπ n).app Z.obj))
  /-- The upper cutoff maps descend to their canonical common-stage maps. -/
  cutoff_upper : ∀ (a b : ℤ) (h : a ≤ b) (Z : S.PairCategory),
    HEq ((canonicalUpper a).hom.app Z ≫
        (common.natTransTruncLTOfLE (a + 1) (b + 1) (Int.add_le_add_right h 1)).app Z ≫
          (canonicalUpper b).inv.app Z)
      ((S.ι Z.stage).map
        (((finite Z.stage).natTransTruncLTOfLE (a + 1) (b + 1)
          (Int.add_le_add_right h 1)).app Z.obj))
  /-- The lower cutoff maps likewise descend. -/
  cutoff_lower : ∀ (a b : ℤ) (h : a ≤ b) (Z : S.PairCategory),
    HEq ((canonicalLower a).hom.app Z ≫
        (common.natTransTruncGEOfLE a b h).app Z ≫ (canonicalLower b).inv.app Z)
      ((S.ι Z.stage).map (((finite Z.stage).natTransTruncGEOfLE a b h).app Z.obj))
  /-- The entire truncation triangle descends, including its shifted third arrow. -/
  truncation_triangle : ∀ (E : I) (n : ℤ)
    (K : C E),
    ∃ e : (common.triangleLEGE n (n + 1) rfl).obj
        ((S.ι E).obj K) ≅
      (S.ι E).mapTriangle.obj
        (((finite E).triangleLEGE n (n + 1) rfl).obj K),
      e.hom.hom₂ = 𝟙 _ ∧
        HEq e.hom.hom₁ ((canonicalUpper n).inv.app ⟨E, K⟩) ∧
        HEq e.hom.hom₃ ((canonicalLower (n + 1)).inv.app ⟨E, K⟩)
  /-- Natural scalar comparison for the degree-zero realization of H^r. -/
  cohomology : ∀ {E F : I} (h : E ≤ F) (r : ℤ),
    (shiftFunctor (C E) r ⋙
        (finite E).homology₀ ⋙ (finite E).heart.ι) ⋙
        S.T h ≅
      S.T h ⋙
        shiftFunctor (C F) r ⋙
          (finite F).homology₀ ⋙ (finite F).heart.ι
  /-- H^r comparisons are the two normalized truncation comparisons and the scalar shift. -/
  cohomology_normalized : ∀ {E F : I} (h : E ≤ F)
    (r : ℤ) (K : C E),
    (cohomology h r).hom.app K =
      (lower h 0).hom.app (((finite E).truncLE 0).obj (K⟦r⟧)) ≫
        ((finite F).truncGE 0).map ((upper h 0).hom.app (K⟦r⟧)) ≫
          ((finite F).homology₀ ⋙ (finite F).heart.ι).map
            (((S.T h).commShiftIso r).hom.app K)
  /-- H^r comparisons are identity on identity coefficient extensions. -/
  cohomology_id : ∀ (E : I) (r : ℤ)
    (K : C E),
    HEq ((cohomology (le_refl E) r).hom.app K)
      (𝟙 (((finite E).homology₀.obj (K⟦r⟧)).obj))
  /-- H^r comparisons obey composition with the specified coefficient associators. -/
  cohomology_comp : ∀ {E F G : I}
    (h : E ≤ F) (k : F ≤ G) (r : ℤ) (K : C E),
    (S.assoc h k).hom.app
        (((finite E).homology₀.obj (K⟦r⟧)).obj) ≫ (cohomology (h.trans k) r).hom.app K =
      (S.T k).map ((cohomology h r).hom.app K) ≫
        (cohomology k r).hom.app ((S.T h).obj K) ≫
          (shiftFunctor (C G) r ⋙
            (finite G).homology₀ ⋙ (finite G).heart.ι).map
              ((S.assoc h k).hom.app K)
  /-- Common-stage cohomology is naturally the included finite-stage cohomology. -/
  common_cohomology : ∀ (E : I) (r : ℤ),
    Nonempty ((S.ι E) ⋙
        shiftFunctor (S.PairCategory) r ⋙ common.homology₀ ⋙ common.heart.ι ≅
      (shiftFunctor (C E) r ⋙
        (finite E).homology₀ ⋙ (finite E).heart.ι) ⋙
          S.ι E)
  /-- Both heart witnesses can be realized at one enlargement of the original field. -/
  heart_enlargement : ∀ Z : S.PairCategory, common.heart Z →
    ∃ (N : I) (h : Z.stage ≤ N),
      (finite N).heart (Z.toStage h) ∧
        Nonempty (Z ≅ (S.ι N).obj
          (((finite N).homology₀.obj (Z.toStage h)).obj))


end CategoryTheory.StageSystem

namespace AlgebraicGeometry.Scheme

/-- Finite scalar extension is t-exact, and normalized truncations, cohomology and
truncation triangles descend to the common-stage pair category, with its bounded
standard t-structure and finite-enlargement description of the heart.

Source: Bhatt--Scholze, Propositions 6.8.11(3) and 6.8.14;
BBD, Proposition 1.3.3 and §1.3.16
(blueprint: lem-per-adic-common-stage-truncations).

The initial existentials supply the geometric consequences of finite type over k;
they are conclusions, not additional hypotheses. The final equations identify the
finite structures with the recorded localized standard structures by their two halves.
The record packages all comparison equations on the actual PBC pair system, with no
choice of an arbitrary scalar functor or an independently specified triangulation.

Proof (the nine steps of the DAG node):

1. The spectrum of the field $k$ has a single point and a finite affine cover by a Noetherian
   ring. Apply [lem-cbc-compactification-geometry-fibre-bound] to $X\to\operatorname{Spec}k$: $X$
   is Noetherian and finite-dimensional, and $\ell$ remains a unit. Thus the integral and
   localized bounded t-structures [prop-weil-pbc-integral-tstructure,
   prop-weil-localized-tstructure] apply at every finite coefficient field. Write $Q_E$ for
   localization and $C_{L/E}$ for integral change of completed coefficient rings. The
   construction of [prop-weil-pbc-scalar-extension] gives $T_{L/E}Q_E\cong Q_LC_{L/E}$; these are
   raw rationalizations throughout.

2. Put $R=B_{E,X}$ and $S=B_{L,X}$. By [lem-weil-finite-free-completed-scalar-comparison], $S$ is
   finite free as an $R$-module, and $C_{L/E}K=K\otimes_R^LS$ is already derived complete. Choose
   an $R$-basis of $S$, of size $d=[L:E]$, only for this calculation. For a K-flat resolution
   $P\to K$, restriction of $P\otimes_RS$ is the complex $P^{\oplus d}$, with componentwise
   differential. Kernels, images and quotients of this finite direct sum are the corresponding
   direct sums; hence $\mathcal H^i(P\otimes_RS)$, after restriction, is $\mathcal H^i(K)^{\oplus
   d}$. Restriction forgets scalar action and detects zero sheaves. Consequently $C_{L/E}$
   preserves both ambient cohomological bounds. It preserves the constructible subcategories with
   their compatible etale-origin witnesses by
   [lem-weil-pbc-finite-free-constructible-scalar-transport]. By
   [prop-weil-pbc-integral-tstructure] it therefore preserves both integral halves. No levelwise
   truncation or Tor-compatibility assertion is used.

3. Every object of a rational half is isomorphic to $Q_EK$ for an integral object $K$ in that
   half [prop-weil-localized-tstructure]. Apply step 2 and $T_{L/E}Q_E\cong Q_LC_{L/E}$
   [prop-weil-pbc-scalar-extension]. Its image lies in the same rational half; shifts give this
   for every cutoff. This proves t-exactness, rather than merely exactness as a triangulated
   functor. Apply [lem-pod-texact-truncation-comparison] to obtain
   $c^-_{L/E,r}:T_{L/E}\tau_E^{\le r}\cong\tau_L^{\le r}T_{L/E}$ and
   $c^+_{L/E,r}:T_{L/E}\tau_E^{\ge r}\cong\tau_L^{\ge r}T_{L/E}$, characterized respectively by
   $\iota c^-=T(\iota)$ and $c^+T(\pi)=\pi$. This also gives their naturality in $K$.

4. For $E\subset L\subset M$, let $a:T_{M/L}T_{L/E}\cong T_{M/E}$ be the specified associator.
   The natural-transformation and composition clauses of [lem-pod-texact-truncation-comparison]
   give, for either truncation $\tau$, $$c_{M/E,K}\,a_{\tau
   K}=\tau(a_K)\,c_{M/L,T_{L/E}K}\,T_{M/L}(c_{L/E,K}).$$ The identity comparison is the identity
   since $T_{E/E}=\operatorname{id}$. These equations use exactly the associator of
   [prop-weil-pbc-scalar-extension]. Define the cohomology comparison by composing the upper and
   lower comparisons for $(\tau^{\ge r}\tau^{\le r}K)[r]$, followed by the iterated scalar shift
   comparison. This is the degree-zero cohomology object $\mathcal H^rK$ (the ambient sheaf when
   an integral representative is used) [def-weil-derived-cohomology-sheaves,
   prop-weil-localized-tstructure]. Substitution of the displayed equations and the
   associator/shift equations gives the identical identity and composition equations for
   $\mathcal H^r$.

5. The comparisons identify the complete truncation triangles, including the third arrow. Indeed,
   apply $T_{L/E}$ to the finite-stage triangle at cutoff $r$, using its specified shift
   comparison [prop-weil-pbc-scalar-extension]. Its first term has bound $\le r$ and its third
   term bound $\ge r+1$. The comparison equations in step 3 commute with the first two arrows to
   the standard truncation triangle of $T_{L/E}K$. For the first term $A$ of the source triangle
   and third term $B'$ of the target, $A[1]$ has bound $\le r-1$, so
   $\operatorname{Hom}(A[1],B')=0$ by [def-weil-t-structure]. Clause (2) of
   [lem-weil-pbc-triangle-morphism-extension] now says that these prescribed first and third
   components, with middle component the identity, form a morphism of triangles: the boundary
   square commutes as well. The same uniqueness applies to cutoff-map diagrams; their
   finite-stage equations follow from the characterizing truncation maps, and remain valid under
   scalar extension.

6. In the pair category [def-weil-pbc-finite-stage-pair-category], set the halves at cutoff $r$
   to be the isomorphism closures of $(E,K)$ with $K\in D_E^{\le r}$ or $D_E^{\ge r}$,
   respectively. These classes have the required shift inclusions by their finite-stage
   counterparts and the pair shift [prop-weil-pbc-common-stage-calculus]. For orthogonality
   choose presentations of an upper object and a lower object with cutoffs $r$ and $r+1$. After
   conjugating by their chosen isomorphisms, any map is $[M,u]$ between their scalar extensions.
   Step 3 places its endpoints in the corresponding halves at $M$, so $u=0$ by finite-stage
   orthogonality [def-weil-t-structure, prop-weil-localized-tstructure]. Thus the original map is
   zero. Each $(E,K)$ has the image of its finite-stage truncation triangle, distinguished
   because $j_E$ is exact [thm-weil-pbc-verdier-axioms]. This supplies the triangle axiom. The
   two finite-stage bounds of $K$ give two bounds of $(E,K)$, proving boundedness. Thus these
   halves form the asserted bounded t-structure.

7. Here is the actual descent formula; it does not apply an exact-functor descent assertion to
   truncation, which is generally not triangulated-exact. For either truncation put
   $\tau(E,K)=(E,\tau_EK)$. For $f=[M,u]:(E,K)\to(F,L)$ define
   $$\tau(f)=[M,c_{M/F,L}^{-1}\,\tau_M(u)\,c_{M/E,K}].$$ If $M\subset N$, the associator equation
   of step 4 and naturality of $c_{N/M}$ show that transporting the displayed representative to
   $N$ gives exactly
   $$c_{N/F,L}^{-1}\,\tau_N(a_{N,M,F,L}\,T_{N/M}(u)\,a_{N,M,E,K}^{-1})\,c_{N/E,K}.$$ The
   expression inside $\tau_N$ is $u_N$ by the pair-category definition. Thus two equivalent
   representatives give equivalent images. For composition, put both arrows at one stage
   [prop-weil-pbc-common-stage-calculus]; the adjacent factors $c_{M/F,L}$ and $c_{M/F,L}^{-1}$
   cancel, and $\tau_M(vu)=\tau_M(v)\tau_M(u)$. The identity formula follows from $c_{E/E}=1$.
   These calculations prove that both truncations are functors with the stated arrow formulas.

8. Represent the upper counit on $(E,K)$ by $[E,\iota_{E,K}]$ and the lower unit by
   $[E,\pi_{E,K}]$. Their naturality for $[M,u]$ follows by substituting step 7 and the two
   characterizing equations of step 3. All equations between truncation maps are checked at a
   common finite stage using [prop-weil-pbc-common-stage-calculus], where they are the ordinary
   finite-stage equations [prop-weil-localized-tstructure, def-weil-t-structure]. Step 5 handles
   the shifted third arrow of the distinguished truncation triangles, and
   [thm-weil-pbc-verdier-axioms] sends each such finite-stage triangle to a distinguished
   pair-category triangle. These are truncation triangles for the halves proved in step 6. Their
   uniqueness follows from [lem-weil-pbc-triangle-morphism-extension](2), since the same
   upper/lower orthogonality gives its vanishing hypothesis in the pair category. Consequently
   the constructed functors are the canonical truncations of that t-structure, including all
   their canonical maps. Applying their composition and the pair shift gives naturally $\mathcal
   H^r(E,K)\cong(E,\mathcal H_E^rK)$.

9. It remains to identify the heart; the witnesses for its two halves need not initially be at
   the same stage. Let $Z=(E,K)$ lie in both halves. Choose isomorphisms from $Z$ to a pair
   $(F,A)$ in the upper half and to a pair $(G,B)$ in the lower half. Include their inverses and
   both inverse equations in one finite diagram. By [prop-weil-pbc-common-stage-calculus] there
   is a finite $N\supset E,F,G$ where these are actual isomorphisms, so $T_{N/E}K\cong T_{N/F}A$
   and $T_{N/E}K\cong T_{N/G}B$. Step 3 places the right-hand sides in the upper and lower
   finite-stage halves respectively. Hence $T_{N/E}K$ belongs to the finite-stage heart. Its two
   degree-zero truncation maps are isomorphisms, giving $T_{N/E}K\cong\mathcal H_N^0(T_{N/E}K)$
   [def-weil-t-structure, prop-weil-localized-tstructure]. The canonical identification
   $j_NT_{N/E}\cong j_E$ [thm-weil-pbc-verdier-axioms] now proves the required isomorphism for
   $Z$ after this one finite enlargement. Conversely every finite-stage heart object belongs to
   both pair halves. Therefore the pair heart is exactly the isomorphism closure of finite-stage
   hearts. No reflection of bounds by scalar extension or faithfulness of $j_E$ was assumed.
-/
theorem perAdicCommonStageTruncations
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))] (_hl : IsUnit (l : k)) :
    ∃ _hNoetherian : IsNoetherian X,
    ∃ hDim : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞)),
    ∃ hInv : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x)),
    ∃ d : (pbcScalarSystem l Ω X hDim.out hInv.out).AdicCommonStageTruncations,
      d.common = pbcQbarStandardT l Ω X ∧
      (∀ (E : Padic.FiniteCoefficientFields l Ω) (n : ℤ)
        (K : pbcStageCategory l Ω X E),
        (d.finite E).le n K ↔ ∃ M : pbcIntegralStage l Ω X E,
          (pbcIntegralTStructure X l (pbcFiniteField.{u} l Ω E)).le n M ∧
            Nonempty (K ≅ (pbcStageLocalization l Ω X E).obj M)) ∧
      (∀ (E : Padic.FiniteCoefficientFields l Ω) (n : ℤ)
        (K : pbcStageCategory l Ω X E),
        (d.finite E).ge n K ↔ ∃ M : pbcIntegralStage l Ω X E,
          (pbcIntegralTStructure X l (pbcFiniteField.{u} l Ω E)).ge n M ∧
            Nonempty (K ≅ (pbcStageLocalization l Ω X E).obj M)) := by
  sorry

end AlgebraicGeometry.Scheme
