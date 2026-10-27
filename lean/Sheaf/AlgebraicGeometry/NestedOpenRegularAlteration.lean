/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
import Sheaf.AlgebraicGeometry.CoverNestedCartierPreparation
import Sheaf.AlgebraicGeometry.AlterationCartierSubboundary
import Sheaf.AlgebraicGeometry.Morphisms.GenericRadicialEtaleFactorization
import WeilConjectures.Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Regular alterations adapted to nested opens

Source: ILO, Travaux de Gabber, Exposé X, Theorem 2.1, printed p.149,
with normalization, two boundary blowups and generic finite-algebra spreading
(blueprint: lem-sfb-nested-open-regular-alteration).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

private theorem generic_eq {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) [IsDominant f] : f (genericPoint X) = genericPoint Z := by
  apply ((genericPoint_spec Z).eq _).symm
  have h := (genericPoint_spec X).image f.continuous
  simpa only [Set.image_univ, f.denseRange.closure_range] using h

private theorem generic_map_spec {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) (hf : f (genericPoint X) = genericPoint Z) :
    Spec.map (f.functionFieldMap hf) ≫ Z.fromSpecFunctionField =
      X.fromSpecFunctionField ≫ f := by
  dsimp only [Scheme.Hom.functionFieldMap]
  rw [Spec.map_comp, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk f

private theorem finite_generic_of_spectrum {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (f : X ⟶ Z) [IsDominant f] (v : Spec X.functionField ⟶ Spec Z.functionField)
    [IsFinite v] (hv : v ≫ Z.fromSpecFunctionField = X.fromSpecFunctionField ≫ f) :
    (f.functionFieldMap (generic_eq f)).hom.Finite := by
  have he : Spec.map (f.functionFieldMap (generic_eq f)) = v := by
    apply (cancel_mono Z.fromSpecFunctionField).mp
    rw [generic_map_spec, hv]
  apply (IsFinite.SpecMap_iff _).mp
  rw [he]
  infer_instance

private theorem generic_map_comp {X Y Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsDominant f] [IsDominant g] :
    (f ≫ g).functionFieldMap (generic_eq (f ≫ g)) =
      g.functionFieldMap (generic_eq g) ≫ f.functionFieldMap (generic_eq f) := by
  apply Spec.map_injective
  apply (cancel_mono Z.fromSpecFunctionField).mp
  rw [generic_map_spec, Spec.map_comp, Category.assoc, generic_map_spec]
  exact (congrArg (fun v ↦ v ≫ g) (generic_map_spec f (generic_eq f)).symm).trans
    (Category.assoc _ _ _)

private theorem generic_map_congr {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (f g : X ⟶ Z) (hf : f (genericPoint X) = genericPoint Z)
    (hg : g (genericPoint X) = genericPoint Z) (he : f = g) :
    f.functionFieldMap hf = g.functionFieldMap hg := by
  subst g
  rfl

private theorem finite_generic_comp {X Y Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsDominant f] [IsDominant g]
    (hf : (f.functionFieldMap (generic_eq f)).hom.Finite)
    (hg : (g.functionFieldMap (generic_eq g)).hom.Finite) :
    ((f ≫ g).functionFieldMap (generic_eq (f ≫ g))).hom.Finite := by
  have : IsFinite (Spec.map (f.functionFieldMap (generic_eq f))) :=
    (IsFinite.SpecMap_iff _).mpr hf
  have : IsFinite (Spec.map (g.functionFieldMap (generic_eq g))) :=
    (IsFinite.SpecMap_iff _).mpr hg
  apply finite_generic_of_spectrum (f ≫ g)
    (Spec.map (f.functionFieldMap (generic_eq f)) ≫
      Spec.map (g.functionFieldMap (generic_eq g)))
  rw [Category.assoc, generic_map_spec, ← Category.assoc, generic_map_spec,
    Category.assoc]

private theorem closeds_iSup_coe {X : Type u} [TopologicalSpace X]
    {n : ℕ} (C : Fin n → Closeds X) :
    ((⨆ i, C i : Closeds X) : Set X) = ⋃ i, (C i : Set X) := by
  rw [← Finset.sup_univ_eq_iSup, Closeds.coe_finset_sup]
  simp

private theorem finite_component_equiv {X : Type u} [TopologicalSpace X]
    (n : ℕ) (Z : Fin n → Set X) (hc : ∀ i, IsClosed (Z i))
    (hi : ∀ i, IsIrreducible (Z i))
    (ha : ∀ i j, Z i ⊆ Z j → i = j) (hcover : ⋃ i, Z i = Set.univ) :
    ∃ e : Fin n ≃ {S : Set X // S ∈ irreducibleComponents X},
      ∀ i, (e i).val = Z i := by
  classical
  have hsub (S : Set X) (hS : IsIrreducible S) : ∃ i, S ⊆ Z i := by
    obtain ⟨z, hz, hSz⟩ := isIrreducible_iff_sUnion_isClosed.mp hS
      (Finset.univ.image Z) (by simpa using hc)
      (by simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ,
        Set.sUnion_range, hcover] using Set.subset_univ S)
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨i, hSz⟩
  have hmem (i) : Z i ∈ irreducibleComponents X := by
    refine ⟨hi i, fun S hS hZS ↦ ?_⟩
    obtain ⟨j, hj⟩ := hsub S hS
    have hij := ha i j (hZS.trans hj)
    exact hij ▸ hj
  let f : Fin n → {S : Set X // S ∈ irreducibleComponents X} :=
    fun i ↦ ⟨Z i, hmem i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact ha i j (congrArg Subtype.val hij).le
    · intro S
      obtain ⟨i, hiS⟩ := hsub S.val S.property.1
      exact ⟨i, Subtype.ext ((S.property.2 (hi i) hiS).antisymm hiS)⟩
  exact ⟨Equiv.ofBijective f hf, fun _ ↦ rfl⟩

private theorem snc_component_equiv {Y : Scheme.{u}} [IsIntegral Y]
    (D : Y.IdealSheafData) (n : ℕ) (C : Fin n → Y.IdealSheafData)
    (hCinj : Function.Injective (fun i ↦ (C i).support))
    (hC : ∀ i, IsIntegral (C i).subscheme)
    (hCsupp : D.support = ⨆ i, (C i).support)
    (hCdim : ∀ i, ∀ z : (C i).subscheme,
      ringKrullDim (Y.presheaf.stalk ((C i).subschemeι z)) =
        ringKrullDim ((C i).subscheme.presheaf.stalk z) + 1) :
    ∃ e : Fin n ≃ {Z : Set (D.support : Set Y) //
        Z ∈ irreducibleComponents (D.support : Set Y)},
      ∀ i, Subtype.val '' (e i).val = ((C i).support : Set Y) := by
  classical
  let Z : Fin n → Set (D.support : Set Y) :=
    fun i ↦ Subtype.val ⁻¹' ((C i).support : Set Y)
  have hle (i) : (C i).support ≤ D.support := by
    rw [hCsupp]
    exact le_iSup (fun j ↦ (C j).support) i
  have hZimage (i) : Subtype.val '' Z i = ((C i).support : Set Y) := by
    ext y
    exact ⟨fun ⟨z, hz, hzy⟩ ↦ hzy ▸ hz, fun hy ↦ ⟨⟨y, hle i hy⟩, hy, rfl⟩⟩
  have hirr (i) : IsIrreducible (Z i) := by
    have := hC i
    let f : (C i).subscheme → (D.support : Set Y) :=
      fun z ↦ ⟨(C i).subschemeι z, hle i (by
        exact Set.mem_of_mem_of_subset (Set.mem_range_self z)
          (show Set.range (C i).subschemeι ⊆ (C i).support from
            (C i).range_subschemeι.le))⟩
    have hf : Continuous f := (C i).subschemeι.continuous.subtype_mk _
    have he : f '' Set.univ = Z i := by
      ext y
      constructor
      · rintro ⟨z, _, rfl⟩
        change (C i).subschemeι z ∈ (C i).support
        exact Set.mem_of_mem_of_subset (Set.mem_range_self z)
          (show Set.range (C i).subschemeι ⊆ (C i).support from
            (C i).range_subschemeι.le)
      · intro hy
        have hy' : y.val ∈ ((C i).support : Set Y) := hy
        have hyr : y.val ∈ Set.range (C i).subschemeι :=
          (C i).range_subschemeι.symm ▸ hy'
        obtain ⟨z, hz⟩ := hyr
        exact ⟨z, trivial, Subtype.ext hz⟩
    rw [← he]
    exact (IrreducibleSpace.isIrreducible_univ _).image f hf.continuousOn
  let ξ := fun i ↦ (C i).subschemeι
    (letI := hC i; genericPoint (C i).subscheme)
  have hgen (i) : IsGenericPoint (ξ i) ((C i).support : Set Y) := by
    have := hC i
    have h := (genericPoint_spec (C i).subscheme).image (C i).subschemeι.continuous
    simpa only [Set.image_univ, (C i).range_subschemeι,
      (C i).support.isClosed.closure_eq] using h
  have hdim (i) : Order.coheight (ξ i) = 1 := by
    have := hC i
    have hh := hCdim i (genericPoint (C i).subscheme)
    rw [ringKrullDim_eq_zero_of_field, zero_add, ringKrullDim_stalk_eq_coheight] at hh
    exact_mod_cast hh
  have hanti (i j) (hij : Z i ⊆ Z j) : i = j := by
    have hij' : ((C i).support : Set Y) ⊆ (C j).support := by
      rw [← hZimage i, ← hZimage j]; exact Set.image_mono hij
    have hs : ξ j ⤳ ξ i := (hgen j).specializes (hij' (hgen i).mem)
    have he : ξ i = ξ j := by
      by_contra hn
      have ht : ξ i < ξ j := lt_iff_le_not_ge.mpr ⟨hs, fun hji ↦
        hn (Specializes.antisymm (show ξ i ⤳ ξ j from hji) hs).eq⟩
      have hh := Order.coheight_strictAnti ht (by rw [hdim j]; norm_num)
      rw [hdim i, hdim j] at hh
      exact lt_irrefl _ hh
    apply hCinj
    apply SetLike.coe_injective
    change ((C i).support : Set Y) = ((C j).support : Set Y)
    rw [← (show closure {ξ i} = ((C i).support : Set Y) from hgen i),
      ← (show closure {ξ j} = ((C j).support : Set Y) from hgen j), he]
  have hcover : ⋃ i, Z i = Set.univ := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have he : (D.support : Set Y) = ⋃ i, ((C i).support : Set Y) :=
      (congrArg (fun K : Closeds Y ↦ (K : Set Y)) hCsupp).trans (closeds_iSup_coe _)
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      ((congrArg (fun U : Set Y ↦ y.val ∈ U) he).mp y.property)
    exact ⟨i, hi⟩
  obtain ⟨e, he⟩ := finite_component_equiv n Z
    (fun i ↦ (C i).support.isClosed.preimage continuous_subtype_val) hirr hanti hcover
  exact ⟨e, fun i ↦ by rw [he i]; exact hZimage i⟩

/-- A regular alteration adapted to two nested dense opens and a prescribed finite étale cover.
The finite family is indexed by `Fin n` and enumerates exactly the irreducible components
of the reduced boundary. The generic field map is the canonical map on generic stalks.
The final shrinking is independent of the normal crossings assertion.
Source: ILO, Exposé X, Theorem 2.1, printed p.149, and the normalization, blowup and
finite-algebra arguments in the DAG (blueprint: lem-sfb-nested-open-regular-alteration).

Proof plan:
1. Put $K=k(T)$. Choose a point of the nonempty finite etale generic fibre $H_K$ and let $F$ be
its residue field; $F/K$ is finite. Let $q:X\to T$ be the normalization of $T$ in $F$. By the
normalization-in-a-residue-field node, $X$ is normal integral with function field $F$; by
finiteness of normalization over a field, $q$ is finite. It is proper by finite-proper, and its
image is closed and contains the generic point, hence it is surjective. Over an affine open of
$S$, the integral-closure description of normalization is unchanged on localization. Thus $X_S$ is
the normalization of $S$ in $\operatorname{Spec}F$. Apply the relative-normalization universal
property to $\operatorname{Spec}F\to H\to S$, whose second arrow is integral: this supplies
$X_S\to H$ over $S$. This argument uses a field factor of $H_K$, not an unsupported assertion that
connected $H$ is integral.
   Uses: def-weil-finite-integral-morphism, lem-weil-pbc-normalization-in-residue-field-extension,
def-fin-normalization-extension, lem-fin-normalization-extension-finite,
lem-weil-pbc-finite-proper, lem-weil-pbc-proper-closed-image,
lem-sbc-relative-normalization-universal-property.
2. The scheme $X$ is separated finite type over $k$, hence Noetherian. Set $U=q^{-1}S\subseteq
U^\circ=q^{-1}T^\circ$; both are dense quasi-compact opens. Choose finite-type quasi-coherent
ideals $\mathcal I,\mathcal J$ with $V(\mathcal I)=X\setminus U$, $V(\mathcal J)=X\setminus
U^\circ$. Let $b_1:B_1=\operatorname{Bl}_{\mathcal I}(X)\to X$, $b_2:B=\operatorname{Bl}_{\mathcal
J\mathcal O_{B_1}}(B_1)\to B_1$, $b=b_1b_2$. As $\mathcal J|_U=\mathcal O_U$, $b_2$ is a
$b_1^{-1}(U)$-admissible blowup. The boundary-divisor lemma, with its clause on a further
admissible blowup, makes $I_B=\mathcal I\mathcal O_B$ effective Cartier with support $B\setminus
b^{-1}U$ and $b^{-1}U$ scheme-theoretically dense in $B$; the Cartier-total-transform lemma gives
the same Cartier property. Applied to $B_1$, $b_1^{-1}U^\circ$ and $\mathcal J\mathcal O_{B_1}$,
it makes $J_B=\mathcal J\mathcal O_B$ effective Cartier with support $B\setminus b^{-1}U^\circ$.
The blowup-complement theorem makes $b_1$ an isomorphism over $U$ and $b_2$ one over $B_1\setminus
V(\mathcal J\mathcal O_{B_1})\supseteq b_1^{-1}U$, so $b^{-1}U\to U$ is an isomorphism and
$b^{-1}U$ is integral with function field $F$. Hence $B$ is integral: it is nonempty, and for a
nonempty affine open $V\subseteq B$ density makes $\mathcal O_B(V)\to\mathcal O_B(V\cap b^{-1}U)$
injective, so $V\cap b^{-1}U\neq\varnothing$; sections of the integral $b^{-1}U$ over a nonempty
open inject into $F$, because they do on each nonempty affine of a cover (affine-fraction lemma),
so $\mathcal O_B(V)$ is a domain. Thus $k(B)=F$ and $b$ is dominant. Blowup properness and proper
composition make $b$ proper. Empty complements give unit ideals and identity blowups.
   Uses: lem-weil-pbc-finite-type-over-noetherian, lemma-nagata-qc-open-complement-ideal-exists,
def-nagata-admissible-blowup, det-nagata-boundary-divisor-cartier,
def-nagata-scheme-theoretically-dense-open, lemma-nagata-cartier-total-transform-blowup,
thm-nagata-global-blowup-complement, def-pc-integral-scheme,
lem-sc-integral-function-field-affine-fraction, lemma-nagata-blowup-proper,
lem-weil-pbc-proper-composition.
3. Choose a prime $\ell\ne p$ and apply the global Gabber theorem to $B$ and $Z=B\setminus
b^{-1}U$. It gives $a:P\to B$ with $P$ smooth over a finite extension $k'/k$ and reduced inverse-
image boundary relative strict normal crossings. Smooth-over-a-field regularity makes $P$ regular.
The regular-normal-components node decomposes this Noetherian scheme into finitely many open-and-
closed integral components. Choose one component $Y$; by the maximal-domination clause of Gabber's
theorem its generic point maps to the generic point of $B$. Restrict $a$ and its boundary to $Y$.
This remains proper (restriction to an open-and-closed component is a closed inclusion followed by
$a$), dominant and generically finite. The restricted boundary $D=\bigcup_{a\in A}D_a$ has
finitely many components and is strict normal crossings; it is regular in the sense of the
regular-scheme boundary definition [def-trf-strict-normal-crossings-boundary] because all the
relative intersections are smooth over $k'$. Set $h=qba|_Y$. By proper composition $h$ is proper.
It is dominant, and $k(Y)/k(T)$ is finite, since $k(Y)/F$ and $F/K$ are finite. All schemes used
are separated finite type over $k$.
   Uses: lem-sfb-gabber-global-snc-alteration, lem-weil-pbc-smooth-scheme-over-field-regular,
rem-pc-regular-normal, lem-weil-pbc-proper-composition, def-weil-proper-morphism,
def-trf-strict-normal-crossings-boundary.
4. Pull back $I_B,J_B$ to $Y$. Both extended ideals are still effective Cartier: a local generator
is nonzero in the function field of $B$, hence remains nonzero in $k(Y)$ by dominance, and every
local ring of $Y$ is a domain. Their supports are $Y\setminus h^{-1}S$ and $Y\setminus
h^{-1}T^\circ$; the first is exactly $|D|$. To check that the second is a union of whole
components, work locally at $y\in Y$. The Gabber boundary has parameter equations $t_1,\ldots,t_r$
there. A generator $f$ of the second ideal becomes a unit off $D$, because its zero set is
contained in $|D|$. In $\mathcal O_{Y,y}[1/(t_1\cdots t_r)]$ it is therefore a unit. The regular-
local-UFD boundary-factorization node gives $f=v\prod t_i^{n_i}$ with $v$ a unit and $n_i\ge0$.
Consequently its support is locally a union of the branches of $D$. At every point of this support
at least one branch through the point is selected, and its generic point also lies in the support.
Since the support is closed, it contains that whole $D_a$. Conversely every selected component
lies in the support. Thus, with $A_{\rm out}$ the components whose generic points lie in it, the
support is $\bigcup_{a\in A_{\rm out}}D_a$. This proves both required open identities without
asserting normal crossings for any later shrinking.
   Uses: lem-trf-regular-local-ufd-boundary-factorization, lem-sfb-gabber-global-snc-alteration,
def-nagata-effective-cartier-ideal.
5. Put $W=h^{-1}S$. The morphism $r:W\to S$ is proper by base change. It is surjective: the proper
image of $h$ is closed and contains the generic point of integral $T$, hence is all of $T$, so its
restriction over $S$ is onto. The composite $W\to X_S\to H$ from step 1 factors $r$ through $c$.
The open $W$ is nonempty integral. The affine-fraction-field lemma identifies every nonempty
affine chart of the generic fibre with a finitely generated $K$-subalgebra of $L=k(Y)$. Its
generators are algebraic over $K$, so it is a finite-dimensional domain, hence a field,
necessarily $L$. These charts all contain the generic point; consequently the whole generic fibre
is $\operatorname{Spec}L$. Apply the generic-finiteness lemma to obtain a nonempty affine open
$\operatorname{Spec}A\subseteq S$ on which $r$ is finite. Write its inverse image as
$\operatorname{Spec}E$, with $E$ a finite $A$-algebra domain and $E\otimes_AK=L$.
   Uses: lem-weil-pbc-proper-base-change, lem-weil-pbc-proper-closed-image,
def-weil-finite-integral-morphism, def-sc-function-field,
lem-sc-integral-function-field-affine-fraction,
lem-weil-pbc-generic-finite-morphism-open-neighborhood.
6. Let $K'\subseteq L$ be the separable closure of $K$ in $L$. The separable-first lemma gives
$K'/K$ finite separable and $L/K'$ finite purely inseparable. Choose a primitive element
$\alpha\in K'$ and write its monic separable minimal polynomial as $g\in K[T]$. Apply the
localized separable-polynomial model lemma and replace $A$ by the resulting nonzero principal
localization, so $g\in A[T]$ and $g$ is coprime to $g'$. Put $A'=A[T]/(g)$. Division by the monic
polynomial shows that $1,T,\ldots,T^{d-1}$ is an $A$-basis, where $d=\deg g=[K':K]\ge1$, and the
map $A'\to K'$ sending $T$ to $\alpha$ is injective: a representative of degree less than $d$
which vanishes at $\alpha$ is zero over $K$, hence over the domain $A$. Thus $A'$ is a domain with
fraction field $K'$. The Bezout relation makes $g'$ a unit in $A'$, so the standard-etale monic-
derivative lemma says $\operatorname{Spec}A'\to\operatorname{Spec}A$ is etale. Its displayed free
basis makes it finite and surjective of constant degree $d$.
   Uses: lem-weil-pbc-separable-first-purely-inseparable,
lem-weil-pbc-finite-separable-extension-primitive-element,
lem-weil-pbc-localized-separable-polynomial-model, lem-weil-pbc-standard-etale-monic-derivative.
7. As $E\otimes_AK=L$, write $\alpha=z/s$ with $z\in E$ and $0\ne s\in A$. After replacing $A$ by
$A[1/s]$ and $E,A'$ by their corresponding base localizations, $\alpha\in E$, and evaluation
defines an injective $A$-algebra map $A'\hookrightarrow E$ compatible with the embeddings in $L$.
The finite $A$-module generators of $E$ also generate $E$ as an $A'$-module: their $A'$-span
contains their $A$-span, which is already all of $E$. Hence $E$ is finite over $A'$. Apply the
spreading-purely-inseparable-factors lemma to the Noetherian domain $A$, the finite etale domain
$A'$, and the finite domain $E$, with fraction fields $K,K',L$. It gives a further nonzero base
localization on which $\operatorname{Spec}E\to\operatorname{Spec}A'$ is surjective radicial and a
universal homeomorphism; it is finite by the preceding module argument. Let $S_0$ be this final
principal open in $S$, $T_0=\operatorname{Spec}A'$ over it, and $W_0=\operatorname{Spec}E$. The
maps $u:W_0\to T_0$ and $e:T_0\to S_0$ have all the asserted properties. The rank-$d$ free
polynomial basis persists under each localization. All localizations are by nonzero elements, so
$S_0$ remains nonempty dense.
   Uses: lem-weil-pbc-spread-purely-inseparable-factors, def-weil-finite-integral-morphism.
-/
theorem exists_nestedOpen_regular_alteration
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p)
    (T : Scheme.{u}) [T.Over (Spec (.of k))] [IsIntegral T]
    [IsSeparated (T ↘ Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))]
    (S Tcirc : T.Opens) (hST : S ≤ Tcirc)
    (hS : Dense (S : Set T)) (hTcirc : Dense (Tcirc : Set T))
    (H : Scheme.{u}) [ConnectedSpace H] (c : H ⟶ S.toScheme)
    [IsFinite c] [Etale c] [Surjective c] :
    ∃ (Y : Over (Spec (.of k))) (_ : IsIntegral Y.left),
      IsRegularScheme Y.left ∧ IsSeparated Y.hom ∧
      LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom ∧
      ∃ (h : Y.left ⟶ T) (_ : IsProper h) (_ : IsDominant h),
        h ≫ (T ↘ Spec (.of k)) = Y.hom ∧
        (∃ hη : h (genericPoint Y.left) = genericPoint T,
          (T.presheaf.stalkSpecializes (specializes_of_eq hη) ≫
            h.stalkMap (genericPoint Y.left)).hom.Finite) ∧
        ∃ (D : Y.left.IdealSheafData), IsStrictNormalCrossingsBoundary D ∧
          ∃ (n : ℕ)
            (C : Fin n ≃ {Z : Set (D.support : Set Y.left) //
              Z ∈ irreducibleComponents (D.support : Set Y.left)})
            (Aout : Finset (Fin n)),
            (h ⁻¹ᵁ S : Set Y.left) = (D.support : Set Y.left)ᶜ ∧
            (h ⁻¹ᵁ Tcirc : Set Y.left) =
              (⋃ a ∈ Aout, Subtype.val '' (C a).val)ᶜ ∧
            IsProper (h ∣_ S) ∧ Surjective (h ∣_ S) ∧
            (∃ b : (h ⁻¹ᵁ S).toScheme ⟶ H, b ≫ c = h ∣_ S) ∧
            ∃ S0 : S.toScheme.Opens,
              Nonempty S0 ∧ Dense (S0 : Set S.toScheme) ∧
              IsFinite (pullback.snd (h ∣_ S) S0.ι) ∧
              ∃ (T0 : Scheme.{u}) (u : pullback (h ∣_ S) S0.ι ⟶ T0)
                (e : T0 ⟶ S0.toScheme) (d : ℕ),
                u ≫ e = pullback.snd (h ∣_ S) S0.ι ∧
                IsFinite u ∧ (topologically IsHomeomorph).universally u ∧
                IsFinite e ∧ Etale e ∧ Surjective e ∧ 1 ≤ d ∧
                ∀ s : S0.toScheme, e.finrank s = d := by
  classical
  have _ := hp
  have hSne : Nonempty S := ⟨hS.nonempty.some, hS.nonempty.some_mem⟩
  let η := S.fromSpecStalkOfMem (genericPoint T)
    (((genericPoint_spec T).mem_open_set_iff S.isOpen).mpr
      (by simpa using hS.nonempty))
  have hη : η ≫ S.ι = T.fromSpecFunctionField := S.fromSpecStalkOfMem_ι _ _
  have : Nonempty (pullback c η : Scheme.{u}) := by
    obtain ⟨x, _⟩ := (pullback.snd c η).surjective
      (IsLocalRing.closedPoint T.functionField)
    exact ⟨x⟩
  let x : (pullback c η : Scheme.{u}) := Classical.choice inferInstance
  obtain ⟨hF, hX, _, _, _, _, hq, _, eX, heX, B, hB, b,
    hBsep, hBft, hBqc, hb, hbdom, eB, _, _, ⟨I, J, hI, hJ, hIs, hJs⟩,
    hg, hgdom, lift, hlift⟩ :=
    exists_cover_nested_cartier_preparation T (T ↘ Spec (.of k))
      S Tcirc hST hS hTcirc H c η hη x
  let F := (pullback c η).residueField x
  let q := T.fromNormalizationIn F
  let g := b ≫ q
  have : IsIntegral B := hB
  have : IsProper g := hg
  have : IsDominant g := hgdom
  have : IsSeparated (g ≫ (T ↘ Spec (.of k))) := hBsep
  have : LocallyOfFiniteType (g ≫ (T ↘ Spec (.of k))) := hBft
  have : QuasiCompact (g ≫ (T ↘ Spec (.of k))) := hBqc
  have : IsIntegral (T.normalizationIn F) := hX
  obtain ⟨eB, heB⟩ := eB
  let eF := eX ≪≫ eB
  have heF : eF.hom ≫ B.fromSpecFunctionField ≫ g =
      T.fromSpecOfAlgebraFunctionField F := by
    calc
      _ = eX.hom ≫ (eB.hom ≫ B.fromSpecFunctionField ≫ b) ≫ q := by
        simp only [eF, Iso.trans_hom, g, Category.assoc]
      _ = eX.hom ≫ (T.normalizationIn F).fromSpecFunctionField ≫ q := by
        rw [heB]
      _ = (T.fromSpecOfAlgebraFunctionField F).toNormalization ≫ q := by
        rw [← Category.assoc, heX]
      _ = _ := Scheme.Hom.toNormalization_fromNormalization _
  have : Module.Finite T.functionField F := hF
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap T.functionField F))) :=
    (IsFinite.SpecMap_iff _).mpr (by simpa using hF)
  have hgf : (g.functionFieldMap (generic_eq g)).hom.Finite := by
    apply finite_generic_of_spectrum g
      (eF.inv ≫ Spec.map (CommRingCat.ofHom (algebraMap T.functionField F)))
    change eF.inv ≫ T.fromSpecOfAlgebraFunctionField F = _
    rw [← heF, Iso.inv_hom_id_assoc]
  have hJI : J.support ≤ I.support := by
    change (J.support : Set B) ⊆ (I.support : Set B)
    rw [hJs, hIs]
    exact Set.compl_subset_compl.mpr (g.preimage_mono hST)
  obtain ⟨Y, a, hY, hadom, hYreg, hYsep, hYft, hYqc, ha, haf,
    D, n, C, Aout, hD, hCinj, hCreg, hCsupp, hCint, _, _, _, _, hDS, hDT⟩ :=
    exists_alteration_cartier_subboundary k B (g ≫ (T ↘ Spec (.of k))) I J hI hJ hJI
  have : IsIntegral Y := hY
  have : IsDominant a := hadom
  have : IsProper a := ha
  let h := a ≫ g
  have : IsProper h := inferInstance
  have : IsDominant h := inferInstance
  have haf' : (a.functionFieldMap (generic_eq a)).hom.Finite := haf
  have hhf := finite_generic_comp a g haf' hgf
  have : Surjective h :=
    surjective_of_isDominant_of_isClosed_range h h.isClosedMap.isClosed_range
  let W := h ⁻¹ᵁ S
  let r := h ∣_ S
  have hrsurj : Surjective r := by
    refine ⟨fun s ↦ ?_⟩
    obtain ⟨y, hy⟩ := h.surjective s.val
    refine ⟨⟨y, show h y ∈ S from hy.symm ▸ s.property⟩, ?_⟩
    apply Subtype.ext
    have he := congrArg (fun m : W.toScheme ⟶ T ↦
      m ⟨y, show h y ∈ S from hy.symm ▸ s.property⟩) (morphismRestrict_ι h S)
    exact he.trans hy
  have : Nonempty W.toScheme := by
    obtain ⟨y, _⟩ := r.surjective ⟨hS.nonempty.some, hS.nonempty.some_mem⟩
    exact ⟨y⟩
  have : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  have : IsIntegral S.toScheme := isIntegral_of_isOpenImmersion S.ι
  have : IsProper r := inferInstance
  have : IsDominant r := inferInstance
  have : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of k))
  have : IsLocallyNoetherian Y := hYreg.1
  have : QuasiCompact S.ι := inferInstance
  have : QuasiCompact W.ι := inferInstance
  have : IsSeparated (S.ι ≫ (T ↘ Spec (.of k))) := inferInstance
  have : LocallyOfFiniteType (S.ι ≫ (T ↘ Spec (.of k))) := inferInstance
  have : QuasiCompact (S.ι ≫ (T ↘ Spec (.of k))) := inferInstance
  have : IsSeparated (h ≫ (T ↘ Spec (.of k))) := by
    simpa only [h, Category.assoc] using hYsep
  have : LocallyOfFiniteType (h ≫ (T ↘ Spec (.of k))) := by
    simpa only [h, Category.assoc] using hYft
  have : QuasiCompact (h ≫ (T ↘ Spec (.of k))) := by
    simpa only [h, Category.assoc] using hYqc
  have : IsSeparated (W.ι ≫ h ≫ (T ↘ Spec (.of k))) := inferInstance
  have : LocallyOfFiniteType (W.ι ≫ h ≫ (T ↘ Spec (.of k))) := inferInstance
  have : QuasiCompact (W.ι ≫ h ≫ (T ↘ Spec (.of k))) := inferInstance
  have : IsDominant W.ι := Opens.isDominant_ι (W.isOpen.dense
    (by obtain ⟨y⟩ := ‹Nonempty W.toScheme›; exact ⟨y.val, y.property⟩))
  have : IsDominant S.ι := Opens.isDominant_ι hS
  have hirr : (W.ι.functionFieldMap (generic_eq W.ι)).hom.Finite := by
    have he : W.ι.functionFieldMap (generic_eq W.ι) = W.ι.functionFieldIso.hom := rfl
    rw [he]
    exact RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
  have hWf := finite_generic_comp W.ι h hirr hhf
  have hrfinite : (r.functionFieldMap (generic_eq r)).hom.Finite := by
    have he : W.ι ≫ h = r ≫ S.ι := (morphismRestrict_ι h S).symm
    have he' : (W.ι ≫ h).functionFieldMap (generic_eq (W.ι ≫ h)) =
        (r ≫ S.ι).functionFieldMap (generic_eq (r ≫ S.ι)) :=
      generic_map_congr _ _ _ _ he
    rw [he', generic_map_comp, CommRingCat.hom_comp] at hWf
    exact hWf.of_comp_finite
  obtain ⟨_, S0, hS0, hS0dense, _, hS0finite, _, T0, _, u0, e, hue,
    hu0, huhomeo, hefinite, heetale, hesum, _⟩ :=
    Scheme.Hom.exists_generic_radicial_etale_factorization k
      (W.ι ≫ h ≫ (T ↘ Spec (.of k))) (S.ι ≫ (T ↘ Spec (.of k)))
      r (by
        dsimp only [r, W]
        exact morphismRestrict_ι_assoc h S (T ↘ Spec (.of k))) hrfinite
  have : IsFinite e := hefinite
  have : Etale e := heetale
  have : Surjective e := hesum
  have hS0ne : Nonempty S0.toScheme := ⟨hS0.some, hS0.some_mem⟩
  have : IsIntegral S0.toScheme := isIntegral_of_isOpenImmersion S0.ι
  let d := e.finrank (genericPoint S0.toScheme)
  have hd : 1 ≤ d := e.one_le_finrank_iff_surjective.mpr hesum _
  have hedegree (s : S0.toScheme) : e.finrank s = d :=
    e.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace s _
  obtain ⟨E, hE⟩ := snc_component_equiv D n C hCinj
    (fun i ↦ (hCreg i).1) hCsupp (fun i z ↦ by
      have hh := hCint {i}
      have he : (⨆ j ∈ ({i} : Finset (Fin n)), C j) = C i := by simp
      rw [he] at hh
      simpa using (hh z).2)
  have hWS : (h ⁻¹ᵁ S : Set Y) = (D.support : Set Y)ᶜ := by
    rw [hIs, compl_compl] at hDS
    exact hDS
  have hVT : (h ⁻¹ᵁ Tcirc : Set Y) =
      (⋃ i ∈ Aout, Subtype.val '' (E i).val)ᶜ := by
    rw [hJs, compl_compl] at hDT
    change a ⁻¹' ((g ⁻¹ᵁ Tcirc : B.Opens) : Set B) = _
    rw [hDT]
    congr 1
    simp_rw [hE]
    rw [← Finset.sup_eq_iSup, Closeds.coe_finset_sup, Finset.sup_eq_iSup]
    rfl
  refine ⟨Over.mk (h ≫ (T ↘ Spec (.of k))), hY, hYreg,
    (show IsSeparated (h ≫ (T ↘ Spec (.of k))) from inferInstance),
    (show LocallyOfFiniteType (h ≫ (T ↘ Spec (.of k))) from inferInstance),
    (show QuasiCompact (h ≫ (T ↘ Spec (.of k))) from inferInstance),
    h, inferInstance, inferInstance, rfl,
    ⟨generic_eq h, hhf⟩, D, hD, n, E, Aout, hWS, hVT,
    inferInstance, inferInstance, ?_, S0, hS0ne, hS0dense,
    hS0finite, T0, u0, e, d, hue, hu0, huhomeo,
    hefinite, heetale, hesum, hd, hedegree⟩
  refine ⟨(a ∣_ g ⁻¹ᵁ S) ≫ lift, ?_⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun m ↦ (a ∣_ g ⁻¹ᵁ S) ≫ m) hlift).trans
      (morphismRestrict_comp a g S).symm)

end AlgebraicGeometry
