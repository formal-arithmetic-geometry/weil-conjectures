/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.BirationalQuasiModification
public import Sheaf.AlgebraicGeometry.CenteredValuation
public import Sheaf.TraceFormula.Modification
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

import WeilConjectures.AlgebraicGeometry.AffineBirationalOfFractionRingEquiv
import WeilConjectures.AlgebraicGeometry.DenseOpenComponentCoproduct
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.Paper.ReducedSourceFactors
import Sheaf.Compactification.BoundaryRefinement
import WeilConjectures.Compactification.Dense
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.RingTheory.Valuation.LocalSubring
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Common proper refinement of a finite valuation cover by quasi-modifications

Source: Temkin, *Stable modification of relative curves*, Proposition 3.2.6 and
Corollaries 3.2.5, 3.2.7, pp. 16--17 (blueprint:
lem-trf-birational-quasi-modification-common-cover).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Every finite family of integral birational quasi-modifications covering all centred
valuations has a common reduced proper modification covered by opens modifying the models.
Source: Temkin, Proposition 3.2.6 and Corollaries 3.2.5, 3.2.7, pp. 16--17; the reduced
finite-component extension is the node's componentwise construction
(blueprint: lem-trf-birational-quasi-modification-common-cover).

The valuation field is the residue field at a component's generic point. For reduced `X`
this is canonically its generic local ring, hence the component function field. The equation
in `IsCenteredValuation` retains the canonical generic morphism, including its field map.

Proof, following the thirteen steps of the DAG node:
1. If $X$ is empty, take $X_1$ empty with its empty cover. Otherwise give its finitely many
irreducible components their reduced induced closed structures $C_a\hookrightarrow X$, using
[lem-weil-pbc-reduced-induced-closed-subscheme]. Each $C_a$ is integral by
[def-pc-integral-scheme], and is qcqs: it is closed in the qcqs scheme $X$, and on an affine
chart its ring is a quotient. Assign $Y_i$ to the component containing the image of its generic
point. Every point of $Y_i$ specializes that generic point, so its image is in $C_a$;
[lem-weil-pbc-reduced-source-factors-through-closed-subscheme] gives a factorization $Y_i\to
C_a\to X$. This factor is separated and of finite type: $Y_i\times_X C_a\cong Y_i$, so its
diagonal is the same closed diagonal, and on affine charts its ring generators over the original
base also generate over the quotient ring of $C_a$. The valuation-cover hypothesis holds over
each $C_a$: a valuation morphism into $C_a$ is one into $X$, and any lift to a $Y_i$ has the
same generic component and is over $C_a$, since $C_a\to X$ is a monomorphism. Taking the field
$k(C_a)$ itself as a valuation ring shows that the family assigned to every component is
nonempty.
2. Fix one component $C=C_a$, write $K=k(C)$, and use only the $Y_i$ assigned to it. By
[sk-thm-nagata-compactification], each separated finite-type map $Y_i\to C$ has a dense
compactification $Y_i\xrightarrow{j_i}\overline Y_i\to C$. Here the theorem applies because $C$
is qcqs. By [sk-def-nagata-sketch-data], $j_i$ is an open immersion and $\overline Y_i\to C$ is
proper, with $\mathcal O_{\overline Y_i}\hookrightarrow j_{i*}\mathcal O_{Y_i}$. The latter
injection kills nilpotents, since $Y_i$ is reduced. It also shows that every nonempty open of
$\overline Y_i$ meets $Y_i$: otherwise its structure sheaf would be zero. Thus $Y_i$ is
topologically dense, $\overline Y_i$ is irreducible, and $\overline Y_i$ is integral by
[def-pc-integral-scheme]. Its generic point and function field are those of its nonempty open
$Y_i$, hence the prescribed $K$.
3. The fibre of each $\overline Y_i$ over the generic point of $C$ is exactly
$\operatorname{Spec}K$, with the specified generic map. Indeed choose a nonempty affine
$\operatorname{Spec}A\subset C$. For any nonempty affine chart $\operatorname{Spec}B$ of its
inverse image, [lem-sc-integral-function-field-affine-fraction] identifies $A$ and $B$ with
subrings of $K$, compatibly with the structural map. Thus $A\subseteq B\subseteq
K=\operatorname{Frac}(A)$ and $B\otimes_A K=K$: localization at the nonzero elements of $A$
already contains $\operatorname{Frac}(A)$ and remains a subring of $K$. By
[lem-weil-pbc-fibre-product-affine-spectra] these are precisely the generic-fibre charts. They
glue to one $\operatorname{Spec}K$, since every two nonempty opens of the integral $\overline
Y_i$ contain its generic point and their identifications induce the identity on $K$. This is an
affine localization computation, with no finiteness or Noetherian assumption on $A$.
4. Form the finite nonempty fibre product $P=\prod_C\overline Y_i$, using
[def-pc-fibre-product]. Repeated proper base change and composition,
[lem-weil-pbc-proper-base-change] and [lem-weil-pbc-proper-composition], show that $P\to C$ is
proper. Step 3 gives $P_K=\operatorname{Spec}K$; denote its point by $\xi$. Let
$Z\hookrightarrow P$ be the reduced induced closed subscheme on $\overline{\{\xi\}}$, which
exists by [lem-weil-pbc-reduced-induced-closed-subscheme]. By
[lem-weil-pbc-closed-immersion-proper], the structural map $r:Z\to C$ is proper. We use this
explicit reduced closure, rather than a whole fibre product with possible extra components.
5. The scheme $Z$ is nonempty, reduced and irreducible, hence integral by
[def-pc-integral-scheme]. Its generic fibre is the full $\operatorname{Spec}K$: it is a closed
subscheme of $P_K=\operatorname{Spec}K$ and contains $\xi$, so its defining ideal in the field
$K$ is zero. In particular the residue field at $\xi$, and thus the function field of $Z$, is
$K$. Every projection $q_i:Z\to\overline Y_i$ induces the identity on this specified $K$. These
assertions use just the reduced closed structure from Step 4 and the calculation of the single
generic fibre.
6. Since $Z\to C$ is proper and $\overline Y_i\to C$ is separated,
[lem-weil-pbc-proper-to-separated] makes each projection $q_i:Z\to\overline Y_i$ proper. Put
$W_i=q_i^{-1}(Y_i)=Z\times_{\overline Y_i}Y_i$. It is open in $Z$ by
[lem-weil-pbc-open-immersion-base-change], and $h_i:W_i\to Y_i$ is proper by
[lem-weil-pbc-proper-base-change]. It contains $\xi$ because the generic point of $\overline
Y_i$ belongs to $Y_i$. Hence $W_i$ is a nonempty integral open with function field $K$, and
$h_i$ induces the identity of $K$ by Step 5 and
[lem-sc-integral-function-field-affine-fraction]. All squares and maps here are over $C$, and
therefore over $X$.
7. For each of the maps $r:Z\to C$ and $h_i:W_i\to Y_i$, choose a nonempty affine target $V$ and
a nonempty affine source chart $U$ inside its inverse image on which the map is of finite type.
Such a chart exists by [def-weil-finite-type-morphism], since these maps are proper and
dominant. Apply [lem-sbc-affine-birational-fraction-ring-equiv] with its affine base $S=V$, its
$X=U$, its $Y=V$, and its two structural maps the restricted morphism and the identity. Both are
locally of finite type; [lem-sc-integral-function-field-affine-fraction] identifies their
fraction fields with the same $K$, and the isomorphism is the identity on every element of the
base ring. The resulting $V$-isomorphism between dense opens of $U$ and $V$ is necessarily the
restriction of the given map, because the second structural map is the identity. Those opens are
also dense in the corresponding integral source and target. Thus $r$ and every $h_i$ induce
isomorphisms between nonempty dense opens; no assertion about a normal target is needed.
8. Every nonempty open of an integral scheme is schematically dense. To verify the particular
claim needed here, take an affine chart $\operatorname{Spec}A$ and a section whose restriction
to the given dense open is zero. Its germ at the generic point is zero, and the injection
$A\hookrightarrow k(Z)$ (or into the function field of the relevant integral scheme) in
[lem-sc-integral-function-field-affine-fraction] makes that section zero. Affine charts test
injectivity of the sheaf map. Consequently all dense opens in Step 7 are schematically dense.
Combined with properness, this proves that $r$ and each $h_i$ are modifications in exactly the
sense of the item. The remaining task is to prove that the opens $W_i$ cover $Z$.
9. Take any $z\in Z$. On an affine neighbourhood $\operatorname{Spec}B$ of $z$, $B$ is a domain
with fraction field $K$ by [lem-sc-integral-function-field-affine-fraction]. The local ring
$\mathcal O_{Z,z}$ is a localization of $B$ by [lem-weil-pbc-affine-open-stalk-localization], so
it too has fraction field $K$. By [lemma-nagata-local-domain-valuation-dominates] choose a
valuation ring $V\subseteq K$ dominating $\mathcal O_{Z,z}$. Its local inclusion gives a
morphism $v:\operatorname{Spec}V\to Z$ sending the closed point to $z$, by
[lem-weil-pbc-morphism-from-spec-local-ring]. Its restriction to $\operatorname{Spec}K$ is the
specified generic point, since the ring map is the inclusion in $K$. Thus $rv$ is one of the
centred valuations of $C$ in the hypothesis.
10. By the hypothesis over $C$ verified in Step 1, $rv$ lifts to some $u:\operatorname{Spec}V\to
Y_i$. Compare the two $C$-morphisms $q_i v$ and $j_i u$ from $\operatorname{Spec}V$ to
$\overline Y_i$. They have the same restriction to $\operatorname{Spec}K$: Step 3 identifies the
whole generic fibre with $\operatorname{Spec}K$ and its structural map with the identity. Since
$\overline Y_i\to C$ is separated, [lemma-nagata-separated-valuation-lift-unique] gives $q_i
v=j_i u$. At the closed point this says $q_i(z)\in Y_i$, so $z\in W_i$. As $z$ was arbitrary,
the finite opens $W_i$ cover $Z$. In particular the cover is proved by comparing actual
valuation morphisms, not just their images in $C$.
11. Perform Steps 2--10 for each $C_a$, producing integral $Z_a$, proper $r_a:Z_a\to C_a$, and
their finite covers by opens proper and birational over the assigned $Y_i$. Form $X_1=\coprod_a
Z_a$ and the map $p:X_1\to X$ with restrictions $Z_a\to C_a\hookrightarrow X$, by
[lem-weil-pbc-scheme-coproduct-family]. Each restriction is proper by
[lem-weil-pbc-closed-immersion-proper] and [lem-weil-pbc-proper-composition]. The finite
coproduct map is proper directly from [def-weil-proper-morphism]: after any base change its
closed images are finite unions of closed images; it is of finite type using the finite union of
the affine covers for the component maps; and its diagonal on each open-and-closed $(a,b)$ block
of $X_1\times_X X_1$ is the closed diagonal of $Z_a\to X$ when $a=b$ and the empty closed
subscheme when $a\ne b$. The scheme $X_1$ is reduced, since all its open-and-closed pieces are
integral. Their $W_i$ are opens of $X_1$ and cover it, with the same proper birational
$X$-morphisms to the $Y_i$.
12. For each $a$, Step 7 supplies nonempty opens $A_a\subset Z_a$ and $B_a\subset C_a$ with
$r_a:A_a\xrightarrow{\sim}B_a$. Apply [lem-weil-pbc-dense-open-component-coproduct] to the
component immersions and these $B_a$. Obtain a dense open $U\subset X$ such that $(\coprod
C_a)|_U\to U$ is an isomorphism and $U\cap C_a\subset B_a$. The inverse images of $U\cap C_a$ in
$A_a$ form an open $U_1\subset X_1$ isomorphic to $U$. Each is nonempty and dense in its
integral $Z_a$, so $U_1$ is schematically dense by Step 8. To check schematic density of $U$ in
the reduced $X$, pull a section zero on $U$ back to each $C_a$. It vanishes at its generic
point, hence vanishes on $C_a$ by [lem-sc-integral-function-field-affine-fraction]. Its value in
every residue field of $X$ is therefore zero, since the components cover $X$. The affine ideal
formula of [lem-weil-pbc-reduced-induced-closed-subscheme], applied to the whole reduced scheme
$X$, makes the section zero. This verifies injectivity of $\mathcal O_X\to j_*\mathcal O_U$.
Together with Step 11, $p$ is a reduced modification, and all required claims now hold.
13. For the optional affine reindexing, each $Y_i$ is quasi-compact (finite type over qcqs $X$),
so choose a finite affine open cover of it. A valuation morphism $\operatorname{Spec}V\to Y_i$
factors through any such affine containing the image of its closed point: its inverse image is
open and contains the closed point of the local spectrum, hence all its points. Therefore these
finitely many affine models still cover all centred valuations. Each is integral and separated
of finite type over $X$: the affine open immersion is quasi-compact because $Y_i$ is
quasi-separated, and finite generation is local on source. The construction of Steps 1--12
applies to this finite family and gives modifications to the selected affine opens. Relabel
these opens by their original $i$, allowing repetitions as stated.
-/
theorem exists_common_reduced_modification_cover
    (X : Scheme.{u}) [IsReduced X] [CompactSpace X] [QuasiSeparatedSpace X]
    (n : ℕ) (Y : Fin n → Scheme.{u}) [∀ i : Fin n, IsIntegral (Y i)]
    (f : ∀ i : Fin n, Y i ⟶ X)
    (hY : ∀ i : Fin n, IsBirationalQuasiModification (f i))
    (hcomponents : Set.Finite (irreducibleComponents X))
    (hvaluation : ∀ η : X, closure ({η} : Set X) ∈ irreducibleComponents X →
      ∀ (V : ValuationSubring (X.residueField η)) (v : Spec (.of V) ⟶ X),
        IsCenteredValuation η V v →
          ∃ i : Fin n, ∃ l : Spec (.of V) ⟶ Y i, l ≫ f i = v) :
    ∃ (X₁ : Scheme.{u}) (p : X₁ ⟶ X), IsReduced X₁ ∧ SchemeModification p ∧
      ∃ W : Fin n → X₁.Opens, (⨆ i, W i) = ⊤ ∧
        ∀ i : Fin n, ∃ a : (W i).toScheme ⟶ Y i,
          SchemeModification a ∧ a ≫ f i = (W i).ι ≫ p := by
  sorry

/-- The common-cover construction also works after replacing each model by any specified
finite affine open cover, with the repeated indices retained as dependent pairs.
Source: Temkin, proof of Proposition 3.2.6, initial affine-cover reduction, pp. 16--17
(blueprint: lem-trf-birational-quasi-modification-common-cover).

Proof: this is step 13 of the node. A valuation morphism into a model factors through an
affine open containing its closed point, because every open containing the closed point of a
local spectrum is the whole spectrum. Thus the affine refinements still cover the centred
valuations. Each affine open is integral and has the same function field; its open immersion
is quasi-compact since the model is quasi-separated. Composition preserves separatedness and
finite type, so apply `exists_common_reduced_modification_cover` to the finite family indexed
by `(i,j)`. Its factorization equations are exactly those below. The other twelve steps are
recorded in that theorem's docstring. Empty families and empty bases are included.
-/
theorem exists_common_reduced_modification_affine_cover
    (X : Scheme.{u}) [IsReduced X] [CompactSpace X] [QuasiSeparatedSpace X]
    (n : ℕ) (Y : Fin n → Scheme.{u}) [∀ i : Fin n, IsIntegral (Y i)]
    (f : ∀ i : Fin n, Y i ⟶ X)
    (hY : ∀ i : Fin n, IsBirationalQuasiModification (f i))
    (hcomponents : Set.Finite (irreducibleComponents X))
    (hvaluation : ∀ η : X, closure ({η} : Set X) ∈ irreducibleComponents X →
      ∀ (V : ValuationSubring (X.residueField η)) (v : Spec (.of V) ⟶ X),
        IsCenteredValuation η V v →
          ∃ i : Fin n, ∃ l : Spec (.of V) ⟶ Y i, l ≫ f i = v)
    (m : Fin n → ℕ) (A : ∀ i : Fin n, Fin (m i) → (Y i).Opens)
    (hA : ∀ (i : Fin n) (j : Fin (m i)), IsAffineOpen (A i j))
    (hcover : ∀ i : Fin n, (⨆ j : Fin (m i), A i j) = ⊤) :
    ∃ (X₁ : Scheme.{u}) (p : X₁ ⟶ X), IsReduced X₁ ∧ SchemeModification p ∧
      ∃ W : (Σ i : Fin n, Fin (m i)) → X₁.Opens, (⨆ j, W j) = ⊤ ∧
        ∀ j : Σ i : Fin n, Fin (m i),
          ∃ a : (W j).toScheme ⟶ (A j.1 j.2).toScheme,
            SchemeModification a ∧ a ≫ (A j.1 j.2).ι ≫ f j.1 = (W j).ι ≫ p := by
  sorry

end AlgebraicGeometry
