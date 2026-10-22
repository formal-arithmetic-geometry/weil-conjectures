/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.NormalTopologicallyNoetherianComponents
import Sheaf.AlgebraicGeometry.AffineGroupoidOrbitFibres
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Generic fields of a finite scheme quotient

Source: Stacks Project, Groupoids, Tag 03BK, lemma-invariants-base-change (3),
and the explicit generic-localization argument of the DAG node
(blueprint: lem-sfb-finite-quotient-generic-fields).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite quotient of normal Noetherian schemes sends generic points to generic
points. Its component images give a bijection on component orbits, expressed as
surjectivity on components and equality of images exactly for translates. The image
of the canonical residue-field map is exactly the stabilizer-fixed elements.

Normality is imposed on all stalks, without an irreducibility hypothesis. The sheaf
hypothesis compares actual pullbacks and restrictions on common subopens. Fixedness
in the final clause uses pullback by each stabilizing automorphism; taking all such
pullbacks gives the same fixed field as the inverse-pullback left action.

Source: Stacks Project, Groupoids, Tag 03BK, lemma-invariants-base-change (3),
agent-formulated consequence used in ILO X 2.3, Step 2, printed p. 151
(blueprint: lem-sfb-finite-quotient-generic-fields).

Proof plan, following the eight steps of the node:
1. Apply [lem-sc-affine-noetherian-underlying-space] to the finitely many affine opens in the
Noetherian hypothesis on each of $X,Z$. A descending chain of closed subsets restricts to a
stabilizing chain on each such open; the maximum of the finitely many stabilization indices works
on their union. Thus both underlying spaces are Noetherian. Apply
[lem-trf-normal-topologically-noetherian-components] to obtain finite, disjoint, clopen normal
integral components $X_i$ and $Z_j$. The hypotheses on local rings are exactly the normality
hypotheses of that node. The empty case has no components and the assertions are vacuous.
2. On an affine open $V=\operatorname{Spec}A$ of $Z$, finiteness
[def-weil-finite-integral-morphism] gives $q^{-1}V=\operatorname{Spec}B$. Invariance of $q$ makes
this open $H$-stable, and the assumed sheaf equality identifies the actual map $A\to B$ with the
inclusion $B^H\subset B$. Apply [lem-a1-affine-groupoid-orbit-fibres] to the constant action
groupoid $R=\coprod_{h\in H}\operatorname{Spec}B$: its affine presentation is supplied by
[lem-weil-pbc-finite-affine-coproduct-spectrum], source is the identity on each copy, and target
is the action automorphism on that copy. Both maps are finite locally free: the source algebra is
$\prod_{h\in H}B$, free over $B$ with its standard coordinate basis; the target is conjugate to
this source projection by the automorphism $(h,x)\mapsto(h,hx)$. Its invariant ring is exactly
$B^H$ . The groupoid identities are the action identities. The cited node therefore says that two
points over $V$ have the same image exactly when one is an $H$-translate of the other. Since any
common image lies in an affine open, this holds on all of $X$.
3. By [lem-weil-pbc-finite-closed-map-finite-fibres], $q$ is closed. The group permutes the
components $X_i$, since its maps are homeomorphisms. For a component orbit $O$, put
$T_O=\bigcup_{i\in O}X_i$. It and its complement are closed. The point-orbit assertion of Step 2
gives $q^{-1}(q(T_O))=T_O$; surjectivity then gives $Z\setminus q(T_O)=q(X\setminus T_O)$. Hence
$q(T_O)$ is clopen. For $i\in O$, invariance gives $q(T_O)=q(X_i)$, an irreducible nonempty
subset: if its image lay in a union of two closed subsets, their inverse images would cover $X_i$,
forcing one to contain it. Thus $q(T_O)$ is a nonempty irreducible clopen subset. By the disjoint
integral component decomposition of $Z$ from Step 1 it is precisely one component $Z_j$. The sets
$q(T_O)$ are disjoint by saturation and cover $Z$ by surjectivity, proving the desired
component-orbit bijection.
4. Let $\eta_i$ be the generic point of $X_i$, whose existence and uniqueness follow from
[lem-sc-scheme-sober]. Continuity gives
$q(X_i)=q(\overline{\{\eta_i\}})\subseteq\overline{\{q(\eta_i)\}}$. The reverse inclusion holds
because $q(X_i)$ is closed and contains $q(\eta_i)$. By Step 3 this closed image is $Z_j$, so
$q(\eta_i)$ is its generic point $\xi_j$. A group element fixes $\eta_i$ exactly when it
stabilizes $X_i$: take closures for one implication, and uniqueness of its generic point for the
other. Thus the stabilizer of this factor is exactly the group $D$ in the statement.
5. Fix $i$ and $j$ as above and choose a nonempty affine open $V\subset Z_j$. Since $Z_j$ is open
in $Z$, this is also an affine open of $Z$. Put $W=q^{-1}V=\operatorname{Spec}B$ and
$A=\Gamma(V,\mathcal O_Z)$, using [def-weil-finite-integral-morphism]. Each $W_k=X_k\cap W$, for
$k\in O$, is clopen in $W$ and is nonempty because $q(X_k)=Z_j$. There are no other components
meeting $W$. By [lem-weil-pbc-spec-clopen-idempotent] it is $D(e_k)$ for an idempotent of $B$, and
by [lem-weil-pbc-affine-open-section-vanishing-prime], part (b), it is affine. It is an open
subscheme of the integral $X_k$. In fact its coordinate ring $B_k=\Gamma(W_k,\mathcal O_X)$ is a
domain by [lem-sc-integral-function-field-affine-fraction], applied to $X_k$. Sheaf gluing on the
disjoint open cover $(W_k)_{k\in O}$ gives the actual restriction isomorphism $B\cong\prod_{k\in
O}B_k$: a tuple of sections glues uniquely since all intersections are empty. This isomorphism
intertwines the $H$-action, which sends the factor $B_k$ to $B_{hk}$ by inverse pullback.
6. Write $h:B_k\to B_{hk}$ for the inverse-pullback action. Projection to factor $i$ identifies
$(\prod_{k\in O}B_k)^H$ with $B_i^D$. Explicitly an invariant tuple satisfies $b_{hi}=h(b_i)$, so
its $i$th entry is fixed by $D$, and it is determined by that entry. Conversely for $a\in B_i^D$
set $b_{hi}=h(a)$. If $hi=h\prime i$, then $h^{-1}h\prime\in D$, so the entries agree; moreover
$b_{ghi}=g(b_{hi})$, proving invariance. The inverse and projection preserve addition,
multiplication and $1$ coordinatewise. Combining this with $A=B^H$ from the sheaf hypothesis gives
an injective map $A\to B_i$ whose image is exactly $B_i^D$. It is the actual restriction of
$q^\sharp$ to $W_i$, not an unspecified isomorphism.
7. By [lem-sc-integral-function-field-affine-fraction] applied to the integral components
$Z_j,X_i$ and their nonempty affine opens $V,W_i$, the generic stalks are respectively
$\operatorname{Frac}A$ and $\operatorname{Frac}B_i$. A field has zero maximal ideal, so
[def-weil-residue-field] identifies these stalks with $\kappa(\xi_j)$ and $M=\kappa(\eta_i)$. By
[def-weil-open-immersion], restricting to these open components does not change the stalks or
residue fields. The map $\kappa(\xi_j)\to M$ is the extension of $A\to B_i$ from Step 6: both send
a section to its germ at the indicated generic point, and functoriality of germs makes that square
commute. Its extension to fractions is unique because each nonzero denominator becomes a unit. The
action of $D$ on $M$ similarly extends its action on $B_i$.
8. The image of $\operatorname{Frac}A$ in $M=\operatorname{Frac}B_i$ is fixed by $D$, by Step 6.
Conversely let $x=b/c\in M$ be fixed by $D$, with $b,c\in B_i$ and $c\ne0$. Set $d=\prod_{g\in
D}g(c)$. This lies in $B_i^D$ and is nonzero because $B_i$ is a domain. Also $xd=b\prod_{g\in
D,\,g\ne1}g(c)$ belongs to $B_i$, and $g(xd)=g(x)g(d)=xd$ for every $g\in D$. Thus both $d$ and
$xd$ belong to $B_i^D$, the image of $A$, so $x=(xd)/d$ lies in the image of
$\operatorname{Frac}A$. This proves $\kappa(\xi_j)=M^D$ through the canonical embedding of Step 7.
The calculation uses finiteness but never faithfulness, never division by $|D|$, and it was
carried out on an arbitrary component orbit; it therefore covers disconnected schemes, nonfree
generic actions and arbitrary characteristic.
-/
theorem finiteQuotient_genericFields
    {X Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Z]
    (hXnormal : ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (hZnormal : ∀ z : Z,
      IsDomain (Z.presheaf.stalk z) ∧ IsIntegrallyClosed (Z.presheaf.stalk z))
    {H : Type v} [Group H] [Finite H] (a : H →* Aut X)
    (q : X ⟶ Z) [IsFinite q] [Surjective q]
    (hinvariant : ∀ h : H, (a h).hom ≫ q = q)
    (hgeometric : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (x y : Spec (.of Ω) ⟶ X), x ≫ q = y ≫ q → ∃ h : H, x ≫ (a h).hom = y)
    (hsheaf : ∀ U : Z.Opens,
      Function.Injective (q.app U).hom ∧
      ∀ s : Γ(X, q ⁻¹ᵁ U),
        (s ∈ Set.range (q.app U).hom ↔
          ∀ (h : H) (W : X.Opens) (hW : W ≤ q ⁻¹ᵁ U)
            (hWh : W ≤ (a h).hom ⁻¹ᵁ (q ⁻¹ᵁ U)),
            ((a h).hom.appLE (q ⁻¹ᵁ U) W hWh).hom s =
              (X.presheaf.map (homOfLE hW).op).hom s)) :
    (∀ (C : Set X), C ∈ irreducibleComponents X →
      ∀ η : X, IsGenericPoint η C → IsGenericPoint (q η) (q '' C) ∧
        q '' C ∈ irreducibleComponents Z) ∧
    (∀ E ∈ irreducibleComponents Z,
      ∃ C ∈ irreducibleComponents X, q '' C = E) ∧
    (∀ C ∈ irreducibleComponents X, ∀ C' ∈ irreducibleComponents X,
      q '' C = q '' C' ↔ ∃ h : H, (a h).hom '' C = C') ∧
    (∀ (C : Set X), C ∈ irreducibleComponents X →
      ∀ η : X, IsGenericPoint η C →
        Function.Injective (q.residueFieldMap η).hom ∧
        ∀ b : X.residueField η,
          (b ∈ Set.range (q.residueFieldMap η).hom ↔
            ∀ (h : H) (eh : (a h).hom η = η),
              (((X.residueFieldCongr eh).inv ≫ (a h).hom.residueFieldMap η).hom b) = b)) := by
  sorry

end AlgebraicGeometry
