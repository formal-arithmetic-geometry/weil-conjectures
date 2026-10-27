/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Irreducible
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import Sheaf.AlgebraicGeometry.FiniteQuotientNormalProper
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.AmpleRestrictClosedImmersion
import Sheaf.AlgebraicGeometry.FiniteNormalAmpleDescent
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.ProperRelativeAmpleProjectiveBundle
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective

/-! # Constants descent and projectivity of a supplied semilinear quotient

Source: ILO, Travaux de Gabber, Expose X 2.3 Step 2, diagram (2.c), printed p. 151;
Stacks Project, Tags 0BD4(2), 0BCL(1), and 087S(1).
(blueprint: lem-sfb-semilinear-quotient-projective-geometry)

The fixed field is `IntermediateField.fixedField ρ.range`, so kernels in the action
are allowed. The inverse in the scalar action accounts for contravariance of `Spec`.
Invariant sections use `appLE` on the invariant inverse images of opens of the quotient.
No quotient object is constructed or chosen.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A supplied geometric categorical quotient of a smooth projective semilinear scheme
has a unique descended fixed-field structure and is normal, Noetherian and projective.
Empty schemes, disconnected schemes and nonfaithful actions are included.

Source: ILO X 2.3 Step 2, diagram (2.c), printed p. 151; Stacks 0BD4(2), 0BCL(1), 087S(1).
(blueprint: lem-sfb-semilinear-quotient-projective-geometry)

Proof (the eight steps of the DAG):
1. Write $a:Y\to\operatorname{Spec}K$ and $a_F:Y\to\operatorname{Spec}F$ for the given structure
map and its composite. The fixed elements form a subfield $e\subseteq F\subseteq K$: sums,
products and inverses of fixed elements are fixed. Both $F/e$ and $K/F$ are finite: $F$ is an
$e$-linear subspace of the finite-dimensional space $K$, and any finite $e$-spanning set of $K$
also spans it over $F$. Equivariance and fixedness of $F$ give $a_Fh=a_F$ for every $h\in H$.
Apply the assumed categorical property to this invariant map to obtain the unique
$s_F:Q\to\operatorname{Spec}F$ with $s_Fq=a_F$. Composing with
$\operatorname{Spec}F\to\operatorname{Spec}e$ gives $s_e$ and $s_eq=a_e$. Any other such
$e$-structure equals $s_e$ by the same categorical uniqueness. Thus $q$ is over $F$ and $e$,
with the asserted descended $e$-structure.

2. Apply [lem-sfb-finite-constant-projective-graph] with extension $K/F$, source $R=Y$, target
$S=\operatorname{Spec}F$, and $c=a_F$. The target is separated over $F$ (its relative diagonal
is the identity). Taking $S'=S$ gives projectivity of $Y$ over $F$ in the
finite-projective-space convention and properness of $a_F$. Apply the same statement with $K/e$
and $S=\operatorname{Spec}e$ to get projectivity and properness over $e$. Properness includes
finite type by [def-weil-proper-morphism]. These uses require no separability of the constant
extensions.

3. The field $F$ is Noetherian, since its only ideals are zero and the unit ideal, so
$\operatorname{Spec}F$ is Noetherian with its single affine chart. Since $a_F$ is of finite
type, [lem-weil-pbc-finite-type-over-noetherian] makes $Y$ Noetherian. Independently, smoothness
over $K$ gives regularity of $Y$ by [lem-weil-pbc-smooth-scheme-over-field-regular]. Clause (1)
of [rem-pc-regular-normal] gives normality, and clause (2) gives the required finite disjoint
union of open and closed normal integral components of $Y$. No connectedness or nonemptiness
assumption is used.

4. The $H$-action is by $F$-automorphisms of $Y$, because $a_Fh=a_F$, and it is by
$e$-automorphisms by hypothesis. The supplied categorical property also holds in $F$-schemes:
for an invariant $F$-map $b:Y\to T$ with structure $t:T\to\operatorname{Spec}F$, let $\bar
b:Q\to T$ be its unique factor as a scheme map. Then $(t\bar b)q=tb=a_F=s_Fq$, and categorical
uniqueness for the map $a_F$ gives $t\bar b=s_F$. Thus the factor is an $F$-map, uniquely. The
identical argument with $e$ shows the categorical property over $e$. Now apply
[lem-sfb-finite-quotient-normal-proper] over $F$, and again over $e$: the source is normal
proper finite type by steps 2--3; the finite surjection, invariant structure sheaf and
geometric-orbit hypotheses are exactly those supplied. It follows that $Q$ is normal and
Noetherian, and proper of finite type over both $F$ and $e$.

5. Apply clause (2) of [rem-pc-regular-normal] to $Q$: write it as a finite disjoint union
$Q=\coprod_{i\in I}Q_i$ of open and closed normal integral schemes. Choose a closed
projective-space embedding of $Y$ over $F$ from step 2. By
[lem-weil-pbc-projective-ample-invertible] its pullback of $\mathcal O(1)$ is an ample
invertible module $M$ on $Y$.

6. For $i\in I$ let $W_i=q^{-1}(Q_i)$, with its open subscheme structure. This is open and
closed in $Y$. Its inclusion $j_i:W_i\to Y$ is a closed immersion: it is a homeomorphism onto a
closed subset and $\mathcal O_Y\to(j_i)_*\mathcal O_{W_i}$ is surjective, with identity stalk
maps on $W_i$ and zero target stalks off $W_i$ [def-weil-closed-immersion]. The restricted map
$q_i:W_i\to Q_i$ is finite: every affine open $V\subseteq Q_i$ is an affine open in $Q$, and its
inverse image and ring map under $q_i$ are those under $q$, so
[def-weil-finite-integral-morphism] applies. It is surjective because $q$ is surjective. The
restriction $j_i^*M$ is ample by [lem-trf-ample-restrict-closed-immersion]. Apply
[lem-sfb-finite-normal-ample-descent] to the finite surjection $q_i$, whose target $Q_i$ is
normal integral, obtaining an ample invertible module $L_i$ on $Q_i$. No assertion of descent of
the particular module $M$ is needed.

7. Define a sheaf of modules $L$ on $Q$ by $L(U)=\prod_{i\in I}\Gamma(U\cap Q_i,L_i)$, with
componentwise restrictions and the action of $\mathcal O_Q(U)$ by restriction. The sheaf axiom
holds componentwise. Its restriction to $Q_i$ is $L_i$, so it is locally free of rank one, hence
invertible by [def-sc-invertible-module]. It is ample by [def-weil-pbc-ample-invertible-module]:
$Q$ is quasi-compact by step 4, and for $x\in Q_i$ choose $n\geq1$ and a global section $u$ of
$L_i^{\otimes n}$ whose nonvanishing locus is affine and contains $x$. Extend $u$ to a section
of $L^{\otimes n}$ by zero on the other disjoint open components. Its nonvanishing locus is
exactly $(Q_i)_u$, an affine open of $Q$. This proves the required affine-locus condition. If
$I$ is empty, the construction gives the unique module on the empty scheme; local rank one and
the affine-locus condition are vacuous, and the empty scheme is quasi-compact.

8. Put $S=\operatorname{Spec}F$. It is quasi-compact and quasi-separated: its only opens are $S$
and the empty set, both quasi-compact, and intersections of affine opens are among these. The
proper map $s_F$ is quasi-compact, and $L$ is $s_F$-relatively ample: its restriction over the
whole affine base is ample by step 7, and the empty restriction satisfies the same definition
vacuously. Apply [lem-sfb-proper-relative-ample-projective-bundle] to obtain projectivity of
$s_F$ in the projective-bundle sense. The trivial invertible module $\mathcal O_S$ is ample: the
section $1$ in tensor degree one has affine nonvanishing locus all of $S$, and $S$ is
quasi-compact [def-weil-pbc-ample-invertible-module]. Therefore
[lem-trf-projective-bundle-to-h-projective] makes $s_F$ projective in precisely the
finite-projective-space convention [def-kun-projective]. The normality, Noetherianity,
properness and finite-type clauses were already obtained in steps 3--4, and the constants and
compatibility clauses in step 1.
-/
theorem semilinear_quotient_projective_geometry
    (e K : Type u) [Field e] [Field K] [Algebra e K] [Module.Finite e K]
    (H : Type v) [Group H] [Finite H] (ρ : H →* (K ≃ₐ[e] K))
    (Y Q : Scheme.{u}) (a : Y ⟶ Spec (CommRingCat.of K))
    [Smooth a] [IsHProjective a] (α : H →* Aut Y)
    (hαe : ∀ h : H, (α h).hom ≫ a ≫ Spec.map (CommRingCat.ofHom (algebraMap e K)) =
      a ≫ Spec.map (CommRingCat.ofHom (algebraMap e K)))
    (hαK : ∀ h : H, (α h).hom ≫ a =
      a ≫ Spec.map (CommRingCat.ofHom (ρ h⁻¹).toRingHom))
    (q : Y ⟶ Q) [IsFinite q] [Surjective q]
    (hinv : ∀ h : H, (α h).hom ≫ q = q)
    (honto : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
      Function.Surjective (fun x : Spec (CommRingCat.of Ω) ⟶ Y ↦ x ≫ q))
    (horbits : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (x y : Spec (CommRingCat.of Ω) ⟶ Y),
      x ≫ q = y ≫ q ↔ ∃ h : H, x ≫ (α h).hom = y)
    (hsections : ∀ U : Q.Opens, Function.Injective (q.app U) ∧
      ∀ s : Γ(Y, q ⁻¹ᵁ U),
        (∃ t : Γ(Q, U), q.app U t = s) ↔
          ∀ (h : H) (hU : q ⁻¹ᵁ U ≤ (α h).hom ⁻¹ᵁ (q ⁻¹ᵁ U)),
            (α h).hom.appLE (q ⁻¹ᵁ U) (q ⁻¹ᵁ U) hU s = s)
    (hcategorical : ∀ (T : Scheme.{u}) (f : Y ⟶ T),
      (∀ h : H, (α h).hom ≫ f = f) → ∃! g : Q ⟶ T, q ≫ g = f) :
    ∃ sF : Q ⟶ Spec (CommRingCat.of (IntermediateField.fixedField ρ.range)),
      q ≫ sF = a ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (IntermediateField.fixedField ρ.range) K)) ∧
      (∀ t : Q ⟶ Spec (CommRingCat.of (IntermediateField.fixedField ρ.range)),
        q ≫ t = a ≫ Spec.map (CommRingCat.ofHom
          (algebraMap (IntermediateField.fixedField ρ.range) K)) → t = sF) ∧
      q ≫ sF ≫ Spec.map (CommRingCat.ofHom
        (algebraMap e (IntermediateField.fixedField ρ.range))) =
          a ≫ Spec.map (CommRingCat.ofHom (algebraMap e K)) ∧
      (∀ se : Q ⟶ Spec (CommRingCat.of e),
        q ≫ se = a ≫ Spec.map (CommRingCat.ofHom (algebraMap e K)) →
          se = sF ≫ Spec.map (CommRingCat.ofHom
            (algebraMap e (IntermediateField.fixedField ρ.range)))) ∧
      (∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
        IsIntegrallyClosed (Y.presheaf.stalk y)) ∧
      IsNoetherian Y ∧
      (∃ (n : ℕ) (U : Fin n → Y.Opens),
        Set.range (fun i : Fin n ↦ (U i : Set Y)) = irreducibleComponents Y ∧
        (∀ i : Fin n, IsClosed (U i : Set Y)) ∧
        (∀ i j : Fin n, i ≠ j → Disjoint (U i) (U j)) ∧
        (⨆ i : Fin n, U i) = ⊤ ∧
        (∀ i : Fin n, IsIntegral (U i).toScheme ∧
          ∀ y : (U i).toScheme, IsDomain ((U i).toScheme.presheaf.stalk y) ∧
            IsIntegrallyClosed ((U i).toScheme.presheaf.stalk y)) ∧
        Nonempty (IsColimit (Cofan.mk Y (fun i : Fin n ↦ (U i).ι)))) ∧
      IsHProjective (a ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (IntermediateField.fixedField ρ.range) K))) ∧
      IsHProjective (a ≫ Spec.map (CommRingCat.ofHom (algebraMap e K))) ∧
      (∀ z : Q, IsDomain (Q.presheaf.stalk z) ∧
        IsIntegrallyClosed (Q.presheaf.stalk z)) ∧
      IsNoetherian Q ∧ IsHProjective sF ∧ IsProper sF ∧
      (LocallyOfFiniteType sF ∧ QuasiCompact sF) ∧
      IsProper (sF ≫ Spec.map (CommRingCat.ofHom
        (algebraMap e (IntermediateField.fixedField ρ.range)))) ∧
      (LocallyOfFiniteType (sF ≫ Spec.map (CommRingCat.ofHom
        (algebraMap e (IntermediateField.fixedField ρ.range)))) ∧
        QuasiCompact (sF ≫ Spec.map (CommRingCat.ofHom
          (algebraMap e (IntermediateField.fixedField ρ.range))))) := by
  sorry

end AlgebraicGeometry
