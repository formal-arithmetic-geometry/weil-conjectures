/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.SemilinearEquivariantChowModification
import Sheaf.AlgebraicGeometry.FiniteOverProjective
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Normal projective birational models

Source: ILO, Travaux de Gabber, Expose X, 2.3, Step 1, printed p. 150;
Stacks Project, Tags 0200, 0201, 0BXR and 0GK4.
(blueprint: lem-sfb-normal-projective-birational-model)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A proper integral scheme over a field has a projective Chow modification whose
normalization in its own function field is finite, integral, normal and projective.
All embeddings commute with the displayed structure morphisms. Birationality is given by
isomorphisms over nonempty dense opens. Function-field identifications use the actual
stalk maps at generic points of the displayed morphisms; these stalks are the existing
`Scheme.functionField`, so no independently chosen field isomorphism is substituted.

Source: ILO, Expose X, 2.3, Step 1, printed p. 150; Stacks Project,
Tags 0200, 0201, 0BXR and 0GK4.
(blueprint: lem-sfb-normal-projective-birational-model)

Proof:
1. Give the one-element group the identity actions on $e$ and $S$. These actions are compatible,
and no faithfulness is needed. Apply [lem-sfb-semilinear-equivariant-chow-modification] with
$k=e$, $X=S$ and this group. Discard the actions. It gives an integral finite-type $e$-scheme $Y$,
a proper surjective $e$-morphism $c:Y\to S$, an isomorphism $c^{-1}V\simeq V$ over a dense open
$V\subseteq S$, and a closed immersion $Y\hookrightarrow\mathbf P^n_e$ for a finite $n$. Since $S$
is nonempty and $V$ is dense open, $V$ is nonempty. Thus $c^{-1}V$ is nonempty as well.
2. The scheme $Y$ is proper over $e$: its structure morphism is $Y\xrightarrow c
S\to\operatorname{Spec}e$, a composite of proper morphisms [lem-weil-pbc-proper-composition]. A
field is Noetherian because its only ideals are $(0)$ and $(1)$; its spectrum is therefore
Noetherian. As $Y$ is finite type over $e$, [lem-weil-pbc-finite-type-over-noetherian] makes $Y$
Noetherian, and [lem-weil-pbc-locally-noetherian-quasi-separated] makes it quasi-separated. Put
$K=k(Y)$ and let $a:\operatorname{Spec}K\to Y$ be its generic-point morphism. The source has one
point, is affine, quasi-compact, quasi-separated and integral; its only local ring is the field
$K$, hence integrally closed. By [lem-weil-pbc-qcqs-morphism-permanence](1), $a$ is quasi-compact
and quasi-separated.
3. Form $n_Y:N=Y^\nu\to Y$ as in [def-sc-normalization]. This is the relative normalization of $Y$
in $a:\operatorname{Spec}K\to Y$: on each nonempty affine open $U\subseteq Y$, its preimage in
$\operatorname{Spec}K$ is the whole point and has section ring $K$, so both constructions take the
integral closure of $\mathcal O_Y(U)$ in $K$. Their affine gluing maps are the same restrictions.
Apply [lem-weil-pbc-relative-normalization](iv) to $a$ to conclude $N$ is integral, hence
nonempty. Apply [lem-weil-pbc-normalization-normal-stalks] to the same $a$ (the qcqs and
normal-integral source hypotheses were checked in step 2) to conclude every local ring of $N$ is
an integrally closed domain. Finally [lem-sc-normalization-exists], applied to the integral
finite-type $e$-scheme $Y$, makes $n_Y$ finite, surjective and birational and makes $N$ proper
over $e$, since $Y$ is proper.
4. To exhibit the normalization isomorphism open explicitly, choose a nonempty affine
$U=\operatorname{Spec}R\subseteq Y$. By [def-sc-normalization] and
[def-weil-finite-integral-morphism], $n_Y^{-1}U=\operatorname{Spec}B$, where $B\subseteq K$ is the
integral closure of $R$ and is finite as an $R$-module. Choose module generators $b_1,\ldots,b_t$;
include $1$ if necessary. By [lem-sc-integral-function-field-affine-fraction], write $b_i=r_i/s_i$
in $K$, with $s_i\ne0$. For $s=\prod_i s_i\ne0$, the inclusions $R\subseteq B\subseteq K$ give
$B[1/s]=R[1/s]$: all generators lie in $R[1/s]$, and the reverse inclusion comes from $R\subseteq
B$. Thus $n_Y^{-1}D_U(s)\to D_U(s)$ is an isomorphism. This target open contains the generic
point, and its nonempty inverse image is open in the integral $N$, so both opens are dense.
5. The embedding of $Y$ in step 1, together with its properness (so quasi-compactness), gives
projectivity in [def-pc-projective-morphism]. Apply [lem-fin-finite-over-projective] with base
$\operatorname{Spec}e$, $T=Y$, and $h=n_Y$. This base is affine Noetherian, as checked in step 2.
Its affine-base conclusion supplies a closed immersion $N\hookrightarrow\mathbf P^m_e$ with finite
$m$. These two embeddings are exactly H-projectivity in [def-kun-projective]. Both schemes are
proper over $e$ by steps 2 and 3. By [def-weil-proper-morphism], proper includes finite type,
giving the remaining finite-type assertion for $N$.
6. The composite $b=c\circ n_Y$ is proper by [lem-weil-pbc-proper-composition]. It is surjective:
for $s\in S$, first lift $s$ to $y\in Y$ along $c$, then lift $y$ to $x\in N$ along $n_Y$. To
check birationality explicitly, choose dense opens $A\subseteq N$ and $B\subseteq Y$ on which
$n_Y$ is an isomorphism, as explicitly constructed in step 4. The open $D=B\cap c^{-1}V$ is
nonempty because $Y$ is irreducible and both factors are nonempty opens. Under $c^{-1}V\simeq V$,
its image is a nonempty open $W\subseteq V\subseteq S$, hence dense in the integral $S$. The open
$A\cap n_Y^{-1}D$ is nonempty and therefore dense in integral $N$, and $b$ restricts there to the
composite isomorphism $A\cap n_Y^{-1}D\simeq D\simeq W$. This proves birationality in the required
dense-open sense.
7. For any of $c$, $n_Y$ and $b$, the preceding steps exhibit an isomorphism between nonempty
opens of its integral source and target. Every such open contains the generic point, and the
generic stalk is the function field [lem-sc-integral-function-field-affine-fraction,
def-sc-function-field]. An open restriction leaves that stalk unchanged (the neighborhoods inside
an open neighborhood are cofinal). Hence taking the stalk map of each displayed open isomorphism
gives an isomorphism of function fields, and this is the stalk map of the original morphism, since
restriction uses the same sheaf maps. Stalk maps compose, so $b^*=n_Y^*\circ c^*$ under these
identifications. Thus the asserted isomorphisms are all induced by the displayed morphisms. -/
theorem exists_normal_projective_birational_model
    (e : Type u) [Field e] (S : Scheme.{u}) [S.Over (Spec (.of e))]
    [IsIntegral S] [IsProper (S ↘ Spec (.of e))] :
    ∃ (Y : Scheme.{u}) (_ : IsIntegral Y) (c : Y ⟶ S),
      LocallyOfFiniteType (c ≫ S ↘ Spec (.of e)) ∧
      QuasiCompact (c ≫ S ↘ Spec (.of e)) ∧
      IsProper c ∧ Surjective c ∧
      (∃ V : S.Opens, (V : Set S).Nonempty ∧ IsIso (c ∣_ V)) ∧
      (∃ (n : ℕ) (i : Y ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of e))),
        IsClosedImmersion i ∧
        i ≫ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of e)) ↘ Spec (.of e) =
          c ≫ S ↘ Spec (.of e)) ∧
      IsFinite Y.fromNormalization ∧ Surjective Y.fromNormalization ∧
      (∃ U : Y.Opens, Dense (U : Set Y) ∧
        Dense ((Y.fromNormalization ⁻¹ᵁ U) : Set Y.normalization) ∧
        IsIso (Y.fromNormalization ∣_ U)) ∧
      IsIntegral Y.normalization ∧
      (∀ x : Y.normalization, IsDomain (Y.normalization.presheaf.stalk x) ∧
        IsIntegrallyClosed (Y.normalization.presheaf.stalk x)) ∧
      (∃ (m : ℕ) (j : Y.normalization ⟶ ℙ(ULift.{u} (Fin (m + 1)); Spec (.of e))),
        IsClosedImmersion j ∧
        j ≫ ℙ(ULift.{u} (Fin (m + 1)); Spec (.of e)) ↘ Spec (.of e) =
          Y.fromNormalization ≫ c ≫ S ↘ Spec (.of e)) ∧
      IsHProjective (c ≫ S ↘ Spec (.of e)) ∧
      IsHProjective (Y.fromNormalization ≫ c ≫ S ↘ Spec (.of e)) ∧
      IsProper (c ≫ S ↘ Spec (.of e)) ∧
      IsProper (Y.fromNormalization ≫ c ≫ S ↘ Spec (.of e)) ∧
      LocallyOfFiniteType (Y.fromNormalization ≫ c ≫ S ↘ Spec (.of e)) ∧
      QuasiCompact (Y.fromNormalization ≫ c ≫ S ↘ Spec (.of e)) ∧
      IsProper (Y.fromNormalization ≫ c) ∧ Surjective (Y.fromNormalization ≫ c) ∧
      (∃ (A : Y.normalization.Opens) (W : S.Opens) (a : A.toScheme ≅ W.toScheme),
        Dense (A : Set Y.normalization) ∧ Dense (W : Set S) ∧
        a.hom ≫ W.ι = A.ι ≫ Y.fromNormalization ≫ c) ∧
      c (genericPoint Y) = genericPoint S ∧ IsIso (c.stalkMap (genericPoint Y)) ∧
      Y.fromNormalization (genericPoint Y.normalization) = genericPoint Y ∧
      IsIso (Y.fromNormalization.stalkMap (genericPoint Y.normalization)) ∧
      (Y.fromNormalization ≫ c) (genericPoint Y.normalization) = genericPoint S ∧
      IsIso ((Y.fromNormalization ≫ c).stalkMap (genericPoint Y.normalization)) := by
  sorry

end AlgebraicGeometry
