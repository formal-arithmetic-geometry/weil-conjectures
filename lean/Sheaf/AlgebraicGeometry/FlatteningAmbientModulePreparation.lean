/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q77
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Topology.ClosedPushforwardAbelianStalks
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Ambient modules for finite-type affine pieces

Source: Stacks Project, `flat.tex`, Tag 081R, proof of
`lemma-flat-after-blowing-up`, affine-cover and ambient-module paragraphs;
`morphisms.tex`, Tag 02FV, `lemma-finite-presentation-permanence`
(blueprint: lem-trf-flattening-ambient-module-preparation).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- A finite-type morphism over a qcqs base has finitely many affine pieces with
closed embeddings into quasi-compact opens of relative affine spaces. The direct
images of their structure modules are quasi-coherent of finite type, and their
restrictions over the good open are finitely presented and flat over that open.

Here the inverse-image open of the ambient projection is the canonical open
model of its fibre product with `U`. `Modules.pushforward` applied to
`SheafOfModules.unit` has exactly the sections and scalar action specified by
Tag 081R. The finite index set `Fin r` allows `r = 0`.

Source: Stacks Project, `flat.tex`, Tag 081R, proof of
`lemma-flat-after-blowing-up`; `morphisms.tex`, Tags 01QO and 02FV
(blueprint: lem-trf-flattening-ambient-module-preparation).

Proof:

1. Choose a finite affine open cover $T=\bigcup_a B_a$ by
[lem-weil-pbc-qcqs-finite-affine-open-cover]. By the finite-type hypothesis and
[def-weil-finite-type-morphism], each $g^{-1}(B_a)$ has a finite affine open cover
$W_{ab}=\operatorname{Spec}C_{ab}$ with $C_{ab}$ a finitely generated algebra over
$A_a=\Gamma(B_a,\mathcal O_T)$. The finitely many $W_{ab}$ cover $W$; reindex them by $i$. In
particular, each $W_i$ maps into a selected affine open $B_{a(i)}$ of $T$. If $W$ is empty, take
the empty family and all assertions are vacuous.

2. For each $i$, choose algebra generators $c_1,\ldots,c_{n_i}$ of $C_i$ over $A_{a(i)}$,
allowing $n_i=0$. The surjection $A_{a(i)}[t_1,\ldots,t_{n_i}]\twoheadrightarrow C_i$,
$t_j\mapsto c_j$, defines a closed immersion $j_i:W_i\hookrightarrow
V_i:=\operatorname{Spec}(A_{a(i)}[t_1,\ldots,t_{n_i}])$ over $B_{a(i)}$, hence over $T$, by
[def-weil-closed-immersion, def-weil-affine-spectrum]. The affine chart description in
[def-nagata-relative-affine-space] identifies $V_i$ with the inverse image of $B_{a(i)}$ in
$\mathbb A_T^{n_i}$, an open subscheme. Thus these choices give the required immersion and
ambient open, with $V_i$ affine and therefore quasi-compact by
[lem-weil-pbc-affine-scheme-qcqs].

3. The projection $V_i=\mathbb A_{B_{a(i)}}^{n_i}\to B_{a(i)}$ is locally of finite presentation
by [sbc-lem-affine-space-smooth, def-sbc-smooth-morphisms]. The open immersion
$B_{a(i)}\hookrightarrow T$ is locally of finite presentation by
[lem-weil-pbc-open-immersion-etale, def-weil-etale-morphism]. Their composite $p_i:V_i\to T$ is
locally of finite presentation by [lem-sbc-locally-finite-presentation-composition]. As $V_i$ is
quasi-compact and $T$ is quasi-separated, [lem-weil-pbc-qcqs-morphism-permanence](1) shows $p_i$
is quasi-compact. These are the two required properties of the ambient morphism.

4. Set $\mathcal F_i=(j_i)_*\mathcal O_{W_i}$ with the section and scalar maps in the statement.
The closed-immersion description in [def-weil-closed-immersion] makes $j_i$ affine; hence
[lem-weil-pbc-affine-morphism-relative-spec](1) makes $\mathcal F_i$ quasi-coherent. On every
affine open $H=\operatorname{Spec}R\subseteq V_i$, that same closed-immersion description gives
$j_i^{-1}H=\operatorname{Spec}(R/I)$ and $\mathcal F_i(H)=R/I$. This module is generated by $1$
(or is zero). By [lem-weil-pbc-quasi-coherent-finite-type-affine](a), $\mathcal F_i|_H$ is of
finite type. Such opens cover $V_i$, so the definition gives finite type everywhere.

5. Write $V_{i,U}=V_i\times_T U$ and $W_{i,U}=W_i\times_T U$. By
[lem-weil-pbc-qcqs-morphism-permanence](3), $V_{i,U}\to U$ is locally of finite presentation; in
particular it is locally of finite type: for every affine open $V\subseteq U$, any affine open
cover of the inverse image of $V$ in $V_{i,U}$ consists of affine opens whose coordinate rings
are finitely presented, hence finitely generated, $\mathcal O_U(V)$-algebras by
[lem-weil-pbc-lfp-affine-opens-finite-presentation], which is the condition of
[def-weil-finite-type-morphism]. The scheme $W_{i,U}$ is the open subscheme of $W_U$
corresponding to $W_i\subseteq W$. Its inclusion in $W_U$ is locally of finite presentation by
[lem-weil-pbc-open-immersion-etale, def-weil-etale-morphism], so $W_{i,U}\to U$ is locally of
finite presentation by the hypothesis on $W_U$ and
[lem-sbc-locally-finite-presentation-composition]. Apply
[lem-a1-map-over-base-finite-presentation] with $S=U$, $X=W_{i,U}$, $Y=V_{i,U}$: the restricted
morphism $j_{i,U}$ is locally of finite presentation. It is still a closed immersion: on any
affine chart the restriction is the same quotient-ring description of $j_i$.

6. By [lem-weil-pbc-affine-morphism-relative-spec](4), $\mathcal
F_i|_{V_{i,U}}=(j_{i,U})_*\mathcal O_{W_{i,U}}$. On every affine open
$H=\operatorname{Spec}R\subseteq V_{i,U}$, the closed immersion has affine inverse image
$\operatorname{Spec}(R/I)$ by [def-weil-closed-immersion]. By step 5 and
[lem-weil-pbc-lfp-affine-opens-finite-presentation], $R/I$ is a finitely presented $R$-algebra.
Apply [lem-weil-pbc-finite-presentation-surjection-kernel-fg] with zero polynomial variables to
$R\twoheadrightarrow R/I$. It gives $I=(f_1,\ldots,f_m)$. Consequently $R^{m}\to R\to R/I\to0$,
with first map $(r_k)\mapsto\sum_k r_k f_k$, is a finite module presentation. The
quasi-coherence from step 4 and [lem-weil-pbc-quasi-coherent-finite-type-affine](b) give a
finite presentation of $\mathcal F_i$ on $H$. These opens cover $V_{i,U}$, proving the asserted
module finite presentation.

7. Finally apply the closed-subspace stalk formula [lem-sc-closed-pushforward-abelian-stalks] to
the underlying additive sheaf of $\mathcal O_{W_{i,U}}$. Off the closed image its direct-image
stalk is zero and hence flat. At $y=j_{i,U}(w)$ it is $\mathcal O_{W_{i,U},w}$. This
identification is compatible with $\mathcal O_{U,u}$-scalars, where $u=p_i(y)$: a germ $a$ on
$U$ acts on both sides by multiplication by its pulled-back germ at $w$, since $j_i$ is over
$T$. Open subschemes have the same local rings, so this is $\mathcal O_{W_U,w}$ as an $\mathcal
O_{U,u}$-module. It is flat by the assumed flatness of $W_U\to U$ and [def-weil-flat-morphism].
Thus every stalk is flat over its base local ring, exactly the stalk criterion in
[def-pc-scheme-module-flat-over]. This proves the final assertion for every $i$.
-/
theorem exists_flattening_ambient_module_preparation
    {T W : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    (U : T.Opens) (hU : IsCompact (U : Set T))
    (g : W ⟶ T) [LocallyOfFiniteType g] [QuasiCompact g]
    [Flat (pullback.snd g U.ι)] [LocallyOfFinitePresentation (pullback.snd g U.ι)] :
    ∃ (r : ℕ) (O : Fin r → W.Opens) (n : Fin r → ℕ)
      (V : ∀ i : Fin r, (AffineSpace (ULift.{u} (Fin (n i))) T).Opens)
      (j : ∀ i : Fin r, (O i).toScheme ⟶ (V i).toScheme),
      (⨆ i : Fin r, O i) = ⊤ ∧
      ∀ i : Fin r,
        IsAffineOpen (O i) ∧
        IsCompact (V i : Set (AffineSpace (ULift.{u} (Fin (n i))) T)) ∧
        IsClosedImmersion (j i) ∧
        j i ≫ ((V i).ι ≫ (AffineSpace (ULift.{u} (Fin (n i))) T ↘ T)) = (O i).ι ≫ g ∧
        QuasiCompact ((V i).ι ≫ (AffineSpace (ULift.{u} (Fin (n i))) T ↘ T)) ∧
        LocallyOfFinitePresentation ((V i).ι ≫
          (AffineSpace (ULift.{u} (Fin (n i))) T ↘ T)) ∧
        Scheme.Modules.IsQuasiCoherentFiniteType
          ((Scheme.Modules.pushforward (j i)).obj
            (SheafOfModules.unit (O i).toScheme.ringCatSheaf)) ∧
        SheafOfModules.IsFinitePresentation
          (((Scheme.Modules.pushforward (j i)).obj
            (SheafOfModules.unit (O i).toScheme.ringCatSheaf)).restrict
            (((V i).ι ≫ (AffineSpace (ULift.{u} (Fin (n i))) T ↘ T)) ⁻¹ᵁ U).ι) ∧
        Scheme.Modules.IsFlatOver
          (((Scheme.Modules.pushforward (j i)).obj
            (SheafOfModules.unit (O i).toScheme.ringCatSheaf)).restrict
            (((V i).ι ≫ (AffineSpace (ULift.{u} (Fin (n i))) T ↘ T)) ⁻¹ᵁ U).ι)
          (((V i).ι ≫ (AffineSpace (ULift.{u} (Fin (n i))) T ↘ T)) ∣_ U) := by
  sorry

end AlgebraicGeometry
