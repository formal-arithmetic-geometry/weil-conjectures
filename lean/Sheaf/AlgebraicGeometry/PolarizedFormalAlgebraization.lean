/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraKernelImageIdeal
import WeilConjectures.AlgebraicGeometry.GradedSerreVanishing
import Sheaf.TraceFormula.SchemeRelativeAmpleAffineCover
import Sheaf.AlgebraicGeometry.RelativeAmpleVeryAmple
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives
import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre
import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.AlgebraicGeometry.FiniteThickeningCartesian
import Sheaf.Paper.AlgebraizeFiniteOverProper
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ModuleSupportProperOverBase
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import Sheaf.AlgebraicGeometry.GrothendieckExistence
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible

/-! # Algebraization of polarized formal schemes

Source: Stacks Project, coherent.tex, Tag 089A, theorem-algebraization;
Tag 0899, lemma-algebraize-formal-closed-subscheme.
(blueprint: lem-sfb-polarized-formal-algebraization).

The Lean index `n : ℕ` denotes the paper's positive index `n + 1`.
Scheme compatibility is expressed after projection to `Y`. Together with the
specified equations over the quotient bases, this is the full compatibility
in the fibre products, by their two-projection universal property.
The line-bundle equation uses the section-normalized pullback comparison.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A proper polarized formal scheme over a complete Noetherian ring algebraizes,
including its prescribed polarization, compatibly at every infinitesimal stage.
The algebraization is projective in the finite-projective-space convention.
Source: Stacks Project, Tag 089A, theorem-algebraization; the embedding is constructed
using Tag 0899, lemma-algebraize-formal-closed-subscheme.
(blueprint: lem-sfb-polarized-formal-algebraization).

Proof plan, following the ten steps of the DAG node:

1. For $m<n$, compose the given cartesian squares to identify $X_m$ with the closed subscheme of
$X_n$ cut out by $I^m\mathcal O_{X_n}$. This uses the affine quotient description of a closed
immersion and base change. Its ideal is nilpotent, so all levels have the same underlying space
and residue fields. For properness reflection substitute the ring $A/I^n$, ideal $J=I/I^n$,
exponent $N=n$, and morphism $X_n\to S_n$. Here $J^n=0$ and its base change along
$\operatorname{Spec}((A/I^n)/J)=S_1$ is $X_1\to S_1$ by the cartesian identifications. The
reverse implication of the cited node therefore makes $X_n\to S_n$ proper; it assumes no prior
finite type or flatness. Every $A/I^n$ is Noetherian: ideals lift to ideals of $A$, whose finite
generating sets descend. Hence every $X_n$ is Noetherian.
Dependencies: def-pc-fibre-product, def-weil-closed-immersion, lem-weil-pbc-proper-fp-
permanence, lem-sfb-proper-nilpotent-base-change-reflection, def-weil-pbc-noetherian-ring, lem-
weil-pbc-finite-type-over-noetherian.

2. Put $F_0=\mathcal O_{X_1}$ and, for $r\ge1$, put $F_r=\ker(\mathcal O_{X_{r+1}}\to\mathcal
O_{X_r})=I^r\mathcal O_{X_{r+1}}$. All are sheaves on the common underlying space. For $m>r$,
the quotient $I^r\mathcal O_{X_m}/I^{r+1}\mathcal O_{X_m}$ is canonically $F_r$, since $\mathcal
O_{X_{r+1}}=\mathcal O_{X_m}/I^{r+1}\mathcal O_{X_m}$. Multiplication in any level $m>r+s$
therefore induces $F_r\otimes F_s\to F_{r+s}$, independent of $m$. Let
$B=\bigoplus_{r\ge0}I^r/I^{r+1}$. A finite set of generators $a_i$ of $I$ gives degree-one
generators $\bar a_i$ of $B$ over $A/I$: monomials generate every ideal power. Thus $B$ is a
finite type graded algebra. The action maps give a surjection $(X_1\to S_1)^*\widetilde
B\to\bigoplus_rF_r$, since every local section of $I^r\mathcal O$ is a sum of scalar ideal
generators times local coefficients. The kernel ideals and their quotients are quasi-coherent,
so $\bigoplus_rF_r$ is a finite type graded quasi-coherent module over this pulled-back algebra
(generated by $1$ in degree zero).
Dependencies: def-pc-module-pullback, def-weil-pbc-noetherian-ring, lem-weil-pbc-quasi-coherent-
algebra-kernel-image-ideal.

3. Apply graded Serre vanishing on the proper scheme $X_1$ over the Noetherian ring $A/I$, to
$B$, $\bigoplus_rF_r$ and the ample line $L_1$. Choose $d_0$ so its positive cohomology vanishes
after twisting by every $d\ge d_0$. Each $F_r$ is a graded direct summand, so its $H^1$ is a
retract of this zero group. Hence $H^1(X_1,F_r\otimes L_1^{\otimes d})=0$ for every $r$ and
every $d\ge d_0$, with one bound independent of $r$.
Dependencies: lem-weil-pbc-formal-systems-graded-vanishing.

4. Apply the relative-ampleness affine-cover criterion to $h:X_1\to S_1$, $N=L_1$, and the
single affine open $U=S_1$. Properness makes $h$ quasi-compact, and $h^{-1}(U)=X_1$, where $L_1$
is ample by hypothesis. Thus $L_1|_{h^{-1}(V)}$ is ample for every affine open $V\subseteq S_1$,
so $L_1$ is $h$-ample. The morphism $h$ is also of finite type and its affine target $S_1$ is
quasi-compact. The common-very-ample-power theorem therefore gives an integer $d_1$ such that
$L_1^{\otimes d}$ is relatively very ample for every $d\ge d_1$. Choose $d\ge\max(1,d_0,d_1)$.
The finite-coordinate-sections theorem over $S_1$ gives finitely many generating sections
$s_{0,1},\ldots,s_{N,1}$ of $L_1^{\otimes d}$, an immersion $\psi_1:X_1\to\mathbf P^N_{S_1}$,
and its quotient-compatible identification $\psi_1^*\mathcal O(1)\cong L_1^{\otimes d}$.
Projective space is proper, hence separated over $S_1$. Properness of $X_1\to S_1$ then makes
$\psi_1$ proper by the proper-to-separated theorem. A proper immersion is closed, so $\psi_1$ is
a closed immersion.
Dependencies: lem-trf-scheme-relative-ample-affine-cover, lem-trf-relative-ample-very-ample,
lem-sfb-very-ample-affine-finite-sections, lemma-nagata-projective-space-base-change-proper,
lem-weil-pbc-proper-over-separated, lem-weil-pbc-proper-immersion-closed.

5. Tensor $0\to F_r\to\mathcal O_{X_{r+1}}\to\mathcal O_{X_r}\to0$ by $L_{r+1}^{\otimes d}$.
This is exact: on an open trivializing the line it is the original sequence. The prescribed
$\varphi_r$ identify the quotient with $L_r^{\otimes d}$ and the kernel with the pushforward of
$F_r\otimes L_1^{\otimes d}$, since $IF_r=0$. The module $F_r\otimes L_1^{\otimes d}$ is quasi-
coherent of finite type on the Noetherian scheme $X_1$, hence coherent by the Noetherian
coherence criterion. Closed-immersion cohomology identifies its $H^1$ with the zero group of
step 3. The long exact sequence for global sections therefore makes
$\Gamma(X_{r+1},L_{r+1}^{\otimes d})\to\Gamma(X_r,L_r^{\otimes d})$ surjective. Starting at the
sections of step 4, lift the finite tuple at each successive level. This constructs $s_{i,r+1}$
with $\varphi_r^{\otimes d}(i_r^*s_{i,r+1})=s_{i,r}$.
Dependencies: def-sc-invertible-module, lem-weil-pbc-invertible-pullback-tensor, lem-pc-closed-
immersion-coherent-cohomology, lem-sc-ringed-space-module-sheaves-enough-injectives, def-sc-
ringed-space-module-cohomology, lem-weil-pbc-derived-functor-long-exact, pqf-lem-coherent-ft-
locnoeth.

6. At every point $x$ of $X_r$, the lifted sections have the same residue-field values as their
generating tuple on $X_1$: by the fibre formula $(e^*\mathcal L)(x)=\mathcal
L(e(x))\otimes\kappa(x)$, $(e^*s)(x)=s(e(x))\otimes1$ for the nilpotent closed immersion
$e:X_1\to X_r$, a homeomorphism with $\kappa(x)=\kappa(e(x))$, applied to $e^*s_{i,r}\cong
s_{i,1}$. They generate $L_r^{\otimes d}$ by the fibre criterion. The projective-space functor
of points thus gives $\psi_r:X_r\to P_r=\mathbf P^N_{S_r}$ with its section-normalized
identification $\psi_r^*\mathcal O(1)\cong L_r^{\otimes d}$. Its pullback compatibility gives
$\psi_{r+1}i_r=\iota_r\psi_r$, because the associated pairs are identified by
$\varphi_r^{\otimes d}$. The resulting squares are cartesian: $P_r=P_{r+1}\times_{S_{r+1}}S_r$,
and pulling back $\psi_{r+1}$ gives precisely $X_{r+1}\times_{S_{r+1}}S_r=X_r$.
Dependencies: lem-weil-pbc-invertible-generating-sections-fibre, lem-weil-pbc-projective-space-
functor-of-points, def-weil-pbc-morphism-to-projective-space-by-sections, def-pc-fibre-product,
lem-weil-pbc-invertible-pullback-tensor.

7. Base change of $\psi_r$ to the finite order thickening $P_1\subset P_r$ is $\psi_1$. A closed
immersion is finite, and finite-morphism reflection across a finite order thickening therefore
makes every $\psi_r$ finite. Apply finite formal-scheme algebraization to the fixed ambient
$P=\mathbf P^N_A$ and the cartesian squares of step 6 (shifting its indices by one). The ambient
scheme is proper over $S$, hence separated and finite type. We obtain a finite morphism $j:Y\to
P$, a proper morphism $Y\to S$, and compatible isomorphisms $a_r:X_r\cong Y\times_SS_r$ over
$P_r$.
Dependencies: def-sbc-first-order-thickening, lem-weil-pbc-closed-immersion-integral-separated-
uc, lem-weil-pbc-thickening-finite-cartesian, lem-weil-pbc-algebraize-finite-over-proper, lemma-
nagata-projective-space-base-change-proper, def-weil-proper-morphism.

8. The morphism $j$ is closed, not merely finite. Both $P$ and $Y$ are Noetherian since they are
proper over the Noetherian affine base. Finite pushforward makes $E=j_*\mathcal O_Y$ coherent,
and the coherent cokernel theorem makes $Q=\operatorname{coker}(\mathcal O_P\to E)$ coherent. On
an affine open $\operatorname{Spec}R\subset P$, write its finite inverse image as
$\operatorname{Spec}C$. Reduction of $E$ modulo $I^r$ is the module $C/I^rC$, so it is the
direct image of $\mathcal O_{X_r}$ under $\psi_r$. Right exactness of tensor (quotienting a
presentation) identifies $Q/I^rQ$ with the cokernel of the reduced algebra map. This map is
surjective: $\psi_r$ is a closed immersion by the following two-line calculation. The finite
algebra map on any affine open of $P_r$ is surjective modulo the nilpotent ideal $J$ defining
$P_1$; its module cokernel $V$ satisfies $V=JV=J^rV=0$. Thus all restrictions of $Q$ vanish.
Every coherent module on proper $P$ has proper support; Grothendieck-existence faithfulness then
sends $1_Q$ to zero at every level, hence $1_Q=0$ and $Q=0$. Thus $\mathcal O_P\to j_*\mathcal
O_Y$ is a surjective map of quasi-coherent algebras; its image on an affine open
$\operatorname{Spec}R$ is the image of $R\to C$, so $R\to C$ is surjective. Since $j$ is finite
and hence affine, the affine surjective-ring-map criterion proves $j$ a closed immersion.
Together with properness of $Y$ this proves the required projectivity.
Dependencies: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-finite-pushforward-
coherent, lem-weil-pbc-coherent-kernel-cokernel-locnoeth, lem-weil-pbc-finite-morphism-
permanence, def-weil-closed-immersion, lem-weil-pbc-module-support-proper-over-base, lem-weil-
pbc-closed-subset-proper-over-base-properties, prop-weil-pbc-grothendieck-existence, def-kun-
projective, lem-weil-pbc-quasi-coherent-algebra-kernel-image-ideal.

9. Use $a_r$ to view $(L_r,\varphi_r)$ as coherent modules on the thickenings of $Y$. The scheme
$Y$ is Noetherian by step 8. They are coherent because they are locally free of rank one on
Noetherian schemes. Apply Grothendieck existence (with index shifted from $r\ge1$ to $r-1\ge0$)
to obtain a coherent module $M$ on $Y$ and compatible isomorphisms $b_r:M|_{X_r}\cong L_r$.
Apply it also to the compatible dual lines $L_r^\vee$ to obtain $D$ with compatible dual
identifications. The restriction comparisons for tensor products identify $(M\otimes D)|_{X_r}$
with $L_r\otimes L_r^\vee\cong\mathcal O_{X_r}$. The module $M\otimes D$ is coherent: tensor
preserves quasi-coherence, and finite local generating sets tensor to a finite generating set;
apply the Noetherian coherence criterion. All coherent modules on the proper scheme $Y$ have
closed support, proper by closed-subset permanence. Full faithfulness of existence lifts these
compatible evaluation isomorphisms and their inverses, and faithfulness makes their composites
identities. Thus $M\otimes D\cong\mathcal O_Y$, so $M$ is invertible. Put $L=M$.
Dependencies: prop-weil-pbc-grothendieck-existence, pqf-lem-coherent-ft-locnoeth, lem-pc-tensor-
dual-invertible, lem-weil-pbc-module-pullback-tensor, lem-weil-pbc-quasi-coherent-tensor-
product-affine-sections, def-sc-invertible-module, lem-weil-pbc-module-support-proper-over-base,
lem-weil-pbc-closed-subset-proper-over-base-properties.

10. Put $H=j^*\mathcal O_{\mathbf P^N_A}(1)$, ample by the projective-ample theorem. The
section-normalized identifications of step 6 and the fact that $a_r$ is over $P_r$ give
isomorphisms $H|_{X_r}\cong L_r^{\otimes d}$ compatible with restriction. The $b_r^{\otimes d}$
identify the same system with $L^{\otimes d}|_{X_r}$. Full faithfulness of Grothendieck
existence lifts the resulting compatible isomorphisms and inverses to $H\cong L^{\otimes d}$.
Hence $L$ is ample directly from its definition: any affine nonvanishing locus $Y_s$ of a
section of $H^{\otimes k}$ is the same locus for the transported section of $L^{\otimes dk}$,
with $dk>0$. Quasi-compactness is unchanged. Finally the compatibility equations for the $a_r$
are those of the algebraized closed-subscheme system, and those for the $b_r$ are exactly the
equations supplied by Grothendieck existence. They are the two equations in the item, including
the specified $\varphi_r$.
Dependencies: lem-weil-pbc-projective-ample-invertible, prop-weil-pbc-grothendieck-existence,
lem-weil-pbc-invertible-pullback-tensor, def-weil-pbc-ample-invertible-module.

In the conclusion, `hcompat` identifies the two maps `X n ⟶ Y`. The source of the
left side of the final equation is pullback along `i n ≫ (a (n+1)).hom ≫ fst`.
The section-normalized comparison followed by pullback of `b (n+1)` and `φ n`
must equal transport along `hcompat n` followed by `b n`. Thus the specified
transition isomorphisms, rather than only their isomorphism classes, are recovered.
-/
theorem polarized_formal_algebraization
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    (X : ℕ → Scheme.{u})
    (f : ∀ n : ℕ, X n ⟶ Spec (.of (A ⧸ I ^ (n + 1))))
    (i : ∀ n : ℕ, X n ⟶ X (n + 1))
    (hcart : ∀ n : ℕ, IsPullback (i n) (f n) (f (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1)))))))
    [IsProper (f 0)]
    (L : ∀ n : ℕ, (X n).Modules) [∀ n : ℕ, (L n).IsInvertible]
    (φ : ∀ n : ℕ, (Scheme.Modules.tensorPullback (i n)).obj (L (n + 1)) ≅ L n)
    (hample : Scheme.Modules.IsAmple (X 0) (L 0)) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of A)),
      IsProper g ∧ IsHProjective g ∧
      ∃ (M : Y.Modules) (hM : M.IsInvertible),
        @Scheme.Modules.IsAmple Y M hM ∧
        ∃ a : ∀ n : ℕ, X n ≅ pullback g
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))),
          (∀ n : ℕ, (a n).hom ≫ pullback.snd g
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) = f n) ∧
          ∃ hcompat : ∀ n : ℕ,
              i n ≫ ((a (n + 1)).hom ≫ pullback.fst g
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) =
              (a n).hom ≫ pullback.fst g
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))),
            ∃ b : ∀ n : ℕ,
                (Scheme.Modules.tensorPullback ((a n).hom ≫ pullback.fst g
                  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj M ≅
                L n,
              ∀ n : ℕ,
                (Scheme.Modules.tensorPullbackSectionComp (i n)
                  ((a (n + 1)).hom ≫ pullback.fst g
                    (Spec.map (CommRingCat.ofHom
                      (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).hom.app M ≫
                  (Scheme.Modules.tensorPullback (i n)).map (b (n + 1)).hom ≫ (φ n).hom =
                (eqToIso (congrArg
                  (fun k : X n ⟶ Y ↦ (Scheme.Modules.tensorPullback k).obj M)
                  (hcompat n))).hom ≫ (b n).hom := by
  sorry

end AlgebraicGeometry
