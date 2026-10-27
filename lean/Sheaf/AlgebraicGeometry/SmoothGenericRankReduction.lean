/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.Blowup.AdmissibleBlowup
public import Sheaf.AlgebraicGeometry.ModuleStrictTransform
public import WeilConjectures.AlgebraicGeometry.FiniteTypeIdealModule
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.GenericFreeBlowup
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.ModuleAdmissibleBlowupCalculus
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Sheaf.RingTheory.FreeSubtractionFlatness
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import Mathlib.Algebra.Module.LocalizedModule.Exact
import WeilConjectures.AlgebraicGeometry.ModuleFinitePresentationCokernel
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportPullback
import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Generic free subtraction with smaller fibre support

Source: Stacks Project, More on Flatness, Tag 0815, `theorem-flatten-module`,
third proof paragraph; Tag 0811, `lemma-flatten-module-pre`
(blueprint: lem-trf-smooth-generic-rank-reduction).

The existential names `g`, `G` and `Ua` are fixed by equalities to the restricted
base-changed family, its strict-transform module and the preserved open, respectively.
The open inverse image model of `X_a` is canonically the base change to the affine chart.
The strict inequality on support dimension includes the empty-support convention and
forces zero fibre modules in relative dimension zero.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- On finitely many affine charts of an admissible blowup, subtract a finite free
module universally exactly, leaving a cokernel with smaller fibre support.
Source: Stacks Project, Tag 0815, `theorem-flatten-module`, third proof paragraph,
and Tag 0811, `lemma-flatten-module-pre`
(blueprint: lem-trf-smooth-generic-rank-reduction).

Proof (the DAG node's steps):
1. First apply [lem-pc-smooth-flat]: $f$ is flat and locally of finite presentation. Since $S$ is
   affine and $X\to S$ is affine, $X$ is affine. The affine finite-presentation criterion
   [lem-weil-pbc-lfp-affine-opens-finite-presentation] makes $f$ finitely presented. The original
   flatness over $U$ holds in particular at all fibre generic points over $U$. Thus every
   hypothesis of [lem-trf-generic-free-blowup] holds, and it supplies a $U$-admissible blowup
   $b:T\to S$ and an open $V\subset X_T$ surjecting onto $T$ on which $\mathcal G=\mathcal F^b$ is
   finite locally free. Keep its specified centre ideal throughout.

2. By [lem-trf-generic-rank-admissible-invariance], applied to the same original family and this
   one blowup, $T$ is quasi-compact and quasi-separated, $X_T\to T$ is affine flat of finite
   presentation with geometrically integral fibres, and $\mathcal G$ is quasi-coherent of finite
   type. Over $U_T=b^{-1}U$ it identifies with the original module over $U$, hence is finitely
   presented and flat there. Also $U_T\cong U$ by [lemma-nagata-admissible-blowup-over-open], so
   $U_T$ is quasi-compact. By [lem-sbc-smooth-relative-dimension-permanence](1), $X_T\to T$ is
   smooth of relative dimension $n$. No flattening theorem is being invoked here: only the
   preliminary generic-free blowup of Step 1.

3. Fix $t\in T$ and take an affine neighbourhood $A\subset T$ using
   [lem-weil-pbc-affine-opens-basis]. Write $X_A=\operatorname{Spec}B$ and $N=\Gamma(X_A,\mathcal
   G)$. By [lem-weil-pbc-quasi-coherent-finite-type-affine], $N$ has a finite generating list. Let
   $\xi$ be the generic point of the integral fibre $(X_A)_t$. The nonempty open $V_t$ contains
   $\xi$. By [lem-sbc-affine-module-germ-localization], the images of the generators of $N$ span
   $\mathcal G_\xi\otimes\kappa(\xi)$. Choose a subset forming a basis, of size $r$; send the
   standard basis to these global sections, using the affine sheaf-module adjunction
   [lem-weil-pbc-affine-tilde-gamma-adjunction], defining $\alpha:\mathcal O_{X_A}^{\oplus
   r}\to\mathcal G|_{X_A}$. Shrink a trivializing open inside $V$ about $\xi$ so its rank is $r$.
   In these frames $\alpha$ is a square matrix whose determinant is nonzero in $\kappa(\xi)$,
   hence is a unit in the local ring at $\xi$. The open where that determinant is invertible is an
   open $W\subset X_A$ containing $\xi$ on which $\alpha$ is an isomorphism. If $r=0$, the
   trivialization is already the zero module and the same conclusion holds.

4. The smooth map $X_A\to A$ is flat and locally of finite presentation by [lem-pc-smooth-flat],
   so [lem-weil-pbc-flat-lfp-open] makes the image of $W$ an open neighbourhood of $t$. Choose an
   affine neighbourhood $T_t$ of $t$ inside that image by [lem-weil-pbc-affine-opens-basis].
   Replace $W$ by its inverse image over $T_t$; it now surjects onto $T_t$. Perform this
   construction for every $t$. Quasi-compactness of $T$ selects finitely many of these affine
   opens, denoted $T_a$, with their maps $\alpha_a$, ranks $r_a$, and opens $W_a$. Restricting the
   base-changed family preserves all properties of Step 2; in particular smoothness of relative
   dimension $n$ follows again from [lem-sbc-smooth-relative-dimension-permanence](1).

5. For each $a$, $U_a=T_a\cap U_T$ is quasi-compact. Indeed cover the quasi-compact open $U_T$ by
   finitely many affine opens of $T$ using [lem-weil-pbc-affine-opens-basis]. Their intersections
   with $T_a$ are quasi-compact by [lem-weil-pbc-quasi-separated-affine-cover-criterion](1), since
   $T$ is quasi-separated, and their finite union is $U_a$. The restrictions of $\mathcal G$ to
   $X_a$ are quasi-coherent of finite type, and their restrictions over $U_a$ are finitely
   presented and flat, by Step 2.

6. Fix $a$ and write $T_a=\operatorname{Spec}R$, $X_a=\operatorname{Spec}B$,
   $N=\Gamma(X_a,\mathcal F_a)$. By [lem-weil-pbc-flat-morphism-affine-criterion] and
   [lem-weil-pbc-lfp-affine-opens-finite-presentation], $R\to B$ is flat and finitely presented;
   $N$ is finite by [lem-weil-pbc-quasi-coherent-finite-type-affine]. For every prime of $R$, its
   fibre is integral and its generic point lies in $W_a$, since $(W_a)_t$ is nonempty open in that
   integral fibre. There $\alpha_a$ is an isomorphism, and $\mathcal F_a$ is free over $\mathcal
   O_{X_a}$, hence flat over the base because $X_a\to T_a$ is flat. In the affine stalk
   identifications of [lem-sbc-affine-module-germ-localization], these are exactly the
   generic-stalk flatness and residue-field-isomorphism hypotheses of
   [lem-trf-free-subtraction-flatness]. That node therefore makes $B^{\oplus r_a}\to N$
   universally injective over $R$, and gives the equivalence of relative flatness of $N$ and its
   cokernel at every stalk.

7. Set $\mathcal H_a=\operatorname{coker}\alpha_a$. By
   [lem-weil-pbc-quasi-coherent-module-cokernel-image] it is quasi-coherent, and its affine module
   is $Q=N/\operatorname{im}\alpha_a$; the images of finitely many generators of $N$ generate $Q$,
   so it is of finite type. For an arbitrary $T'\to T_a$, work on each affine open
   $\operatorname{Spec}R'\subset T'$. Use [lem-weil-pbc-affine-tilde-gamma-adjunction] to identify
   the original quasi-coherent modules with their affine section modules, and
   [lem-weil-pbc-tilde-pullback-base-change] to identify their tensor pullbacks. The pulled-back
   sequence is associated to $0\to R'\otimes_R B^{\oplus r_a}\to R'\otimes_R N\to R'\otimes_R
   Q\to0$. Its left map is injective by Step 6, taking the $R$-module $L=R'$; the remaining
   exactness follows from the quotient presentation of $Q$. Localization preserves this module
   exactness by [lem-weil-pbc-localization-module-exact], so it is exact on every stalk and hence
   as a sheaf sequence on this affine cover and hence on $X_a\times_{T_a}T'$. This proves the
   asserted universal exactness, including the original sequence by $R'=R$.

8. At each point lying over $U_a$, $\mathcal F_a$ is flat over $U_a$ by Step 2. The stalkwise
   flatness equivalence in [lem-trf-free-subtraction-flatness] therefore proves that $\mathcal
   H_a|_{X_{U_a}}$ is flat over $U_a$. On that open $\mathcal O^{\oplus r_a}$ is of finite type
   and $\mathcal F_a$ is of finite presentation. Thus
   [lem-weil-pbc-module-finite-presentation-cokernel] makes $\mathcal H_a|_{X_{U_a}}$ finitely
   presented. Neither conclusion requires global finite presentation of $\mathcal F_a$.

9. For $t\in T_a$, the fibre of $\mathcal H_a$ is finite type with closed support
   $Z_t\subset(X_a)_t$, by [lem-weil-pbc-support-pullback-finite-type]. It vanishes on the
   nonempty open $(W_a)_t$ because $\alpha_a$ is an isomorphism there. Thus $Z_t$ is a proper
   closed subset of the integral fibre. By [def-sbc-smooth-morphisms], $\dim_x((X_a)_t)=n$ for
   every $x\in(X_a)_t$, with $\dim_x$ as in [def-kun-dimension]. For any chain of nonempty
   irreducible closed subsets $Z_0\subsetneq\cdots\subsetneq Z_k$ in $Z_t$, the same subsets are
   closed in $(X_a)_t$, and appending the irreducible closed set $(X_a)_t$ gives a chain of length
   $k+1$ in $(X_a)_t$. Pick $x\in Z_0$ and an open $O\ni x$ of $(X_a)_t$. Each member of the chain
   is irreducible and meets $O$, so its intersection with $O$ is a nonempty open, hence
   irreducible and dense, subset of it; the intersections form a chain of irreducible closed
   subsets of $O$, strict because their closures are the original members. Thus $\dim O\ge k+1$
   for every such $O$, so $k+1\le\dim_x((X_a)_t)=n$ [def-kun-topological-krull-dimension]. Hence
   $\dim Z_t\le n-1$ if $Z_t$ is nonempty. If $n=0$, a nonempty $Z_t$ would already give a chain
   of length one, a contradiction, so the fibre sheaf is zero. Assigning empty support dimension
   $-1$, the bound holds for every $t$. If $T$ is empty take the empty finite cover; rank zero and
   empty $U$ impose no additional conditions. This completes all clauses. -/
theorem exists_admissibleBlowup_smooth_genericRankReduction
    {X S : Scheme.{u}} [IsAffine S] (n : ℕ)
    (f : X ⟶ S) [IsAffineHom f] [SmoothOfRelativeDimension n f]
    [GeometricallyIntegral f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (U : S.Opens) (hU : IsCompact (U : Set S))
    (hfp : (F.restrict (f ⁻¹ᵁ U).ι).IsFinitePresentation)
    (hflat : (F.restrict (f ⁻¹ᵁ U).ι).IsFlatOver (f ∣_ U)) :
    ∃ (B : IsAdmissible S U) (m : ℕ) (V : Fin m → B.I.blowup.Opens),
      (⨆ a, V a) = ⊤ ∧ (∀ a : Fin m, IsAffineOpen (V a)) ∧
      ∀ a : Fin m,
        ∃ (g : ((pullback.snd f B.I.blowupMap) ⁻¹ᵁ V a).toScheme ⟶ (V a).toScheme)
          (G : ((pullback.snd f B.I.blowupMap) ⁻¹ᵁ V a).toScheme.Modules)
          (Ua : (V a).toScheme.Opens),
          g = (pullback.snd f B.I.blowupMap) ∣_ V a ∧
          G = (@moduleStrictTransform X S f B.I
            (B.I.isFiniteType_toModules_sheaf B.finiteType) F inferInstance).restrict
              ((pullback.snd f B.I.blowupMap) ⁻¹ᵁ V a).ι ∧
          Ua = (V a).ι ⁻¹ᵁ (B.I.blowupMap ⁻¹ᵁ U) ∧
          IsAffineHom g ∧ SmoothOfRelativeDimension n g ∧ GeometricallyIntegral g ∧
          IsCompact (Ua : Set (V a).toScheme) ∧ G.IsQuasicoherent ∧ G.IsFiniteType ∧
          (G.restrict (g ⁻¹ᵁ Ua).ι).IsFinitePresentation ∧
          (G.restrict (g ⁻¹ᵁ Ua).ι).IsFlatOver (g ∣_ Ua) ∧
          ∃ (r : ℕ)
            (α : SheafOfModules.free
              (R := ((pullback.snd f B.I.blowupMap) ⁻¹ᵁ V a).toScheme.ringCatSheaf)
                (ULift.{u} (Fin r)) ⟶ G)
            (W : ((pullback.snd f B.I.blowupMap) ⁻¹ᵁ V a).toScheme.Opens),
            Surjective (W.ι ≫ g) ∧ IsIso ((restrictFunctor W.ι).map α) ∧
            (ShortComplex.mk α (cokernel.π α) (cokernel.condition α)).ShortExact ∧
            (∀ (T' : Scheme.{u}) (t' : T' ⟶ (V a).toScheme),
              ∃ w : (tensorPullback (pullback.fst g t')).map α ≫
                  (tensorPullback (pullback.fst g t')).map (cokernel.π α) = 0,
                (ShortComplex.mk ((tensorPullback (pullback.fst g t')).map α)
                  ((tensorPullback (pullback.fst g t')).map (cokernel.π α)) w).ShortExact) ∧
            (cokernel α).IsQuasicoherent ∧ (cokernel α).IsFiniteType ∧
            ((restrictFunctor (g ⁻¹ᵁ Ua).ι).obj (cokernel α)).IsFinitePresentation ∧
            ((restrictFunctor (g ⁻¹ᵁ Ua).ι).obj (cokernel α)).IsFlatOver (g ∣_ Ua) ∧
            (∀ t : (V a).toScheme,
              topologicalKrullDim {x : g.fiber t |
                ¬ Subsingleton (((tensorPullback (g.fiberι t)).obj
                  (cokernel α)).presheaf.stalk x)} < (n : WithBot ℕ∞)) ∧
            (n = 0 → ∀ t : (V a).toScheme,
              IsZero ((tensorPullback (g.fiberι t)).obj (cokernel α))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
