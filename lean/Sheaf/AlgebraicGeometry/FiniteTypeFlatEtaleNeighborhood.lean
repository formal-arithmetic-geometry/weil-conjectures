/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.TraceFormula.FlatAssociatedEquidimensional
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction

import Mathlib.RingTheory.Nakayama
import Sheaf.Topology.FiniteTypeSurjectiveNearStalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
import WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent
import Sheaf.TraceFormula.ElementaryModuleDevissage
import Sheaf.TraceFormula.ElementaryDevissageFinitePresentation
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType
import WeilConjectures.AlgebraicGeometry.AffinePushforwardBaseChange
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.FiniteStability
import WeilConjectures.AlgebraicGeometry.FinitePushforwardFiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.TraceFormula.LocalGenericBasisUniversalInjective
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.RingTheory.Unramified.LocalRing
import Sheaf.TraceFormula.ElementaryDevissageFlatness

/-!
# Finite-type flatness gives a finitely presented étale neighbourhood

Source: Stacks Project, `flat.tex`, Tag 05I5, proposition-finite-type-flat-at-point,
first proof (affine reduction and induction)
(blueprint: lem-trf-finite-type-flat-etale-neighborhood).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A finite-type quasi-coherent module flat at a point becomes finitely presented and flat
on an open neighbourhood after elementary étale base change and localization at its marked point.

Source: Stacks Project, `flat.tex`, Tag 05I5, `proposition-finite-type-flat-at-point`, first proof
(blueprint: lem-trf-finite-type-flat-etale-neighborhood).

Proof (the eleven DAG steps):

1. Restrict to affine neighbourhoods of $x$ and $s$. If $x\notin\operatorname{Supp}(\mathcal
   F_s)$, then $\mathcal F_x/\mathfrak m_s\mathcal F_x=0$. The stalk $\mathcal F_x$ is finite over
   the local ring $\mathcal O_{X,x}$, and $\mathfrak m_s\mathcal O_{X,x}$ is contained in its
   maximal ideal. Nakayama gives $\mathcal F_x=0$. Apply the surjective-on-stalk lemma to
   $0\to\mathcal F$: it is surjective on a neighbourhood, so $\mathcal F$ vanishes there. The
   identity neighbourhood of $S$ then works, since the zero module has an empty finite
   presentation and is flat. Otherwise put $n=\dim_x\operatorname{Supp}(\mathcal F_s)$ and use
   strong induction on $n\ge0$. This is finite: the affine fibre is of finite type over
   $\kappa(s)$, hence has finite dimension, and its support has dimension at most that of the
   fibre.
   Uses: lem-weil-pbc-nakayama-jacobson, lem-weil-pbc-module-finite-type-surjective-on-stalk, lem-
   kun-dimension-finite-type, def-kun-dimension.

2. Bookkeeping for local bases. One may replace a pointed base $(T,t)$ by
   $\operatorname{Spec}\mathcal O_{T,t}$ during the induction. Indeed this spectrum is the
   directed inverse limit of the affine open neighbourhoods of $t$, with affine transitions and
   all stages qcqs. An affine etale neighbourhood of finite presentation over that local spectrum
   descends to an etale scheme of finite presentation over one such open, by the object clause of
   etale finite-data descent. Its marked point has the same residue field as its image on that
   open, since the fibre at $t$ is unchanged by localization. Its local ring is the same as the
   marked local ring before descent. Thus a further elementary etale change of a local base is
   realized by an elementary etale change of the preceding scheme, with the same final local base.
   Composing these finitely many changes is etale by composition, and the residue-field
   isomorphisms compose. The neighbourhood in the conclusion only lives over the final local ring,
   so no spreading of the possibly non-finitely-presented sheaf is being asserted.
   Uses: lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods, lem-weil-pbc-etale-finite-data-
   descent, lem-weil-pbc-etale-composition-cancellation.

3. Apply elementary module devissage to $f,\mathcal F,x$ (locally finite presentation implies
   locally finite type). It gives affine $X',Z',Y',S'$, elementary etale $g,e$, a finitely
   presented closed immersion $i$, a finite map $\pi$ with singleton marked fibre, and $\mathcal
   G$ with $i_*\mathcal G=g^*\mathcal F$; $Y'\to S'$ is smooth with geometrically integral fibres
   of dimension $n$. Replace the base by $T=\operatorname{Spec}\mathcal O_{S',s'}$. The comparison
   $X'\to X\times_SS'$ is etale by cancellation between schemes etale over $X$, hence its base
   change to $T$ is etale. The other diagram properties persist: the defining closed-immersion
   ideal has finitely many generators, a finite algebra remains finite after tensor product, and
   the marked fibres are unchanged because $\kappa(s')$ is unchanged. Finite presentation of the
   affine structure maps survives tensor base change. Smoothness survives base change and
   geometric integrality is defined after arbitrary residue-field extension. Pullback preserves
   quasi-coherence and finite type, and affine pushforward commutes with this base change,
   preserving $i_*\mathcal G=g^*\mathcal F$ and identifying the base change of $\pi_*\mathcal G$
   with the new finite pushforward.
   Uses: lem-trf-elementary-module-devissage, lem-weil-pbc-etale-composition-cancellation, lem-
   weil-pbc-etale-scheme-base-change, lem-weil-pbc-module-pullback-quasi-coherent, lem-weil-pbc-
   module-pullback-finite-type, lem-weil-pbc-affine-pushforward-base-change, lem-weil-pbc-smooth-
   ring-map-base-change-composition, lem-weil-pbc-finite-presentation-base-change-composition.

4. The devissage flatness equivalence shows that the finite pushforward $\pi_*\mathcal G$ is flat
   at $y'$ over the local base; the finite-pushforward lemma makes it quasi-coherent of finite
   type. The devissage finite-presentation equivalence applies because $f$ is locally of finite
   presentation. Both equivalences concern properties on actual neighbourhoods, not merely finite
   presentation or flatness of an isolated stalk. They therefore reduce the desired conclusion to
   that for $\pi_*\mathcal G$ on $Y'$. The equivalences can also be applied after any further
   elementary etale base change followed by localization: the same affine diagram, singleton
   marked fibre and residue fields persist as in step 3. We are consequently reduced to
   $S=\operatorname{Spec}A$ local, $X=\operatorname{Spec}B$ smooth over $A$, with geometrically
   integral fibres of dimension $n$, and $\mathcal F=\widetilde N$ for a finite $B$-module. Write
   $\mathfrak m$ for the maximal ideal of $A$ and $\mathfrak q$ for $x$. Smoothness makes $A\to B$
   flat and finitely presented, and $N_{\mathfrak q}$ is $A$-flat.
   Uses: lem-trf-elementary-devissage-flatness, lem-trf-elementary-devissage-finite-presentation,
   lem-pc-f3-finite-pushforward-finite-type, lem-pc-smooth-flat, lem-weil-pbc-lfp-affine-opens-
   finite-presentation.

5. The integral closed fibre $\operatorname{Spec}(B/\mathfrak mB)$ has generic prime $\mathfrak
   p=\mathfrak mB$. The images of a finite generating list of $N$ span the finite-dimensional
   vector space $N\otimes_B\kappa(\mathfrak p)$. Select a basis from this spanning list and lift
   its elements by the corresponding generators of $N$. They define $\alpha:B^r\to N$ inducing an
   isomorphism at $\kappa(\mathfrak p)$; allow $r=0$ if that vector space is zero.

6. Apply the local generic-basis universal-injectivity criterion to $R=A$, $S=B$, $\xi=\mathfrak
   p$ and the chosen $\alpha$. Its hypotheses are exactly flat finite presentation with
   geometrically integral fibres, $\mathfrak q$ over $\mathfrak m$, finiteness of $N$, flatness of
   $N_{\mathfrak q}$ over $A$, and the residue-field basis from step 5. Thus $\alpha$ is
   $A$-universally injective and $Q_{\mathfrak q}$ is $A$-flat for $Q=\operatorname{coker}\alpha$.
   In particular $0\to B^r\to N\to Q\to0$ is exact, and remains left exact after every base change
   of $A$.
   Uses: lem-trf-local-generic-basis-universal-injective.

7. The module $Q$ is finite, and $(Q/\mathfrak mQ)_{\mathfrak p}=0$: reduce the chosen basis
   isomorphism at $\mathfrak p$ and use right exactness of tensor products. Its support is a
   proper closed subset of the integral $n$-dimensional closed fibre. Here closedness can be
   checked directly: for a finite generating list, vanishing at a prime means a product of
   denominators outside that prime kills every generator; hence support equals the zero locus of
   its annihilator. Every chain of irreducible closed subsets of this proper closed subset extends
   by appending the whole integral fibre, so its length is at most $n-1$. Consequently the
   dimension at $\mathfrak q$ of this support is $<n$ whenever it is nonempty. For $n=0$ the
   support is empty.
   Uses: def-kun-dimension.

8. If $Q_{\mathfrak q}/\mathfrak mQ_{\mathfrak q}=0$ (in particular in dimension zero), Nakayama
   over $B_{\mathfrak q}$ gives $Q_{\mathfrak q}=0$, and the finite-type surjective-on-stalk lemma
   shrinks to a principal open $D(g)$ containing $\mathfrak q$ on which $Q_g=0$. Otherwise apply
   the strong induction hypothesis to $\widetilde Q$ on $\operatorname{Spec}B$ at $\mathfrak q$:
   it is finite type, the morphism is locally finitely presented, $Q_{\mathfrak q}$ is $A$-flat by
   step 6, and its fibre-support dimension is strictly smaller by step 7. It gives a further
   elementary etale local base and an open neighbourhood where the pullback of $Q$ is finitely
   presented and flat. Shrink that neighbourhood to a principal $D(g)$ about the marked point.
   Rename the new base and modules $A,B,N,Q$; sections on this affine open give $Q_g$ finitely
   presented over $B_g$ and $A$-flat. Universal injectivity from step 6 and exactness of
   localization give $0\to B_g^r\to N_g\to Q_g\to0$.
   Uses: lem-weil-pbc-nakayama-jacobson, lem-weil-pbc-module-finite-type-surjective-on-stalk, lem-
   weil-pbc-finite-presentation-affine-sections, def-pc-scheme-module-flat-over, lem-weil-pbc-
   localization-module-exact.

9. Put $R=B_g$. The module $R$ is flat over $A$ because $D(g)\to\operatorname{Spec}A$ is a
   restriction of the smooth morphism, and $Q_g$ is $A$-flat. To prove $N_g$ flat, let
   $U\hookrightarrow V$ be any injection of $A$-modules. The flat-quotient tensor lemma gives
   exact rows $0\to U\otimes_A R^r\to U\otimes_A N_g\to U\otimes_A Q_g\to0$ and the analogous row
   for $V$. The outer vertical maps are injective by flatness. An element in the kernel of the
   middle vertical map maps to zero on the right, hence comes from the left; injectivity on the
   left and exactness of the lower row make that lift zero. Thus the middle map is injective,
   which is precisely $A$-flatness of $N_g$.
   Uses: lem-pc-smooth-flat, lem-weil-pbc-flat-quotient-tensor-injective, def-weil-pbc-flat-ring-
   map.

10. For finite presentation of $N_g$, choose $R^a\to R^b\to Q_g\to0$. Lift the $b$ generators to
   $N_g$ and adjoin the $r$ generators of its submodule $R^r$. For each of the $a$ generating
   relations of $Q_g$, its lifted combination lies in $R^r$; subtract its unique expression in
   that basis. These $a$ relations generate the kernel of the resulting surjection $R^{b+r}\to
   N_g$: any kernel vector first projects to a relation of $Q_g$, so subtract a combination of the
   chosen lifted relations, leaving a relation in the injected free submodule, hence zero. This is
   a finite presentation of $N_g$. Its associated sheaf on $D(g)$ therefore has a finite
   presentation.
   Uses: def-sc-finitely-presented-module, def-weil-pbc-module-finite-type-presentation.

11. We have solved the smooth case, including $n=0$. Transfer its finitely presented neighbourhood
   and its flat neighbourhood back through the devissage using the two neighbourhood equivalences,
   and intersect the resulting opens about the marked point; both properties persist under
   restriction. This gives the required $V$ in the base change of the original $X$ to the final
   local base. Step 2 realizes all base changes as a single elementary etale neighbourhood
   $(S',s')\to(S,s)$. Finally the points above $x$ in the base change along
   $\operatorname{Spec}\mathcal O_{S',s'}$ are the points of
   $\operatorname{Spec}(\kappa(x)\otimes_{\mathcal O_{S,s}}\mathcal O_{S',s'})$. This tensor
   product is $\kappa(x)\otimes_{\kappa(s)}\kappa(s')=\kappa(x)$: the closed fibre of the local
   etale map is its residue field and $\kappa(s')=\kappa(s)$. Thus this point is unique, as
   required.
   Uses: lem-trf-elementary-devissage-finite-presentation, lem-trf-elementary-devissage-flatness,
   lem-weil-pbc-etale-prime-generates-maximal.
-/
theorem exists_finite_type_flat_etale_neighborhood
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) (hF : Scheme.Modules.IsQuasiCoherentFiniteType F) (x : X)
    (hflat : moduleFlatAt f F x) :
    ∃ (S' : Scheme.{u}) (s' : S') (e : S' ⟶ S),
      Etale e ∧ e s' = f x ∧ IsIso (e.residueFieldMap s') ∧
      ∃ (V : (CategoryTheory.Limits.pullback f
          (Scheme.fromSpecStalk S' s' ≫ e)).Opens) (x' : V),
        (CategoryTheory.Limits.pullback.fst f
          (Scheme.fromSpecStalk S' s' ≫ e)) (V.ι x') = x ∧
        (V.ι ≫ CategoryTheory.Limits.pullback.snd f
          (Scheme.fromSpecStalk S' s' ≫ e)) x' =
          IsLocalRing.closedPoint (S'.presheaf.stalk s') ∧
        SheafOfModules.IsFinitePresentation
          ((Scheme.Modules.restrictFunctor V.ι).obj
            ((Scheme.Modules.tensorPullback (CategoryTheory.Limits.pullback.fst f
              (Scheme.fromSpecStalk S' s' ≫ e))).obj F)) ∧
        (∀ y : ↥(CategoryTheory.Limits.pullback f
            (Scheme.fromSpecStalk S' s' ≫ e)),
          (CategoryTheory.Limits.pullback.fst f
            (Scheme.fromSpecStalk S' s' ≫ e)) y = x → y = V.ι x') ∧
        Scheme.Modules.IsFlatOver
          ((Scheme.Modules.restrictFunctor V.ι).obj
            ((Scheme.Modules.tensorPullback (CategoryTheory.Limits.pullback.fst f
              (Scheme.fromSpecStalk S' s' ≫ e))).obj F))
          (V.ι ≫ CategoryTheory.Limits.pullback.snd f
            (Scheme.fromSpecStalk S' s' ≫ e)) := by
  sorry

end AlgebraicGeometry
