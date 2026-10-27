/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.HigherDirectImageOpenRestriction
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.OrdinaryHigherImageQuasiCoherent
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.ProperFinitePresentationClosedLimit
import Sheaf.AlgebraicGeometry.LimitFibreDimensionBound
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.ProperNoetherianStage
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Sheaf.AlgebraicGeometry.ModuleDirectedColimitFinitePresentation
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.OpenModuleCohomologyDirectedColimit
import WeilConjectures.AlgebraicGeometry.FormalFunctionsStalk
import WeilConjectures.Topology.NoetherianTopologicalCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.OpenModuleCohomologyComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleStalkFinite
import Mathlib.RingTheory.Filtration
import WeilConjectures.AlgebraicGeometry.Cohomology.FiniteFibre

/-! # Proper quasi-coherent higher direct images vanish above fibre dimension

Source: Stacks Project, Limits, Tag 0E7D, part (1), applied at every point;
compare Cohomology of Schemes, Tag 02V7.
(blueprint: lem-sfb-proper-quasicoherent-fibre-dimension-vanishing).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For a proper morphism whose scheme-theoretic fibres have dimension at most `d`,
all higher direct images of every quasi-coherent structure-sheaf module vanish in
natural degrees strictly greater than `d`. There is no Noetherian or flatness assumption.

Source: Stacks Project, Limits, Tag 0E7D, part (1), at every point of the target.
(blueprint: lem-sfb-proper-quasicoherent-fibre-dimension-vanishing).

Proof (the accepted DAG split):
1. Work locally on the target. For an affine open $V\subset Y$, put $X_V=f^{-1}V$ and restrict
   $F$ to $X_V$. The restricted morphism is proper by base change, its fibres are the original
   fibres, and the restricted module is quasi-coherent by pullback. Higher direct images restrict
   to the higher direct images of this restricted morphism. Consequently it suffices to prove the
   assertion with $Y$ affine. A proper morphism is quasi-compact by finite type and quasi-
   separated by separatedness. For such a morphism, $R^pf_*F$ is quasi-coherent and its sections
   over the affine target identify with $H^p(X,F)$. The affine tilde/Gamma counit identifies
   $R^pf_*F$ with the sheaf associated to these sections. It therefore suffices to show
   $H^p(X,F)=0$ for $p>d$.
   Uses:
   - lem-pc-higher-direct-image-open-restriction
   - lem-weil-pbc-proper-fp-permanence
   - lem-weil-pbc-module-pullback-quasi-coherent
   - def-weil-proper-morphism
   - def-weil-finite-type-morphism
   - lem-pc-separated-quasi-separated
   - lem-pc-ordinary-higher-image-quasi-coherent
   - lem-pc-cohomology-sections-affine-base
   - lem-weil-pbc-affine-tilde-gamma-adjunction

2. Keep $Y$ affine, hence quasi-compact and quasi-separated by the affine-scheme lemma. Write
   $X=\varprojlim_iX_i$ over $Y$, with each $X_i\to Y$ proper and finitely presented and all
   transitions and projections $a_i:X\to X_i$ closed immersions. Apply the fibre-dimension limit
   lemma to the constant base system $Y$: it provides an index $i$ such that every fibre of
   $X_i\to Y$ has dimension at most $d$. Its comparison maps are precisely the given closed
   immersions. For the given $F$, $a_{i,*}F$ is quasi-coherent, because a closed immersion is
   affine, hence quasi-compact and quasi-separated. Affine-morphism cohomology gives
   $H^p(X_i,a_{i,*}F)\cong H^p(X,F)$. Thus it remains to prove cohomology vanishing for proper
   finitely presented morphisms over an affine base, with arbitrary quasi-coherent coefficients.
   Uses:
   - lem-weil-pbc-affine-scheme-qcqs
   - lem-weil-pbc-proper-closed-in-proper-fp
   - lem-trf-limit-fibre-dimension-bound
   - def-weil-closed-immersion
   - lem-weil-pbc-affine-morphism-permanence
   - pqf-lem-pushforward-qcoh
   - lem-weil-pbc-affine-morphism-cohomology-edge

3. Now assume $f$ finitely presented. Express $Y=\operatorname{Spec}A$ as the inverse limit of
   spectra of finitely generated $\mathbf Z$-subalgebras of $A$. These form a small nonempty
   directed set (the subalgebra generated by the union of two finite sets is an upper bound).
   Apply proper Noetherian-stage descent to obtain a proper finitely presented model $f_0:X_0\to
   Y_0$ whose pullback is $f$. Above this stage take its base changes $f_j:X_j\to Y_j$. They
   remain proper, and their comparison morphisms are isomorphisms, hence closed immersions. The
   system has limit $f$: a compatible map into its pullbacks is uniquely the pair of a map into
   $X_0$ and a compatible family into the $Y_j$, by the fibre-product universal property. The
   fibre-dimension limit lemma supplies a stage $j$ with all fibres of $f_j$ of dimension at most
   $d$. The affine $Y_j$ is Noetherian, being of finite type over $\mathbf Z$. The projection
   $h:X\to X_j$ is affine, as the base change of the morphism $Y\to Y_j$ between affine schemes:
   use the single-open cover $Y_j$ in the affine-local-target criterion. Therefore $h_*F$ is
   quasi-coherent and $H^p(X,F)\cong H^p(X_j,h_*F)$. It suffices to prove the assertion over an
   affine Noetherian base.
   Uses:
   - lemma-nagata-noetherian-inverse-system-affine
   - def-nagata-noetherian-inverse-system
   - lem-weil-pbc-proper-noetherian-stage
   - lem-weil-pbc-proper-fp-permanence
   - lem-trf-limit-fibre-dimension-bound
   - lem-weil-pbc-finite-type-over-noetherian
   - pqf-lem-affine-local-target
   - lem-weil-pbc-affine-morphism-permanence
   - pqf-lem-pushforward-qcoh
   - lem-weil-pbc-affine-morphism-cohomology-edge

4. Let $f:X\to Y$ now be proper with $Y$ affine Noetherian and fibres of dimension at most $d$.
   Then $X$ is Noetherian by finite-type permanence, and it is quasi-separated by separatedness
   over the affine base. Express $F$ as a directed colimit of finitely presented module sheaves
   $F_\lambda$. A finite presentation is a quotient of a finite free module, hence is of finite
   type; it is quasi-coherent by the finite-presentation lemma, and therefore coherent by the
   locally Noetherian coherence criterion. The cohomology-colimit theorem applies to $X$: its
   affine opens form a basis, and its Noetherian topology makes every open quasi-compact. For
   completeness the latter topology follows from a finite cover by spectra of Noetherian rings: a
   descending sequence of closed sets stabilizes on each member, hence globally after the maximum
   of the finitely many stabilization indices. Thus $H^p(X,F)=\varinjlim_\lambda
   H^p(X,F_\lambda)$. It remains to prove cohomology vanishing for coherent coefficients.
   Uses:
   - lem-weil-pbc-finite-type-over-noetherian
   - lem-pc-separated-quasi-separated
   - lem-weil-pbc-qcqs-morphism-permanence
   - lem-weil-pbc-module-directed-colimit-finite-presentation
   - lem-weil-pbc-quasi-coherent-finite-type-affine
   - pqf-lem-coherent-ft-locnoeth
   - lem-sc-affine-noetherian-underlying-space
   - lem-weil-pbc-qs-scheme-cohomology-directed-colimit

5. Fix a coherent $F$, $p>d$, and $y\in Y$. Use the infinitesimal fibres $X_n$ and pullbacks
   $F_n$ of the formal-functions stalk theorem, with $n\ge1$ and $A_y=\mathcal O_{Y,y}$. The
   fibre $X_y$ is proper, hence finite type, over the field $\kappa(y)$ and is Noetherian. It has
   a finite cover by spectra of Noetherian rings; those spaces are Noetherian, and the finite-
   cover stabilization argument of step 4 proves that $|X_y|$ is Noetherian. On $X_n$ the ideal
   generated by $\mathfrak m_y$ has $n$th power zero, and its quotient defines $X_y$. Every prime
   contains every nilpotent element, so on each affine chart passing to this quotient preserves
   the prime spectrum and its closed sets. These identifications agree on overlaps, yielding
   $|X_n|\cong|X_y|$. Hence $|X_n|$ is Noetherian of dimension at most $d$. Topological
   Grothendieck vanishing applied to the underlying abelian sheaf of $F_n$ gives zero cohomology
   in degree $p$. The module/abelian cohomology comparison, applied with the whole open $X_n$,
   gives $H^p(X_n,F_n)=0$. This includes empty fibres.
   Uses:
   - lem-weil-pbc-formal-functions-stalk
   - lem-weil-pbc-proper-fp-permanence
   - def-weil-proper-morphism
   - lem-weil-pbc-finite-type-over-noetherian
   - lem-sc-affine-noetherian-underlying-space
   - lem-sc-noetherian-topological-cohomology-vanishing
   - lem-pqf-open-module-cohomology-comparison

6. Put $M=(R^pf_*F)_y$. The formal-functions stalk theorem identifies its completion with
   $\varprojlim_n H^p(X_n,F_n)$, which is zero by step 5. Proper coherent direct image makes
   $R^pf_*F$ coherent, so its finite-type stalk $M$ is finitely generated over the Noetherian
   local ring $A_y$. If $m\in M$, its image in the zero completion is zero, so $m\in\mathfrak
   m_y^nM$ for every $n$ (these are exactly the kernels of the quotient coordinates of the
   completion). Krull intersection, applied to $\mathfrak m_y$, which is the Jacobson radical of
   this local ring, gives $m=0$. Thus $M=0$ for every $y$. The zero-stalk criterion yields
   $R^pf_*F=0$. The affine-base sections/cohomology comparison then yields $H^p(X,F)=0$ for
   coherent $F$.
   Uses:
   - lem-weil-pbc-formal-functions-stalk
   - lem-pc-coherent-hi
   - lem-weil-pbc-finite-type-module-stalk-finite
   - pqf-def-coherent
   - lem-weil-pbc-krull-intersection-jacobson
   - pqf-lem-sheaf-zero-stalks
   - lem-pc-cohomology-sections-affine-base

7. For arbitrary quasi-coherent $F$ in the Noetherian case, step 4 identifies its degree-$p$
   cohomology with a directed colimit whose terms vanish by steps 5--6. Such a colimit is zero:
   every class has a representative in a zero term. Step 3 transports this vanishing to every
   proper finitely presented morphism over an affine base, and step 2 to every proper morphism
   over an affine base. Finally step 1 identifies the sections of $R^pf_*F$ over each affine open
   with the zero cohomology group and identifies the quasi-coherent restriction with the sheaf
   associated to its zero module of sections. Thus these restrictions, and hence $R^pf_*F$, are
   zero. No flatness hypothesis was used, and Noetherian hypotheses occurred only on intermediate
   models. The case $Y=\varnothing$ is immediate, and $d=0$ is covered by the same argument for
   every $p>0$. -/
theorem proper_quasicoherent_higherDirectImage_vanishing
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) (hF : SheafOfModules.IsQuasicoherent.{u} F) (i : ℕ) (hi : d < i) :
    IsZero (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived i).obj F) := by
  sorry

end AlgebraicGeometry
