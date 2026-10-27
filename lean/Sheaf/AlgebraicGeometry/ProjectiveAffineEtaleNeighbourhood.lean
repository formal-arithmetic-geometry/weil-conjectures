/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.Algebra.Module.Projective
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import WeilConjectures.RingTheory.OpenFlatLocus
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.FiniteType
import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation
import Sheaf.AlgebraicGeometry.AffineAssociatedPointsPrimes
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Sheaf.AlgebraicGeometry.RelativeAssassin
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.RelativelyFlatModulePullback
import WeilConjectures.AlgebraicGeometry.TensorPullback
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.AlgebraicGeometry.AffineChartRelativeFlatCriterion
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.Properties
import Sheaf.AlgebraicGeometry.FlatRelativeAssociatedSpecialization
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Projective affine sections after an elementary etale base neighbourhood

Source: Stacks Project, flat.tex, Tag 05ME,
lemma-flat-finite-presentation-affine-neighbourhood-projective
(blueprint: lem-sfb-finitely-presented-flat-point-projective-etale-neighbourhood).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A finitely presented quasi-coherent module flat at a point has projective affine
sections after an affine elementary etale neighbourhood of its image in the base.
Projectivity is over the base's ring of global sections, with no finite-rank condition.
Source: Stacks Project, flat.tex, Tag 05ME
(blueprint: lem-sfb-finitely-presented-flat-point-projective-etale-neighbourhood).

Proof (the nine steps of the DAG node):

1. Choose affine neighbourhoods $S_0=\operatorname{Spec}A$ of $s$ and
   $X_0=\operatorname{Spec}B\subset f^{-1}(S_0)$ of $x$ on which $G=\mathcal G|_{X_0}$ has a
   finite presentation, as allowed by the hypotheses. The all-affine-pairs theorem gives $A\to
   B$ finitely presented. The affine dictionary writes $G=\widetilde M$ with $M$ finitely
   presented over $B$; its stalk at a prime $\mathfrak q$ is $M_{\mathfrak q}$. At $x$, with
   base prime $\mathfrak p$, the assumed $A_{\mathfrak p}$-flatness implies $A$-flatness by
   flatness of localization and transitivity. Apply algebraic openness of flatness to $(A,B,M)$
   to get an open neighbourhood of $x$ where every $M_{\mathfrak q}$ is $A$-flat. Such a module
   is flat over $A_{\mathfrak q\cap A}$: for an injection of $A_{\mathfrak q\cap A}$-modules,
   its tensor with $M_{\mathfrak q}$ is the same as its tensor over $A$, since every inverted
   scalar already acts invertibly. Choose a smaller affine $X_0$ inside this open. The stalk
   criterion says $G$ is flat over $S_0$. Restriction preserves the displayed finite
   presentations and quasi-coherence.
   Inputs: lem-weil-pbc-lfp-affine-opens-finite-presentation, lem-weil-pbc-quasi-coherent-
   finite-type-affine, pqf-def-coherent, lem-weil-pbc-affine-tilde-gamma-adjunction, lem-weil-
   pbc-spec-tilde-stalk-localization, lem-weil-pbc-localization-flat, lem-pc-module-flat-
   transitive, lem-weil-pbc-openness-of-flatness, def-pc-scheme-module-flat-over.

2. The affine fibre $(X_0)_s$ is the spectrum of a finite type $\kappa(s)$-algebra, hence has
   Noetherian coordinate ring: a field has only the ideals zero and one, and finite type
   algebras over a Noetherian ring are Noetherian. Pullback of the local finite presentation of
   $G$ gives a finite presentation of $G_s$. The affine dictionary and finiteness of associated
   primes of a finite module over a Noetherian ring show that
   $E=\operatorname{Ass}_{(X_0)_s}(G_s)$ is finite. For every $a\in E$ which does not specialize
   to $x$, remove the closed subset $\overline{\{a\}}$ of $X_0$. None contains $x$, and removing
   their finite union leaves an open neighbourhood of $x$. Choose a smaller affine $X_0$
   therein. On an open subscheme the stalks and their annihilators are unchanged; thus every
   remaining associated point of $G_s$ specializes to $x$. Finite presentation over $S_0$ still
   holds by the affine-pairs theorem and the qcqs permanence lemma. No Noetherian hypothesis on
   $S_0$ was used.
   Inputs: def-pc-scheme-fibre, lem-weil-pbc-finite-presentation-base-change-composition, lem-
   weil-pbc-finite-type-algebra-noetherian, lem-pc-tensor-pullback-finite-presentation, lem-
   weil-pbc-quasi-coherent-finite-type-affine, lem-sfb-affine-associated-points-primes, lem-
   weil-pbc-noetherian-associated-primes-finite, def-trf-relative-assassin, lem-weil-pbc-lfp-
   affine-opens-finite-presentation, lem-weil-pbc-qcqs-morphism-permanence.

3. Apply the pointwise projective-chart theorem to $X_0/S_0$, $G$, and $x$. Write its affine
   elementary base neighbourhood as $(S_1,s_1)\to(S_0,s)$ and its affine source neighbourhood as
   $g:(Y,y)\to(X_0,x)$, with $q:Y\to S_1$. Put $X_1=X_0\times_{S_0}S_1$. The induced map
   $h=(g,q):Y\to X_1$ is etale: $X_1\to X_0$ is etale by base change, and its composite with $h$
   is the etale $g$, so etale cancellation applies. Its marked point maps to the unique $x_1$
   above $(x,s_1)$. Moreover $Y\to S_1$ is finitely presented: $Y\to X_0\to S_0$ is locally
   finitely presented by composition, $S_1\to S_0$ is locally of finite type, and finite-
   presentation cancellation makes $q$ locally finitely presented; $Y,S_1$ affine then give
   qcqs. Put $F=\operatorname{pr}_{X_0}^*G$ and $H=h^*F\cong g^*G$. The chart theorem gives
   $Q=\Gamma(Y,H)$ projective over $A_1=\Gamma(S_1,\mathcal O)$. Both sheaves remain quasi-
   coherent and finitely presented, and $F$ remains flat over $S_1$. The specified residue
   isomorphism identifies the fibre $(X_1)_{s_1}$, its sheaf and its marked point with
   $(X_0)_s,G_s,x$. Thus all its associated points specialize to $x_1$; this persists under
   every further elementary pointed base neighbourhood.
   Inputs: lem-sfb-flat-point-projective-etale-source-chart, lem-weil-pbc-etale-scheme-base-
   change, lem-weil-pbc-etale-composition-cancellation, def-weil-etale-morphism, lem-sbc-
   locally-finite-presentation-composition, lem-a1-map-over-base-finite-presentation, lem-weil-
   pbc-qcqs-morphism-permanence, lem-weil-pbc-module-pullback-quasi-coherent, lem-pc-tensor-
   pullback-finite-presentation, lem-pc-relatively-flat-module-pullback, lem-pc-module-pullback-
   identity-composition, def-pc-scheme-fibre.

4. Projectivity of $Q$ makes it $A_1$-flat. The affine-chart flatness criterion then makes $H$
   flat over $S_1$. Apply the affine projectivity-purity theorem to $Y/S_1$ and $H$: its
   hypotheses are finite presentation of the morphism and sheaf, quasi-coherence, and the
   flatness just checked. It follows that $H$ is universally pure over $S_1$. Since $h$ is
   etale, its image is open. Choose an affine open $U\subseteq h(Y)$ containing $x_1$. We will
   show $F|_U$ is pure along $U_{s_1}$.
   Inputs: lem-weil-pbc-projective-module-flat, lem-pc-affine-chart-relative-flat-criterion,
   def-pc-scheme-module-flat-over, lem-sfb-affine-flat-fp-projectivity-purity, lem-weil-pbc-
   etale-morphism-open-map.

5. Test purity using its definition. Take an arbitrary elementary etale neighbourhood
   $(T,t)\to(S_1,s_1)$, a specialization $t'\leadsto t$, and
   $\xi\in\operatorname{Ass}_{U_T/T}(F_T|_{U_T})$ over $t'$. Put $Y_T=Y\times_{S_1}T$, and let
   $h_T:Y_T\to(X_1)_T$ be the base-changed etale map. The restriction $h^{-1}(U)\to U$ is etale
   and surjective by the definition of its image; its arbitrary base change to $U_T$ remains
   surjective by the etale-covering base-change theorem. Choose $\xi'\in Y_T$ above $\xi$. On
   the $t'$ fibres the schemes are locally Noetherian, being locally of finite type over the
   field $\kappa(t')$. Etale invariance of associated points applied to $(h_T)_{t'}$ implies
   $\xi'\in\operatorname{Ass}_{Y_T/T}(H_T)$. Here association on the open $U_T$ agrees with
   association in $(X_1)_T$ by the identical local stalks. Universal purity of $H$, with this
   arbitrary $T\to S_1$, supplies a specialization of $\xi'$ to some point of $(Y_T)_t$.
   Inputs: def-sfb-scheme-relative-purity, lem-a1-etale-open-restriction, lem-weil-pbc-etale-
   scheme-base-change, lem-weil-pbc-etale-covering-base-change, pqf-lem-locnoeth-lft, lem-sfb-
   scheme-etale-assassin-invariance, def-trf-relative-assassin.

6. We need the limiting point to be associated. Form $Z=\overline{\{\xi'\}}\subset Y_T$ with its
   reduced induced closed-scheme structure. Its fibre $Z_t$ is nonempty by step 5. Choose an
   irreducible component $C$ of $Z_t$ and its generic point $y$, using component coverage and
   sobriety of schemes. Thus $\xi'\leadsto y$. The module $H_T$ is flat over $T$ by base change
   of $H$; it is also quasi-coherent and finitely presented, and $Y_T/T$ is finitely presented,
   by base change of the data in step 4. Apply the existing relative-associated-specialization
   theorem (Tag 0GSI) to $Y_T/T$, $H_T$, $\xi'$, and this component $C$. In particular its
   required flatness at $y$ holds. Its conclusion gives
   $y\in\operatorname{Ass}_{(Y_T)_t}((H_T)_t)$. The dimension clause of that theorem is not
   needed.
   Inputs: lem-weil-pbc-reduced-induced-closed-subscheme, lem-sc-irreducible-components-cover,
   lem-sc-scheme-sober, lem-pc-relatively-flat-module-pullback, lem-weil-pbc-qcqs-morphism-
   permanence, lem-weil-pbc-module-pullback-quasi-coherent, lem-pc-tensor-pullback-finite-
   presentation, lem-trf-flat-relative-associated-specialization.

7. The map $(h_T)_t:(Y_T)_t\to((X_1)_T)_t$ is etale between locally Noetherian schemes over
   $\kappa(t)$. Etale assassin invariance sends the associated point $y$ of step 6 to an
   associated point $h_T(y)$ of $((F_T)_t)$. Since $\kappa(t)=\kappa(s_1)$ through the specified
   elementary-neighbourhood isomorphism, the fibre identification in step 3 says that $h_T(y)$
   specializes to the point $x_t$ above $x_1$. This point lies in $U_T$. Opens contain all
   generalizations of their points: if an open containing $x_t$ omitted $h_T(y)$, its closed
   complement would contain its specialization $x_t$. Therefore $h_T(y)\in(U_T)_t$. Continuity
   sends $\xi'\leadsto y$ to $\xi\leadsto h_T(y)$. We have found a specialization in $(U_T)_t$
   for every proposed impurity in step 5. By definition, $F|_U$ is pure along $U_{s_1}$.
   Inputs: lem-weil-pbc-etale-scheme-base-change, pqf-lem-locnoeth-lft, lem-sfb-scheme-etale-
   assassin-invariance, def-sfb-scheme-relative-purity.

8. The map $U\to S_1$ is finitely presented: $X_1/S_1$ is locally of finite presentation by base
   change, restriction to $U$ preserves this local property by composition with the etale open
   inclusion, and a locally finitely presented map from an affine scheme to the affine $S_1$ is
   finitely presented by qcqs permanence. The module $F|_U$ is quasi-coherent, finitely
   presented and flat over $S_1$. By openness of purity, the set of $v\in S_1$ for which $F|_U$
   is pure along $U_v$ is an open neighbourhood of $s_1$. Choose an affine open $V$ inside it
   containing $s_1$, and put $W=U\times_{S_1}V$. Since $U\to S_1$ is a map of affine schemes, it
   is affine, so $W$ is affine. It is an open subscheme of $X_0\times_{S_0}V$, contains the
   unique point above $(x,s_1)$, and its module is pure relative to $V$: every elementary
   neighbourhood of a point in the open $V$ is also one in $S_1$, with the same relevant fibre
   and specializations. Finite presentation of $W/V$ and relative flatness of its module survive
   base change.
   Inputs: lem-weil-pbc-qcqs-morphism-permanence, lem-sbc-locally-finite-presentation-
   composition, lem-weil-pbc-etale-composition-cancellation, def-weil-etale-morphism, lem-weil-
   pbc-module-pullback-quasi-coherent, lem-pc-tensor-pullback-finite-presentation, lem-pc-
   module-pullback-identity-composition, lem-sfb-flat-fp-purity-open, lem-weil-pbc-morphism-
   affine-schemes-affine, lem-pc-relatively-flat-module-pullback, lem-weil-pbc-open-immersion-
   base-change, def-sfb-scheme-relative-purity.

9. Apply the affine projectivity-purity equivalence to $W/V$: both schemes are affine, the map
   and module are finitely presented, and the module is relatively flat and pure relative to
   $V$, by step 8. It gives $\Gamma(W,F_W)$ projective over $\Gamma(V,\mathcal O_V)$. Finally
   the composite $V\to S_1\to S_0\to S$ is etale: open immersions are etale and etale maps
   compose. It sends the retained point to $s$ with unchanged residue field. The open
   $W\subseteq X_0\times_{S_0}V$ is also open in $X\times_SV$, since $X_0\subset f^{-1}(S_0)$
   was an open subscheme. Pullback composition identifies $F_W$ with
   $(\operatorname{pr}_X^*\mathcal G)|_W$. Taking $S'=V$ proves every requested clause, with
   arbitrary-rank projectivity rather than finite projectivity.
   Inputs: lem-sfb-affine-flat-fp-projectivity-purity, lem-weil-pbc-etale-composition-
   cancellation, lem-pc-module-pullback-identity-composition, lem-weil-pbc-open-immersion-base-
   change.
-/
theorem exists_projective_affine_etale_neighbourhood
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G]
    [SheafOfModules.IsFinitePresentation.{u} G] (x : X)
    (hflat : Module.Flat (S.presheaf.stalk (f x))
      ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G))) :
    ∃ (S' : Scheme.{u}) (e : S' ⟶ S) (s' : S'),
      IsAffine S' ∧ Etale e ∧ e s' = f x ∧ IsIso (e.residueFieldMap s') ∧
      ∃ (W : (pullback f e).Opens) (z : ↥(pullback f e)),
        IsAffineOpen W ∧ (pullback.fst f e) z = x ∧
        (pullback.snd f e) z = s' ∧ z ∈ W ∧
        @Module.Projective Γ(S', ⊤) _
          Γ((Scheme.Modules.tensorPullback (pullback.fst f e)).obj G, W) _
          (Module.compHom _ (((pullback.snd f e).appTop ≫
            (pullback f e).presheaf.map (homOfLE le_top : W ⟶ ⊤).op).hom)) := by
  sorry

end AlgebraicGeometry
