/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.KInjectiveResolutions
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity
import Sheaf.Paper.HypercoverCohomology
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.AlgebraicGeometry.BaseChangeTargetLimitGeometry
import Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Sheaf.CategoryTheory.RightDerivedFunctorTruncationIso
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import Sheaf.Algebra.Homology.KInjectiveComparisonPrinciple
import Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.CategoryTheory.TruncationTriangle

/-!
# Continuity for bounded-below étale complexes

Source: blueprint sec-proper-base-change/sk-thm-properbasechange,
lemma lem-weil-pbc-derived-cohomology-continuity
(blueprint: lem-weil-pbc-derived-cohomology-continuity).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- For a finite commutative coefficient ring, the canonical restriction cocone on
`(Over i₀)ᵒᵖ` is a colimit in every integer degree. The isomorphisms `e` and `eY`
only present its objects; `hm` and `hs` prescribe the canonical restriction maps
via the derived adjunction unit, Leray, and inverse-image composition.
Source: blueprint sec-proper-base-change/sk-thm-properbasechange,
lemma lem-weil-pbc-derived-cohomology-continuity
(blueprint: lem-weil-pbc-derived-cohomology-continuity).

Proof:
1. Choose $a$ with $\mathcal H^r(K_i)=0$ for $r<a$, using [def-weil-pbc-derived-categories]. The
   coefficient pullback is exact and agrees with abelian inverse image by [prop-weil-pbc-
   inverse-image-modules-exact], not merely by the abelian-sheaf exactness theorem. By [lem-sp-
   exact-functor-preserves-homology] it commutes with cohomology. Canonical truncation has terms
   $\ker d^b$ at its upper endpoint; exactness preserves that kernel and all its inclusion maps.
   Thus pullback commutes naturally with $\tau_{\leq b}$, its inclusions, and its cohomology-
   sheaf projections. All $K_j$ and $K$ have the same lower bound $a$. The category $I/i$ is
   nonempty (it contains $\mathrm{id}_i$). For $(j\to i)$ and $(k\to i)$ choose a common
   predecessor in $I$, then equalize its two composites to $i$; this gives a common predecessor
   in $I/i$. Parallel arrows in $I/i$ are equalized by an equalizer predecessor in $I$. Thus
   $(I/i)^{\mathrm{op}}$ is filtered, as required for the colimit.
2. First prove continuity for a module sheaf $F_i$ in degree zero. If $m$ is the additive order
   of $1\in\Lambda$, then $mF_i=0$, so its underlying abelian sheaf is torsion; coefficient
   pullback preserves this underlying sheaf by [prop-weil-pbc-inverse-image-modules-exact].
   Apply [lemma-weil-pbc-etale-cohomology-continuity] to those underlying sheaves. The limit $X$
   is also qcqs: specialize [lem-sbc-target-limit-geometry] to $S=T=\operatorname{Spec}\mathbf
   Z$, $p=g=\mathrm{id}_S$, and the given diagram over this terminal scheme. Its pullback
   functor is the identity, and its conclusion says the limit structure map to $S$ is qcqs,
   which is precisely that $X$ is qcqs. To identify its cohomology with module-derived
   cohomology, use both clauses of [thm-weil-pbc-hypercover-cohomology]: for each finite
   hypercover, the module cochain complex and the abelian cochain complex have exactly the same
   underlying groups, alternating differentials, and restriction maps. Their kernels, images and
   quotients therefore agree, and the underlying group of the colimit agrees too: scalar
   multiplication on a representative is $\lambda[x]=[\lambda x]$. The resulting comparison is
   the canonical restriction comparison, is $\Lambda$-linear, and is bijective on underlying
   groups; its inverse is consequently $\Lambda$-linear. For $F_i[-b]$ it gives continuity in
   degree $r$ as continuity for $F_i$ in degree $r-b\geq0$. For $r-b<0$ both sides vanish by
   [lem-weil-pbc-derived-functor-negative-vanishing]. Shift compatibility of derived sections
   comes from [lem-weil-pbc-derived-direct-image-triangulated], applied to the left exact
   additive sections functor.
3. The categories of module sheaves are Grothendieck abelian by [lem-weil-pbc-module-sheaves-
   grothendieck-abelian], and $\Mod(\Lambda)$ is Grothendieck abelian by [lem-weil-pbc-ring-
   modules-grothendieck-abelian]. Sections at the terminal object are additive and left exact: a
   section of a kernel is exactly a section annihilated by the given map. Thus the general
   derived-functor results apply. If $n<a$, [lem-weil-pbc-derived-functor-negative-vanishing]
   makes every degree-$n$ group zero, proving the assertion. If $n\geq a$, [lem-weil-pbc-
   derived-functor-truncation-iso] identifies $H^nR\Gamma(\tau_{\leq n}K_j)$ with
   $H^nR\Gamma(K_j)$, and likewise at $X$. These are the maps induced by the canonical
   truncation inclusions. It suffices to prove continuity for complexes with cohomology in a
   finite interval $[a,b]$.
4. We verify the boundary squares needed for the induction. For any transition $u:Y\to T$,
   compute restriction on a module complex $L$ using resolutions $L\to I$ and $u^{-1}L\to J$, as
   $\Gamma(T,I)\xrightarrow{\eta}\Gamma(Y,u^{-1}I)\to\Gamma(Y,J)$. The adjunction unit is that
   of [prop-weil-pbc-inverse-image-modules-exact], and resolutions are supplied by [prop-weil-
   pbc-kinjective-resolutions-exist]. Write $s:L\to I$ and $t:u^{-1}L\to J$ for the resolution
   maps. Exactness makes $u^{-1}s$ a quasi-isomorphism. Apply [lem-sp-kinjective-comparison-
   principle] in the target module-sheaf category, with K-injective target $J$: there is a
   unique homotopy class $h:u^{-1}I\to J$ with $h\circ u^{-1}s=t$ in the homotopy category. This
   is the comparison used above; it does not require $u^{-1}I$ to be K-injective. Uniqueness
   gives naturality in $L$ and independence of the resolutions. This defines a natural derived
   restriction transformation; for a composable pair, [lem-weil-pbc-inverse-image-composition-
   module-linear] identifies the composite unit with the single unit by a module-linear
   composition isomorphism. The composite resolution comparisons and the single comparison agree
   after precomposition with the pulled-back resolution of $L$, hence agree up to homotopy by
   [lem-sp-kinjective-comparison-principle]. For the identity the comparison is the identity up
   to homotopy by the same uniqueness. Thus the maps form the prescribed stage diagram. By [lem-
   weil-pbc-kinjective-shift] we may use $I[1]$ and $J[1]$ for $L[1]$. In degree $r$ the unit
   and comparison then equal the original maps in degree $r+1$, including the shifted
   differential sign. Hence restriction commutes with the shift isomorphisms. Derived sections
   are triangulated by [lem-weil-pbc-derived-direct-image-triangulated]. Exact module pullback
   induces the triangulated derived pullback [def-weil-pbc-derived-inverse-image]. Apply [lem-
   weil-pbc-commshift-nattrans-triangle-morphism] to this shift-compatible natural
   transformation, and then [lem-weil-pbc-derived-cohomology-ladder]. Restriction therefore
   gives a morphism of long exact cohomology sequences, including the connecting arrows;
   exactness of those sequences is [lem-sf-derived-homology-long-exact]. These arguments apply
   to all transitions and to the projections to $X$.
5. For a complex $L_i$ with cohomology supported in $[a,b]$, set $P_t=\tau_{\leq t}L_i$. Start
   with $P_{a-1}=0$ in the derived category, since all its cohomology is zero by [lem-weil-pbc-
   truncation-cohomology]; quasi-isomorphisms are inverted by [def-weil-abstract-derived-
   category]. For $a\leq t\leq b$, [lem-weil-pbc-truncation-triangle] gives the functorial
   distinguished triangle $P_{t-1}\to P_t\to\mathcal H^t(L_i)[-t]\to P_{t-1}[1]$, and step 1
   identifies its pullbacks with the corresponding triangles at each stage. Inductively assume
   comparison is an isomorphism in every degree for $P_{t-1}$; step 2 gives this for $C=\mathcal
   H^t(L_i)[-t]$. By step 4 the stage sequences and the limit sequence form a commutative
   ladder. Filtered colimits of $\Lambda$-modules are exact by [lem-weil-pbc-ring-modules-
   grothendieck-abelian], so the top row remains exact. For each integer $r$, take the five
   terms $H^{r-1}(C)\to H^r(P_{t-1})\to H^r(P_t)\to H^r(C)\to H^{r+1}(P_{t-1})$, with the top
   row understood as stage colimits. All four outer vertical arrows are isomorphisms. The middle
   arrow is an isomorphism by [lem-weil-pbc-five-lemma]. This proves the inductive assertion
   simultaneously in all degrees. Finally $P_b\to L_i$ is a quasi-isomorphism by [lem-weil-pbc-
   truncation-cohomology], hence continuity holds for $L_i$.
6. Apply step 5 to $L_i=\tau_{\leq n}K_i$. Its cohomology is supported in $[a,n]$ by [lem-weil-
   pbc-truncation-cohomology], and step 1 identifies all its inverse images with the analogous
   truncations. Step 3 identifies the top and bottom degree-$n$ groups with those for $K_j$ and
   $K$. The square between these identifications and restriction commutes by the naturality
   established in step 4, applied to the inclusions $\tau_{\leq n}K_i\to K_i$. Thus the
   isomorphism obtained is exactly the canonical restriction map in the statement. The case
   $n<a$ was settled in step 3.
-/
theorem derived_cohomology_continuity
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (i₀ : I)
    (K : DerivedCategory.Plus (Sheaf (D.obj i₀).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (n : ℤ) (F : (Over i₀)ᵒᵖ ⥤ (ModuleCat.{u + 1} Λ))
    (e : ∀ i : Over i₀, F.obj (op i) ≅
      (Etale.cohomology (ModuleCat.{u + 1} Λ) (D.obj i.left) n).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map i.hom)).mapDerivedCategory.obj K.obj))
    (hm : ∀ {i j : Over i₀} (f : i ⟶ j), F.map f.op =
      (e j).hom ≫
      (Etale.cohomology (ModuleCat.{u + 1} Λ) (D.obj j.left) n).map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (D.map f.left)).unit.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map j.hom)).mapDerivedCategory.obj
              K.obj)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) n).map
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          (ModuleCat.{u + 1} Λ) (D.map f.left)).hom.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map f.left)).mapDerivedCategory.obj
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map j.hom)).mapDerivedCategory.obj
                K.obj))) ≫
      (Etale.cohomology (ModuleCat.{u + 1} Λ) (D.obj i.left) n).map
        ((Functor.mapDerivedCategoryNatIso
          (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (D.map f.left) (D.map j.hom)
            (D.map i.hom) ((congrArg D.map f.w).symm.trans (D.map_comp f.left j.hom))) ≪≫
          Functor.mapDerivedCategoryCompIso
            (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map j.hom))
            (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map f.left))).inv.app K.obj) ≫
      (e i).inv)
    (s : Cocone F)
    (eY : s.pt ≅ (Etale.cohomology (ModuleCat.{u + 1} Λ) c.pt n).obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app i₀)).mapDerivedCategory.obj K.obj))
    (hs : ∀ i : Over i₀, s.ι.app (op i) =
      (e i).hom ≫
      (Etale.cohomology (ModuleCat.{u + 1} Λ) (D.obj i.left) n).map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (c.π.app i.left)).unit.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map i.hom)).mapDerivedCategory.obj
              K.obj)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) n).map
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          (ModuleCat.{u + 1} Λ) (c.π.app i.left)).hom.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app i.left)).mapDerivedCategory.obj
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map i.hom)).mapDerivedCategory.obj
                K.obj))) ≫
      (Etale.cohomology (ModuleCat.{u + 1} Λ) c.pt n).map
        ((Functor.mapDerivedCategoryNatIso
          (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app i.left) (D.map i.hom) (c.π.app i₀)
            (c.w i.hom).symm) ≪≫
          Functor.mapDerivedCategoryCompIso
            (Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map i.hom))
            (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app i.left))).inv.app K.obj) ≫
      eY.inv) : Nonempty (IsColimit s) := by
  sorry

end AlgebraicGeometry
