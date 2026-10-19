/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.Compactification.Defs
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Basic

public import Sheaf.AlgebraicGeometry.ProperSupportSheafComposition
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

import Sheaf.AlgebraicGeometry.EtaleSumStalks
import Mathlib.Algebra.DirectSum.Module
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.Paper.UnboundedProperOpenInterchange
import WeilConjectures.Compactification.CategoryBaseChange
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import Sheaf.AlgebraicGeometry.ProperSupportGeometricStalk
import Sheaf.AlgebraicGeometry.CompatibleCompactificationTriangle
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.AlgebraicGeometry.UnramifiedQuasiFinite
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
import Sheaf.AlgebraicGeometry.EtaleGeometricFibreCompactSections
import Sheaf.Paper.ProperOpenTowerDerivedUnit
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Quasi-finite compact support is exact

Source: Stacks Project, More on Étale Cohomology, Tag 0GKM, with Tags 0F4Y, 0F50,
0F7J and 0F5F (blueprint: lem-sfb-quasifinite-compact-support-exact).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- Proper-support direct image for a separated quasi-finite finite-type map is exact and
agrees on all unbounded complexes with every compactification construction. The comparison
family is compatible with canonical compactification changes, composition, étale sum extension,
and identity normalization.
Source: Stacks Project, More on Étale Cohomology, Tags 0GKM, 0F4Y, 0F50, 0F7J and 0F5F.
(blueprint: lem-sfb-quasifinite-compact-support-exact)

Identity comparisons are shared with the three comparison families whenever their
compactifications coincide. The heterogeneous equalities only account for the scheme and
morphism indices of those compactifications; specializing an index to an identity makes them
ordinary equalities of the comparison isomorphisms.

Proof (the eight steps of the DAG node).

1. A Noetherian scheme in the stated convention is quasi-compact (use its finite affine cover) and
locally Noetherian, hence quasi-separated by [lem-weil-pbc-locally-noetherian-quasi-separated].
Apply [thm-pqf-zmt-factorization] to $h$ to obtain $h=pj_0$ with $j_0:V\hookrightarrow V_0$ a
quasi-compact open immersion and $p:V_0\to T$ finite. A finite algebra is generated as an algebra
by any finite set of module generators, so $p$ is of finite type. By [lem-weil-pbc-finite-type-
over-noetherian] $V_0$ is Noetherian, and by [lem-weil-pbc-finite-proper] $p$ is proper. Thus
$(j_0,p)$ is an admissible compactification. No excellence, finite dimension, or invertibility of
the order of $A$ has been used.

2. The support-composition theorem [lem-cbc-proper-support-sheaf-composition], applied to $j_0,p$,
gives the natural $A$-linear identification $h^{\mathrm{supp}}_!=p_*j_{0!}$: the proper-support
functor is ordinary direct image for $p$, and extension by zero for $j_0$. The functor $j_{0!}$ is
exact by [lem-weil-pbc-extension-by-zero-exact]. The finite direct-image theorem [lemma-weil-pbc-
finite-direct-image-exact] gives exactness of $p_*$ on underlying abelian sheaves. It also gives
exactness for constant-$A$ module sheaves: direct image commutes with forgetting the action by its
sectionwise definition [def-weil-pbc-direct-image], and [lem-weil-pbc-module-sheaves-colimits-
forgetful] identifies the underlying kernels and cokernels. Vanishing of an underlying
kernel/cokernel is vanishing of that module sheaf, so the faithful forgetful functor reflects
exactness. Hence $h^{\mathrm{supp}}_!$ is exact.

3. For an arbitrary compactification $c=(j,r)$, its ambient scheme $\overline V$ is Noetherian:
$r$ is proper, hence of finite type by definition, and its target $T$ is Noetherian, so [lem-weil-
pbc-finite-type-over-noetherian] applies. The locally Noetherian ambient scheme is quasi-separated
by [lem-weil-pbc-locally-noetherian-quasi-separated]. Since $V$ is quasi-compact, [lem-weil-pbc-
qcqs-morphism-permanence] (1) makes $j$ quasi-compact, as required by the compactification
category in step 5. For every compactification $c=(j,r)$, the same support-composition theorem
identifies $r_*j_!$ with the exact functor $h^{\mathrm{supp}}_!$. Define a comparison in the
reverse direction, $\delta_c:D(h^{\mathrm{supp}}_!)\to Rr_*Dj_!$, by the derived-functor unit for
$r_*$. Explicitly, on a complex $K$ choose a K-injective resolution $j_!K\to I$; its component is
$Q_T(r_*j_!K)\to Q_T(r_*I)$. Resolutions exist by [prop-weil-pbc-kinjective-resolutions-exist],
and [def-amb-etale-compact-support, lem-weil-pbc-kinjective-total-derived] specify this unit and
its naturality. Since the source functor is exact, [lem-weil-pbc-exact-functor-derived-
factorization] makes its termwise functor invert quasi-isomorphisms; [lem-weil-pbc-localization-
universal-property] therefore descends the natural comparison to the derived category. This
construction uses all complexes, without truncations. For the finite compactification
$c_0=(j_0,p)$, [lem-weil-pbc-exact-functor-derived-functor] applied to the exact module functor
$p_*$ says that its derived unit is an isomorphism on every complex. Consequently $\delta_{c_0}$
is an isomorphism on the entire unbounded category.

4. Check the normalization under a proper refinement $u:V_1\to V_2$, with $uj_1=j_2$ and
$r_2u=r_1$. Write $\beta_u:Rr_{2*}Dj_{2!}\to Rr_{1*}Dj_{1!}$ for its refinement comparison. We
claim $\beta_u\delta_{c_2}=\delta_{c_1}$. Represent the input by a K-injective $J$ and resolve
$j_{1!}J\to I$. By [lem-amb-unbounded-proper-open-interchange], for the square with left proper
edge $\mathrm{id}_V$, right proper edge $u$, top open $j_1$ and bottom open $j_2$, the proper/open
map is represented by $j_{2!}J=u_*j_{1!}J\to u_*I$; the equality is the support identification of
[lem-cbc-proper-support-sheaf-composition]. Direct image preserves K-injectives by [prop-weil-pbc-
inverse-image-modules-exact, lem-weil-pbc-right-adjoint-preserves-kinjective]. Thus for a
resolution $j_{2!}J\to I_2$, the comparison to $u_*I$ lifts to $I_2\to u_*I$, with the triangle
commuting up to homotopy by [lem-weil-pbc-kinjective-hom-derived]. Apply $r_{2*}$ to this
triangle. Its top map is $r_{2*}j_{2!}J=r_{1*}j_{1!}J\to r_{1*}I$. The resolution normalization of
[lem-weil-pbc-ringed-topoi-derived-pushforward-composition] identifies the other path with
$\beta_u\delta_{c_2}$. This proves the claim, first on representatives and then on the derived
category by [lem-weil-pbc-localization-universal-property]. The comparisons here are precisely the
proper/open refinement comparisons in [lem-amb-unbounded-compact-support-comparisons].

5. Any compactification $c$ and the finite compactification $c_0$ have a common proper refinement
$d\xrightarrow{u}c$, $d\xrightarrow{v}c_0$ by [lem-cbc-compactifiable-cofiltered]. Its ambient
scheme is Noetherian by the properness argument of step 3. Put $F_c=Rr_*Dj_!$ for each
compactification. The comparisons $\beta_u:F_c\to F_d$ and $\beta_v:F_{c_0}\to F_d$ are
isomorphisms with coherent composition by [lem-amb-unbounded-compact-support-comparisons]. Step 4
gives $$\beta_u\delta_c=\delta_d=\beta_v\delta_{c_0},\qquad
\delta_c=\beta_u^{-1}\beta_v\delta_{c_0}.$$ Thus $\delta_c$ is invertible. Set
$c_h^c=\delta_c^{-1}$. For every refinement $w:c_1\to c_2$, inverting
$\beta_w\delta_{c_2}=\delta_{c_1}$ gives $c_h^{c_1}\beta_w=c_h^{c_2}$. In the common-refinement
diagram this says $$c_h^c=c_h^{c_0}\beta_v^{-1}\beta_u.$$ The right side equals the fixed map
$\delta_c^{-1}$ for every $d,u,v$; the coherent comparison cocycle identifies these expressions
with the canonical compactification comparisons. This proves the required independence without any
choice of an unspecified isomorphism.

6. It remains to compare composition maps. Choose the finite compactification of $e$ from step 1.
Apply [lem-weil-pbc-compatible-compactification-triangle] to $V\xrightarrow{h}T\xrightarrow{e}B$
and this compactification of $e$; the three schemes are qcqs by step 1. It supplies the tower used
in [lem-amb-unbounded-compact-support-comparisons]. Write $T\xrightarrow{i}\overline
T\xrightarrow{s}B$, $V\xrightarrow{a}\overline V\xrightarrow{p}\overline T$, and $U=\overline
V\times_{\overline T}T$, with $b:U\hookrightarrow\overline V$, $q:U\to T$, $j:V\hookrightarrow U$,
$bj=a$ and $pb=iq$. The geometric triangle node states that these are compactifications of
$e,h,eh$, with $s,p,q$ proper and $i,a,b,j$ open immersions. Their ambient schemes are Noetherian:
$s,p,q$ are of finite type and [lem-weil-pbc-finite-type-over-noetherian] applies successively
over $B$, $\overline T$, and $T$. On sheaves both $e^{\mathrm{supp}}_!h^{\mathrm{supp}}_!$ and
$(eh)^{\mathrm{supp}}_!$ identify with $s_*p_*a_!$ through $i_!q_*=p_*b_!$; each identification
keeps the section itself, by [lem-cbc-proper-support-sheaf-composition]. In particular
$(eh)^{\mathrm{supp}}_!$ is exact, since $e^{\mathrm{supp}}_!$ and $h^{\mathrm{supp}}_!$ are
exact, so its $D$ is defined even before making any separate geometric argument about $eh$.  Here
is the chain-level check of the comparison. Represent the input by a K-injective $J$ on $V$.
Choose resolutions $j_!J\to I$ on $U$ and $b_!I\to M$ on $\overline V$. The complex $q_*I$ is
K-injective by [prop-weil-pbc-inverse-image-modules-exact, lem-weil-pbc-right-adjoint-preserves-
kinjective]. Choose a resolution $i_!q_*I\to L$ on $\overline T$. The proper/open comparison of
[lem-amb-unbounded-proper-open-interchange] is the class of $i_!q_*I=p_*b_!I\to p_*M$. Since
$p_*M$ is K-injective, this map lifts to $L\to p_*M$, commuting with the resolution map up to
homotopy by [lem-weil-pbc-kinjective-hom-derived]. Naturality of $\delta_e$ rewrites
$(Re_!\delta_h)\circ(\delta_eD(h^{\mathrm{supp}}_!))$ as $(\delta_eRh_!)\circ
D(e^{\mathrm{supp}}_!)(\delta_h)$. Hence the successive units, followed by $\alpha_{e,h}$, are
represented by the composite $$s_*i_!q_*j_!J\longrightarrow s_*i_!q_*I\longrightarrow
s_*L\longrightarrow s_*p_*M.$$ Using the lifting triangle and the sheaf equality $i_!q_*=p_*b_!$,
this is exactly $s_*p_*b_!j_!J\to s_*p_*M$, induced by $a_!J=b_!j_!J\to b_!I\to M$. By [lem-weil-
pbc-extension-by-zero-exact], $b_!$ preserves the quasi-isomorphism $j_!J\to I$, so
$a_!J=b_!j_!J\to b_!I\to M$ is a K-injective resolution of $a_!J$. The open-extension composition
of [lem-cbc-extension-zero-composition] and the resolution normalization of [lem-weil-pbc-ringed-
topoi-derived-pushforward-composition] identify the last map with $\delta_{eh}$, after the
section-preserving map $D(\sigma_{e,h})$. Thus
$$\alpha_{e,h}\circ(Re_!\delta_h)\circ(\delta_eD(h^{\mathrm{supp}}_!))=\delta_{eh}\circ
D(\sigma_{e,h}).$$ Invert the $\delta$ maps to obtain the displayed equation of the statement.
Equality descends by [lem-weil-pbc-localization-universal-property]. For any other choices let
$\eta_h,\eta_e,\eta_{eh}$ be their canonical compactification comparisons, and write $\star$ for
horizontal composition of natural transformations. The cited refinement compatibility of
composition is $\alpha^{\prime}(\eta_e\star\eta_h)=\eta_{eh}\alpha$. Step 4 gives
$\delta_h^{\prime}=\eta_h\delta_h$ and the corresponding equalities for $e,eh$. Substitute these
equalities, using naturality to move $\eta$ past the whiskered $\delta$ maps, and both sides of
the displayed equation are postcomposed with the same $\eta_{eh}$. Hence the equation holds for
those choices too; step 5 identifies the comparisons through any common refinement.

7. Now let $h$ be separated etale of finite type. By [def-weil-etale-morphism] it is unramified,
and [lem-weil-pbc-unramified-quasi-finite-at-points] makes it locally quasi-finite. It is quasi-
compact because it is of finite type, so [pqf-lem-qf-locqf-qc] makes it quasi-finite. Construct a
morphism $h_{\Sigma!}F\to h^{\mathrm{supp}}_!F$ directly from the sum presheaf [def-weil-pbc-
etale-sum-extension]. For a lift $t:W\to V$ over $T$, its graph is a section of the separated
etale map $V_W\to W$. By [lem-weil-pbc-etale-base-change-finite-limits, lem-weil-pbc-separated-
base-change, lem-weil-pbc-etale-section-clopen-immersion] that graph is open and closed. Extend a
section in the summand indexed by $t$ by zero on the complementary open. Its support is a closed
subset of the graph, and hence proper over $W$ by [lem-weil-pbc-closed-subset-proper-over-base-
properties], since the graph is isomorphic over $W$ to $W$. Addition and restriction give a map of
presheaves into the proper-support sheaf; sheafification gives the claimed natural $A$-linear map.
It is an isomorphism on stalks. Indeed [lem-cbc-proper-support-geometric-stalk] identifies the
target stalk at $\bar t:\operatorname{Spec}\Omega\to T$ with $H^0_c(V_{\bar t},F|_{V_{\bar t}})$.
The geometric fibre is separated etale over $\Omega$; by [sbc-lem-etale-over-normal] applied to
the integral normal scheme $\operatorname{Spec}\Omega$ it is a disjoint union of copies of
$\operatorname{Spec}\Omega$. This union is finite: $h$ is quasi-compact and quasi-compactness is
preserved under base change by [lem-weil-pbc-qcqs-morphism-permanence], so its cover by these
disjoint open points has a finite subcover. A finite union of such points is finite over $\Omega$
(on rings it is the finite free algebra $\Omega^n$), hence proper by [lem-weil-pbc-finite-proper];
every closed support is proper by [lem-weil-pbc-closed-subset-proper-over-base-properties].
Sections are the finite product of the sections on the points by the sheaf axiom, and [lem-weil-
pbc-geometric-point-pullback-stalk, lem-weil-pbc-inverse-image-stalk-germ] identify each with
$F_{\bar v}$. Thus the target stalk is $\bigoplus_{h\bar v=\bar t}F_{\bar v}$. Under the generator
formula in [lem-amb-etale-sum-stalks], the source-to-target map sends a germ in the summand of $t$
to the same germ in the summand of $t\bar w$. It is the identity on these finite sums. Therefore
it is an isomorphism by [lemma-weil-pbc-geometric-stalk-conservative]; forgetting scalars detects
isomorphisms by [lem-weil-pbc-module-sheaves-colimits-forgetful].

8. For composable separated etale $V\xrightarrow{h}T\xrightarrow{e}B$, the sheaf map
$\sigma_{e,h}$ keeps the section on $V\times_BW$ unchanged by [lem-cbc-proper-support-sheaf-
composition]. A generator with a lift $v:W\to T$ and a lift $w:W\to V$ satisfying $hw=v$ first
extends its section along the graph of $w$ over $T$, then along the graph of $v$ over $B$. This is
its extension by zero along the graph of $w$ over $B$: its restriction there is the original
section and its restriction to the complementary open is zero in both constructions. The sheaf
axiom on that clopen decomposition proves equality of the two sections. Finite sums and
sheafification prove that $\sigma_{e,h}$ is exactly the stated nested-summand comparison. For the
identity morphism, the only lift over each test object is its structural map, so the same
construction is the identity. For its identity compactification, the derived unit $\delta$ is also
the identity, choosing the exact identity functor as its own derived functor with identity unit,
as permitted by [lem-weil-pbc-exact-functor-derived-functor]. Step 4 gives the identical
normalization after comparison with any other compactification.
-/
theorem quasifiniteCompactSupportExact
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T B : Scheme.{u}}
    [IsNoetherian V] [IsNoetherian T] [IsNoetherian B]
    (h : V ⟶ T) (e : T ⟶ B)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (hhq : h.IsQuasiFinite) (ehq : e.IsQuasiFinite) :
    ∃ (L : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
        [LocallyOfFiniteType f],
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
          Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)),
      ∃ (ι : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f]
        [LocallyOfFiniteType f],
        L f ⟶ lowerStar (ModuleCat.{u + 1} A) f),
      ∃ (o : ∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
          (f : X ⟶ Y) [Etale f] [IsSeparated f] [QuasiCompact f],
          etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ≅ L f),
      ∃ (hA : (L h).Additive),
      ∃ (hL : PreservesFiniteLimits (L h)),
      ∃ (hC : PreservesFiniteColimits (L h)),
      ∃ (eA : (L e).Additive),
      ∃ (eL : PreservesFiniteLimits (L e)),
      ∃ (eC : PreservesFiniteColimits (L e)),
      ∃ (heA : (L (h ≫ e)).Additive),
      ∃ (heL : PreservesFiniteLimits (L (h ≫ e))),
      ∃ (heC : PreservesFiniteColimits (L (h ≫ e))),
      ∃ (c_h : ∀ c : Compactification h,
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
          @Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (L h) hA hL hC),
      ∃ (c_e : ∀ c : Compactification e,
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
          @Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (L e) eA eL eC),
      ∃ (c_he : ∀ c : Compactification (h ≫ e),
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
          @Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (L (h ≫ e)) heA heL heC),
      ∃ (idA : ∀ (X : Scheme.{u}) [IsNoetherian X], (L (𝟙 X)).Additive),
      ∃ (idL : ∀ (X : Scheme.{u}) [IsNoetherian X],
        PreservesFiniteLimits (L (𝟙 X))),
      ∃ (idC : ∀ (X : Scheme.{u}) [IsNoetherian X],
        PreservesFiniteColimits (L (𝟙 X))),
      ∃ (c_id : ∀ (X : Scheme.{u}) [IsNoetherian X] (c : Compactification (𝟙 X)),
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
        @Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (L (𝟙 X)) (idA X) (idL X) (idC X)),
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) [IsSeparated f]
        [LocallyOfFiniteType f]
        (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
        (V : Y.Etale),
        Function.Injective (((ι f).app F).hom.app (Opposite.op V)) ∧
        (∀ s : F.obj.obj (Opposite.op
            ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)),
          (∃ t, (((ι f).app F).hom.app (Opposite.op V)) t = s) ↔
          ∃ T₀ : TopologicalSpace.Closeds
              ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).left,
            (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
              (v₀ : Spec (.of Ω) ⟶
                ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).left),
              v₀ default ∈ T₀ ↔
                (Scheme.pointSmallEtale
                  (v₀ ≫ ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V).hom)).toPresheafFiber
                    ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)
                    (Over.homMk v₀) F.obj s ≠ 0) ∧
            IsProper ((Scheme.IdealSheafData.vanishingIdeal T₀).subschemeι ≫
              pullback.fst V.hom f))) ∧
      (∀ c d : Compactification h,
        (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
            (c_h d).hom = (c_h c).hom) ∧
      (∀ c d : Compactification e,
        (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
            (c_e d).hom = (c_e c).hom) ∧
      (∀ c d : Compactification (h ≫ e),
        (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
            (c_he d).hom = (c_he c).hom) ∧
      (∀ (X : Scheme.{u}) [IsNoetherian X] (c d : Compactification (𝟙 X)),
        (rightDerivedLowerShriekOfCompactificationIso A c d).hom ≫
            (c_id X d).hom = (c_id X c).hom) ∧
      (∀ (c : Compactification h) (d : Compactification (𝟙 V)),
        HEq c d → HEq (c_h c) (c_id V d)) ∧
      (∀ (c : Compactification e) (d : Compactification (𝟙 T)),
        HEq c d → HEq (c_e c) (c_id T d)) ∧
      (∀ (c : Compactification (h ≫ e)) (d : Compactification (𝟙 V)),
        HEq c d → HEq (c_he c) (c_id V d)) ∧
      (∃ σ : L h ⋙ L e ≅ L (h ≫ e),
        (∀ F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A),
          σ.hom.app F ≫ (ι (h ≫ e)).app F =
            (ι e).app ((L h).obj F) ≫
              (lowerStar (ModuleCat.{u + 1} A) e).map ((ι h).app F) ≫
              (lowerStarComp (ModuleCat.{u + 1} A) h e).hom.app F) ∧
        ((unboundedEtaleLowerShriekCompIso A h e ≪≫
          (rightDerivedLowerShriekIso A
            (HasCompactification.compactification (h ≫ e))).symm ≪≫
          c_he (HasCompactification.compactification (h ≫ e))) =
          (Functor.isoWhiskerRight
            ((rightDerivedLowerShriekIso A
                (HasCompactification.compactification h)).symm ≪≫
              c_h (HasCompactification.compactification h))
            (rightDerivedLowerShriek (ModuleCat.{u + 1} A) e) ≪≫
          Functor.isoWhiskerLeft
            (@Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (L h) hA hL hC)
            ((rightDerivedLowerShriekIso A
                (HasCompactification.compactification e)).symm ≪≫
              c_e (HasCompactification.compactification e)) ≪≫
          (Functor.mapDerivedCategoryCompIso (L h) (L e)).symm ≪≫
          Functor.mapDerivedCategoryNatIso σ)) ∧
        (∀ [Etale h] [Etale e]
          (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : V.Etale),
          ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) h).unit.app F).hom.app
              (Opposite.op W) ≫
            ((o h).hom.app F).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W)) ≫
            ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) e).unit.app
              ((L h).obj F)).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W)) ≫
            ((o e).hom.app ((L h).obj F)).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj
                ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W))) ≫
            (σ.hom.app F).hom.app
              (Opposite.op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj
                ((MorphismProperty.Over.map ⊤ (inferInstance : Etale h)).obj W))) =
          ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A)
              (h ≫ e)).unit.app F).hom.app (Opposite.op W) ≫
            ((o (h ≫ e)).hom.app F).hom.app
              (Opposite.op
                ((MorphismProperty.Over.map ⊤ (inferInstance : Etale (h ≫ e))).obj W)) ≫
            ((L (h ≫ e)).obj F).obj.map
              ((MorphismProperty.Over.mapComp ⊤ (inferInstance : Etale h)
                (inferInstance : Etale e)).inv.app W).op)) ∧
      (∀ (X Y : Scheme.{u}) [IsNoetherian X] [IsNoetherian Y]
        (f : X ⟶ Y) [Etale f] [IsSeparated f] [QuasiCompact f]
        (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)),
        (o f).hom.app F ≫ (ι f).app F =
          etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) f F) ∧
      (∀ (X : Scheme.{u}) [IsNoetherian X], ∃ i_id : L (𝟙 X) ≅ 𝟭 (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} A)),
        i_id.hom = ι (𝟙 X) ≫ (lowerStarId (ModuleCat.{u + 1} A) X).hom ∧
        (rightDerivedLowerShriekIso A (Compactification.ofIsProper (𝟙 X))).symm ≪≫
          c_id X (Compactification.ofIsProper (𝟙 X)) ≪≫
          @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _
            (F := L (𝟙 X))
            (G := 𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
            (idA X) (by infer_instance) (idL X) (idC X)
            (by infer_instance) (by infer_instance) i_id ≪≫
          Functor.mapDerivedCategoryIdIso _ =
          unboundedEtaleLowerShriekId A X) := by
  sorry
end AlgebraicGeometry.Etale
