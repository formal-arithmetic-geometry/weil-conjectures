/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.KInjectiveResolutions
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import Sheaf.Paper.UnboundedProperOpenInterchange
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.Compactification.CategoryBaseChange
import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Unbounded compact support composed with a proper direct image

Source: Stacks Project, Tags 0F7H, 0F7I, 0F7J and 0F7B, case (b)
(blueprint: lem-sf-unbounded-compact-support-proper-composition).

The common-refinement isomorphism and the proper/open tower isomorphism are the existing
ordinary small-etale constructions. We state their normalization on arbitrary proper
refinements, including noncartesian ones. The two definitions assemble the trivial proper
compactification normalization and the resulting composition comparison, with real data.
All categories here are unbounded, with constant finite commutative module coefficients.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Normalize a proper compact-support candidate by comparison with `(id_X,f)` and the
canonical identity-open adjunction. Source: Stacks Project, Tags 0F7H and 0F7I
(blueprint: lem-sf-unbounded-compact-support-proper-composition). -/
noncomputable def unboundedEtaleProperCandidateIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      R((f)_*[ModuleCat.{u + 1} A]) :=
  rightDerivedLowerShriekOfCompactificationIso A c (Compactification.ofIsProper f) ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso
          (Adjunction.leftAdjointIdIso
            (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
            (upperStarId (ModuleCat.{u + 1} A) X)) ≪≫
        Functor.mapDerivedCategoryIdIso _) _ ≪≫
    Functor.leftUnitor _

/-- The specified proper/open composition comparison: compactify `f` into `d.Z` by the
closure construction `c.ofComp d`, use the existing proper/open tower isomorphism, and compare
its output with `c`. No arbitrary isomorphism is chosen. Source: Stacks Project, Tag 0F7J
(blueprint: lem-sf-unbounded-compact-support-proper-composition). -/
noncomputable def unboundedEtaleProperCompositionIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsProper f]
    [QuasiCompact g] (d : Compactification g) (c : Compactification (f ≫ g)) :
    R((f)_*[ModuleCat.{u + 1} A]) ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c :=
  Functor.isoWhiskerRight
      (unboundedEtaleProperCandidateIso A f (c.ofComp d).restrict).symm _ ≪≫
    rightDerivedLowerShriekOfCompactificationCompIso A d (c.ofComp d) ≪≫
    rightDerivedLowerShriekOfCompactificationIso A (d.comp (c.ofComp d)) c

/-- On every proper refinement, the common-refinement isomorphism is the proper direct
image of the specified proper/open map. Its sheaf identification is fixed inside the common
direct image, and its derived value is fixed on every K-injective representative and every
K-injective resolution of its extension by zero. No cartesian or density condition is used.

Source: Stacks Project, Tags 0F7B (b) and 0F7I
(blueprint: lem-sf-unbounded-compact-support-proper-composition).
Proof, steps 1--2: finite-type schemes over the field, and their proper compactification
ambients, are Noetherian (lem-weil-pbc-finite-type-over-noetherian). A finite ring is torsion.
Apply lem-amb-unbounded-proper-open-interchange to the square with left edge `id_X`, right
edge `r.hom` and open edges `c.i,d.i`. Its sheaf map is the equality of the proper-support
subsheaves, hence restricts to the identity on X. The K-injective formula is precisely the
one below, after identifying the derived identity image with the identity. Apply `R(d.g)_*`
and the canonical direct-image compositor
(lem-weil-pbc-ringed-topoi-derived-pushforward-composition). Step 3 compares this map through
common refinements; vertical pasting and equalizing parallel refinements identify it with
the existing common-refinement isomorphism. -/
theorem unboundedEtaleProperRefinement_normalization
    (k : Type u) [Field k] (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    {c d : Compactification h} (r : c.Refinement d) :
    ∃ (θ : (d.i)_!open[ModuleCat.{u + 1} A] ≅
          (c.i)_!open[ModuleCat.{u + 1} A] ⋙ (r.hom)_*[ModuleCat.{u + 1} A])
      (γ : D((d.i)_!open[ModuleCat.{u + 1} A]) ≅
          D((c.i)_!open[ModuleCat.{u + 1} A]) ⋙ R((r.hom)_*[ModuleCat.{u + 1} A])),
      (∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A),
        θ.hom.app F ≫
            (r.hom)_*[ModuleCat.{u + 1} A].map
              ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app F) ≫
            (lowerStarComp (ModuleCat.{u + 1} A) c.i r.hom d.i r.i_hom.symm).hom.app F =
          (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) d.i).app F) ∧
      (∀ (J : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [J.IsKInjective]
        (I : CochainComplex (Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [I.IsKInjective]
        (ρ : ((c.i)_!open[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).obj J ⟶ I)
        [QuasiIso ρ],
        γ.hom.app (DerivedCategory.Q.obj J) ≫
            R((r.hom)_*[ModuleCat.{u + 1} A]).map
              (((c.i)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app J ≫
                DerivedCategory.Q.map ρ) ≫
            (((r.hom)_*[ModuleCat.{u + 1} A]).rightDerivedFunctorObjQIso I).hom =
          ((d.i)_!open[ModuleCat.{u + 1} A]).mapDerivedCategoryFactors.hom.app J ≫
            DerivedCategory.Q.map
              ((NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app J) ≫
            DerivedCategory.Q.map
              (((r.hom)_*[ModuleCat.{u + 1} A].mapHomologicalComplex (.up ℤ)).map ρ)) ∧
      (rightDerivedLowerShriekOfCompactificationIso A d c).hom =
        Functor.whiskerRight γ.hom R((d.g)_*[ModuleCat.{u + 1} A]) ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft D((c.i)_!open[ModuleCat.{u + 1} A])
            (Functor.rightDerivedFunctorCompIso'
              ((r.hom)_*[ModuleCat.{u + 1} A]) ((d.g)_*[ModuleCat.{u + 1} A])
              (lowerStarComp (ModuleCat.{u + 1} A) r.hom d.g c.g r.hom_g.symm)).hom := by
  sorry

/-- The normalized refinement comparisons have identity and composition laws. Comparisons
through arbitrary common refinements are independent of the refinement and satisfy the
cocycle condition. Source: Stacks Project, Tag 0F7I
(blueprint: lem-sf-unbounded-compact-support-proper-composition).
Proof, step 3: vertical proper/open pasting gives `C_(vu)=C_v ≫ C_u`, and the identity square
gives the identity. The cofiltered category of compactifications
(lem-cbc-compactifiable-cofiltered) supplies a common dominating object and equalizers of
parallel arrows. Cancelling the added invertible factors shows common-refinement
independence. Choose one refinement dominating three compactifications and cancel the
middle comparison and its inverse to obtain the cocycle. -/
theorem unboundedEtaleProperRefinement_coherence
    (k : Type u) [Field k] (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h] :
    (∀ c : Compactification h,
      rightDerivedLowerShriekOfCompactificationIso A c c = Iso.refl _) ∧
    (∀ c d e : Compactification h,
      rightDerivedLowerShriekOfCompactificationIso A c d ≪≫
        rightDerivedLowerShriekOfCompactificationIso A d e =
          rightDerivedLowerShriekOfCompactificationIso A c e) ∧
    (∀ (c d e : Compactification h) (r : e.Refinement c) (s : e.Refinement d),
      (rightDerivedLowerShriekOfCompactificationIso A c e).hom ≫
        (rightDerivedLowerShriekOfCompactificationIso A d e).inv =
          (rightDerivedLowerShriekOfCompactificationIso A c d).hom) := by
  sorry

/-- Every proper/open tower computes the same specified composition isomorphism; hence it
is natural in the unbounded input and compatible with all proper-refinement identifications.
The proper identification uses exactly the trivial compactification.

Source: Stacks Project, Tags 0F7H--0F7J
(blueprint: lem-sf-unbounded-compact-support-proper-composition).
Proof, step 4: for `(id_X,f)` the degreewise extension by zero is the identity, by the
presheaf formula of def-weil-pbc-extension-by-zero. Comparing any compactification with this
one gives the displayed normalization. Step 5: use lem-cbc-compactifiable-compatible-tower
to compactify `f` over the ambient of a compactification of `g`. Apply the unbounded
proper/open interchange in its cartesian square, then compose proper direct images and
open extensions by lem-weil-pbc-ringed-topoi-derived-pushforward-composition and
lem-cbc-extension-zero-composition. This is the existing model composition isomorphism.
Step 6: two towers have a common refining tower. Horizontal and vertical pasting of
lem-amb-unbounded-proper-open-interchange and naturality commute its six proper/open
squares. The resulting equation is `C_gf D_2 = D_1 (C_g F_f1) (F_g2 C_f)`.
Cancel the invertible common-refinement comparisons using the preceding cocycle. This
proves the equation for every tower and compatibility with arbitrary refinements of the
input and output compactifications. Every factor is a natural transformation on the
whole unbounded category; no boundedness or constructibility hypothesis is used.

Full DAG proof for subsequent proof work:

1. Check the geometric and coefficient hypotheses first. A field is Noetherian since its only
ideals are zero and the unit ideal. By [lem-weil-pbc-finite-type-over-noetherian], $X,Y,S$ are
Noetherian, and so is every ambient compactification scheme: its proper structural map is of
finite type over its Noetherian target. Properness includes separatedness and finite type
[def-weil-proper-morphism]. The separatedness and local finite type of $gf$ follow from
[lem-weil-pbc-proper-fp-permanence](e); quasi-compactness follows by taking a finite affine
cover of $g^{-1}(W)$ for an affine $W\subset S$ and then finite affine covers of its inverse
images under $f$ [def-weil-finite-type-morphism]. The compactifications in the statement
therefore have exactly the type required by [def-amb-etale-compact-support]. A finite ring is a
torsion ring: its additive group has finite exponent. In particular, the unbounded, finite-ring
assertion of [lem-amb-unbounded-proper-open-interchange] applies; no invertible prime is needed.

2. Let $u:c_1\to c_2$ be a refinement for $h:T\to B$. Apply
[lem-amb-unbounded-proper-open-interchange] to the square with top
$j_1:T\hookrightarrow\overline T_1$, bottom $j_2:T\hookrightarrow\overline T_2$, left proper map
$1_T$ and right proper map $u$. The square need not be cartesian. Its map, after identifying
$R1_{T,*}$ with the identity, is an isomorphism $\gamma_u:j_{2,!}\to Ru_*j_{1,!}$. On a
K-injective representative $J$, the cited statement specifies exactly $j_{2,!}J\cong
u_*j_{1,!}J\to u_*I$ for a K-injective resolution $j_{1,!}J\to I$; the sheaf identification is
the identity on $T$. Thus it is the map specified in the item, not merely an unspecified
isomorphism between its source and target. Put $F_c=Rr_*j_!$ and define
$$C_u:F_{c_2}\xrightarrow{Rr_{2,*}\gamma_u}Rr_{2,*}Ru_*j_{1,!}\xrightarrow{\kappa^{-1}}F_{c_1}.$$
Here $r_2u=r_1$ and $\kappa$ is the canonical natural comparison of
[lem-weil-pbc-ringed-topoi-derived-pushforward-composition], applied to the constant-$A$ ringed
small etale topoi. Every factor is invertible and natural on the entire unbounded category.

3. For $u:c_1\to c_2$ and $v:c_2\to c_3$, the vertical-pasting and identity assertions of
[lem-amb-unbounded-proper-open-interchange], with all left proper maps identities, give
$\gamma_{vu}=(Rv_*\gamma_u)\gamma_v$ and $\gamma_{1}=1$, with the specified direct-image
compositors inserted. Whiskering by the proper structural direct image, as in step 2, gives
$C_{vu}=C_uC_v$ and $C_1=1$. The cofilteredness statement [lem-cbc-compactifiable-cofiltered]
supplies both common refinements and equalizers of parallel arrows. For $d\xrightarrow{u_1}c_1$,
$d\xrightarrow{u_2}c_2$, set $I_{12}=C_{u_2}^{-1}C_{u_1}:F_{c_1}\to F_{c_2}$. For two such
choices, first dominate their refinement objects and then equalize the resulting two pairs of
arrows to $c_1,c_2$. The equation $C_{vu}=C_uC_v$ makes both expressions equal, since the extra
invertible factor from the common dominating object cancels. For three compactifications choose
a single dominating object and write all three comparisons this way. Direct cancellation gives
$I_{23}I_{12}=C_{u_3}^{-1}C_{u_2}C_{u_2}^{-1}C_{u_1}=I_{13}$. Also $I_{11}=1$ and
$I_{21}=I_{12}^{-1}$. These equations prove choice independence and the cocycle condition for
the actual maps of step 2, and justify the notation $Rh_!$.

4. Because $f$ is proper, $(1_X,f)$ is a compactification. For an identity open immersion every
object of the small etale site factors through the open. The presheaf formula in
[def-weil-pbc-extension-by-zero] is therefore already the original sheaf, with its original
restrictions and maps, so $(1_X)_!=1$ naturally, also degreewise on complexes. The candidate of
[def-amb-etale-compact-support] for $(1_X,f)$ is consequently exactly $Rf_*$. The comparisons
$I$ of step 3 identify every other $Rf_!^c$ with this candidate. This defines the required
normalization $Rf_!\cong Rf_*$; its value at the trivial compactification is the identity by
$I_{11}=1$.

5. Construct the composition comparison on compatible models. Fix
$d=(i:Y\hookrightarrow\overline Y,s:\overline Y\to S)$ for $g$ and any compactification of $gf$.
By [lem-cbc-compactifiable-compatible-tower], choose $e=(a:X\hookrightarrow\overline
X,p:\overline X\to\overline Y)$ compactifying $if$. Its statement supplies $V=\overline
X\times_{\overline Y}Y$, $b:V\hookrightarrow\overline X$, $q:V\to Y$ and $j:X\hookrightarrow V$
with $pb=iq$, $bj=a$, $qj=f$, and all the required proper/open properties. The square with
horizontal maps $b,i$ has the unbounded interchange isomorphism $\Gamma:i_!Rq_*\to Rp_*b_!$ of
[lem-amb-unbounded-proper-open-interchange]. Whisker it by $Rs_*$ and $j_!$. The canonical
direct-image composition of [lem-weil-pbc-ringed-topoi-derived-pushforward-composition] and the
degreewise open composition of [lem-cbc-extension-zero-composition] give the natural isomorphism
$$D_{d,e}: (Rs_*i_!)(Rq_*j_!)\xrightarrow{Rs_*\Gamma
j_!}Rs_*Rp_*b_!j_!\xrightarrow{\sim}R(sp)_*a_!.$$ These are exactly the candidates of
[def-amb-etale-compact-support] for $g,f,gf$. Use step 4 and $I_{(1_X,f),(j,q)}$ to identify the
second input candidate with $Rf_*$. Finally use the comparisons of step 3 for $g$ and $gf$. This
gives $\alpha_{g,f}:Rg_!Rf_*\xrightarrow{\sim}R(gf)_!$ with precisely the proper/open
composition normalization in the statement.

6. Verify compatibility with refinement of a whole tower. Any two towers have a common refining
tower by [lem-cbc-compactifiable-compatible-tower], so consider a tower indexed by $1$ mapping
to one indexed by $2$. The cited statement supplies proper maps $u:\overline Y_1\to\overline
Y_2$, $v:\overline X_1\to\overline X_2$, $w:V_1\to V_2$ with $ui_1=i_2$, $va_1=a_2$, $wj_1=j_2$,
$vb_1=b_2w$, $p_2v=up_1$, $q_2w=q_1$, and $s_2u=s_1$. For this calculation abbreviate
$I_i=i_{i!}$, $J_i=j_{i!}$, $B_i=b_{i!}$, $P_i=Rp_{i*}$, $L_i=Rq_{i*}$, $M=Ru_*$, $H=Rv_*$ and
$H'=Rw_*$. Write $\gamma_A:J_2\to H'J_1$, $\gamma_D:I_2\to MI_1$, $\gamma_E:B_2J_2\to HB_1J_1$,
$\gamma_F:B_2H'\to HB_1$ for the interchange maps of the four refinement squares, and
$\gamma_B:I_2L_2\to P_2B_2$, $\gamma_C:I_1L_1\to P_1B_1$ for the two model squares. Every square
has proper verticals and open horizontals; the refinement squares need not be cartesian. The two
pasting laws in [lem-amb-unbounded-proper-open-interchange] say
$$\gamma_E=(\gamma_FJ_1)(B_2\gamma_A),\qquad(M\gamma_C)(\gamma_DL_1)=(P_2\gamma_F)(\gamma_BH').$$
Naturality of $\gamma_B$ at $\gamma_A$ says
$$(P_2B_2\gamma_A)(\gamma_BJ_2)=(\gamma_BH'J_1)(I_2L_2\gamma_A).$$ Substitute these equalities
to obtain $$(P_2\gamma_E)(\gamma_BJ_2)=(M\gamma_CJ_1)(\gamma_DL_1J_1)(I_2L_2\gamma_A).$$
Composition is read right to left. Applying $Rs_{2,*}$ and inserting the canonical direct-image
compositors of [lem-weil-pbc-ringed-topoi-derived-pushforward-composition] and the open
compositors of [lem-cbc-extension-zero-composition] identifies this with
$$C_{gf}D_2=D_1(C_gF_{f,1})(F_{g,2}C_f).$$ Here $F_{f,i}=L_iJ_i$, $F_{g,i}=Rs_{i,*}I_i$,
$D_i=D_{d_i,e_i}$, and $C_f,C_g,C_{gf}$ are precisely the comparisons from model $2$ to model
$1$ constructed in step 2. Thus the composition map intertwines all three specified refinement
comparisons. Compare two towers through their common refining tower and cancel invertible
comparisons using the cocycle in step 3. The normalized map of step 5 is independent of all
tower and compactification choices. All its factors are natural transformations on unbounded
derived categories, so naturality in the input complex is also established; no boundedness or
constructibility hypothesis entered the argument.
-/
theorem unboundedEtaleProperComposition_normalization
    (k : Type u) [Field k] (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y S : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [IsSeparated (S ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (f : X ⟶ Y) (g : Y ⟶ S)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))] [IsProper f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] :
    (∀ (c : Compactification f) (d : Compactification f),
      rightDerivedLowerShriekOfCompactificationIso A c d ≪≫
        unboundedEtaleProperCandidateIso A f d = unboundedEtaleProperCandidateIso A f c) ∧
    (unboundedEtaleProperCandidateIso A f (Compactification.ofIsProper f) =
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso
            (Adjunction.leftAdjointIdIso
              (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
              (upperStarId (ModuleCat.{u + 1} A) X)) ≪≫
          Functor.mapDerivedCategoryIdIso _) _ ≪≫ Functor.leftUnitor _) ∧
    (∀ (d : Compactification g) (c : Compactification (f ≫ g))
      (e : Compactification (f ≫ d.i)),
      (unboundedEtaleProperCompositionIso A f g d c).hom =
        Functor.whiskerRight (unboundedEtaleProperCandidateIso A f e.restrict).inv
            (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d) ≫
          (rightDerivedLowerShriekOfCompactificationCompIso A d e).hom ≫
          (rightDerivedLowerShriekOfCompactificationIso A (d.comp e) c).hom) ∧
    (∀ (d₁ d₂ : Compactification g) (c₁ c₂ : Compactification (f ≫ g)),
      Functor.whiskerLeft R((f)_*[ModuleCat.{u + 1} A])
          (rightDerivedLowerShriekOfCompactificationIso A d₁ d₂).hom ≫
        (unboundedEtaleProperCompositionIso A f g d₂ c₂).hom =
      (unboundedEtaleProperCompositionIso A f g d₁ c₁).hom ≫
        (rightDerivedLowerShriekOfCompactificationIso A c₁ c₂).hom) := by
  sorry

end AlgebraicGeometry.Etale
