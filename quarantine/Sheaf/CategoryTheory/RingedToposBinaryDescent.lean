module


public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal

import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.CategoryTheory.SheafSubcategoryComparison
import WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems

/-!
# Binary derived open descent for modules on a ringed topos

Source: literature/stacks-project/cohomology.tex, Tags 08DG and 08BU (blueprint:
lem-sp-ringed-topos-binary-descent).
-/


@[expose] public section

universe u v r w s

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-- Expose Mathlib's small-model abelian sheafification at the chosen site universe.
Source: Stacks 03CV (blueprint: lem-sp-ringed-topos-binary-descent). -/
noncomputable instance binaryDescent_hasSheafify {C : Type u} [Category.{v} C]
    [EssentiallySmall.{s} C] (J : GrothendieckTopology C) :
    HasSheafify J AddCommGrpCat.{s} :=
  hasSheafifyEssentiallySmallSite J AddCommGrpCat.{s}

/-- Expose Mathlib's transport of the local criterion for abelian sheafification.
Source: Stacks 03CV (blueprint: lem-sp-ringed-topos-binary-descent). -/
noncomputable instance binaryDescent_wEqualsLocallyBijective
    {C : Type u} [Category.{v} C] [EssentiallySmall.{s} C]
    (J : GrothendieckTopology C) :
    J.WEqualsLocallyBijective AddCommGrpCat.{s} :=
  letI : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{s} C).inverse.op) AddCommGrpCat.{s} :=
    fun _ ↦ HasLimitsOfShape.of_small.{s, s} AddCommGrpCat.{s} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J (A := AddCommGrpCat.{s})

/-- Termwise restriction to the localized site, using the recorded restriction functor.
Source: Stacks 03DH and 03DJ (blueprint: lem-sp-ringed-topos-binary-descent). -/
noncomputable def moduleOverComplex {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r}) (U : C) :=
  letI := module_overFunctor_preservesZero.{u, v, max u v r, r} R U
  (SheafOfModules.overFunctor.{max u v r} R U).mapHomologicalComplex (.up ℤ)

/-- Termwise relocalization along a map of objects of the site.
Source: Stacks 03DH (blueprint: lem-sp-ringed-topos-binary-descent). -/
noncomputable def moduleOverMapComplex {C : Type u} [Category.{v} C] [HasPullbacks C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r}) {U V : C} (f : U ⟶ V) :=
  (SheafOfModules.overMap.{max u v r} R f).mapHomologicalComplex (.up ℤ)

/-- The sectionwise identity comparing restriction with iterated restriction on complexes.
Source: Stacks 03DH (blueprint: lem-sp-ringed-topos-binary-descent). -/
noncomputable def moduleOverComplexComp {C : Type u} [Category.{v} C] [HasPullbacks C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r}) {U V : C} (f : U ⟶ V) :
    moduleOverComplex R U ≅ moduleOverComplex R V ⋙ moduleOverMapComplex R f :=
  letI := module_overFunctor_preservesZero.{u, v, max u v r, r} R U
  letI := module_overFunctor_preservesZero.{u, v, max u v r, r} R V
  NatIso.mapHomologicalComplex (SheafOfModules.overFunctorMap R f).symm (.up ℤ)

/-- The direct-image restriction map is the adjoint of restriction of the counit.
Source: Stacks 08DG, cone construction (blueprint: lem-sp-ringed-topos-binary-descent). -/
noncomputable def restrictionAdjunctionMap
    {D DU DW : Type*} [Category D] [Category DU] [Category DW]
    {rU : D ⥤ DU} {rW : D ⥤ DW} {rUW : DU ⥤ DW}
    {RU : DU ⥤ D} {RW : DW ⥤ D}
    (adjU : rU ⊣ RU) (adjW : rW ⊣ RW) (comp : rW ≅ rU ⋙ rUW) (A : DU) :
    RU.obj A ⟶ RW.obj (rUW.obj A) :=
  (adjW.homEquiv _ _) (comp.hom.app (RU.obj A) ≫ rUW.map (adjU.counit.app A))

set_option maxHeartbeats 800000 in
-- The five localization models require simultaneous universe and instance elaboration.
/-- Binary descent for unbounded derived module sheaves on a ringed Grothendieck topos.

Source: Stacks Project, Cohomology, Tags 08DG (gluing over two opens) and 08BU
(the lower-shriek Mayer--Vietoris triangle); the extension from ringed spaces to a
ringed Grothendieck topos is the statement of this blueprint node
(blueprint: lem-sp-ringed-topos-binary-descent).

The site has a terminal object and pullbacks and represents the two subterminal
objects. Every small-site topos and pair of subterminals has such a presentation
by Step 1 below. Site object, morphism and ring universes are independent; modules
live in their maximum. The natural isomorphisms `qU`, `qV`, `qW`, `qUW`, `qVW`
identify restriction on EVERY complex and cochain map, so determine the functors
by localization. The two `comp_on_complexes` equations fix the derived composition
comparisons to the sectionwise identities, rather than arbitrary isomorphisms.
The left and right adjoints are specified by their universal properties. Exact
termwise extension by zero is the left adjoint, hence any displayed left adjoint
is uniquely isomorphic to it compatibly with its adjunction. The right adjoints
are likewise the derived direct images. All arrow formulas are adjunction mates.
The gluing is unconditional; every common cohomological interval is preserved
by this same glued object. One connecting transformation works for every M.

Proof:
1. Choose a small site $\mathcal S$ presenting $\mathcal T$. Starting with its sheafified
   representables and $1,U,V$, close a set of chosen objects under finite limits, by adjoining the
   limits of all finite diagrams at each of countably many stages. Such limits exist by [lem-weil-
   pbc-site-sheaf-sets-limits-sectionwise]; each stage is a set since the sheaf category has set-
   valued Hom sets. Apply [lem-weil-pbc-sheaf-subcategory-comparison] to the resulting full
   subcategory $\mathcal E$, retaining the epimorphic families $\{C\times U,C\times V\}\to C$.
   They are epimorphic because $U\cup V=1$, and local surjectivity is preserved by pullback. This
   gives a small subcanonical site with $1,U,V,W$ represented by its objects. Under the nerve
   equivalence, a ring or module is sent to its sheaf of generalized sections
   $C\mapsto\operatorname{Hom}(C,-)$; its operations are the induced operations on these sections.
   The inverse equivalence recovers the operations, since an equivalence preserves finite products
   and their diagrams of identities. Thus the ring and module categories are identified, including
   the slice categories as follows. A sheaf $F$ on $\mathcal E/Z$ corresponds to the sheaf
   $H(C)=\coprod_{s:C\to Z}F(C,s)$ over $h_Z$, with projection $(s,x)\mapsto s$. This is a sheaf:
   a matching family first glues its $s$ coordinates in $h_Z$, then glues its $x$ coordinates in
   $F$ on the localized site. Conversely take the fibre over $s$ of a sheaf $H\to h_Z$; the two
   constructions are inverse sectionwise. Ring and module operations are the same operations in
   each fibre, identifying modules over the restricted ring in both descriptions. These are
   additive exact equivalences: their inverse functors preserve kernels and cokernels by their
   universal properties. They induce derived equivalences by [lem-sf-exact-functor-derived-
   triangulated], so it suffices to work on $\mathcal E$ and its localized sites.
2. On $\mathcal E/Z$, restriction and relocalization are the sectionwise functors of [def-pur-
   localized-ringed-site]. By [lem-pur-site-restriction-module-adjunction-exact], $j_Z^*$ and
   $j_{Z!}$ are exact, with $j_{Z!}\dashv j_Z^*$. The explicit presheaf in [def-weil-extension-by-
   zero-presheaf] is $P_F(C)=F(C\to Z)$ if $C\to Z$ exists, and $0$ otherwise, because $Z$ is
   subterminal; $j_{Z!}F=P_F^\#$. Restriction commutes with underlying abelian sheafification by
   [lem-cbc-sieve-slice-sheafification]; the comparison is module-linear since both actions are
   the extensions of the same sectionwise scalar action through the sheafification unit [lem-pc-
   sites-module-sheafification-interface]. For $C\to U$, a map $C\to V$ is exactly a map $C\to W$.
   The presheaf formula therefore gives $j_U^*j_{V!}F=k_{U!}(F|_W)$, where $k_U:W\to U$; taking
   $V=U$ gives $j_U^*j_{U!}F=F$. Interchanging the displayed names gives
   $j_V^*j_{U!}F=k_{V!}(F|_W)$ and $j_V^*j_{V!}F=F$. These comparisons preserve units, counits and
   nested-open maps, since before sheafification each nonzero component is the identity on the
   indicated summand.
3. For module sheaves [def-weil-sheaf-of-modules-category], restriction to $U,V$ jointly detects
   zero objects: if $F|_U=F|_V=0$, a section of $F(C)$ restricts to zero on the covering $C\times
   U,C\times V$ from Step 1, hence is zero by the separatedness part of the sheaf condition. Exact
   restriction then detects exactness of any module sequence by applying this zero test to its
   kernel, cokernel and middle homology. Also, exact restriction commutes with $H^q=\ker
   d^q/\operatorname{im}d^{q-1}$ [def-weil-abstract-derived-category]. Consequently it detects
   vanishing of cohomology and quasi-isomorphisms of complexes.
4. The module categories on $\mathcal E$ and all its slices have K-injective resolutions by [prop-
   pur-kinjective-resolutions-exist]. For a K-injective $I$ and an acyclic complex $L$ on a slice,
   the termwise adjunction gives
   $\operatorname{Hom}_{K}(L,j_Z^*I)=\operatorname{Hom}_{K}(j_{Z!}L,I)=0$, since $j_{Z!}$ is
   exact. Thus restriction preserves K-injectives, directly from [def-pur-kinjective-complex]. For
   a K-injective $J$ on the slice,
   $\operatorname{Hom}_{K}(L,j_{Z*}J)=\operatorname{Hom}_{K}(j_Z^*L,J)=0$ for every acyclic $L$ on
   the ambient site, so direct image preserves K-injectives as well. Here $j_Z^*\dashv j_{Z*}$ is
   the module adjunction [lem-weil-pbc-ringed-topoi-module-adjunction], with the unchanged
   restricted ring. Hence $Rj_{Z*}$ is computed as $j_{Z*}J$ on a K-injective representative $J$,
   and its adjunction with exact restriction is [lem-pc-derived-adjoint-functors]. Exact
   restriction and extension by zero induce triangulated functors termwise by [lem-sf-exact-
   functor-derived-triangulated].
5. Using the slice evaluation rule [def-pur-localized-ringed-site], for a module sheaf $F$ on
   $\mathcal E/Z$, the underived right adjoint is $(j_{Z*}F)(C)=F(C\times Z\to Z)$, with $R(C)$
   acting through restriction to $R(C\times Z)$. It is a sheaf because $C\mapsto C\times Z$ takes
   covers and their overlaps to the corresponding covers and overlaps in the slice. Indeed a map
   $M|_Z\to F$ defines $M(C)\to M(C\times Z)\to F(C\times Z)$; the inverse evaluates on $C\to Z$,
   where $C\times Z=C$. These formulas are inverse by naturality. For $C\to U$, $C\times V=C\times
   W$, so $j_U^*j_{V*}F=k_{U*}(F|_W)$ as module functors, and $j_U^*j_{U*}=1$. Apply these
   equalities to a K-injective representative of $B$; its restriction to $W$ is K-injective by
   Step 4. Thus $j_U^*Rj_{V*}B=Rk_{U*}(B|_W)$ and $j_U^*Rj_{W*}D=Rk_{U*}D$, while
   $j_U^*Rj_{U*}A=A$. On $V$ the formulas give $j_V^*Rj_{U*}A=Rk_{V*}(A|_W)$,
   $j_V^*Rj_{W*}D=Rk_{V*}D$ and $j_V^*Rj_{V*}B=B$. Under these identifications the derived counits
   are identities on the equal complexes, and the maps to the overlap are the derived units for
   $k_U,k_V$. The composition identification $Rj_{U*}Rk_{U*}=Rj_{W*}$ is computed on the same
   K-injective complex, since $k_{U*}$ preserves K-injectives by Step 4 and
   $j_{U*}k_{U*}F(C)=F(C\times U\times W)=F(C\times W)$; the $V$ composition has $C\times V\times
   W=C\times W$.
6. Put $D=B|_W$ and let $r_A:Rj_{U*}A\to Rj_{W*}(A|_W)$ and $r_B:Rj_{V*}B\to Rj_{W*}D$ be the
   derived unit maps for the nested restrictions, followed by the direct-image composition
   identifications. Define $d=(Rj_{W*}(c)\circ r_A,-r_B)$. Complete this morphism to a
   distinguished triangle $G\xrightarrow{f}Rj_{U*}A\oplus Rj_{V*}B\xrightarrow{d}Rj_{W*}D\to G[1]$
   using the triangulated structure in [def-weil-abstract-derived-category]. In particular $G$ is
   a fibre, that is a cone shifted by $[-1]$. Define $a$ as $f|_U$ followed by the first
   projection and the $U$-counit, and $b$ as $f|_V$ followed by the second projection and the
   $V$-counit.
7. By Step 5 the restricted middle arrow on $U$ is $(h,-1):A\oplus D_U\to D_U$, where
   $D_U=Rk_{U*}D$ and $h$ is the unit $A\to Rk_{U*}(A|_W)$ followed by $Rk_{U*}c$. On $V$ identify
   the first summand with $D_V=Rk_{V*}D$ using $Rk_{V*}c$; its middle arrow is $(1,-r):D_V\oplus
   B\to D_V$, where $r$ is the unit on $B$. Apply the long exact cohomology sequence [lem-sf-
   derived-homology-long-exact]. In every degree the first map is surjective with kernel
   $\{(x,H^q(h)x)\}$, and the second is surjective with kernel $\{(H^q(r)y,y)\}$. Surjectivity in
   the preceding degree makes $H^q(f|_U)$ and $H^q(f|_V)$ injections onto these kernels.
   Projection therefore makes $H^q(a)$ and $H^q(b)$ isomorphisms for every $q$, so $a,b$ are
   isomorphisms in the derived categories (their cones are acyclic, hence zero in the localization
   [def-weil-abstract-derived-category]). On $W$ the counits identify the middle arrow with
   $(c,-1)$. The relation $d\circ f=0$ of the distinguished triangle reads $c\circ a|_W-b|_W=0$.
   This is exactly the required compatibility.
8. If $q\notin[a_0,b_0]$, exact restriction gives $H^q(G)|_U=H^q(A)=0$ and $H^q(G)|_V=H^q(B)=0$
   via $a,b$. The sheaf zero test of Step 3 gives $H^q(G)=0$. This proves the common interval
   bound, including $a_0=b_0$ and zero inputs. It imposes no bound on the intermediate $Rj_*$
   objects and makes no assertion that direct image is exact.
9. For a module sheaf $F$ form the nested-open maps and counits
   $j_{W!}F|_W\xrightarrow{(i_U,-i_V)}j_{U!}F|_U\oplus
   j_{V!}F|_V\xrightarrow{(\epsilon_U,\epsilon_V)}F$. The composite is zero: both nested-open
   counits restrict to the identity of $F|_W$ under $j_{W!}\dashv j_W^*$, so they are equal. On
   $U$, Step 2 identifies this sequence with $L\xrightarrow{(i,-1)}F|_U\oplus
   L\xrightarrow{(1,i)}F|_U$, where $L=k_{U!}F|_W$. Its first map is injective, its second has
   section $x\mapsto(x,0)$, and a kernel element satisfies $x=-i(y)$, hence is the image of $-y$.
   On $V$ it is $L'\xrightarrow{(1,-i')}L'\oplus F|_V\xrightarrow{(i',1)}F|_V$: the section is
   $y\mapsto(0,y)$ and the kernel consists of $(x,-i'x)$. Both restricted sequences are short
   exact, so Step 3 gives the short exact sequence globally. Apply this natural construction to
   each $K^n$ of a complex $K$; naturality makes the maps commute with its differential.
10. Choose a complex $K$ representing $M$. The degreewise short exact sequence of Step 9 gives a
   distinguished triangle by [lem-weil-pbc-complex-ses-triangle]. Exactness of restriction and
   extension by zero and [lem-sf-exact-functor-derived-triangulated] identify its vertices with
   $j_{W!}(M|_W)$, $j_{U!}(M|_U)\oplus j_{V!}(M|_V)$, and $M$. Its first two arrows are precisely
   the difference of the nested-open maps and the pair of counits constructed in Step 9, and its
   last vertex is $j_{W!}(M|_W)[1]$. Naturality of the connecting map in [lem-weil-pbc-complex-
   ses-triangle] makes this triangle natural in maps of complexes; it descends to $D(\mathcal
   T,R)$ because these exact termwise functors send quasi-isomorphisms to quasi-isomorphisms, so
   the triangle maps associated with an inverted quasi-isomorphism are isomorphisms. This proves
   clause (2) for every $M$, without any morphism-gluing uniqueness claim. -/
theorem ringedTopos_binary_descent
    {C : Type u} [Category.{v} C] [HasTerminal C] [HasPullbacks C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (R : Sheaf J CommRingCat.{r})
    (U V : C) [Mono (terminal.from U)] [Mono (terminal.from V)]
    (hcover : Sieve.ofArrows (fun b : Bool => if b then U else V)
        (fun b => terminal.from (if b then U else V)) ∈ J (⊤_ C))
    [HasDerivedCategory.{w} (ringedSiteModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    [HasDerivedCategory.{w} (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V))]
    [HasDerivedCategory.{w} (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over
        (pullback (terminal.from U) (terminal.from V))))]
    (rU : DerivedCategory (ringedSiteModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)))
    (rV : DerivedCategory (ringedSiteModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)))
    (rW : DerivedCategory (ringedSiteModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over
          (pullback (terminal.from U) (terminal.from V)))))
    (rUW : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over
          (pullback (terminal.from U) (terminal.from V)))))
    (rVW : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over
          (pullback (terminal.from U) (terminal.from V)))))
    (lU : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (lV : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (lW : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over
        (pullback (terminal.from U) (terminal.from V)))) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (RU : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (RV : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (RW : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over
        (pullback (terminal.from U) (terminal.from V)))) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (adjU : rU ⊣ RU) (adjV : rV ⊣ RV) (adjW : rW ⊣ RW)
    (bangAdjU : lU ⊣ rU) (bangAdjV : lV ⊣ rV) (bangAdjW : lW ⊣ rW)
    (compU : rW ≅ rU ⋙ rUW) (compV : rW ≅ rV ⋙ rVW)
    (qU : DerivedCategory.Q ⋙ rU ≅
      moduleOverComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U ⋙
        DerivedCategory.Q)
    (qV : DerivedCategory.Q ⋙ rV ≅
      moduleOverComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) V ⋙
        DerivedCategory.Q)
    (qW : DerivedCategory.Q ⋙ rW ≅
      moduleOverComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        (pullback (terminal.from U) (terminal.from V)) ⋙ DerivedCategory.Q)
    (qUW : DerivedCategory.Q ⋙ rUW ≅
      moduleOverMapComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        (pullback.fst (terminal.from U) (terminal.from V)) ⋙ DerivedCategory.Q)
    (qVW : DerivedCategory.Q ⋙ rVW ≅
      moduleOverMapComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        (pullback.snd (terminal.from U) (terminal.from V)) ⋙ DerivedCategory.Q)
    (compU_on_complexes : ∀ K,
      compU.hom.app (DerivedCategory.Q.obj K) ≫
        rUW.map (qU.hom.app K) ≫
          qUW.hom.app
            ((moduleOverComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U).obj K) =
      qW.hom.app K ≫ DerivedCategory.Q.map
        ((moduleOverComplexComp ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
          (pullback.fst (terminal.from U) (terminal.from V))).hom.app K))
    (compV_on_complexes : ∀ K,
      compV.hom.app (DerivedCategory.Q.obj K) ≫
        rVW.map (qV.hom.app K) ≫
          qVW.hom.app
            ((moduleOverComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) V).obj K) =
      qW.hom.app K ≫ DerivedCategory.Q.map
        ((moduleOverComplexComp ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
          (pullback.snd (terminal.from U) (terminal.from V))).hom.app K)) :
    (∀ (A : DerivedCategory (ringedSiteModules.{max u v r}
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)))
      (B : DerivedCategory (ringedSiteModules.{max u v r}
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)))
      (c : rUW.obj A ≅ rVW.obj B),
      ∃ (G : DerivedCategory (ringedSiteModules.{max u v r}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
        (f : G ⟶ RU.obj A ⊞ RV.obj B)
        (d : RU.obj A ⊞ RV.obj B ⟶ RW.obj (rVW.obj B))
        (h : RW.obj (rVW.obj B) ⟶ (shiftFunctor _ (1 : ℤ)).obj G),
        d = biprod.desc
          (restrictionAdjunctionMap (rUW := rUW) adjU adjW compU A ≫
            RW.map c.hom)
          (-restrictionAdjunctionMap (rUW := rVW) adjV adjW compV B) ∧
        Pretriangulated.Triangle.mk f d h ∈ distTriang _ ∧
        (∃ (a : rU.obj G ≅ A) (b : rV.obj G ≅ B),
          a.hom = rU.map f ≫ rU.map biprod.fst ≫ adjU.counit.app A ∧
          b.hom = rV.map f ≫ rV.map biprod.snd ≫ adjV.counit.app B ∧
          compU.hom.app G ≫ rUW.map a.hom ≫ c.hom =
            compV.hom.app G ≫ rVW.map b.hom) ∧
        (∀ (a₀ b₀ : ℤ),
          (∀ q : ℤ, q < a₀ ∨ b₀ < q →
            IsZero ((DerivedCategory.homologyFunctor _ q).obj A)) →
          (∀ q : ℤ, q < a₀ ∨ b₀ < q →
            IsZero ((DerivedCategory.homologyFunctor _ q).obj B)) →
          ∀ q : ℤ, q < a₀ ∨ b₀ < q →
            IsZero ((DerivedCategory.homologyFunctor _ q).obj G))) ∧
    (∃ (delta : 𝟭 _ ⟶ rW ⋙ lW ⋙ shiftFunctor _ (1 : ℤ)),
      ∀ (M : DerivedCategory (ringedSiteModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))),
        Pretriangulated.Triangle.mk
            (biprod.lift
              ((bangAdjW.homEquiv (rW.obj M) (lU.obj (rU.obj M))).symm
                (compU.hom.app M ≫ rUW.map (bangAdjU.unit.app (rU.obj M)) ≫
                  compU.inv.app (lU.obj (rU.obj M))))
              (-((bangAdjW.homEquiv (rW.obj M) (lV.obj (rV.obj M))).symm
                (compV.hom.app M ≫ rVW.map (bangAdjV.unit.app (rV.obj M)) ≫
                  compV.inv.app (lV.obj (rV.obj M))))))
            (biprod.desc (bangAdjU.counit.app M)
              (bangAdjV.counit.app M))
            (delta.app M) ∈ distTriang _)
    := by
  sorry

end CategoryTheory

end
