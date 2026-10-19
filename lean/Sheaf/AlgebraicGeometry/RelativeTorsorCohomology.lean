/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.RelativeEtaleCohomology
public import Sheaf.CategoryTheory.Sites.TorsorWithSection
public import Sheaf.CategoryTheory.Sites.ContractedProductPresentation
public import Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

import Sheaf.AlgebraicGeometry.RelativeTorsorClassNaturality
import Sheaf.AlgebraicGeometry.RelativeTorsorForgetNormalization
import Mathlib.CategoryTheory.Preadditive.Comma
import WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions

/-!
# Relative first cohomology and torsors with an open section

Source: Stacks Project, Cohomology on Sites, Tag 03AJ, relative refinement in the
DAG proof; compare Cohomology Tags 0G71 and 0G78
(blueprint: lem-amb-relative-torsor-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The restriction square for a morphism of sheaf complexes commutes.
Source: Stacks Project, Tag 03AJ, relative refinement
(blueprint: lem-amb-relative-torsor-cohomology).
Proof: evaluate naturality of the complex morphism at the map from U to the terminal
object, and extend the resulting equality by zero in negative degrees. -/
theorem relativeSectionMap_square (T : Scheme.{u}) (U : T.Etale)
    {I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (f : I ⟶ J) :
    HomologicalComplex.extendMap
        (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex _).map f)
        ComplexShape.embeddingUpNat ≫ relativeSectionRestriction T U J =
      relativeSectionRestriction T U I ≫ HomologicalComplex.extendMap
        (((etaleSectionFunctor U).mapHomologicalComplex _).map f)
        ComplexShape.embeddingUpNat := by
  dsimp only [relativeSectionRestriction]
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
  congr 1
  apply HomologicalComplex.hom_ext
  intro n
  change (f.f n).hom.app _ ≫ (J.X n).obj.map _ =
    (I.X n).obj.map _ ≫ (f.f n).hom.app _
  exact ((f.f n).hom.naturality _).symm

/-- The map of actual relative complexes induced by a coefficient-complex map.
Source: Stacks Project, Tag 03AJ, relative refinement; Tag 0G78
(blueprint: lem-amb-relative-torsor-cohomology). -/
noncomputable def relativeSectionMap (T : Scheme.{u}) (U : T.Etale)
    {I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (f : I ⟶ J) : relativeSectionComplex T U I ⟶ relativeSectionComplex T U J :=
  relativeFiberMap (relativeSectionRestriction T U I) (relativeSectionRestriction T U J)
    (HomologicalComplex.extendMap
      (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex _).map f)
      ComplexShape.embeddingUpNat)
    (HomologicalComplex.extendMap (((etaleSectionFunctor U).mapHomologicalComplex _).map f)
      ComplexShape.embeddingUpNat) (relativeSectionMap_square T U f)

/-- The restriction square for scheme pullback, followed by a coefficient map.
Source: Stacks Project, Tag 0G78
(blueprint: lem-amb-relative-torsor-cohomology).
Proof: use resolutionSectionTransfer_naturality and terminalSectionPullback_naturality;
extension by zero preserves their commuting square. -/
theorem relativeTransfer_square {T T' : Scheme.{u}} (h : T' ⟶ T) (W : T.Opens)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (a : I ⟶ ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj J) :
    HomologicalComplex.extendMap (globalResolutionSectionTransfer h I J a)
        ComplexShape.embeddingUpNat ≫
        relativeSectionRestriction T' (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) J =
      relativeSectionRestriction T (Scheme.Etale.mk W.ι) I ≫
        HomologicalComplex.extendMap (openResolutionSectionTransfer h I J a W)
          ComplexShape.embeddingUpNat := by
  dsimp only [relativeSectionRestriction]
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
  congr 1
  have hT : (MorphismProperty.Over.mkIdTerminal @Etale T).from (Scheme.Etale.mk W.ι) =
      MorphismProperty.Over.homMk W.ι (Category.comp_id _) :=
    (MorphismProperty.Over.mkIdTerminal @Etale T).hom_ext _ _
  have hT' : (MorphismProperty.Over.mkIdTerminal @Etale T').from
      (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) =
      MorphismProperty.Over.homMk (h ⁻¹ᵁ W).ι (Category.comp_id _) :=
    (MorphismProperty.Over.mkIdTerminal @Etale T').hom_ext _ _
  rw [hT, hT']
  exact (resolutionSectionTransfer_naturality h I J a _ _ _ _
    (terminalSectionPullback_naturality h W)).symm

/-- Pullback on the shifted restriction cone, computed on a resolution comparison.
Source: Stacks Project, Tag 0G78
(blueprint: lem-amb-relative-torsor-cohomology). -/
noncomputable def relativeTransfer {T T' : Scheme.{u}} (h : T' ⟶ T) (W : T.Opens)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (J : CochainComplex (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (a : I ⟶ ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj J) :
    relativeSectionComplex T (Scheme.Etale.mk W.ι) I ⟶
      relativeSectionComplex T' (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) J :=
  relativeFiberMap _ _
    (HomologicalComplex.extendMap (globalResolutionSectionTransfer h I J a)
      ComplexShape.embeddingUpNat)
    (HomologicalComplex.extendMap (openResolutionSectionTransfer h I J a W)
      ComplexShape.embeddingUpNat) (relativeTransfer_square h W I J a)

/-- Forgetting the specified open section, with the normalized ordinary H1 comparison.
Source: Stacks Project, Tag 03AJ, canonical extension class
(blueprint: lem-amb-relative-torsor-cohomology). -/
noncomputable def relativeForgetH1 (T : Scheme.{u}) (W : T.Opens)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G)
    (c : ResolutionSectionCanonicalComparison G I) :
    relativeCohomology T (Scheme.Etale.mk W.ι) I 1 → Sheaf.H G 1 :=
  fun x ↦ c.globalEquiv 1
    (((((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex).extendHomologyIso ComplexShape.embeddingUpNat (rfl : (1 : ℤ) = 1)).hom
        (HomologicalComplex.homologyMap
          (relativeForgetComplex T (Scheme.Etale.mk W.ι) I.cocomplex) 1 x))

/-- Canonical relative torsor classification, normalized and compatible with forgetting
and contracted products. The simultaneous family includes all injective-resolution
models; its compatibility under comparison lifts is stated below.
Source: Stacks Project, Tag 03AJ, relative refinement; Tags 0G71 and 0G78
(blueprint: lem-amb-relative-torsor-cohomology).

Proof plan from the DAG:
1. Choose a resolution $0\to G\xrightarrow{\epsilon}I^0\xrightarrow d I^1\to\cdots$ with zero
negative terms. Enough injectives and the bounded-below injective representative theorem supply it
and say it is K-injective. The open restriction $j^{-1}I$ is K-injective: restriction is right
adjoint to the exact extension-by-zero functor, so the right-adjoint K-injectivity theorem
applies, with $\Lambda=\mathbf Z$. Exact inverse image makes it a resolution of $j^{-1}G$. Thus
both terms of the relative cone are computed by $A^r=I^r(T)$ and $B^r=(j^{-1}I^r)(V)$, with
restriction $r:A\to B$.

2. Use the signed model $C^n=A^n\oplus B^{n-1}$ with $D(a,b)=(da,r(a)-db)$ for
$\operatorname{Cone}(r)[-1]$. This is the cone convention in the cited definition, after changing
the sign on the $B$ summand; $D^2=0$ since $rd=dr$. In degree one its cocycles are pairs $a\in
I^1(T)$, $b\in(j^{-1}I^0)(V)$ with $da=0$ and $r(a)=db$. Its boundaries are $(dx,r(x))$ for $x\in
I^0(T)$, since $B^{-1}=0$.

3. For a cocycle $(a,b)$ form the sheaf $P_a$ of solutions $t\in I^0$ to $dt=a$ (on each etale
object use the restriction of $a$). Exactness of the resolution says $I^0\to\ker(d:I^1\to I^2)$ is
epi; local surjectivity therefore supplies such solutions on a covering. Two solutions differ by a
unique section of $G=\ker(d:I^0\to I^1)$, so addition through $\epsilon$ makes $P_a$ a $G$-torsor.
The equation $db=r(a)$ makes $b$ a specified section on $V$. If $(a',b')=(a,b)+(dx,r(x))$,
translation $t\mapsto t+x$ is a torsor isomorphism carrying $b$ to $b'$. This constructs a map
from $H^1(C)$ to pairs modulo section-preserving isomorphism.

4. This map is injective. Given a section-preserving equivariant isomorphism $F:P_a\to P_{a'}$, on
any object admitting a section $t$ put $x=F(t)-t\in I^0$. For another section $t+\epsilon(g)$
equivariance gives $F(t+\epsilon(g))-(t+\epsilon(g))=F(t)-t$. These local sections therefore agree
on overlaps and glue, by the sheaf axiom for $I^0$, to $x\in I^0(T)$. Applying $d$ gives
$dx=a'-a$, and evaluating on the specified open section gives $r(x)=b'-b$. The two cocycles differ
by the boundary $D(x)$ computed in step 2.

5. For surjectivity take a pair $(P,s)$. The named canonical extension in the statement of the
absolute torsor theorem gives $0\to G\to E_P\xrightarrow p\mathbf Z_T\to0$, whose fibre over $1$
is $P$. By injectivity of $I^0$, extend $\epsilon:G\to I^0$ across $G\hookrightarrow E_P$ to
$f:E_P\to I^0$. The composite $df$ kills $G$, hence factors through $p$ as $\bar a:\mathbf Z_T\to
I^1$; let $a=\bar a(1)$. Since $d\bar a=0$, $da=0$. Set $b=f(s)$ on $V$, so $db=r(a)$. On the
fibre over $1$, $f$ is equivariant and takes values in $P_a$; locally choosing a point of $P$
identifies this map with a translation $G\to G$, hence it is an isomorphism and carries $s$ to
$b$. Different extensions $f'$ differ by a morphism $\mathbf Z_T\to I^0$, hence by a global $x$,
giving exactly $(a',b')-(a,b)=(dx,r(x))$. We have proved a bijection, rather than selected an
arbitrary lift of the ordinary torsor class.

6. For $(a,b)=(0,0)$, $P_a=\epsilon(G)$ and its open section is zero, the identity section of the
additive torsor. Projection $C\to A$ sends $(a,b)$ to $a$. In the extension of step 5, $f$ lifts
the section $1$ to degree zero of the resolution, and its differential is $a$. Thus the connecting
class $\delta_{E_P}(1)$ is $[a]$. The absolute torsor theorem names exactly this class as the
ordinary class of $P$. Consequently projection is the required forgetful map, with the asserted
normalization.

7. The construction is independent of resolutions and natural in coefficients and schemes. For
$h:T'\to T$ and $\varphi:h^{-1}G\to G'$, choose a nonnegative injective resolution $J$ of $G'$.
Direct image is right adjoint to exact inverse image and therefore preserves injectives.
Into $h_*J$ extend the augmentation map from $G$ across $G\hookrightarrow I^0$ by injectivity.
At each subsequent degree use exactness of $I$ to factor the differential through its image,
and extend into the next injective term of $h_*J$. This gives a comparison $I\to h_*J$.
For two comparisons with the same augmentation, apply the same recursion to their difference
to construct a null-homotopy. Transposition gives $u:h^{-1}I\to J$ lifting $\varphi$.
Sections and their restrictions give $U_A:A\to A'$, $U_B:B\to B'$ with $U_Br=r'U_A$.
The resulting map on $C$ sends $(a,b)$ to $(U_Aa,U_Bb)$. If two comparisons differ by $dH+Hd$,
the homotopy on these signed cones is
$(a,b)\mapsto(Ha,-Hb)$; substituting $D$ gives $DH_C+H_CD$. Hence comparison choices give the same
cohomology map; identity comparisons and composite comparisons prove independence and composition.
By the cited cohomology pullback definition this is the derived pullback and coefficient map on
the relative cone.

8. Inverse image commutes with finite limits of underlying sheaves of sets and with their abelian
structures, so preserves the kernel-and-fibre construction of $P_a$. The absolute etale torsor
functoriality theorem guarantees that $h^{-1}P_a$ remains a torsor. The contracted-product
existence theorem supplies its sheaf quotient. The chain map $u$ of step 7 therefore gives an
equivariant morphism $h^{-1}P_a\to P_{U_Aa}$ under $\varphi$; it sends the pulled-back chosen
section to $U_Bb$. It induces an isomorphism from the contracted product
$h^{-1}P_a\wedge^{h^{-1}G}G'$: locally pick a section $t$ of the source torsor, and both torsors
become $G'$; the map is $g'\mapsto u(t)+g'$, a translation. These local identifications agree by
equivariance and the defining quotient relation of the contracted product. For the coefficient
identity this is just inverse image of the torsor. Thus the bijection, including its specified
section, is natural for every $\varphi$, without assuming $h^{-1}G=G'$.

9. For a short exact coefficient sequence choose a horseshoe of nonnegative injective resolutions
$I_1,I_2,I_3$. Its degreewise short exact rows split since the first term is injective. Taking
sections on $T$ or $V$, and then the finite sums defining $C(I_k)$, preserves those split rows.
Thus $0\to C(I_1)\to C(I_2)\to C(I_3)\to0$ is degreewise short exact. The complex
long-exact-sequence theorem supplies $\delta^q_{T,V}$. Explicitly lift a relative cocycle $z$ to
$y\in C(I_2)^q$; $Dy$ lies in the image of $C(I_1)^{q+1}$, and the class of its unique preimage is
$\delta[z]$. The projections to $A(I_k)$ form a morphism of these short exact complex sequences,
so long-exact-sequence naturality proves compatibility with forgetting support.

10. For canonicity and pullback naturality extend the relative construction to bounded below
complexes. Write $F(I)=C(\Gamma(T,I)\to\Gamma(V,j^{-1}I))$ on the homotopy category. The homotopy
formula in step 7 shows that this is a functor. Its shift isomorphism $F(I[1])\to F(I)[1]$ is
$(a,b)\mapsto(a,-b)$: the respective differentials are $(-da,r(a)+db)$ and $(-da,-r(a)+db)$. For a
chain map $f:I\to J$, order the summands of $F(\operatorname{Cone}(f))^n$ as $(x,y,z,w)\in
A_J^n\oplus A_I^{n+1}\oplus B_J^{n-1}\oplus B_I^n$. Its differential is
$(d_Jx+f_Ty,-d_Iy,r_Jx-d_Jz-f_Vw,r_Iy+d_Iw)$. Write $\Phi(x,y,z,w)=(x,z,y,-w)$. In the target
order $(X,Z,Y,W)$, the cone differential is
$d_{\mathrm{out}}(X,Z,Y,W)=(d_JX+f_TY,r_JX-d_JZ+f_VW,-d_IY,-r_IY+d_IW)$. Substituting
$(X,Z,Y,W)=(x,z,y,-w)$ gives the identity
$$d_{\mathrm{out}}\Phi(x,y,z,w)=(d_Jx+f_Ty,r_Jx-d_Jz-f_Vw,-d_Iy,-r_Iy-d_Iw)=\Phi
d_{\mathrm{in}}(x,y,z,w).$$ Thus $\Phi$ is an isomorphism of complexes, with inverse
$(X,Z,Y,W)\mapsto(X,Y,Z,-W)$. It respects the cone inclusion. For the boundary convention $-p$,
the two routes to $F(I)[1]$ both give $(-y,w)$: one first projects by $-p$ to $F(I[1])$ and
applies $(a,b)\mapsto(a,-b)$, while the other applies $\Phi$ and then the outer $-p$. Thus $F$ is
exact. Bounded below K-injective complexes represent every object of $D^+$ by the
injective-representative theorem, and their homotopy morphisms are exactly their derived morphisms
by K-injective Hom-to-derived bijectivity. Use bounded below complexes of injective objects as the
representatives. Their shifts and cones remain bounded below and termwise injective: each cone
term is a finite sum of injectives, and a map into that sum extends across a monomorphism by
extending its two components using the definition of injectivity. The cited bounded-below theorem
then makes each shift and cone K-injective. Hence $F$ defines an exact functor on $D^+$ by
computing on these representatives, without invoking an unbounded existence theorem. Choose
degreewise splittings of the horseshoe in step 9 and write $I_2=I_1\oplus I_3$ with differential
$\begin{pmatrix}d_1&t\\0&d_3\end{pmatrix}$. The equality $d_2^2=0$ gives $d_1t+td_3=0$, so the
off-diagonal is a chain map $t:I_3\to I_1[1]$. To check its boundary sign with the cited cone
convention, let $\alpha:I_1\to I_2$ be the inclusion and let $q:\operatorname{Cone}(\alpha)\to
I_3$ project $((a,c),e)$ to $c$. It has a chain section $\sigma(c)=((0,c),-tc)$. Its kernel
consists of $(a,e)$ with differential $(d_1a+e,-d_1e)$; the homotopy $(a,e)\mapsto(0,a)$ contracts
this kernel. Hence $q$ is a homotopy equivalence, and the boundary $-p q^{-1}$ is represented by
$-p\sigma=t$. The horseshoe augmentations identify this cone triangle with the distinguished
triangle of $0\to G_1\to G_2\to G_3\to0$; thus $t$ represents its coefficient boundary $w:G_3\to
G_1[1]$. This explicitly identifies the morphism supplied by the short-exact-sequence triangle
theorem rather than assuming a sign for it. The differential of the split relative sequence has
off-diagonal $(a,b)\mapsto(t_Ta,-t_Vb)$, which is precisely $F(t)$ followed by the displayed shift
isomorphism. For a closed $(a,b)$ the lift $(0,(a,b))$ therefore has differential equal to this
off-diagonal; the lift-and-differentiate boundary in step 9 is $H^q(F(w))$. For scheme pullback,
the unit followed by the comparisons of step 7 defines a natural transformation on these derived
relative functors. To verify naturality explicitly, for $f:I\to L$ and a comparison
$u_I:h^{-1}I\to I'$ choose $u_L:h^{-1}L\to L'$ and a target comparison $f':I'\to L'$. The maps
$u_Lh^{-1}f$ and $f'u_I$ into the K-injective $L'$ represent the same derived morphism and so
differ by $dH+Hd$. The unit is natural on both $T$ and $V$; applying sections yields the
compatible homotopies on their restriction maps, and $(a,b)\mapsto(Ha,-Hb)$ makes the resulting
relative square commute up to homotopy. This applies to $f=t$ as well as to ordinary coefficient
maps. The derived-unit description identifies its absolute component with the required cohomology
pullback; the displayed shift isomorphism identifies its relative shifted component. Exact inverse
image preserves the short exact coefficient sequence and its cone triangle, so its image of $w$ is
the pulled-back coefficient boundary. Consequently $H^q(F(w))$ commutes with scheme pullback. For
a morphism of coefficient sequences, the horseshoe-morphism-lift theorem supplies a morphism of
their short exact resolution sequences in the same sheaf category, and complex long-exact
naturality proves the boundary square. Applying this to identity coefficient-sequence maps proves
independence of horseshoe choices. Together with step 9's projection square these give all the
asserted connecting-map compatibilities. -/
theorem relative_torsor_cohomology :
    ∃ e : ∀ (T : Scheme.{u}) (W : T.Opens)
      (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G),
      Sheaf.Torsor.WithSection.Classes G (Scheme.Etale.mk W.ι) ≃
        relativeCohomology T (Scheme.Etale.mk W.ι) I 1,
    (∀ T W G I,
      e T W G I (Quotient.mk _
        ⟨Sheaf.Torsor.trivial G, @id (G.obj.obj (op (Scheme.Etale.mk W.ι))) 0⟩) = 0) ∧
    (∀ T W G I (c : ResolutionSectionCanonicalComparison G I)
      (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk W.ι)),
      relativeForgetH1 T W G I c (e T W G I (Quotient.mk _ P)) =
        Sheaf.Torsor.classH1 G (MorphismProperty.Over.mkIdTerminal @Etale T)
          (Quotient.mk _ P.1)) ∧
    (∀ (T : Scheme.{u}) (W : T.Opens)
      (G G' : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (f : G ⟶ G')
      (I : InjectiveResolution G) (J : InjectiveResolution G')
      (a : I.Hom J f) (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk W.ι))
      (Q : Sheaf.Torsor G') (q : Sheaf.Torsor.ContractedProductPresentation.{u, u} T f P.1 Q),
      HomologicalComplex.homologyMap
          (relativeSectionMap T (Scheme.Etale.mk W.ι) a.hom) 1
          (e T W G I (Quotient.mk _ P)) =
        e T W G' J (Quotient.mk _ ⟨Q, q.quotient (op (Scheme.Etale.mk W.ι)) P.2 0⟩)) ∧
    (∀ (T T' : Scheme.{u}) (h : T' ⟶ T) (W : T.Opens)
      (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
      (G' : Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1})
      (f : G ⟶ (lowerStar AddCommGrpCat.{u + 1} h).obj G')
      (I : InjectiveResolution G) (J : InjectiveResolution G')
      (a : I.cocomplex ⟶
        ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
      (_ha : I.ι.f 0 ≫ a.f 0 = f ≫ (lowerStar AddCommGrpCat.{u + 1} h).map (J.ι.f 0))
      (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk W.ι)) (Q : Sheaf.Torsor G')
      (b : P.1.sheaf.obj ⟶
        (MorphismProperty.Over.pullback @Etale ⊤ h).op ⋙ Q.sheaf.obj)
      (_hb : ∀ (A : T.Etaleᵒᵖ) (g : G.obj.obj A) (t : P.1.sheaf.obj.obj A),
        b.app A (P.1.vadd A g t) =
          Q.vadd (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj A.unop))
            (f.hom.app A g) (b.app A t)),
      HomologicalComplex.homologyMap (relativeTransfer h W I.cocomplex J.cocomplex a) 1
          (e T W G I (Quotient.mk _ P)) =
        e T' (h ⁻¹ᵁ W) G' J (Quotient.mk _
          ⟨Q, Q.sheaf.obj.map (openSectionPullback h W).op
            (b.app (op (Scheme.Etale.mk W.ι)) P.2)⟩)) := by
  set_option backward.isDefEq.respectTransparency false in
    classical
    -- Mathlib's cone boundary is minus the first projection, so the ordinary Ext
    -- normalization requires the negative of the raw lifting-cocycle classification.
    let e : ∀ (T : Scheme.{u}) (W : T.Opens)
        (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G),
        Sheaf.Torsor.WithSection.Classes G (Scheme.Etale.mk W.ι) ≃
          relativeCohomology T (Scheme.Etale.mk W.ι) I 1 :=
      fun T W G I ↦ (relativeTorsorEquiv T (Scheme.Etale.mk W.ι) I).trans
        { toFun := fun x ↦ -x
          invFun := fun x ↦ -x
          left_inv := neg_neg
          right_inv := neg_neg }
    refine ⟨e, ?_, ?_, ?_, ?_⟩
    · intro T W G I
      change -relativeTorsorEquiv T (Scheme.Etale.mk W.ι) I _ = 0
      rw [relativeTorsorEquiv_zero, neg_zero]
    · intro T W G I c P
      change c.globalEquiv 1
        (((((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
          I.cocomplex).extendHomologyIso ComplexShape.embeddingUpNat
            (rfl : (1 : ℤ) = 1)).hom
          (HomologicalComplex.homologyMap
            (relativeForgetComplex T (Scheme.Etale.mk W.ι) I.cocomplex) 1
            (-relativeTorsorEquiv T (Scheme.Etale.mk W.ι) I (Quotient.mk _ P)))) = _
      rw [map_neg, map_neg, map_neg]
      let hT := MorphismProperty.Over.mkIdTerminal @Etale T
      let : Injective (I.cocomplex.X 0) := I.injective 0
      obtain ⟨s, ⟨ε⟩⟩ := Sheaf.Torsor.exists_equiv_lifts hT
        (resolutionLiftSequence_shortExact T I) P.1
      rw [relativeTorsorEquiv_presentation T (Scheme.Etale.mk W.ι) I P s ε,
        relativeFrameClass_forget, neg_neg]
      have hp : (Quotient.mk _ P.1 : _root_.Quotient (Sheaf.Torsor.setoid (G := G))) =
          Quotient.mk _ (Sheaf.Torsor.lifts hT (resolutionLiftSequence_shortExact T I) s) :=
        Quotient.sound ⟨ε⟩
      rw [hp, Sheaf.Torsor.classH1_lifts]
      rfl
    · intro T W G G' f I J a P Q q
      change HomologicalComplex.homologyMap
        (relativeSectionMap T (Scheme.Etale.mk W.ι) a.hom) 1
        (-relativeTorsorEquiv T (Scheme.Etale.mk W.ι) I (Quotient.mk _ P)) =
        -relativeTorsorEquiv T (Scheme.Etale.mk W.ι) J
          (Quotient.mk _ ⟨Q, q.quotient (op (Scheme.Etale.mk W.ι)) P.2 0⟩)
      rw [map_neg]
      apply congrArg Neg.neg
      let σ : P.1.sheaf.obj ⟶ Q.sheaf.obj :=
        { app A := TypeCat.ofHom fun t ↦ q.quotient A t 0
          naturality A B k := by
            ext t
            change q.quotient B (P.1.sheaf.obj.map k t) 0 =
              Q.sheaf.obj.map k (q.quotient A t 0)
            rw [q.quotient_natural, map_zero] }
      apply relativeTorsorEquiv_coefficient T (Scheme.Etale.mk W.ι) f I J a P Q σ
        (fun A g t => ?_) (relativeSectionMap_square T (Scheme.Etale.mk W.ι) a.hom)
      change q.quotient A (P.1.vadd A g t) 0 = Q.vadd A (f.hom.app A g) (q.quotient A t 0)
      calc
        _ = q.quotient A t (f.hom.app A g) := by
          simpa only [sub_self] using q.quotient_invariant A g t (f.hom.app A g)
        _ = _ := by simpa only [zero_add] using q.quotient_vadd A t 0 (f.hom.app A g)
    · intro T T' h W G G' f I J a ha P Q b hb
      change HomologicalComplex.homologyMap (relativeTransfer h W I.cocomplex J.cocomplex a) 1
        (-relativeTorsorEquiv T (Scheme.Etale.mk W.ι) I (Quotient.mk _ P)) =
        -relativeTorsorEquiv T' (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) J (Quotient.mk _
          ⟨Q, Q.sheaf.obj.map (openSectionPullback h W).op
            (b.app (op (Scheme.Etale.mk W.ι)) P.2)⟩)
      rw [map_neg]
      apply congrArg Neg.neg
      exact relativeTorsorEquiv_transfer h W f I J a ha P Q b hb
        (relativeTransfer_square h W I.cocomplex J.cocomplex a)
set_option backward.isDefEq.respectTransparency false in
private lemma comparisonIntoInjectives
    {C : Type*} [Category C] [Abelian C] {G : C} (I : InjectiveResolution G)
    (L : CochainComplex C ℕ) [∀ n, Injective (L.X n)]
    (t : G ⟶ L.X 0) (ht : t ≫ L.d 0 1 = 0) :
    ∃ a : I.cocomplex ⟶ L, I.ι.f 0 ≫ a.f 0 = t := by
  classical
  -- Extend degree zero, then extend along each differential image.
  let a₀ := Injective.factorThru t (I.ι.f 0)
  let a₁ := I.exact₀.descToInjective (a₀ ≫ L.d 0 1) (by
    dsimp [a₀]
    rw [← Category.assoc, Injective.comp_factorThru, ht])
  have w₀ : a₀ ≫ L.d 0 1 = I.cocomplex.d 0 1 ≫ a₁ :=
    (I.exact₀.comp_descToInjective _ _).symm
  let a : I.cocomplex ⟶ L := CochainComplex.mkHom _ _ a₀ a₁ w₀
    (fun n ⟨g, g', w⟩ ↦
      ⟨(I.exact_succ n).descToInjective (g' ≫ L.d (n + 1) (n + 2)) (by
        rw [← Category.assoc, ← w, Category.assoc, L.d_comp_d, comp_zero]),
        ((I.exact_succ n).comp_descToInjective _ _).symm⟩)
  exact ⟨a, by simp [a, a₀]⟩

/-- An adjoint coefficient morphism has an augmentation-preserving resolution comparison.
Source: Stacks Project, Tag 03AJ, comparison of resolutions; Tag 08FI
(blueprint: lem-amb-relative-torsor-cohomology).
Proof: transpose the coefficient map under inverse image/direct image. Exact inverse
image makes the pulled-back source a resolution. Extend its degree-zero map to J0 by
injectivity, then successively extend the maps on the images of the differentials to
Jn. Transposing the resulting chain map gives the required comparison. -/
theorem relative_comparison_exists {T T' : Scheme.{u}} (h : T' ⟶ T)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G' : Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (f : G ⟶ (lowerStar AddCommGrpCat.{u + 1} h).obj G')
    (I : InjectiveResolution G) (J : InjectiveResolution G') :
    ∃ a : I.cocomplex ⟶
      ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj J.cocomplex,
      I.ι.f 0 ≫ a.f 0 = f ≫ (lowerStar AddCommGrpCat.{u + 1} h).map (J.ι.f 0) := by
  let L := ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj
    J.cocomplex
  have hinj (n : ℕ) : Injective (L.X n) :=
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).map_injective _ (J.injective n)
  exact comparisonIntoInjectives I L (f ≫ (lowerStar AddCommGrpCat.{u + 1} h).map
    (J.ι.f 0)) (by
      change (f ≫ (lowerStar AddCommGrpCat.{u + 1} h).map (J.ι.f 0)) ≫
        (lowerStar AddCommGrpCat.{u + 1} h).map (J.cocomplex.d 0 1) = 0
      rw [Category.assoc, ← Functor.map_comp, J.ι_f_zero_comp_complex_d, Functor.map_zero,
        comp_zero])


set_option backward.isDefEq.respectTransparency false in
private lemma comparisonHomotopy
    {C : Type*} [Category C] [Abelian C] {G : C} (I : InjectiveResolution G)
    (L : CochainComplex C ℕ) [∀ n, Injective (L.X n)]
    (a b : I.cocomplex ⟶ L) (hab : I.ι.f 0 ≫ a.f 0 = I.ι.f 0 ≫ b.f 0) :
    Nonempty (Homotopy a b) := by
  classical
  let f : I.cocomplex ⟶ L := a - b
  have hf : I.ι.f 0 ≫ f.f 0 = 0 := by
    simp only [f, HomologicalComplex.sub_f_apply, Preadditive.comp_sub, hab, sub_self]
  let h₀ := I.exact₀.descToInjective (f.f 0) hf
  have hh₀ : I.cocomplex.d 0 1 ≫ h₀ = f.f 0 :=
    I.exact₀.comp_descToInjective _ _
  have hz : I.cocomplex.d 0 1 ≫ (f.f 1 - h₀ ≫ L.d 0 1) = 0 := by
    rw [Preadditive.comp_sub, ← Category.assoc, hh₀, f.comm, sub_self]
  let h₁ := (I.exact_succ 0).descToInjective (f.f 1 - h₀ ≫ L.d 0 1) hz
  have hh₁ : I.cocomplex.d 1 2 ≫ h₁ = f.f 1 - h₀ ≫ L.d 0 1 :=
    (I.exact_succ 0).comp_descToInjective _ _
  have hnull : Homotopy f 0 := by
    refine Homotopy.mkCoinductive f h₀ ?_ h₁ ?_ ?_
    · simpa using hh₀.symm
    · exact (eq_add_of_sub_eq hh₁.symm).trans (add_comm _ _)
    · intro n data
      rcases data with ⟨g, g', w⟩
      have hz' : I.cocomplex.d (n + 1) (n + 2) ≫
          (f.f (n + 2) - g' ≫ L.d (n + 1) (n + 2)) = 0 := by
        rw [Preadditive.comp_sub, ← f.comm, ← Category.assoc, w,
          Preadditive.add_comp, Category.assoc, Category.assoc,
          HomologicalComplex.d_comp_d, comp_zero, zero_add, sub_self]
      refine ⟨(I.exact_succ (n + 1)).descToInjective _ hz', ?_⟩
      have hh := (I.exact_succ (n + 1)).comp_descToInjective _ hz'
      exact (eq_add_of_sub_eq hh.symm).trans (add_comm _ _)
  exact ⟨Homotopy.equivSubZero.invFun hnull⟩

set_option backward.isDefEq.respectTransparency false in
private lemma cofiberMap_eq_map
    {A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ r' = r ≫ b) :
    HomologicalComplex.homotopyCofiber.mapArrowHom r r'
        (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h) =
      CochainComplex.mappingCone.map r r' a b h.symm := by
  apply HomologicalComplex.hom_ext
  intro n
  apply CochainComplex.mappingCone.ext_from r (n + 1) n rfl <;>
    simp only [CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inl_v_desc_f, CochainComplex.mappingCone.inr_f_desc_f,
      CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
      CochainComplex.HomComplex.Cochain.ofHom_v, HomologicalComplex.comp_f]
  all_goals simp [HomologicalComplex.homotopyCofiber.mapArrowHom,
      CochainComplex.mappingCone.inl,
      CochainComplex.mappingCone.inr,
      HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom r' _ (n + 1) n rfl]

open CochainComplex.HomComplex in
set_option backward.isDefEq.respectTransparency false in
private lemma coneMap_homotopy
    {A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (a a' : A ⟶ A') (b b' : B ⟶ B')
    (h : a ≫ r' = r ≫ b) (h' : a' ≫ r' = r ≫ b')
    (H : Homotopy a a') (K : Homotopy b b')
    (hk : (Cochain.ofHomotopy H).comp (Cochain.ofHom r') (add_zero (-1)) =
      (Cochain.ofHom r).comp (Cochain.ofHomotopy K) (zero_add (-1))) :
    Nonempty (Homotopy
      (CochainComplex.mappingCone.map r r' a b h.symm)
      (CochainComplex.mappingCone.map r r' a' b' h'.symm)) := by
  -- The suspended source summand carries the negative of the source homotopy.
  let γ₁ := -((Cochain.ofHomotopy H).comp
    (CochainComplex.mappingCone.inl r') (by decide : (-1 : ℤ) + -1 = -2))
  let γ₂ := (Cochain.ofHomotopy K).comp
    (Cochain.ofHom (CochainComplex.mappingCone.inr r')) (add_zero (-1))
  refine ⟨CochainComplex.mappingCone.descHomotopy r _ _ γ₁ γ₂ ?_ ?_⟩
  · simp only [CochainComplex.mappingCone.map, CochainComplex.mappingCone.inl_desc]
    dsimp only [γ₁, γ₂]
    rw [δ_neg, δ_comp _ _ _ 0 0 (-1) (by decide) (by decide) (by decide)]
    simp only [CochainComplex.mappingCone.δ_inl, δ_ofHomotopy,
      Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
      Cochain.ofHom_comp, Cochain.comp_assoc_of_third_is_zero_cochain,
      ← Cochain.comp_assoc_of_first_is_zero_cochain, ← hk,
      Cochain.comp_assoc_of_third_is_zero_cochain, Cochain.sub_comp]
    abel
  · simp only [CochainComplex.mappingCone.map, CochainComplex.mappingCone.inr_desc]
    dsimp only [γ₂]
    simp [Cochain.ofHom_comp, δ_ofHomotopy]

set_option backward.isDefEq.respectTransparency false in
private lemma extend_homotopy_square
    {A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℕ}
    {a a' : A ⟶ A'} {b b' : B ⟶ B'}
    (r : A ⟶ B) (r' : A' ⟶ B') (H : Homotopy a a') (K : Homotopy b b')
    (hk : ∀ i j, H.hom i j ≫ r'.f j = r.f i ≫ K.hom i j) (i j : ℤ) :
    (H.extend ComplexShape.embeddingUpNat).hom i j ≫
        (HomologicalComplex.extendMap r' ComplexShape.embeddingUpNat).f j =
      (HomologicalComplex.extendMap r ComplexShape.embeddingUpNat).f i ≫
        (K.extend ComplexShape.embeddingUpNat).hom i j := by
  -- Outside the embedding, the source or target of the component is zero.
  by_cases hi : ∃ n, ComplexShape.embeddingUpNat.f n = i
  · obtain ⟨n, rfl⟩ := hi
    by_cases hj : ∃ m, ComplexShape.embeddingUpNat.f m = j
    · obtain ⟨m, rfl⟩ := hj
      rw [Homotopy.extend_hom_eq H _ rfl rfl, Homotopy.extend_hom_eq K _ rfl rfl,
        HomologicalComplex.extendMap_f r _ rfl, HomologicalComplex.extendMap_f r' _ rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc (H.hom n m), hk]
      simp only [Category.assoc]
    · exact (HomologicalComplex.isZero_extend_X B' _ j (by simpa using hj)).eq_of_tgt _ _
  · exact (HomologicalComplex.isZero_extend_X A _ i (by simpa using hi)).eq_of_src _ _

open CochainComplex.HomComplex in
set_option backward.isDefEq.respectTransparency false in
private lemma sectionMap_homotopy (T : Scheme.{u}) (U : T.Etale)
    {I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (a b : I ⟶ J) (H : Homotopy a b) :
    Nonempty (Homotopy (relativeSectionMap T U a) (relativeSectionMap T U b)) := by
  let A := Scheme.Etale.mk (𝟙 T)
  let v := (MorphismProperty.Over.mkIdTerminal @Etale T).from U
  let hA := (etaleSectionFunctor A).mapHomotopy H
  let hB := (etaleSectionFunctor U).mapHomotopy H
  have hk (i j : ℕ) : hA.hom i j ≫ (etaleSectionMap v J).f j =
      (etaleSectionMap v I).f i ≫ hB.hom i j :=
    ((H.hom i j).hom.naturality v.op).symm
  have he (i j : ℤ) := extend_homotopy_square (etaleSectionMap v I)
    (etaleSectionMap v J) hA hB hk i j
  obtain ⟨K⟩ := coneMap_homotopy (relativeSectionRestriction T U I)
    (relativeSectionRestriction T U J) _ _ _ _
    (relativeSectionMap_square T U a) (relativeSectionMap_square T U b)
    (hA.extend ComplexShape.embeddingUpNat) (hB.extend ComplexShape.embeddingUpNat) (by
      apply Cochain.ext
      intro i j hij
      simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
        Cochain.ofHom_v]
      exact he i j)
  unfold relativeSectionMap relativeFiberMap
  rw [cofiberMap_eq_map, cofiberMap_eq_map]
  exact ⟨K.shift (-1)⟩

set_option backward.isDefEq.respectTransparency false in
private lemma fiberMap_comp
    {A B A' B' A'' B'' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (r'' : A'' ⟶ B'')
    (a : A ⟶ A') (b : B ⟶ B') (a' : A' ⟶ A'') (b' : B' ⟶ B'')
    (h : a ≫ r' = r ≫ b) (h' : a' ≫ r'' = r' ≫ b') :
    relativeFiberMap r r'' (a ≫ a') (b ≫ b')
        (by rw [Category.assoc, h', ← Category.assoc, h, Category.assoc]) =
      relativeFiberMap r r' a b h ≫ relativeFiberMap r' r'' a' b' h' := by
  unfold relativeFiberMap
  rw [← Functor.map_comp, ← HomologicalComplex.homotopyCofiber.mapArrowHom_comp]
  congr 2

set_option backward.isDefEq.respectTransparency false in
private lemma sectionMap_id (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    relativeSectionMap T U (𝟙 I) = 𝟙 _ := by
  have hA : HomologicalComplex.extendMap
      (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex _).map (𝟙 I))
      ComplexShape.embeddingUpNat = 𝟙 _ := by
    rw [CategoryTheory.Functor.map_id, HomologicalComplex.extendMap_id]
  have hB : HomologicalComplex.extendMap
      (((etaleSectionFunctor U).mapHomologicalComplex _).map (𝟙 I))
      ComplexShape.embeddingUpNat = 𝟙 _ := by
    rw [CategoryTheory.Functor.map_id, HomologicalComplex.extendMap_id]
  have hid : Arrow.homMk _ _ (relativeSectionMap_square T U (𝟙 I)) =
      𝟙 (Arrow.mk (relativeSectionRestriction T U I)) := by
    apply Arrow.hom_ext
    · exact hA
    · exact hB
  unfold relativeSectionMap relativeFiberMap
  rw [hid, HomologicalComplex.homotopyCofiber.mapArrowHom_id]
  exact (shiftFunctor _ (-1 : ℤ)).map_id _

set_option backward.isDefEq.respectTransparency false in
private lemma sectionMap_comp (T : Scheme.{u}) (U : T.Etale)
    {I J K : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (a : I ⟶ J) (b : J ⟶ K) :
    relativeSectionMap T U (a ≫ b) = relativeSectionMap T U a ≫ relativeSectionMap T U b := by
  unfold relativeSectionMap
  rw [← fiberMap_comp]
  simp only [Functor.map_comp, HomologicalComplex.extendMap_comp]

set_option backward.isDefEq.respectTransparency false in
private lemma fiberMap_comp_zero
    {A B A' B' A'' B'' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (r'' : A'' ⟶ B'')
    (a : A ⟶ A') (b : B ⟶ B') (a' : A' ⟶ A'') (b' : B' ⟶ B'')
    (h : a ≫ r' = r ≫ b) (h' : a' ≫ r'' = r' ≫ b')
    (ha : a ≫ a' = 0) (hb : b ≫ b' = 0) :
    relativeFiberMap r r' a b h ≫ relativeFiberMap r' r'' a' b' h' = 0 := by
  unfold relativeFiberMap
  rw [← Functor.map_comp, ← HomologicalComplex.homotopyCofiber.mapArrowHom_comp]
  have hz : (Arrow.homMk a b h : Arrow.mk r ⟶ Arrow.mk r') ≫
      (Arrow.homMk a' b' h' : Arrow.mk r' ⟶ Arrow.mk r'') = 0 := by
    apply Arrow.hom_ext <;> assumption
  rw [hz]
  have hc : HomologicalComplex.homotopyCofiber.mapArrowHom r r''
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) 0 = 0 := by
    apply HomologicalComplex.hom_ext
    intro n
    apply HomologicalComplex.homotopyCofiber.ext_from_X r (n + 1) n rfl <;>
      simp [HomologicalComplex.homotopyCofiber.mapArrowHom]
  rw [hc]
  exact Functor.map_zero _ _ _

/-- Relative complex maps preserve a zero composite.
Source: Stacks Project, Tag 03AJ, relative cone construction
(blueprint: lem-amb-relative-torsor-cohomology).
Proof: the strictly functorial map of arrows preserves composition and zero. Apply
extension by zero, the mapping-cone map and the shift to the zero-composite square. -/
theorem relativeSectionMap_comp_zero (T : Scheme.{u}) (U : T.Etale)
    {I J K : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (a : I ⟶ J) (b : J ⟶ K) (hab : a ≫ b = 0) :
    relativeSectionMap T U a ≫ relativeSectionMap T U b = 0 := by
  apply fiberMap_comp_zero <;>
    simp only [← HomologicalComplex.extendMap_comp, ← Functor.map_comp, hab,
      Functor.map_zero, HomologicalComplex.extendMap_zero]


/-- Apply the relative shifted-cone construction to a short complex of resolutions.
Source: Stacks Project, Tag 013T and the relative refinement of Tag 03AJ
(blueprint: lem-amb-relative-torsor-cohomology). -/
noncomputable def relativeShortComplex (T : Scheme.{u}) (U : T.Etale)
    (S : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)) :
    ShortComplex (CochainComplex AddCommGrpCat.{u + 1} ℤ) :=
  ShortComplex.mk (relativeSectionMap T U S.f) (relativeSectionMap T U S.g)
    (relativeSectionMap_comp_zero T U S.f S.g S.zero)

set_option backward.isDefEq.respectTransparency false in
private lemma extendedSections_split (T : Scheme.{u}) (U : T.Etale)
    (S : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (hs : ∀ n : ℕ, Nonempty ((S.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))
    (q : ℤ) : Nonempty ((S.map
      ((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ) ⋙
        ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1})).map
          (HomologicalComplex.eval _ (.up ℤ) q)).Splitting := by
  classical
  let F := etaleSectionFunctor U
  let E := ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}
  let R := S.map (F.mapHomologicalComplex (.up ℕ) ⋙ E)
  change Nonempty (R.map (HomologicalComplex.eval _ (.up ℤ) q)).Splitting
  by_cases hq : ∃ n : ℕ, (n : ℤ) = q
  · obtain ⟨n, rfl⟩ := hq
    let e : R.map (HomologicalComplex.eval _ (.up ℤ) (n : ℤ)) ≅
        (S.map (HomologicalComplex.eval _ (.up ℕ) n)).map F :=
      ShortComplex.isoMk
        (HomologicalComplex.extendXIso _ _ rfl)
        (HomologicalComplex.extendXIso _ _ rfl)
        (HomologicalComplex.extendXIso _ _ rfl)
        (by
          change _ ≫ F.map (S.f.f n) =
            (HomologicalComplex.extendMap ((F.mapHomologicalComplex (.up ℕ)).map S.f)
              ComplexShape.embeddingUpNat).f (n : ℤ) ≫ _
          erw [HomologicalComplex.extendMap_f _ _ (rfl :
            ComplexShape.embeddingUpNat.f n = (n : ℤ))]
          simp)
        (by
          change _ ≫ F.map (S.g.f n) =
            (HomologicalComplex.extendMap ((F.mapHomologicalComplex (.up ℕ)).map S.g)
              ComplexShape.embeddingUpNat).f (n : ℤ) ≫ _
          erw [HomologicalComplex.extendMap_f _ _ (rfl :
            ComplexShape.embeddingUpNat.f n = (n : ℤ))]
          simp)
    exact ⟨((hs n).some.map F).ofIso e.symm⟩
  · have hz (I : CochainComplex
        (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
        IsZero ((E.obj ((F.mapHomologicalComplex (.up ℕ)).obj I)).X q) :=
      HomologicalComplex.isZero_extend_X _ _ _ (by simpa using hq)
    exact ⟨{
      r := 0
      s := 0
      f_r := (hz S.X₁).eq_of_src _ _
      s_g := (hz S.X₃).eq_of_src _ _
      id := (hz S.X₂).eq_of_src _ _ }⟩

private noncomputable def sumRow (S R : ShortComplex AddCommGrpCat.{u + 1}) :
    ShortComplex AddCommGrpCat.{u + 1} :=
  ShortComplex.mk (biprod.map S.f R.f) (biprod.map S.g R.g) (by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp [biprod.map])

private noncomputable def sumRowSplitting (S R : ShortComplex AddCommGrpCat.{u + 1})
    (s : S.Splitting) (t : R.Splitting) : (sumRow S R).Splitting where
  r := biprod.map s.r t.r
  s := biprod.map s.s t.s
  f_r := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp [sumRow, biprod.map]
  s_g := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp [sumRow, biprod.map]
  id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp [sumRow, biprod.map, Category.assoc, s.id, t.id]

/-- Split horseshoe rows remain short exact after relative sections.
Source: Stacks Project, Tag 013T; relative refinement of Tag 03AJ
(blueprint: lem-amb-relative-torsor-cohomology).
Proof: each evaluation and extension-by-zero functor preserves the supplied split rows.
Each shifted cone term is a finite sum of the two evaluated rows, hence is short exact.
Short exactness of complexes is degreewise short exactness. -/
theorem relativeShortComplex_shortExact (T : Scheme.{u}) (U : T.Etale)
    (S : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (hs : (∀ n : ℕ, Nonempty ((S.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))) :
    (relativeShortComplex T U S).ShortExact := by
  classical
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let A := (S.map
    ((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ) ⋙
      ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1})).map
        (HomologicalComplex.eval _ (.up ℤ) (n + -1 + 1))
  let B := (S.map ((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ) ⋙
      ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1})).map
        (HomologicalComplex.eval _ (.up ℤ) (n + -1))
  let e (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :=
    HomologicalComplex.homotopyCofiber.XIsoBiprod
      (relativeSectionRestriction T U I) (n + -1) (n + -1 + 1) rfl
  let iso : (relativeShortComplex T U S).map (HomologicalComplex.eval _ (.up ℤ) n) ≅
      sumRow A B := ShortComplex.isoMk (e S.X₁) (e S.X₂) (e S.X₃)
        (coneMap_XIso _ _ _ _ (relativeSectionMap_square T U S.f) (n + -1)).symm
        (coneMap_XIso _ _ _ _ (relativeSectionMap_square T U S.g) (n + -1)).symm
  exact ShortComplex.shortExact_of_iso iso.symm
    (sumRowSplitting A B
      (extendedSections_split T (Scheme.Etale.mk (𝟙 T)) S hs (n + -1 + 1)).some
      (extendedSections_split T U S hs (n + -1)).some).shortExact


/-- The canonical relative connecting map in any split horseshoe model.
Its sign is the homology-sequence sign, not an independently chosen homomorphism.
Source: Stacks Project, Tag 013T and Tag 03AJ, relative refinement
(blueprint: lem-amb-relative-torsor-cohomology). -/
noncomputable def relativeConnecting (T : Scheme.{u}) (U : T.Etale)
    (S : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (hs : (∀ n : ℕ, Nonempty ((S.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))) (q : ℤ) :
    (relativeSectionComplex T U S.X₃).homology q ⟶
      (relativeSectionComplex T U S.X₁).homology (q + 1) :=
  (relativeShortComplex_shortExact T U S hs).δ q (q + 1) rfl

/-- Absolute sections of the same short complex, extended by zero.
Source: Stacks Project, Tag 013T and Tag 03AJ
(blueprint: lem-amb-relative-torsor-cohomology). -/
noncomputable def relativeAbsoluteShortComplex (T : Scheme.{u})
    (S : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)) :
    ShortComplex (CochainComplex AddCommGrpCat.{u + 1} ℤ) :=
  S.map (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)) ⋙
    ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1})

/-- The absolute evaluated horseshoe is short exact.
Source: Stacks Project, Tag 013T
(blueprint: lem-amb-relative-torsor-cohomology).
Proof: sections preserve each supplied split row and extension by zero adds zero rows.
Exactness of complexes is checked degreewise. -/
theorem relativeAbsoluteShortComplex_shortExact (T : Scheme.{u})
    (S : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (hs : (∀ n : ℕ, Nonempty ((S.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))) :
    (relativeAbsoluteShortComplex T S).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro q
  exact (extendedSections_split T (Scheme.Etale.mk (𝟙 T)) S hs q).some.shortExact


set_option backward.isDefEq.respectTransparency false in
private lemma coneMap_fst
    {A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ r' = r ≫ b) :
    HomologicalComplex.homotopyCofiber.mapArrowHom r r'
        (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h) ≫
      CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (CochainComplex.mappingCone.fst r') =
    CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (CochainComplex.mappingCone.fst r) ≫ a⟦(1 : ℤ)⟧' := by
  rw [← CochainComplex.HomComplex.Cocycle.equivHomShift_symm_precomp,
    ← CochainComplex.HomComplex.Cocycle.equivHomShift_symm_postcomp]
  congr 1
  apply CochainComplex.HomComplex.Cocycle.ext
  apply CochainComplex.HomComplex.Cochain.ext
  intro i j hij
  change ((CochainComplex.HomComplex.Cochain.ofHom _).comp
      (CochainComplex.mappingCone.fst r').1 (zero_add 1)).v i j hij =
    ((CochainComplex.mappingCone.fst r).1.comp
      (CochainComplex.HomComplex.Cochain.ofHom a) (add_zero 1)).v i j hij
  simp only [CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.comp_zero_cochain_v,
    CochainComplex.HomComplex.Cochain.ofHom_v]
  obtain rfl := hij
  apply HomologicalComplex.homotopyCofiber.ext_from_X r (i + 1) i rfl <;>
    simp [CochainComplex.mappingCone.fst,
      HomologicalComplex.homotopyCofiber.mapArrowHom,
      HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom r' _ (i + 1) i rfl]

set_option backward.isDefEq.respectTransparency false in
private lemma sectionMap_forget (T : Scheme.{u}) (U : T.Etale)
    {I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (a : I ⟶ J) :
    relativeSectionMap T U a ≫ relativeForgetComplex T U J =
      relativeForgetComplex T U I ≫ HomologicalComplex.extendMap
        (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex _).map a)
        ComplexShape.embeddingUpNat := by
  let e := (shiftFunctorAdd' (CochainComplex AddCommGrpCat.{u + 1} ℤ)
      (1 : ℤ) (-1 : ℤ) 0 (by decide)).symm ≪≫
    shiftFunctorZero (CochainComplex AddCommGrpCat.{u + 1} ℤ) ℤ
  let f := HomologicalComplex.extendMap
    (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex _).map a)
    ComplexShape.embeddingUpNat
  change relativeSectionMap T U a ≫
      ((shiftFunctor _ (-1 : ℤ)).map _ ≫ e.hom.app _) =
    ((shiftFunctor _ (-1 : ℤ)).map _ ≫ e.hom.app _) ≫ f
  unfold relativeSectionMap relativeFiberMap
  rw [← Category.assoc, ← Functor.map_comp]
  erw [coneMap_fst]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  exact e.hom.naturality f

/-- Relative connecting maps commute with forgetting support.
Source: Stacks Project, Tag 03AJ, relative refinement; Tag 013T
(blueprint: lem-amb-relative-torsor-cohomology).
Proof: cone projection is natural in complex maps, so the three forgetful projections
form a morphism from the relative horseshoe to the absolute horseshoe. Apply homology
long-exact-sequence naturality. This uses the same lift-and-differentiate boundary on
both rows, hence also fixes its sign. -/
theorem relativeConnecting_forget (T : Scheme.{u}) (U : T.Etale)
    (S : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (hs : (∀ n : ℕ, Nonempty ((S.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))) (q : ℤ) :
    relativeConnecting T U S hs q ≫
        HomologicalComplex.homologyMap (relativeForgetComplex T U S.X₁) (q + 1) =
      HomologicalComplex.homologyMap (relativeForgetComplex T U S.X₃) q ≫
        (relativeAbsoluteShortComplex_shortExact T S hs).δ q (q + 1) rfl := by
  let m : relativeShortComplex T U S ⟶ relativeAbsoluteShortComplex T S := {
    τ₁ := relativeForgetComplex T U S.X₁
    τ₂ := relativeForgetComplex T U S.X₂
    τ₃ := relativeForgetComplex T U S.X₃
    comm₁₂ := (sectionMap_forget T U S.f).symm
    comm₂₃ := (sectionMap_forget T U S.g).symm }
  exact HomologicalComplex.HomologySequence.δ_naturality m
    (relativeShortComplex_shortExact T U S hs)
    (relativeAbsoluteShortComplex_shortExact T S hs) q (q + 1) rfl


set_option backward.isDefEq.respectTransparency false in
private lemma resolutionTransfer_comp_square {T T' : Scheme.{u}} (h : T' ⟶ T)
    {I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    {I' J' : CochainComplex (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (f : I ⟶ J) (f' : I' ⟶ J')
    (a : I ⟶ ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj I')
    (b : J ⟶ ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj J')
    (comm : a ≫ ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).map f' =
      f ≫ b) (A : T.Etale) (B : T'.Etale)
    (k : B ⟶ (MorphismProperty.Over.pullback @Etale ⊤ h).obj A) :
    resolutionSectionTransfer h I I' a A B k ≫
        ((etaleSectionFunctor B).mapHomologicalComplex (.up ℕ)).map f' =
      ((etaleSectionFunctor A).mapHomologicalComplex (.up ℕ)).map f ≫
        resolutionSectionTransfer h J J' b A B k := by
  apply HomologicalComplex.hom_ext
  intro n
  have hc := congrArg (fun v ↦ (v.f n).hom.app (op A)) comm
  change (a.f n).hom.app (op A) ≫ (f'.f n).hom.app _ =
    (f.f n).hom.app (op A) ≫ (b.f n).hom.app (op A) at hc
  change ((a.f n).hom.app (op A) ≫ (I'.X n).obj.map k.op) ≫
    (f'.f n).hom.app (op B) =
      (f.f n).hom.app (op A) ≫ (b.f n).hom.app (op A) ≫ (J'.X n).obj.map k.op
  rw [Category.assoc, (f'.f n).hom.naturality, ← Category.assoc, hc, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private lemma transfer_comp_square {T T' : Scheme.{u}} (h : T' ⟶ T) (W : T.Opens)
    {I J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    {I' J' : CochainComplex (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (f : I ⟶ J) (f' : I' ⟶ J')
    (a : I ⟶ ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj I')
    (b : J ⟶ ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj J')
    (comm : a ≫ ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).map f' =
      f ≫ b) :
    relativeTransfer h W I I' a ≫ relativeSectionMap T' (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) f' =
      relativeSectionMap T (Scheme.Etale.mk W.ι) f ≫ relativeTransfer h W J J' b := by
  unfold relativeTransfer relativeSectionMap
  rw [← fiberMap_comp, ← fiberMap_comp]
  congr 1
  · rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
    exact congrArg (fun v ↦ HomologicalComplex.extendMap v ComplexShape.embeddingUpNat)
      (resolutionTransfer_comp_square h f f' a b comm _ _ _)
  · rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
    exact congrArg (fun v ↦ HomologicalComplex.extendMap v ComplexShape.embeddingUpNat)
      (resolutionTransfer_comp_square h f f' a b comm _ _ _)

/-- Relative connecting maps are natural under scheme pullback and coefficient maps.
This includes identity scheme pullback, and hence independence of horseshoe choices.
Source: Stacks Project, Tags 0G71 and 0G78; Tag 013T
(blueprint: lem-amb-relative-torsor-cohomology).
Proof: the three comparison maps induce compatible strict squares of restriction maps,
hence a morphism of the short exact relative complex sequences. Homology-sequence
naturality gives the displayed identity. For coefficient resolutions, lift a morphism
of short exact coefficient sequences by the horseshoe-morphism-lift theorem, applying
exact inverse image first for scheme pullback. The resulting homotopy class is canonical.
The relative functor is exact on bounded-below injective models: its shift comparison
is (a,b) ↦ (a,-b), and its cone comparison is (x,y,z,w) ↦ (x,z,y,-w).
The horseshoe off-diagonal t represents the coefficient boundary for the -p cone
convention. The relative off-diagonal (t_T,-t_V) therefore gives precisely this boundary,
so the derived pullback and the displayed complex calculation agree. -/
theorem relativeConnecting_pullback_naturality {T T' : Scheme.{u}} (h : T' ⟶ T)
    (W : T.Opens)
    (S : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (S' : ShortComplex
      (CochainComplex (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (hs : (∀ n : ℕ, Nonempty ((S.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting)))
    (hs' : (∀ n : ℕ, Nonempty ((S'.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting)))
    (a : S ⟶ S'.map ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)))
    (q : ℤ) :
    relativeConnecting T (Scheme.Etale.mk W.ι) S hs q ≫
        HomologicalComplex.homologyMap (relativeTransfer h W S.X₁ S'.X₁ a.τ₁) (q + 1) =
      HomologicalComplex.homologyMap (relativeTransfer h W S.X₃ S'.X₃ a.τ₃) q ≫
        relativeConnecting T' (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) S' hs' q := by
  let m : relativeShortComplex T (Scheme.Etale.mk W.ι) S ⟶
      relativeShortComplex T' (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) S' := {
    τ₁ := relativeTransfer h W S.X₁ S'.X₁ a.τ₁
    τ₂ := relativeTransfer h W S.X₂ S'.X₂ a.τ₂
    τ₃ := relativeTransfer h W S.X₃ S'.X₃ a.τ₃
    comm₁₂ := transfer_comp_square h W S.f S'.f a.τ₁ a.τ₂ a.comm₁₂
    comm₂₃ := transfer_comp_square h W S.g S'.g a.τ₂ a.τ₃ a.comm₂₃ }
  exact HomologicalComplex.HomologySequence.δ_naturality m
    (relativeShortComplex_shortExact T (Scheme.Etale.mk W.ι) S hs)
    (relativeShortComplex_shortExact T' (Scheme.Etale.mk (h ⁻¹ᵁ W).ι) S' hs') q (q + 1) rfl


/-- Every short exact coefficient sequence has a split resolution model to which the
relative connecting-map construction applies.
Source: Stacks Project, Tag 013T; Tag 03AJ, relative refinement
(blueprint: lem-amb-relative-torsor-cohomology).
Proof: choose a horseshoe of nonnegative injective resolutions, with the augmentations
commuting with the two coefficient maps. Its rows split with the given inclusion and
projection. Evaluation, extension by zero, finite cone sums and shift preserve these
split rows, so the resulting relative complex sequence is short exact. Its homology
boundary is relativeConnecting, in every integer degree. -/
theorem relative_coefficient_sequence (T : Scheme.{u}) (W : T.Opens)
    (S : ShortComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hS : S.ShortExact) :
    ∃ (I : InjectiveResolution S.X₁) (J : InjectiveResolution S.X₂)
      (K : InjectiveResolution S.X₃) (a : I.cocomplex ⟶ J.cocomplex)
      (b : J.cocomplex ⟶ K.cocomplex) (hab : a ≫ b = 0),
      I.ι ≫ a = (CochainComplex.single₀ _).map S.f ≫ J.ι ∧
      J.ι ≫ b = (CochainComplex.single₀ _).map S.g ≫ K.ι ∧
      (∀ n : ℕ, Nonempty (((ShortComplex.mk a b hab).map
        (HomologicalComplex.eval _ (.up ℕ) n)).Splitting)) ∧
      (relativeShortComplex T (Scheme.Etale.mk W.ι) (ShortComplex.mk a b hab)).ShortExact := by
  obtain ⟨I, J, K, a, b, ha, hb, hab, hrows⟩ :=
    InjectiveResolution.exists_horseshoe_resolutions S hS
  have hs : ∀ n : ℕ, Nonempty (((ShortComplex.mk a b hab).map
      (HomologicalComplex.eval _ (.up ℕ) n)).Splitting) := fun n ↦ by
    let hinj : Injective (((ShortComplex.mk a b hab).map
        (HomologicalComplex.eval _ (.up ℕ) n)).X₁) := I.injective n
    exact ⟨(hrows n).1.splittingOfInjective⟩
  exact ⟨I, J, K, a, b, hab, ha, hb, hs,
    relativeShortComplex_shortExact T (Scheme.Etale.mk W.ι) _ hs⟩


/-- The relative boundary is natural for coefficient-sequence comparison maps.
Source: Stacks Project, Tag 013T; Tag 03AJ, relative refinement
(blueprint: lem-amb-relative-torsor-cohomology).
Proof: section maps and the shifted cone are functorial, giving a morphism of the
relative short exact complex sequences. Apply naturality of the homology long exact
sequence. Horseshoe morphism lifting supplies such a comparison for any morphism of
short exact coefficient sequences; applying it to identities proves independence of
the horseshoe model. -/
theorem relativeConnecting_coefficient_naturality (T : Scheme.{u}) (U : T.Etale)
    (S S' : ShortComplex
      (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (hs : (∀ n : ℕ, Nonempty ((S.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting)))
    (hs' : (∀ n : ℕ, Nonempty ((S'.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting)))
    (a : S ⟶ S') (q : ℤ) :
    relativeConnecting T U S hs q ≫
        HomologicalComplex.homologyMap (relativeSectionMap T U a.τ₁) (q + 1) =
      HomologicalComplex.homologyMap (relativeSectionMap T U a.τ₃) q ≫
        relativeConnecting T U S' hs' q := by
  let m : relativeShortComplex T U S ⟶ relativeShortComplex T U S' := {
    τ₁ := relativeSectionMap T U a.τ₁
    τ₂ := relativeSectionMap T U a.τ₂
    τ₃ := relativeSectionMap T U a.τ₃
    comm₁₂ := by
      change relativeSectionMap T U a.τ₁ ≫ relativeSectionMap T U S'.f =
        relativeSectionMap T U S.f ≫ relativeSectionMap T U a.τ₂
      rw [← sectionMap_comp, ← sectionMap_comp, a.comm₁₂]
    comm₂₃ := by
      change relativeSectionMap T U a.τ₂ ≫ relativeSectionMap T U S'.g =
        relativeSectionMap T U S.g ≫ relativeSectionMap T U a.τ₃
      rw [← sectionMap_comp, ← sectionMap_comp, a.comm₂₃] }
  exact HomologicalComplex.HomologySequence.δ_naturality m
    (relativeShortComplex_shortExact T U S hs)
    (relativeShortComplex_shortExact T U S' hs') q (q + 1) rfl


/-- Cohomology of the cone comparison does not depend on its resolution lift.
Source: Stacks Project, Tag 03AJ, relative refinement; Tag 08FI
(blueprint: lem-amb-relative-torsor-cohomology).
Proof: direct image preserves injectives, since it is right adjoint to exact inverse
image. The difference of the comparisons vanishes on the augmentation. Exactness of the
source resolution and injectivity of the target terms recursively construct a null-homotopy
of that difference. Evaluation and extension by zero give compatible homotopies on the two
section complexes. The induced cone homotopy has the negative sign on its suspended summand;
the cochain differential verifies its identity. Shift and compose with the transfer from
direct-image sections to target sections. Homotopic maps have equal homology maps. -/
theorem relativeTransfer_independent {T T' : Scheme.{u}} (h : T' ⟶ T) (W : T.Opens)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G' : Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (f : G ⟶ (lowerStar AddCommGrpCat.{u + 1} h).obj G')
    (I : InjectiveResolution G) (J : InjectiveResolution G')
    (a b : I.cocomplex ⟶
      ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    (ha : I.ι.f 0 ≫ a.f 0 = f ≫ (lowerStar AddCommGrpCat.{u + 1} h).map (J.ι.f 0))
    (hb : I.ι.f 0 ≫ b.f 0 = f ≫ (lowerStar AddCommGrpCat.{u + 1} h).map (J.ι.f 0)) (q : ℤ) :
    HomologicalComplex.homologyMap (relativeTransfer h W I.cocomplex J.cocomplex a) q =
      HomologicalComplex.homologyMap (relativeTransfer h W I.cocomplex J.cocomplex b) q := by
  let L := ((lowerStar AddCommGrpCat.{u + 1} h).mapHomologicalComplex (.up ℕ)).obj
    J.cocomplex
  have hinj (n : ℕ) : Injective (L.X n) :=
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).map_injective _ (J.injective n)
  obtain ⟨H⟩ := comparisonHomotopy I L a b (ha.trans hb.symm)
  obtain ⟨Hrel⟩ := sectionMap_homotopy T (Scheme.Etale.mk W.ι) a b H
  let c := relativeTransfer h W L J.cocomplex (𝟙 L)
  have fac (v : I.cocomplex ⟶ L) :
      relativeTransfer h W I.cocomplex J.cocomplex v =
        relativeSectionMap T (Scheme.Etale.mk W.ι) v ≫ c := by
    simpa only [sectionMap_id, Category.comp_id] using
      (transfer_comp_square h W v (𝟙 J.cocomplex) v (𝟙 L) (by simp))
  rw [fac a, fac b]
  exact (Hrel.compRight c).homologyMap_eq q

end AlgebraicGeometry.Etale
