/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.Paper.OrientedConstructibleSheaf
public import Sheaf.Paper.OrientedProductPointsConservative
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Products

import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.AlgebraicGeometry.DimensionExtension
import Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound
import Sheaf.CategoryTheory.Sites.OrientedProductLargeSites
import Sheaf.AlgebraicGeometry.EtaleLowerShriekConstantConstructible
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.OrientedNearbyCycles
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalCohomology
import Sheaf.CategoryTheory.Sites.CoherentTopos
import Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget
import Sheaf.Paper.QcqsOrientedTriplePresentation
import Sheaf.CategoryTheory.SitePointFibre
import Sheaf.CategoryTheory.Sites.CoherentToposRepair
import Sheaf.Paper.CoherentSetCriterion
import Sheaf.Paper.OrientedConstructibleSheafVanishing
import Sheaf.Paper.OrientedConstructibleSubquotients
import Sheaf.Paper.OrientedProperFibreExchange
import Sheaf.Paper.PsiConstructibilityDescent
import Sheaf.TraceFormula.FinitarySiteCoherentGenerators
import Sheaf.TraceFormula.FiniteBaseSplitsEtale

/-!
# Proper source direct image on vanishing topoi

Source: Orgogozo, Modifications et cycles proches sur une base générale,
§§9.1.1--9.1.2 and Lemma 8.3.3
(blueprint: lem-trf-oriented-proper-image-constructibility).

The comparison to the general oriented-product constructibility predicate uses the
canonical identity-base-change isomorphism. Geometric points are composed with the
point of their algebraically closed field, so composition comparisons use the recorded
étale-composition isomorphisms. All coefficient and site universes remain independent.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v s

open CategoryTheory CategoryTheory.Limits CategoryTheory.AdicSites
open AlgebraicGeometry.OrientedNearbyCycles

namespace AlgebraicGeometry.OrientedProperImage

/-- Identity base change on the transported small étale site, via the first projection
of its fibre products. Source: ILO XI §1.1; Orgogozo §8.1
(blueprint: lem-trf-oriented-proper-image-constructibility). -/
def etaleIdentity (S : Scheme.{u}) : etaleBaseChange.{u, v} (𝟙 S) ≅ 𝟭 _ :=
  Functor.isoWhiskerLeft AsSmall.down
      (Functor.isoWhiskerRight (MorphismProperty.Over.pullbackId @Etale ⊤ S) AsSmall.up) ≪≫
    AsSmall.equiv.counitIso

/-- Replace the identity leg of a vanishing triple by base change along the identity.
This is the canonical isomorphism of the two triple-site presentations.
Source: ILO XI §1.1; Orgogozo §8.1
(blueprint: lem-trf-oriented-proper-image-constructibility). -/
def vanishingToProduct {X S : Scheme.{u}} (f : X ⟶ S) :
    VanishingSite.{u, v} f ⥤ OrientedConstructibleSheaf.ProductSite.{u, v} f (𝟙 S) :=
  Comma.map (F₁ := 𝟭 _) (F₂ := 𝟭 _) (F := 𝟭 _)
    (Functor.leftUnitor _).hom
    (NatTrans.prod' (Functor.rightUnitor _).inv
      ((etaleIdentity S).inv ≫ (Functor.rightUnitor _).inv))

/-- The constant-scalar map from the constant presheaf to the underlying ring sheaf.
It is precisely the commutative-ring sheafification unit with commutativity forgotten.
Source: Stacks 03CY; Orgogozo §8.1
(blueprint: lem-trf-oriented-proper-image-constructibility). -/
def scalarMap (T : Site.{max (u + 1) v}) (Λ : Type v) [CommRing Λ] :=
  Functor.whiskerRight
    (toSheafify T.topology
      ((Functor.const T.objectsᵒᵖ).obj (CommRingCat.of (Coeff.{u, v} Λ))))
    (forget₂ CommRingCat.{max (u + 1) v} RingCat.{max (u + 1) v})

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to constant scalars, on the very same section groups.
Source: Stacks 03CY; Orgogozo §8.1
(blueprint: lem-trf-oriented-proper-image-constructibility). -/
def fixedPresheaf (T : Site.{max (u + 1) v}) (Λ : Type v) [CommRing Λ]
    (M : T.modules (Coeff.{u, v} Λ)) :
    T.objectsᵒᵖ ⥤ ModuleCat.{max (u + 1) v} (Coeff.{u, v} Λ) :=
  let P := (PresheafOfModules.restrictScalars (scalarMap T Λ)).obj M.val
  { obj := P.obj
    map := fun f => P.map f
    map_id := fun X => by ext x; exact congrArg (fun f => f x) (P.map_id X)
    map_comp := fun f g => by ext x; exact P.map_comp_apply f g x }

set_option backward.isDefEq.respectTransparency false in
/-- Retain the actual fixed scalar action on each section group. The sheaf condition
is reflected by forgetting to abelian groups. Source: Stacks 03CY; Orgogozo §8.1
(blueprint: lem-trf-oriented-proper-image-constructibility). -/
def fixedModules (T : Site.{max (u + 1) v}) (Λ : Type v) [CommRing Λ] :
    T.modules (Coeff.{u, v} Λ) ⥤
      Sheaf T.topology (ModuleCat.{max (u + 1) v} (Coeff.{u, v} Λ)) where
  obj M := ⟨fixedPresheaf T Λ M,
    Presheaf.isSheaf_of_isSheaf_comp T.topology _
      (forget₂ (ModuleCat.{max (u + 1) v} (Coeff.{u, v} Λ))
        AddCommGrpCat.{max (u + 1) v}) M.isSheaf⟩
  map f := { hom :=
    { app := fun X => (ModuleCat.restrictScalars ((scalarMap T Λ).app X).hom).map
        (f.val.app X)
      naturality := fun _ _ g => by
        ext x
        exact PresheafOfModules.naturality_apply f.val g x } }

/-- Transport to the general oriented-product presentation by the sheafified left Kan
extension along the explicit identity comparison on triples. This changes no topos or
coefficient ring. Source: ILO XI §1.1; Orgogozo §8.1
(blueprint: lem-trf-oriented-proper-image-constructibility). -/
def constructibilityTransport {X S : Scheme.{u}} (f : X ⟶ S)
    (Λ : Type v) [CommRing Λ] :
    (vanishingDatum.{u, v} f).modules (Coeff.{u, v} Λ) ⥤
      OrientedConstructibleSheaf.Modules f (𝟙 S) Λ :=
  fixedModules (vanishingDatum f) Λ ⋙
    sheafToPresheaf (vanishingTopology f) (ModuleCat (Coeff.{u, v} Λ)) ⋙
    (vanishingToProduct.{u, v} f).op.lan ⋙
    presheafToSheaf (OrientedConstructibleSheaf.productTopology f (𝟙 S))
      (ModuleCat (Coeff.{u, v} Λ)) ⋙
    (constant_ring_module_sheaves
      (OrientedConstructibleSheaf.productTopology f (𝟙 S)) (Coeff.{u, v} Λ)).1.choose.inverse

/-- The recorded constructibility predicate on the canonically identified vanishing
site, with precisely its finite source/base stratifications and finite local values.
Source: Orgogozo §8.1 (blueprint: lem-trf-oriented-proper-image-constructibility). -/
abbrev IsConstructible {X S : Scheme.{u}} (f : X ⟶ S)
    (Λ : Type v) [CommRing Λ] [Finite Λ]
    (F : (vanishingDatum.{u, v} f).modules (Coeff.{u, v} Λ)) : Prop :=
  OrientedConstructibleSheaf.IsConstructible f (𝟙 S) Λ
    ((constructibilityTransport f Λ).obj F)

/-- The geometric stalk point composed with the scheme map from its algebraically
closed field. Source: ILO XI §1.8; Orgogozo Lemma 9.1.1
(blueprint: lem-trf-oriented-proper-image-constructibility). -/
def fieldPoint {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :=
  (geometricEtalePoint.{u, v} (𝟙 (Spec (.of Ω)))).comp (etaleMorphism x)

/-- Composition of these geometric points, given by the canonical fibre-product
composition comparison, including its associator. Source: ILO XI §1.9
(blueprint: lem-trf-oriented-proper-image-constructibility). -/
def fieldPointComp {X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (h : X ⟶ Y) :
    ((fieldPoint.{u, v} x).comp (etaleMorphism h)).direct ≅
      (fieldPoint.{u, v} (x ≫ h)).direct :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (etaleComposition x h)

/-- Pull the oriented specialization at y back to the selected geometric fibre point x.
Only composition isomorphisms and the equation xh=y enter this construction.
Source: ILO XI §1.8; Orgogozo Lemma 9.1.1
(blueprint: lem-trf-oriented-proper-image-constructibility). -/
def fibreOrientation {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (y : Spec (.of Ω) ⟶ Y) (t : Spec (.of Ξ) ⟶ S)
    (c : ((fieldPoint.{u, v} t).comp (identity _)).direct ⟶
      ((fieldPoint.{u, v} y).comp (etaleMorphism g)).direct)
    (x : {x : Spec (.of Ω) ⟶ X // x ≫ h = y}) :
    ((fieldPoint.{u, v} t).comp (identity _)).direct ⟶
      ((fieldPoint.{u, v} x.val).comp (etaleMorphism (h ≫ g))).direct :=
  c ≫ (fieldPointComp y g).hom ≫
    (eqToIso (congrArg (fun z : Spec (.of Ω) ⟶ S => (fieldPoint.{u, v} z).direct)
      ((Category.assoc x.val h g).symm.trans (congrArg (fun z => z ≫ g) x.property)))).inv ≫
    (fieldPointComp x.val (h ≫ g)).inv

/-- The actual constant-module stalk at the universal oriented lift of (x,t,c), valued
in modules on the one-object site presenting sets. Source: ILO XI §§1.4, 1.8;
Orgogozo Lemma 9.1.1 (blueprint: lem-trf-oriented-proper-image-constructibility). -/
def stalk {X S : Scheme.{u}} (f : X ⟶ S)
    {Ω Ξ : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
    (x : Spec (.of Ω) ⟶ X) (t : Spec (.of Ξ) ⟶ S)
    (c : ((fieldPoint.{u, v} t).comp (identity _)).direct ⟶
      ((fieldPoint.{u, v} x).comp (etaleMorphism f)).direct)
    (Λ : Type v) [CommRing Λ] :=
  (moduleMorphism (vanishingDatum.{u, v} f) punctualSite.{max (u + 1) v}
    (lift f _ (sheaf_isTopos punctualSite.{max (u + 1) v}.topology)
      (fieldPoint x) (fieldPoint t) c).morphism).modulePull (Coeff.{u, v} Λ)


/-- The source map on vanishing topoi induced by (h,1), using the recorded square lift.
Source: ILO XI §1.9; Orgogozo §9.1
(blueprint: lem-trf-oriented-proper-image-constructibility). -/
def sourceMorphism {X Y S : Scheme.{u}} (h : X ⟶ Y) (g : Y ⟶ S) :=
  squareModules.{u, v} g (h ≫ g) h (𝟙 S) (Category.comp_id (h ≫ g)).symm

/-- Cohomology in the recorded standard localization of constant-module sheaves.
Source: Orgogozo §9.1.2; Stacks 05RU
(blueprint: lem-trf-oriented-proper-image-constructibility). -/
def cohomology (T : Site.{s}) (A : Type s) [CommRing A] (q : ℤ) :
    T.derived A ⥤ T.modules A :=
  @DerivedCategory.homologyFunctor (T.modules A) _ _ (HasDerivedCategory.standard _) q

/-- Proper direct image preserves all constructible cohomology of bounded objects;
finite direct image is exact, detects constructibility, and has the finite stalk-product
formula naturally in the sheaf. Products are in the punctual module category, canonically
modules over the coefficient ring; in particular its empty product is the zero module.
Source: Orgogozo §§9.1.1--9.1.2 and Lemma 8.3.3
(blueprint: lem-trf-oriented-proper-image-constructibility).

Proof plan (the numbered steps are the DAG node's complete proof):

1. The finite-presentation morphisms in the statement are finite type and qcqs. Since $S$ is
   Noetherian, [lem-weil-pbc-finite-type-over-noetherian] makes $X$ and $Y$ Noetherian, and
   [lem-weil-pbc-locally-noetherian-quasi-separated] makes them quasi-separated. Thus their
   vanishing topoi admit the finite-cover triple sites of [lem-trf-qcqs-oriented-triple-
   presentation]. We use triples $Z=(E\to V\leftarrow W)$ with $E\to X$ and $V,W\to S$ separated
   etale of finite presentation, and write $H_Z=h_Z^\#$ and $G_Z=\Lambda[H_Z]$, the sheafified
   free constant-$\Lambda$ module on $H_Z$. This is the free sheaf characterized by maps to $F$
   being sections $F(Z)$ in [lem-weil-pbc-sheaf-free-separator].

2. Choose $d$ bounding the dimensions of the fibres of $h$ by [lem-fin-finite-type-fibre-
   dimension-bound], and set $c=2d$. The geometric fibres have the same dimension as the
   residue-field fibres by [lem-kun-dimension-extension]; they are proper by [lem-pc-proper-
   base-change], and finite type by the finite-presentation base-change clause of [lem-weil-pbc-
   qcqs-morphism-permanence]. For every sheaf $A$ on $V_f$, [lem-trf-oriented-proper-fibre-
   exchange] computes $(R^j\bar h_*A)_z$ as $H^j(X_y,\phi_z^*A)$. The proper map
   $X_y\to\operatorname{Spec}\Omega$ has fibre dimension at most $d$, so [lem-kun-proper-
   torsion-cd-bound] makes this zero for $j>c$. Its hypotheses apply to the underlying torsion
   abelian sheaf, and [lem-pe-left-module-derived-evaluation-forget] identifies its cohomology
   with the forgotten module cohomology. Finally [lem-trf-oriented-product-points-conservative]
   detects zero. We have proved $R^j\bar h_*A=0$ for all sheaves $A$ and $j>c$, with no
   constructibility assumption on $A$. This uniform bound is what will make the generator
   argument finite.

3. Each $H_Z$ is coherent by [lem-trf-finitary-site-coherent-generators] applied to the site in
   Step 1. By [lem-trf-coherent-set-criterion], it is finite locally constant on a finite
   collection of source/base strata. On such a restriction, the free module $G_Z$ is the
   constant free module on that finite set, locally on the same covering. It has finite
   underlying set since $\Lambda$ is finite. Hence $G_Z$ is constructible by [def-trf-oriented-
   constructible-sheaf]. The same criterion says that the underlying set sheaf of any
   constructible module sheaf $F$ is coherent, in particular quasi-compact in the explicit
   covering-family sense of [def-trf-coherent-topos].

4. The representable generators give a covering family $H_Z\to|F|$, one map for each section of
   $F$ on $Z$. By quasi-compactness in Step 3, finitely many of these maps cover $|F|$. For each
   selected section the free-sheaf property [lem-weil-pbc-sheaf-free-separator] gives $G_Z\to
   F$, sending its basis generator to that section. Their sum $P\to F$ is epic: every section of
   $F$ locally lies in one selected $H_Z$, and hence locally is the image of a basis generator.
   Local surjectivity is the epimorphism criterion [lem-weil-pbc-site-sheaf-sets-epi-locally-
   surjective], and also gives an epimorphism of modules. Here $P$ is a finite sum of
   constructible $G_Z$, and its kernel is constructible by [lem-trf-oriented-constructible-
   subquotients]. Repeating with the kernel gives, for any prescribed finite $N$, exact
   sequences $0\to K_{i+1}\to P_i\to K_i\to0$ for $0\leq i<N$, with $K_0=F$, all $K_i$
   constructible and $P_i$ finite sums of the $G_Z$. No infinite totalization or finite
   projective resolution is used.

5. Fix one triple $Z=(E\to V\leftarrow W)$. Apply [lem-trf-finite-base-splits-etale] to the two
   separated etale maps $V\to S$, $W\to S$, obtaining a finite surjection $T\to S$ for which
   both are finite coproducts of opens of $T$. Pulling back triples represents inverse image by
   [lem-trf-qcqs-oriented-triple-presentation]. Decompose $E_T$ by the components of $V_T$;
   further decompose each open component of $W_T$ by its inverse images of the components of
   $V_T$. These are finitely many open-and-closed pieces of that component and therefore open
   subsets of $T$. Thus the pulled-back triple sheaf is a finite coproduct of triples $(E_a\to
   V_a\leftarrow W_a)$, where $V_a,W_a\subseteq T$ are opens and $W_a\subseteq V_a$, and $E_a\to
   X_T$ is separated etale of finite presentation. The cases of empty components give zero
   summands.

6. For each triple in Step 5 put $A_a=(u_a)_!\underline\Lambda$ on $(X_T)_{\mathrm{Et}}$, where
   $u_a:E_a\to X_T$, and $B_a=p_{f_T,2}^*(j_{a!}\underline\Lambda)$, where
   $j_a:W_a\hookrightarrow T$. The inverse-image formula in [lem-trf-oriented-product-universal]
   identifies its representable with $p_{f_T,1}^{-1}h_{E_a}\times p_{f_T,2}^{-1}h_{W_a}$: since
   $V_a$ is an open containing the image of $E_a$ and $W_a\subseteq V_a$, the compatibility over
   $V_a$ is automatic. Taking free modules gives $G_{Z_a}\cong p_{f_T,1}^*A_a\otimes_\Lambda
   B_a$, by the basis bijection $\Lambda[P\times Q]\cong\Lambda[P]\otimes_\Lambda\Lambda[Q]$.
   This also follows from the explicit free-sheaf property [lem-weil-pbc-sheaf-free-separator].
   The direct-sum description of $(u_a)_!$ in [def-weil-pbc-etale-sum-extension] identifies
   $A_a$ with the free sheaf on $h_{E_a}$. It is constructible in the stalk-based predicate by
   [lem-weil-pbc-etale-free-sheaf-constructible-core], and [lem-weil-pbc-constructible-etale-
   module-sheaf-comparison] identifies this with finite-stratification constructibility. The
   sheaf $j_{a!}\underline\Lambda$ is constant $\Lambda$ on $W_a$ and zero outside, so $B_a$ has
   the analogous two base strata.

7. Apply ordinary etale proper-image constructibility [lem-weil-pbc-etale-compactification-
   constructibility] to $h_T:X_T\to Y_T$ with the identity open compactification and coefficient
   $A_a$. It applies without a finite-dimensional hypothesis: the schemes are qcqs, $h_T$ is
   proper of finite presentation, and $\Lambda$ is finite. These facts persist under base change
   by [lem-weil-pbc-qcqs-morphism-permanence] and [lem-pc-proper-base-change]. The first-
   projection exchange of [lem-trf-oriented-proper-fibre-exchange] now gives $$R\bar
   h_{T,*}p_{f_T,1}^*A_a\simeq p_{g_T,1}^*Rh_{T,*}A_a.$$ Its cohomology is constructible on
   $V_{g_T}$: inverse image is exact, and the constructible strata on $Y_T$ pull back along the
   first projection, using the single base stratum $T$ in [def-trf-oriented-constructible-
   sheaf].

8. On $V_{g_T}$ put $B=p_{g_T,2}^*j_{a!}\underline\Lambda$, so $\bar h_T^*B=B_a$. Tensoring with
   $B$ or $B_a$ is exact: at each oriented point it tensors with either $0$ or $\Lambda$;
   inverse image commutes with tensor by [lem-weil-pbc-ringed-topoi-derived-tensor-pullback],
   and the exact conservative points in [lem-trf-site-point-fibre, lem-trf-oriented-product-
   points-conservative] test exactness. The projection map $$R\bar h_{T,*}C\otimes^L
   B\longrightarrow R\bar h_{T,*}(C\otimes^L\bar h_T^*B)$$ is defined by adjunction from the
   tensor of the counit with $1_{\bar h_T^*B}$, using the derived adjunction of [def-trf-
   oriented-nearby-cycles]. By the fibre formula [lem-trf-oriented-proper-fibre-exchange], at
   $z=(y,t)$ it is the projection map for $R\Gamma(X_y,-)$ and the constant coefficient $B_z$,
   which is $\Lambda$ if $t\in W_a$ and zero otherwise. In both cases this is the identity unit
   isomorphism or the isomorphism $0\to0$. Conservativity proves the map invertible. Take
   $C=p_{f_T,1}^*A_a$ and use Step 7. Exact tensor with $B$ keeps each cohomology sheaf on the
   base-open $W_a$ and makes it zero on the complement. Refining the base strata by $W_a$ and
   its closed complement proves constructibility of $R\bar h_{T,*}G_{Z_a}$ in every degree.

9. The finite sums in Step 5 and Step 8 show that $R\bar h_{T,*}v_f^*G_Z$ has constructible
   cohomology. By the base-change exchange of [lem-trf-oriented-proper-fibre-exchange] and
   exactness of inverse image, this is $v_g^*\mathcal H^q(R\bar h_*G_Z)$ in each degree. The map
   $T\to S$ is proper by [lem-weil-pbc-finite-proper]. Apply [lem-trf-psi-constructibility-
   descent] to the sheaf $\mathcal H^q(R\bar h_*G_Z)$ on $V_g$. Its hypotheses concern $S$
   Noetherian and $g$ of finite presentation, exactly our hypotheses; it does not require that
   this sheaf be a nearby-cycle sheaf. Thus $R^q\bar h_*G_Z$ is constructible for every
   $q\geq0$, and the same holds for finite sums $P$ of the generators.

10. Now let $F$ be any constructible sheaf. Use Step 4 with $N=c+1$. Fix $q\geq0$. Step 2 gives
   $R^{q+c+1}\bar h_*K_{c+1}=0$. Descend on $i=c,c-1,\ldots,0$. The long exact sequence of [lem-
   weil-pbc-derived-functor-long-exact] contains $$R^{q+i}\bar h_*P_i\longrightarrow R^{q+i}\bar
   h_*K_i\longrightarrow R^{q+i+1}\bar h_*K_{i+1}.$$ The first term is constructible by Step 9,
   and the third is constructible by the descending induction. The middle term is an extension
   of a quotient of the first term by a subsheaf of the third. Therefore it is constructible by
   [lem-trf-oriented-constructible-subquotients]. At $i=0$ this proves $R^q\bar h_*F$
   constructible. Negative degrees vanish for a sheaf because direct image is right derived, and
   the uniform bound from Step 2 also applies. The sheaf categories have enough injectives by
   [prop-pur-kinjective-resolutions-exist], as required by the long exact sequence.

11. For the bounded constructible complex $L$, choose a finite interval $[a,b]$ containing its
   cohomology. Its successive truncation triangles [lem-weil-pbc-truncation-triangle] build it
   in finitely many steps from $H^r(L)[-r]$, $a\leq r\leq b$. Derived direct image commutes with
   shifts and sends these triangles to triangles by [lem-pc-right-derived-functor-triangulated].
   Step 10 handles every $H^r(L)$. In the cohomology long exact sequence of each image triangle
   supplied by [lem-sf-derived-homology-long-exact], each new cohomology sheaf is an extension
   of a quotient of one known constructible sheaf by a subobject of another, so [lem-trf-
   oriented-constructible-subquotients] applies. Induction on the finite number of truncations
   proves constructibility of every $H^q(R\bar h_*L)$, the first clause.

12. Suppose $h$ is finite. At $z=(y,t)$ the fibre formula [lem-trf-oriented-proper-fibre-
   exchange] and the zero-dimensional calculation [lem-weil-pbc-zero-dimensional-cohomology]
   give $$(\bar h_*F)_z\cong\prod_{x\in|X_y|}F_{(x,t)},\qquad (R^q\bar h_*F)_z=0\quad(q>0).$$ By
   [def-weil-finite-integral-morphism], $X_y$ is the spectrum of a finite-dimensional
   $\Omega$-algebra: tensor the finite module generators for an affine finite model of $h$ with
   $\Omega$. Every prime quotient is a finite-dimensional domain over $\Omega$; multiplication
   by a nonzero element is injective and hence surjective, so the quotient is a field. All
   primes are maximal and $\dim X_y\leq0$. Properness gives separatedness, and the finite
   algebra generators give finite type. These verify the hypotheses of the cited calculation;
   nilpotents are permitted there. The product is over the finitely many geometric fibre points,
   not over arbitrary repeated representatives of one point. The identification of module and
   abelian cohomology is [lem-pe-left-module-derived-evaluation-forget]. For a short exact
   sequence on $V_f$, each factor stalk sequence is exact by [lem-trf-site-point-fibre], and
   finite products of module sequences are exact componentwise. The formula therefore makes its
   direct-image sequence exact at every point of $V_g$; exact conservative points detect zero
   kernels and cokernels by [lem-trf-oriented-product-points-conservative]. Thus $\bar h_*$ is
   exact and we have also proved the requested stalk formula, including the empty-fibre case
   (zero module).

13. If $F$ is constructible, Step 10 gives constructibility of $\bar h_*F$. Conversely assume
   $\bar h_*F$ constructible. Its exact inverse image $\bar h^*\bar h_*F$ is constructible by
   [def-trf-oriented-constructible-sheaf]: pull a source stratum of $Y$ back by $h$, keep each
   base stratum of $S$, and pull back the finite locally constant module sheaves. Consider the
   counit $\bar h^*\bar h_*F\to F$. At $(x,t)$ its map is the projection from the finite product
   in Step 12 to the $x$-factor, since the fibre isomorphism is induced by restriction. This
   projection is surjective: extend an element in that factor by zero in the others. Exact
   conservative points [lem-trf-site-point-fibre, lem-trf-oriented-product-points-conservative]
   therefore make the counit epic. Hence $F$ is a quotient of a constructible sheaf and is
   constructible by [lem-trf-oriented-constructible-subquotients]. This proves detection without
   imposing surjectivity on $h$; an oriented point of $V_f$ already supplies its selected
   nonempty fibre factor.
-/
theorem proper_image_constructibility {X Y S : Scheme.{u}} [IsNoetherian S]
    (h : X ⟶ Y) (g : Y ⟶ S)
    [LocallyOfFinitePresentation h] [QuasiCompact h] [QuasiSeparated h] [IsProper h]
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]
    (Λ : Type v) [CommRing Λ] [Finite Λ]
    (N : ℕ) (hkill : (N : Λ) = 0) (hunit : IsUnit (N : Γ(S, ⊤))) :
    (∀ L : VanishingDerived.{u, v} (h ≫ g) Λ,
      IsBounded (vanishingDatum.{u, v} (h ≫ g)) (Coeff.{u, v} Λ) L →
      (∀ q : ℤ, IsConstructible.{u, v} (h ≫ g) Λ
        ((cohomology (vanishingDatum.{u, v} (h ≫ g)) (Coeff.{u, v} Λ) q).obj L)) →
      ∀ q : ℤ, IsConstructible.{u, v} g Λ
        ((cohomology (vanishingDatum.{u, v} g) (Coeff.{u, v} Λ) q).obj
          (((sourceMorphism.{u, v} h g).push (Coeff.{u, v} Λ)).obj L))) ∧
    (IsFinite h →
      PreservesFiniteLimits ((sourceMorphism.{u, v} h g).modulePush (Coeff.{u, v} Λ)) ∧
      PreservesFiniteColimits ((sourceMorphism.{u, v} h g).modulePush (Coeff.{u, v} Λ)) ∧
      (∀ F : (vanishingDatum.{u, v} (h ≫ g)).modules (Coeff.{u, v} Λ),
        IsConstructible.{u, v} (h ≫ g) Λ F ↔ IsConstructible.{u, v} g Λ
          (((sourceMorphism.{u, v} h g).modulePush (Coeff.{u, v} Λ)).obj F)) ∧
      ∀ (Ω Ξ : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ξ] [IsAlgClosed Ξ]
        (y : Spec (.of Ω) ⟶ Y) (t : Spec (.of Ξ) ⟶ S)
        (c : ((fieldPoint.{u, v} t).comp (identity _)).direct ⟶
          ((fieldPoint.{u, v} y).comp (etaleMorphism g)).direct),
        Finite {x : Spec (.of Ω) ⟶ X // x ≫ h = y} ∧
        Nonempty
          (((sourceMorphism.{u, v} h g).modulePush (Coeff.{u, v} Λ) ⋙ stalk.{u, v} g y t c Λ) ≅
            (Functor.pi' (fun x : {x : Spec (.of Ω) ⟶ X // x ≫ h = y} =>
              stalk.{u, v} (h ≫ g) x.val t
                (fibreOrientation.{u, v} h g y t c x) Λ) ⋙ Pi.functor _))) := by
  sorry

end AlgebraicGeometry.OrientedProperImage
