/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Sheaf.CategoryTheory.Sites.AbelianInverseImagePresentation
public import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Connecting
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.Algebra.Homology.ModelCategory.Injective
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import Mathlib.Algebra.Homology.Homotopy
import WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDerivedTriangleComparison
import WeilConjectures.CategoryTheory.Abelian.NatComplexDerivedBoundary
import WeilConjectures.CategoryTheory.Abelian.HorseshoeMorphismLiftExactSource
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor

/-! # Resolution pullback and derived connecting maps for geometric morphisms

Source: Stacks, Cohomology on Sites, Tags 01FT and 08J6; Cohomology, Tag 01F8;
Derived Categories, Tags 013P, 013S, 013T and 015B
(blueprint: lem-sfb-topos-cohomology-pullback-delta).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uC vC uD vD w dC dD dA

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ToposCohomologyPullback

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]

/-- Sheafification on a site essentially small relative to the coefficient universe.
Source: Stacks 00YV (blueprint: lem-sfb-topos-cohomology-pullback-delta). -/
instance abelianSheafification : HasSheafify J AddCommGrpCat.{w} :=
  hasSheafifyEssentiallySmallSite.{vC, w, uC, w + 1, w} J AddCommGrpCat.{w}

/-- Global sections exist by transporting limits from an essentially small model.
Source: Stacks 01FT (blueprint: lem-sfb-topos-cohomology-pullback-delta). -/
instance globalSectionsExist : HasGlobalSectionsFunctor J AddCommGrpCat.{w} :=
  letI : HasLimitsOfShape Cᵒᵖ AddCommGrpCat.{w} :=
    hasLimitsOfShape_of_essentiallySmall.{w} Cᵒᵖ AddCommGrpCat.{w}
  hasGlobalSectionsFunctor_of_hasLimitsOfShape J _

/-- Enough injectives on a site essentially small relative to the coefficient universe.
Source: Stacks 01FT and 079H (blueprint: lem-sfb-topos-cohomology-pullback-delta). -/
instance abelianSheavesGrothendieck :
    IsGrothendieckAbelian.{w} (Sheaf J AddCommGrpCat.{w}) :=
  letI (U : Cᵒᵖ) : HasLimitsOfShape
      (StructuredArrow U (equivSmallModel.{w} C).inverse.op) AddCommGrpCat.{w} :=
    HasLimitsOfShape.of_small.{w, w} AddCommGrpCat.{w} _
  Sheaf.isGrothendieckAbelian_of_essentiallySmall.{w, w, vC, w + 1, uC}
    J AddCommGrpCat.{w}

/-- A global abelian section as a map from the terminal set sheaf.
Source: Stacks, 01FT (blueprint: lem-sfb-topos-cohomology-pullback-delta). -/
def sectionGraph (M : Sheaf J AddCommGrpCat.{w})
    (x : (Sheaf.Γ J AddCommGrpCat.{w}).obj M) :
    Sheaf.terminal J Types.isTerminalPUnit ⟶
      (sheafCompose J (forget AddCommGrpCat.{w})).obj M where
  hom :=
    { app := fun U ↦ ↾fun _ ↦ M.ΓRes U x
      naturality := by
        intro U V a
        ext t
        exact (ConcreteCategory.congr_hom (M.ΓRes_map a) x).symm }

variable (f : GeometricMorphism
  (Sheaf K (Type (w))) (Sheaf J (Type (w))))

/-- The unique identification of the image of the terminal sheaf with the terminal sheaf.
Source: geometric-morphism finite limits, Stacks 00XA and 01FT
(blueprint: lem-sfb-topos-cohomology-pullback-delta). -/
def terminalIso :
    f.inverse.obj (Sheaf.terminal J Types.isTerminalPUnit) ≅
      Sheaf.terminal K Types.isTerminalPUnit :=
  letI := f.leftExact
  ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).isTerminalObj f.inverse).uniqueUpToIso
    (Sheaf.isTerminalTerminal K Types.isTerminalPUnit)

variable (A : AbelianInverseImagePresentation f.inverse)

/-- Additivity supplied by the induced exact inverse image.
Source: Stacks 00YV (blueprint: lem-sfb-topos-cohomology-pullback-delta). -/
instance inverseAdditive : A.functor.Additive :=
  letI : PreservesFiniteLimits A.functor :=
    ((GeometricMorphism.geometric_inverse_image_exact J K f).2.1 A).1
  Functor.additive_of_preserves_binary_products A.functor

/-- Left exactness supplied by the induced exact inverse image.
Source: Stacks 00YV (blueprint: lem-sfb-topos-cohomology-pullback-delta). -/
instance inverseLeftExact : PreservesFiniteLimits A.functor :=
  ((GeometricMorphism.geometric_inverse_image_exact J K f).2.1 A).1

/-- Right exactness supplied by the induced exact inverse image.
Source: Stacks 00YV (blueprint: lem-sfb-topos-cohomology-pullback-delta). -/
instance inverseRightExact : PreservesFiniteColimits A.functor :=
  ((GeometricMorphism.geometric_inverse_image_exact J K f).2.1 A).2

/-- The resolution formula, using the global-section transformation followed by a comparison.
Source: Stacks 01F8 and 01FT (blueprint: lem-sfb-topos-cohomology-pullback-delta). -/
def resolutionMap
    (t : Sheaf.Γ J AddCommGrpCat.{w} ⟶
      A.functor ⋙ Sheaf.Γ K AddCommGrpCat.{w})
    (F : Sheaf J AddCommGrpCat.{w}) (I : InjectiveResolution F)
    (R : InjectiveResolution (A.functor.obj F))
    (β : (A.functor.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ R.cocomplex)
    (q : ℕ) :
    ((Sheaf.Γ J AddCommGrpCat.{w}).rightDerived q).obj F ⟶
      ((Sheaf.Γ K AddCommGrpCat.{w}).rightDerived q).obj (A.functor.obj F) :=
  (I.isoRightDerivedObj (Sheaf.Γ J AddCommGrpCat.{w}) q).hom ≫
    HomologicalComplex.homologyMap
      ((t.mapHomologicalComplex (.up ℕ)).app I.cocomplex ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl
          (A.functor ⋙ Sheaf.Γ K AddCommGrpCat.{w})) (.up ℕ)).inv.app
            I.cocomplex ≫
        ((Sheaf.Γ K AddCommGrpCat.{w}).mapHomologicalComplex (.up ℕ)).map β) q ≫
    (R.isoRightDerivedObj (Sheaf.Γ K AddCommGrpCat.{w}) q).inv

/-- Pullback computed with arbitrary injective resolutions is natural, normalized on global
sections, independent of all comparison choices, and respects the derived boundary maps.
Source: Stacks, 01FT, 08J6, 01F8 and 015B
(blueprint: lem-sfb-topos-cohomology-pullback-delta).

`A` presents the induced abelian inverse image, rather than an unrelated exact functor.
`t` is specified on every global section by the terminal-sheaf graph equation. Under
adjunction this is exactly the unit followed by the global-section direct-image
identification. `P` consists of natural transformations in every nonnegative degree.
The formula quantifies over every pair of resolutions and every augmented comparison;
thus it asserts independence of both resolutions and of the comparison. The boundary
is the existing `ShortComplex.ShortExact.rightDerivedδ`, constructed from the image
under the derived functor of the single-object distinguished triangle.

Proof (the node's seven steps):
1. Write $\mathcal A=\operatorname{Ab}(\mathcal C)$, $\mathcal B=\operatorname{Ab}(\mathcal D)$
and $G=\Gamma_{\mathcal C}$, $T=\Gamma_{\mathcal D}$. Global sections are additive: their addition
is pointwise addition of maps into an abelian group object. They preserve kernels, since a map
from the terminal sheaf lands in a kernel exactly when its composite with the defining map is
zero. Thus $G,T$ are left exact additive. Adjunction and the finite-limit preservation in the
geometric-morphism datum give
$\operatorname{Hom}(*,f_*M)\cong\operatorname{Hom}(L*,M)\cong\operatorname{Hom}(*,M)$. Under this
bijection the unit defines a natural additive map $t_M:G(M)\to T(LM)$ sending $s$ to $Ls$ after
$*\cong L*$. This also defines a natural map of complexes $t_K:G(K)\to T(LK)$. No representing
terminal object of either site is used. Uses: def-trf-geometric-morphism.
2. Both $\mathcal A$ and $\mathcal B$ are abelian with enough injectives by [lem-weil-pbc-site-
sheaves-enough-injectives]; take nonnegative injective resolutions, whose augmentations and
degree-zero identifications are supplied by [lem-weil-pbc-left-exact-injective-resolution-degree-
zero]. Exactness of the given $L$ makes $LF[0]\to LI^\bullet$ a degreewise monomorphic quasi-
isomorphism. Apply [lem-weil-pbc-lift-along-injective-quasi-iso] with $K=LF[0]$,
$L^\bullet=LI^\bullet$, target $J^\bullet$, and $\gamma$ the target augmentation. It gives
$\beta:LI^\bullet\to J^\bullet$ strictly over $LF$. Therefore the chain map
$w_{I,J}=T(\beta)t_I:G(I^\bullet)\to T(J^\bullet)$ gives the claimed map on cohomology under the
resolution identifications. Uses: lem-weil-pbc-site-sheaves-enough-injectives, lem-weil-pbc-left-
exact-injective-resolution-degree-zero, lem-weil-pbc-lift-along-injective-quasi-iso.
3. Any two choices of $\beta$ agree after the quasi-isomorphism $LF[0]\to LI$ and hence are
homotopic by [lem-weil-pbc-lift-to-injective-unique-up-to-homotopy]; applying $T$ and then
cohomology gives equal maps by [lem-weil-pbc-homotopic-maps-equal-cohomology]. More generally, for
$h:F\to F'$ and resolutions $(I,J)$, $(I',J')$, choose augmented lifts $u:I\to I'$ of $h$ and
$v:J\to J'$ of $Lh$ by [lem-weil-pbc-injective-resolution-lift-exists]. The maps $v\beta$ and
$\beta'Lu$ from $LI$ to $J'$ have the same composite with $LF[0]\to LI$; the same uniqueness lemma
makes them homotopic. Naturality of $t$ gives $t_{I'}G(u)=T(Lu)t_I$, so on cohomology
$H^q(Tv)H^q(w_{I,J})=H^q(w_{I',J'})H^q(Gu)$. The map-via-lift formula of [lem-weil-pbc-derived-
functor-map-via-lift] identifies the two outer maps with $H^q(Lh)$ and $H^q(h)$. This proves
naturality. For $h=1_F$ it proves independence of both resolutions, since the same formula
identifies the resolution changes with the canonical identity maps on $R^qG(F)$ and $R^qT(LF)$.
Uses: lem-weil-pbc-lift-to-injective-unique-up-to-homotopy, lem-weil-pbc-homotopic-maps-equal-
cohomology, lem-weil-pbc-injective-resolution-lift-exists, lem-weil-pbc-derived-functor-map-via-
lift.
4. By [lem-weil-pbc-left-exact-injective-resolution-degree-zero], $G(F)\to H^0(GI)$ and $T(LF)\to
H^0(TJ)$ are the canonical isomorphisms induced by the augmentations. The augmented square for
$w_{I,J}$ commutes, because $\beta$ is over $LF$ and $t$ is natural. Consequently its degree-zero
map is $t_F$, which step 1 computed as $s\mapsto Ls$ with domain identified using $*\cong L*$.
Uses: lem-weil-pbc-left-exact-injective-resolution-degree-zero.
5. Fix a short exact sequence $E$ and choose a horseshoe $I_1\to I_2\to I_3$ by [lem-weil-pbc-
injective-resolution-ses]. Every row splits by [lem-weil-pbc-ses-injective-kernel-splits]. Its
images under $G$ and under $TL$ therefore split: applying an additive functor to $pi=1$, $rs=1$,
$ip+sr=1$ gives the same splitting equations. In particular both image sequences are degreewise
short exact; extension by zero remains so. We identify precisely which boundary $\partial_I$ on
$H^q(GI_3)$ this computes. In the derived category of [def-weil-abstract-derived-category], [lem-
sc-p1-horseshoe-derived-triangle-comparison] gives a triangle morphism from $RG(E[0])$ to the
derived triangle of $G(I)$, with endpoint homology maps $j_{I_i}\theta_{F_i}$. By boundary
naturality in [lem-sp-long-exact-of-triangle] and the snake/derived identification of [lem-
sc-p1-nat-complex-derived-boundary], its endpoint equation is
$j_{I_1}^{q+1}\delta_E^q=\partial_I^q j_{I_3}^q$, after the single-object identifications
$\theta$. Thus this is the derived global-section connecting map specified in the item. The
identical application to $T$ identifies $\delta_{LE}$ with the boundary of any target horseshoe
$J_1\to J_2\to J_3$. All these applications have enough injectives by step 2, left exactness by
step 1, and the required image exactness by the splitting equations just given. Uses: lem-weil-
pbc-injective-resolution-ses, lem-weil-pbc-ses-injective-kernel-splits, def-weil-abstract-derived-
category, lem-sc-p1-horseshoe-derived-triangle-comparison, lem-sp-long-exact-of-triangle, lem-
sc-p1-nat-complex-derived-boundary.
6. Choose a target horseshoe $J$ resolving $LE$ as in step 5. The source row $LI_1\to LI_2\to
LI_3$ has exact augmented columns, since $L$ is exact, and short exact rows, since its original
rows split. The lifting argument of step 2 gives endpoint maps $\beta_1:LI_1\to J_1$,
$\beta_3:LI_3\to J_3$ over the identity maps of $LF_1,LF_3$. Apply [lem-weil-pbc-horseshoe-
morphism-lift-exact-source] to this augmented source row and the target horseshoe, with morphism
$1_{LE}$. It supplies $\beta_2$ making both row squares commute strictly and preserving the middle
augmentation. Here no $LI_i^n$ is required to be injective. The maps $w_i=T(\beta_i)t_{I_i}$
consequently give a morphism of short exact complexes $G(I_1\to I_2\to I_3)\to T(J_1\to J_2\to
J_3)$. Its rows are short exact by step 5. By [lem-weil-pbc-complex-ses-long-exact-naturality],
$H^{q+1}(w_1)\partial_I^q=\partial_J^q H^q(w_3)$. Step 3 identifies its endpoint maps with the
specified $P_f$, independently of these convenient choices, and step 5 identifies its boundaries
with the derived $\delta_E,\delta_{LE}$. Substitution proves
$P_f^{q+1}(F_1)\delta_E^q=\delta_{LE}^qP_f^q(F_3)$. Uses: lem-weil-pbc-horseshoe-morphism-lift-
exact-source, lem-weil-pbc-complex-ses-long-exact-naturality.
7. For a morphism $(a,b,c):E\to E'$ on either site, apply [lem-weil-pbc-horseshoe-delta-functor]
to that site's global-section functor. Its hypotheses hold by steps 1 and 2, and clause (1) gives
$H^{q+1}(a)\delta_H^q=\delta_{H'}^qH^q(c)$ for horseshoe boundaries. Step 5 identifies both of
these with the specified derived boundaries. This gives the last assertion on either site. The
whole argument used only the geometric adjunction, the terminal sheaf and exactness of its abelian
inverse image, so it applies without a functor between the presenting sites or a final object of
either site. Uses: lem-weil-pbc-horseshoe-delta-functor.
-/
theorem pullback_delta
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
    (A : AbelianInverseImagePresentation f.inverse)
    [HasDerivedCategory.{dC} (Sheaf J AddCommGrpCat.{w})]
    [HasDerivedCategory.{dD} (Sheaf K AddCommGrpCat.{w})]
    [HasDerivedCategory.{dA} AddCommGrpCat.{w}] :
    ∃ (t : Sheaf.Γ J AddCommGrpCat.{w} ⟶
        A.functor ⋙ Sheaf.Γ K AddCommGrpCat.{w})
      (P : ∀ q : ℕ, (Sheaf.Γ J AddCommGrpCat.{w}).rightDerived q ⟶
        A.functor ⋙ (Sheaf.Γ K AddCommGrpCat.{w}).rightDerived q),
      (∀ (F : Sheaf J AddCommGrpCat.{w})
        (x : (Sheaf.Γ J AddCommGrpCat.{w}).obj F),
        sectionGraph K (A.functor.obj F) (t.app F x) =
          (terminalIso J K f).inv ≫ f.inverse.map (sectionGraph J F x) ≫
            A.underlying.inv.app F) ∧
      (∀ (F : Sheaf J AddCommGrpCat.{w}) (I : InjectiveResolution F)
        (R : InjectiveResolution (A.functor.obj F)),
        ∃ β : (A.functor.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ R.cocomplex,
          A.functor.map (I.ι.f 0) ≫ β.f 0 = R.ι.f 0) ∧
      (∀ (F : Sheaf J AddCommGrpCat.{w}) (I : InjectiveResolution F)
        (R : InjectiveResolution (A.functor.obj F))
        (β : (A.functor.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ R.cocomplex),
        A.functor.map (I.ι.f 0) ≫ β.f 0 = R.ι.f 0 → ∀ q : ℕ,
          (P q).app F = resolutionMap J K f A t F I R β q) ∧
      (∀ F : Sheaf J AddCommGrpCat.{w},
        (P 0).app F ≫
            (Sheaf.Γ K AddCommGrpCat.{w}).rightDerivedZeroIsoSelf.hom.app
              (A.functor.obj F) =
          (Sheaf.Γ J AddCommGrpCat.{w}).rightDerivedZeroIsoSelf.hom.app F ≫
            t.app F) ∧
      (∀ (S : ShortComplex (Sheaf J AddCommGrpCat.{w})) (hS : S.ShortExact),
        ∃ hLS : (S.map A.functor).ShortExact, ∀ q : ℕ,
          hS.rightDerivedδ (Sheaf.Γ J AddCommGrpCat.{w}) q ≫
              (P (q + 1)).app S.X₁ =
            (P q).app S.X₃ ≫ hLS.rightDerivedδ (Sheaf.Γ K AddCommGrpCat.{w}) q) ∧
      (∀ (S T : ShortComplex (Sheaf J AddCommGrpCat.{w}))
        (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (q : ℕ),
        hS.rightDerivedδ (Sheaf.Γ J AddCommGrpCat.{w}) q ≫
            ((Sheaf.Γ J AddCommGrpCat.{w}).rightDerived (q + 1)).map φ.τ₁ =
          ((Sheaf.Γ J AddCommGrpCat.{w}).rightDerived q).map φ.τ₃ ≫
            hT.rightDerivedδ (Sheaf.Γ J AddCommGrpCat.{w}) q) ∧
      (∀ (S T : ShortComplex (Sheaf K AddCommGrpCat.{w}))
        (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (q : ℕ),
        hS.rightDerivedδ (Sheaf.Γ K AddCommGrpCat.{w}) q ≫
            ((Sheaf.Γ K AddCommGrpCat.{w}).rightDerived (q + 1)).map φ.τ₁ =
          ((Sheaf.Γ K AddCommGrpCat.{w}).rightDerived q).map φ.τ₃ ≫
            hT.rightDerivedδ (Sheaf.Γ K AddCommGrpCat.{w}) q) := by
  sorry

end CategoryTheory.ToposCohomologyPullback
