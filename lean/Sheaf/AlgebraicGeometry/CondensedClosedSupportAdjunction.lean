/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedSupport
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions

import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.CategoryTheory.SitePullbackAbelianExact

/-!
# Closed support for arbitrary condensed coefficients

Source: blueprint `sec-smooth-purity/sk-prop-sf-localization`,
`sk-lem-formal-closed-support-adjunction.md` and its proof
(blueprint: det-lem-formal-closed-support-adjunction).

Inverse image uses the canonical coefficient isomorphism and restriction of scalars along
its inverse. This works for noncommutative rings as well. The finite constant-coefficient
kernel construction is generalized to these coefficients, with the same module operations.
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped CategoryTheory.Obj

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]

/-- The existing category of left module objects over the pulled-back ring.
Source: blueprint opening paragraph (blueprint: det-lem-formal-closed-support-adjunction).
This is the ring-object presentation of module sheaves, with sectionwise linear maps. -/
abbrev supportModules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

/-- Grothendieck structure for arbitrary left modules, without commutativity.
Source: blueprint proof Step 6 (blueprint: det-lem-formal-closed-support-adjunction). -/
noncomputable instance supportModules_grothendieck (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (supportModules Λ X) :=
  Mod.isGrothendieckAbelian.{u + 1, u + 1, u + 2} (condensedRingObj Λ X)

/-- Canonical inverse image, transporting the action through the inverse of alpha.
Source: blueprint proof Steps 1--2 (blueprint: det-lem-formal-closed-support-adjunction). -/
noncomputable def supportPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    supportModules Λ Y ⥤ supportModules Λ X :=
  (ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y) ⋙
    Mod.comap (asIso (condensedPullbackHom Λ f)).inv

/-- Exactness and additivity are inherited from inverse image and scalar transport.
Source: blueprint proof Step 2 (blueprint: det-lem-formal-closed-support-adjunction). -/
noncomputable instance supportPullback_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (supportPullback Λ f).Additive := inferInstanceAs
      (((ProEtale.upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y) ⋙
        Mod.comap (asIso (condensedPullbackHom Λ f)).inv).Additive)

/-- Inverse image preserves finite limits.
Source: blueprint proof Step 2 (blueprint: det-lem-formal-closed-support-adjunction). -/
noncomputable instance supportPullback_leftExact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (supportPullback Λ f) := by
  unfold supportPullback
  infer_instance

/-- Inverse image preserves finite colimits.
Source: blueprint proof Step 2 (blueprint: det-lem-formal-closed-support-adjunction). -/
noncomputable instance supportPullback_rightExact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (supportPullback Λ f) := by
  unfold supportPullback
  infer_instance

/-- Scalar transport equivalence along alpha. Both functors restrict scalars.
Source: blueprint proof Step 1 (blueprint: det-lem-formal-closed-support-adjunction). -/
noncomputable def supportCoefficientEquivalence {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((ProEtale.upperStar Ab.{u + 1} f).obj (condensedRingObj Λ Y)) ≌
        supportModules Λ X :=
  CategoryTheory.Equivalence.mk (Mod.comap (asIso (condensedPullbackHom Λ f)).inv)
    (Mod.comap (condensedPullbackHom Λ f))
    ((Mod.comapId _).symm ≪≫ Mod.comapCongr (by simp) ≪≫
      Mod.comapComp (condensedPullbackHom Λ f) (asIso (condensedPullbackHom Λ f)).inv)
    ((Mod.comapComp (asIso (condensedPullbackHom Λ f)).inv
      (condensedPullbackHom Λ f)).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapId _)

/-- Canonical module inverse/direct-image adjunction, including its specified unit.
Source: blueprint proof Step 2 (blueprint: det-lem-formal-closed-support-adjunction). -/
noncomputable def supportPullbackAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    supportPullback Λ f ⊣ lowerStar Λ f :=
  (((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).mapModAdjunction
    (condensedRingObj Λ Y)).comp (supportCoefficientEquivalence Λ f).toAdjunction).ofNatIsoRight
      ((Functor.associator _ _ _).symm ≪≫ comapPullbackHomCompIso Λ f)

/-- The kernel of the canonical open unit, functorially in the module.
Source: blueprint formula for Gamma (blueprint: det-lem-formal-closed-support-adjunction). -/
noncomputable def supportKernel {U X : Scheme.{u}} (j : U ⟶ X) :
    supportModules Λ X ⥤ supportModules Λ X where
  obj M := kernel ((supportPullbackAdjunction Λ j).unit.app M)
  map f := kernel.map _ _ f ((lowerStar Λ j).map ((supportPullback Λ j).map f))
    ((supportPullbackAdjunction Λ j).unit.naturality f).symm
  map_id M := equalizer.hom_ext (by simp)
  map_comp f g := equalizer.hom_ext (by simp)

/-- Kernel inclusion, natural in the module.
Source: blueprint proof Step 5 (blueprint: det-lem-formal-closed-support-adjunction). -/
noncomputable def supportKernelι {U X : Scheme.{u}} (j : U ⟶ X) :
    supportKernel Λ j ⟶ 𝟭 _ where
  app M := kernel.ι _
  naturality M N f := by simp [supportKernel]

/-- The support functor is precisely i* ker(id -> j* j*).
Source: blueprint statement formula (blueprint: det-lem-formal-closed-support-adjunction). -/
noncomputable def closedSupport {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) :
    supportModules Λ X ⥤ supportModules Λ Z :=
  supportKernel Λ j ⋙ supportPullback Λ i

/-- Additivity of the kernel formula.
Source: blueprint proof Step 5 (blueprint: det-lem-formal-closed-support-adjunction).
The induced map on kernels is the restriction of the given module map; restriction commutes
with zero and addition. Inverse image is additive, so the composite is additive. -/
@[instance] theorem closedSupport_additive {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X) :
    (closedSupport Λ i j).Additive := by
  sorry


/-- The comparison from the kernel to i* i^* of that kernel, given by the unit.
Source: blueprint proof Step 5 (blueprint: det-lem-formal-closed-support-adjunction). -/
noncomputable def closedSupportKernelComparison {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) :
    supportKernel Λ j ⟶ closedSupport Λ i j ⋙ lowerStar Λ i :=
  Functor.whiskerLeft (supportKernel Λ j) (supportPullbackAdjunction Λ i).unit ≫
    (Functor.associator _ _ _).inv

/-- Clause (1): the kernel comparison is a natural isomorphism.
Source: blueprint proof Steps 3--5 (blueprint: det-lem-formal-closed-support-adjunction).
Restriction of the open unit is invertible, hence the kernel restricts to zero on U.
The open--closed exact sequence applied to the kernel then identifies it, by its closed
unit, with i* i^* of itself. The coefficient actions lift these abelian-sheaf identities. -/
theorem closedSupportKernelComparison_isIso {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    IsIso (closedSupportKernelComparison Λ i j) := by
  sorry

/-- The support inclusion, obtained from the inverse kernel comparison.
Source: blueprint proof Step 5 (blueprint: det-lem-formal-closed-support-adjunction). -/
noncomputable def closedSupportCounit {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    closedSupport Λ i j ⋙ lowerStar Λ i ⟶ 𝟭 _ :=
  letI := closedSupportKernelComparison_isIso Λ i j hij
  (asIso (closedSupportKernelComparison Λ i j)).inv ≫ supportKernelι Λ j

/-- Clause (1): the adjunction with its canonical support inclusion as counit.
Source: blueprint proof Step 5 (blueprint: det-lem-formal-closed-support-adjunction).
A map from i*A to M has zero composite to j*j^*M, by the open adjunction and j^*i*=0.
It factors uniquely through the kernel. Full faithfulness of i* gives a unique A -> H M.
The construction is natural in both variables and its counit is the displayed inclusion.
A fixed counit determines an adjunction, giving the asserted uniqueness. -/
theorem existsUnique_closedSupportAdjunction {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    ∃! adj : lowerStar Λ i ⊣ closedSupport Λ i j,
      adj.counit = closedSupportCounit Λ i j hij := by
  sorry

/-- The uniquely counit-normalized support adjunction.
Source: blueprint clause (1) (blueprint: det-lem-formal-closed-support-adjunction). -/
noncomputable def closedSupportAdjunction {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    lowerStar Λ i ⊣ closedSupport Λ i j :=
  Classical.choose (ExistsUnique.exists (existsUnique_closedSupportAdjunction Λ i j hij))

/-- Clause (1): left exactness of the additive support functor.
Source: blueprint proof Step 5 (blueprint: det-lem-formal-closed-support-adjunction).
The natural Hom bijection turns the universal property of any finite limit into the same
universal property after applying H. Thus the right adjoint preserves finite limits. -/
theorem closedSupport_leftExact {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    PreservesFiniteLimits (closedSupport Λ i j) := by
  sorry

/-- Closed direct image is exact, also for noncommutative coefficient rings.
Source: blueprint proof Step 3 (blueprint: det-lem-formal-closed-support-adjunction).
The abelian-sheaf closed direct image is exact. The action through the coefficient unit
lifts it to left modules; the forgetful functor detects kernels and sheafified cokernels. -/
@[instance] theorem closedSupport_lowerStarExact {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] : PreservesFiniteColimits (lowerStar Λ i) := by
  sorry

/-- Clause (2): the total right derived support functor is right adjoint to exact i*.
Source: blueprint proof Steps 6--7 (blueprint: det-lem-formal-closed-support-adjunction).
The uniquely normalized sheaf adjunction has exact left adjoint. Its right adjoint sends
K-injectives to K-injectives. The termwise Hom adjunction descends to homotopy categories,
and the Hom bijection into K-injectives identifies it with the derived adjunction. -/
noncomputable def closedSupportDerivedAdjunction {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    (lowerStar Λ i).mapDerivedCategory ⊣ (closedSupport Λ i j).rightDerivedFunctor :=
  (closedSupportAdjunction Λ i j hij).mapDerivedCategoryRightDerivedAdjunction

/-- The open derived adjunction, with its canonical derived unit.
Source: blueprint proof Steps 6 and 10 (blueprint: det-lem-formal-closed-support-adjunction). -/
noncomputable def closedSupportOpenDerivedAdjunction {U X : Scheme.{u}} (j : U ⟶ X) :
    (supportPullback Λ j).mapDerivedCategory ⊣ (lowerStar Λ j).rightDerivedFunctor :=
  (supportPullbackAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction

/-- The open pullback of a K-injective is K-injective.
Source: blueprint proof Steps 3 and 10 (blueprint: det-lem-formal-closed-support-adjunction).
Extension by zero is an exact left adjoint to open restriction, so its right adjoint
preserves K-injectives. This applies to modules with the transported coefficient action. -/
theorem closedSupport_open_isKInjective {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (I : CochainComplex (supportModules Λ X) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((supportPullback Λ j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  sorry

/-- Clause (2), global RHom form, specified componentwise on K-injective representatives.
Source: blueprint proof Step 8 (blueprint: det-lem-formal-closed-support-adjunction).
In degree n apply the sheaf Hom adjunction to every component A^p -> H(I)^(p+n).
Naturality in both differentials intertwines d(f)=d_I f-(-1)^n f d_A. These components
therefore give a Hom-complex isomorphism. H(I) is K-injective by the exact-left-adjoint
criterion; hence both sides compute global RHom. Quasi-isomorphisms in A induce
quasi-isomorphisms here, and changes of injective resolution are homotopy equivalences.
The component formula determines the isomorphism and makes it natural in both variables. -/
theorem closedSupport_globalRHom {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (A : CochainComplex (supportModules Λ Z) ℤ)
    (I : CochainComplex (supportModules Λ X) ℤ) [I.IsKInjective] :
    ∃ e : CochainComplex.HomComplex
        (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I ≅
      CochainComplex.HomComplex A
        (((closedSupport Λ i j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I),
      ∀ (n : ℤ) (a : CochainComplex.HomComplex.Cochain
        (((lowerStar Λ i).mapHomologicalComplex (ComplexShape.up ℤ)).obj A) I n)
        (p q : ℤ) (hpq : p + n = q),
        (e.hom.f n a) ⟨p, q, hpq⟩ =
          (closedSupportAdjunction Λ i j hij).homEquiv (A.X p) (I.X q) (a ⟨p, q, hpq⟩) := by
  sorry

/-- Clause (3): the open unit is an epimorphism for every injective module.
Source: blueprint proof Step 9 (blueprint: det-lem-formal-closed-support-adjunction).
The comparison j!j^*I -> j*j^*I is monic: its kernel has zero open and closed
restrictions, hence is zero by localization. Extend its map to I using injectivity.
After restriction the resulting section is the identity. Faithfulness on open direct
images implies that it splits the unit, which is therefore an epimorphism of sheaves. -/
theorem closedSupport_injective_unit_epi {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (I : supportModules Λ X) [Injective I] :
    Epi ((supportPullbackAdjunction Λ j).unit.app I) := by
  sorry

/-- Clause (4): the counit/unit localization triangle, natural on the unbounded category.
Source: blueprint proof Steps 10--11 (blueprint: det-lem-formal-closed-support-adjunction).
Resolve K by a K-injective I with injective terms. Open restriction preserves
K-injectives, so j*j^*I computes Rj*j^*K. The kernel identification and surjectivity in
Step 9 give a degreewise short exact sequence i*H(I) -> I -> j*j^*I. Its canonical
connecting morphism gives the distinguished triangle. The short-exact-sequence triangle
is natural; maps between K-injective resolutions represent all derived maps, and
homotopies descend, giving a natural transformation as the connecting arrow. -/
theorem closedSupport_triangle {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    ∃ δ : (supportPullback Λ j).mapDerivedCategory ⋙ (lowerStar Λ j).rightDerivedFunctor ⟶
      ((closedSupport Λ i j).rightDerivedFunctor ⋙ (lowerStar Λ i).mapDerivedCategory) ⋙
        shiftFunctor (DerivedCategory (supportModules Λ X)) (1 : ℤ),
      ∀ K : DerivedCategory (supportModules Λ X),
        Triangle.mk ((closedSupportDerivedAdjunction Λ i j hij).counit.app K)
          ((closedSupportOpenDerivedAdjunction Λ j).unit.app K) (δ.app K) ∈
            Pretriangulated.distinguishedTriangles := by
  sorry

/-- Clause (4), explicit fibre comparison on K-injective representatives.
Source: blueprint proof Step 11 (blueprint: det-lem-formal-closed-support-adjunction).
First replace I by a homotopy equivalent K-injective J with injective terms. Additive
functors and the cone construction preserve this equivalence. For g:J -> j*j^*J the
canonical map i*H(J) -> cone(g)[-1] is n |-> (0,n).
Locally lift the first component of a fibre cocycle along the degreewise epimorphism g
and subtract d(0,-c); this proves surjectivity on cohomology. For a boundary (0,k)=d(a,b),
lift a to c and write k=d(b+dc) in the kernel; this proves injectivity. The map is thus a
quasi-isomorphism. Exact i^* and i^*i*=id identify RH(QI) with i^* of that fibre.
The fibre used here is the actual shifted mapping cone of the canonical unit. -/
theorem closedSupport_fiber {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (K : DerivedCategory (supportModules Λ X))
    (I : CochainComplex (supportModules Λ X) ℤ) [I.IsKInjective]
    (e : K ≅ DerivedCategory.Q.obj I) :
    Nonempty ((closedSupport Λ i j).rightDerivedFunctor.obj K ≅
      (supportPullback Λ i).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          ((CochainComplex.mappingCone
            ((NatTrans.mapHomologicalComplex (supportPullbackAdjunction Λ j).unit
              (ComplexShape.up ℤ)).app I))⟦(-1 : ℤ)⟧))) := by
  sorry

/-- The recorded arbitrary-resolution derived functor agrees with the upstream total
right derived functor, including its unit; no monomorphic-resolution hypothesis is added.
Source: blueprint proof Step 6 (blueprint: det-lem-formal-closed-support-adjunction).
Both pairs have the same universal property. Apply the two natural-transformation
bijections to their units; the comparison maps are inverse by uniqueness. This is the
unique unit-compatible comparison, and so also identifies computation on K-injectives. -/
theorem closedSupport_recordedDerived {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X)
    (h : ∀ K : CochainComplex (supportModules Λ X) ℤ,
      ∃ (I : CochainComplex (supportModules Λ X) ℤ) (s : K ⟶ I),
        I.IsKInjective ∧ QuasiIso s) :
    ∃! e : (closedSupport Λ i j).rightDerivedFunctorOfQuasiIsoResolutions h ≅
      (closedSupport Λ i j).rightDerivedFunctor,
      (closedSupport Λ i j).rightDerivedFunctorOfQuasiIsoResolutionsUnit h ≫
        Functor.whiskerLeft DerivedCategory.Qh e.hom =
          (closedSupport Λ i j).rightDerivedFunctorUnit := by
  sorry

/-- The total derived support functor is computed termwise on every K-injective complex.
Source: blueprint clause (2), proof Steps 6--7
(blueprint: det-lem-formal-closed-support-adjunction).
The total right-derived unit is invertible on K-injectives. Invert its component and
transport between Q and the homotopy localization, giving precisely this comparison. -/
noncomputable def closedSupportComputedOnKInjective {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X)
    (I : CochainComplex (supportModules Λ X) ℤ) [I.IsKInjective] :
    (closedSupport Λ i j).rightDerivedFunctor.obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj
        (((closedSupport Λ i j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  (closedSupport Λ i j).rightDerivedFunctorObjQIso I

end AlgebraicGeometry.ProEtale.CondensedRing
