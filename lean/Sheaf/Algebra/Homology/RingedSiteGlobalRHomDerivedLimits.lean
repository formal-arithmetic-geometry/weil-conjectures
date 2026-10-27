module

public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Functor
import Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction
import Sheaf.Algebra.Homology.RingedDerivedTensorNative
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import Sheaf.CategoryTheory.InjectiveTowerRoosShifts
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import Sheaf.CategoryTheory.StrictRoosComparison
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-! # Global derived Hom and strict derived inverse limits

Source: Stacks Project, sites-cohomology.tex, Tag 0B6E (section-global-RHom),
and spaces-perfect.tex, Tag 0D3F (lemma-pullback-and-limits), second proof paragraph.
(blueprint: lem-sfb-ringed-site-global-rhom-derived-limits).

The comparison is stated on the category of resolved strict towers: K-injective
complexes of towers whose terms are injective towers. Every strict tower admits
such a resolution. Its ordinary limit represents its resolution-derived limit.
The target uses ordinary limits of the resulting global Hom complexes; the Roos
triangle clause identifies these, with their actual projections, as derived limits.
Thus the natural isomorphism specifies the resolution-derived limiting cone.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v r a w z

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RingedSiteGlobalRHom

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}


/-- The recorded category of module sheaves, without any quasi-coherence restriction.
Source: Stacks 0B6E (blueprint: lem-sfb-ringed-site-global-rhom-derived-limits). -/
abbrev Modules [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r, r, v, c} ((sheafCompose J
    (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- The existing ring of compatible global ring sections.
Source: Stacks 0B6E (blueprint: lem-sfb-ringed-site-global-rhom-derived-limits). -/
abbrev Scalars (R : Sheaf J CommRingCat.{r}) :=
  RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat.{r} RingCat.{r})

/-- The existing canonical global-section action on sheaf morphisms.
Source: Stacks 04TT (blueprint: lem-sfb-ringed-site-global-rhom-derived-limits). -/
instance modulesLinear [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (R : Sheaf J CommRingCat.{r}) : Linear (Scalars.{c, v, r} R) (Modules.{c, v, r} R) :=
  SheafOfModules.homLinear.{r, v, c, r} R.obj
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).property

/-- Module-valued global sections with the specified coefficient action. The Hom
module is the existing pointwise section action, restricted along the given ring map.
Source: Stacks 0B6E (blueprint: lem-sfb-ringed-site-global-rhom-derived-limits). -/
abbrev sections [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    (R : Sheaf J CommRingCat.{r}) (A : Type a) [CommRing A] (φ : A →+* Scalars.{c, v, r} R) :
    Modules.{c, v, r} R ⥤ ModuleCat.{max c r} A :=
  letI := modulesLinear.{c, v, r} R
  (linearCoyoneda (Scalars.{c, v, r} R) (Modules.{c, v, r} R)).obj
      (op (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) ⋙
    ModuleCat.restrictScalars.{max c r} φ

variable (R : Sheaf J CommRingCat.{max c v r})

variable [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

variable [HasDerivedCategory.{w} (Modules.{c, v, max c v r} R)]
  (A : Type a) [CommRing A] (φ : A →+* Scalars.{c, v, max c v r} R)
  [HasDerivedCategory.{z} (ModuleCat.{max c v r} A)]

/-- Full unbounded global RHom, with values in D(A), using the recorded internal Hom
and the right derived module-valued global sections functor.
Source: Stacks 0B6E (blueprint: lem-sfb-ringed-site-global-rhom-derived-limits). -/
def globalHom (E : DerivedCategory (Modules.{c, v, max c v r} R)) :
    DerivedCategory (Modules.{c, v, max c v r} R) ⥤ DerivedCategory (ModuleCat.{max c v r} A) :=
  letI : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, max c v r} R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  (Functor.curry.obj (derivedInternalHomOfUniverses.{c, v, r, w} J R)).obj (op E) ⋙
    (sections.{c, v, max c v r} R A φ).rightDerivedFunctor

/-- The representative complex Γ(Hom(L,-)), retaining the specified A-action.
Source: Stacks 0B6E, 08JA
(blueprint: lem-sfb-ringed-site-global-rhom-derived-limits). -/
def representative (L : CochainComplex (Modules.{c, v, max c v r} R) ℤ) :
    CochainComplex (Modules.{c, v, max c v r} R) ℤ ⥤ CochainComplex (ModuleCat.{max c v r} A) ℤ :=
  (homComplexFunctor (R := R)).obj (op L) ⋙
    (sections.{c, v, max c v r} R A φ).mapHomologicalComplex (.up ℤ)

/-- Resolved strict towers, in the existing category of complexes of inverse systems.
The index n in Lean is the positive index n+1 in the statement.
Source: Stacks 0941 (blueprint: lem-sfb-ringed-site-global-rhom-derived-limits). -/
def resolvedProperty : ObjectProperty (CochainComplex (ℕᵒᵖ ⥤ Modules.{c, v, max c v r} R) ℤ) :=
  fun I ↦ I.IsKInjective ∧ ∀ p : ℤ, Injective (I.X p)

/-- The source comparison functor on resolved strict towers. Its limit is the
ordinary inverse limit of a tower resolution, hence the resolution-derived limit.
Source: Stacks 0941 (blueprint: lem-sfb-ringed-site-global-rhom-derived-limits). -/
def limitGlobalHom (E : DerivedCategory (Modules.{c, v, max c v r} R)) :
    (resolvedProperty.{c, v, r} R).FullSubcategory ⥤ DerivedCategory (ModuleCat.{max c v r} A) :=
  (resolvedProperty.{c, v, r} R).ι ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
    (lim : (ℕᵒᵖ ⥤ CochainComplex (Modules.{c, v, max c v r} R) ℤ) ⥤
      CochainComplex (Modules.{c, v, max c v r} R) ℤ) ⋙
    DerivedCategory.Q ⋙ globalHom.{c, v, r, a, w, z} R A φ E

/-- The strict tower of global Hom complexes, including its transition maps.
Source: Stacks 0941, 0B6E
(blueprint: lem-sfb-ringed-site-global-rhom-derived-limits). -/
def representativeTowers (L : CochainComplex (Modules.{c, v, max c v r} R) ℤ) :
    (resolvedProperty.{c, v, r} R).FullSubcategory ⥤
      (ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{max c v r} A) ℤ) :=
  (resolvedProperty.{c, v, r} R).ι ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
    (Functor.whiskeringRight _ _ _).obj (representative.{c, v, r, a} R A φ L)

/-- The limiting complex of the resolved global Hom tower. The theorem below equips
its localization with the normalized Roos triangle, so it computes Rlim in D(A).
Source: Stacks 0941 (blueprint: lem-sfb-ringed-site-global-rhom-derived-limits). -/
def globalHomLimit (L : CochainComplex (Modules.{c, v, max c v r} R) ℤ) :
    (resolvedProperty.{c, v, r} R).FullSubcategory ⥤ DerivedCategory (ModuleCat.{max c v r} A) :=
  representativeTowers.{c, v, r, a} R A φ L ⋙ lim ⋙ DerivedCategory.Q

/-- Global RHom preserves resolution-derived inverse limits, with the actual limiting
cone, naturally for maps of strict towers; its cohomology computes all derived Homs.

Source: Stacks 0B6E and 0D3F; resolution and Roos normalization in Tag 0941
(blueprint: lem-sfb-ringed-site-global-rhom-derived-limits).

Proof:
1. Choose a K-flat representative of E (lem-pc-kflat-resolution). The tensor-Hom
adjunction and native symmetry (lem-sf-ringed-derived-tensor-hom-adjunction and
lem-sf-ringed-derived-native-tensor) identify internal RHom with Hom into a
K-injective representative. The sections model
(lem-sfb-derived-internal-hom-sections-model), using def-pur-hom-complex and
lem-pur-hom-kflat-into-kinjective, identifies global RHom with representative L.
All constructions are A-linear by postmultiplication through φ; the same comparison
works for any representative L by quasi-isomorphism invariance.
2. Resolve a strict tower by a K-injective complex of injective towers
(lem-pur-injective-tower-roos-shifts and
lem-weil-pbc-ringed-strict-tower-homotopy-limit). Evaluations are K-injective,
transitions split in every degree, and the ordinary limit represents Rlim.
The constant-tower functor is exact (lem-weil-tower-category-levelwise-abelian),
so its right adjoint lim preserves K-injectives
(lem-weil-pbc-right-adjoint-preserves-kinjective).
3. In degree q the representative has product terms Hom(L^p,I^(p+q)).
The universal property of inverse limits and interchange of products identify
representative(lim I) with lim representative(I), with the same differential and
projections. This yields the natural isomorphism α and its projection formula.
4. The resolved transitions split, so transitions of these Hom groups are surjective.
The endomorphism 1-s on their product is surjective: recursively lift x_n-b_n to
choose x_(n+1). Its kernel is the ordinary limit. Apply
lem-weil-degreewise-epi-kernel-cocone-qis and lem-weil-strict-roos-comparison.
Products in A-modules are exact, and the normalized kernel-to-cone inclusion has
zero shifted component. It identifies this limit with the resolution-derived Rlim
and supplies exactly the Roos triangle and projection equations stated here.
5. Postcomposition commutes with every projection. Thus the construction is natural
on resolved towers. Maps and homotopies between resolutions induce the same derived
map by lem-weil-pbc-kinjective-hom-derived, so the projection-normalized comparison
is independent of the resolution and natural on original strict towers.
6. The sections-model cohomology formula gives the additive equivalences in every
integer degree. Its naturality and the postmultiplication action give the displayed
naturality and scalar equations. No boundedness or quasi-coherence is used. -/
theorem preserves_derived_limits
    (E : DerivedCategory (Modules.{c, v, max c v r} R))
    (L : CochainComplex (Modules.{c, v, max c v r} R) ℤ)
    (eL : DerivedCategory.Q.obj L ≅ E) :
    (∀ X : CochainComplex (ℕᵒᵖ ⥤ Modules.{c, v, max c v r} R) ℤ,
      ∃ (I : (resolvedProperty.{c, v, r} R).FullSubcategory) (q : X ⟶ I.obj), QuasiIso q) ∧
    ∃ (β : ∀ (I : CochainComplex (Modules.{c, v, max c v r} R) ℤ) (_hI : I.IsKInjective),
        DerivedCategory.Q.obj ((representative.{c, v, r, a} R A φ L).obj I) ≅
          (globalHom.{c, v, r, a, w, z} R A φ E).obj (DerivedCategory.Q.obj I))
      (α : limitGlobalHom.{c, v, r, a, w, z} R A φ E ≅ globalHomLimit.{c, v, r, a} R A φ L),
      (∀ (I I' : CochainComplex (Modules.{c, v, max c v r} R) ℤ) (hI : I.IsKInjective)
        (hI' : I'.IsKInjective) (f : I ⟶ I'),
        DerivedCategory.Q.map ((representative.{c, v, r, a} R A φ L).map f) ≫ (β I' hI').hom =
          (β I hI).hom ≫ (globalHom.{c, v, r, a, w, z} R A φ E).map (DerivedCategory.Q.map f)) ∧
      (∀ I : (resolvedProperty.{c, v, r} R).FullSubcategory,
        ∃ hLim : CochainComplex.IsKInjective (limit I.obj.asFunctor),
          α.hom.app I = (β (limit I.obj.asFunctor) hLim).inv ≫
            DerivedCategory.Q.map (limit.post I.obj.asFunctor
              (representative.{c, v, r, a} R A φ L))) ∧
      (∀ I : (resolvedProperty.{c, v, r} R).FullSubcategory,
        ∃ hp : HasProduct (fun n : ℕ ↦
            DerivedCategory.Q.{w}.obj (I.obj.asFunctor.obj (op n))),
        ∃ (p : DerivedCategory.Q.{w}.obj (limit I.obj.asFunctor) ⟶
            ∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (I.obj.asFunctor.obj (op n))))
          (δ : (∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj
              (I.obj.asFunctor.obj (op n)))) ⟶
            (DerivedCategory.Q.{w}.obj (limit I.obj.asFunctor))⟦(1 : ℤ)⟧),
          IsDerivedLimitTriangle
            (fun n : ℕ ↦ DerivedCategory.Q.{w}.map
              (I.obj.asFunctor.map (homOfLE (Nat.le_succ n)).op))
            (DerivedCategory.Q.{w}.obj (limit I.obj.asFunctor)) p δ ∧
          ∀ n : ℕ, p ≫ Pi.π _ n = DerivedCategory.Q.{w}.map
            (limit.π I.obj.asFunctor (op n))) ∧
      (∀ (I : (resolvedProperty.{c, v, r} R).FullSubcategory) (n : ℕ),
        ∃ hIn : CochainComplex.IsKInjective (I.obj.asFunctor.obj (op n)),
          α.hom.app I ≫ DerivedCategory.Q.map
              (limit.π ((representativeTowers.{c, v, r, a} R A φ L).obj I) (op n)) ≫
              (β (I.obj.asFunctor.obj (op n)) hIn).hom =
            (globalHom.{c, v, r, a, w, z} R A φ E).map
              (DerivedCategory.Q.map (limit.π I.obj.asFunctor (op n)))) ∧
      (∀ I : (resolvedProperty.{c, v, r} R).FullSubcategory,
        ∃ hp : HasProduct (fun n : ℕ ↦ DerivedCategory.Q.obj
            (((representativeTowers.{c, v, r, a} R A φ L).obj I).obj (op n))),
        ∃ (p : (globalHomLimit.{c, v, r, a} R A φ L).obj I ⟶
            ∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.obj
              (((representativeTowers.{c, v, r, a} R A φ L).obj I).obj (op n))))
          (δ : (∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.obj
              (((representativeTowers.{c, v, r, a} R A φ L).obj I).obj (op n)))) ⟶
            ((globalHomLimit.{c, v, r, a} R A φ L).obj I)⟦(1 : ℤ)⟧),
          IsDerivedLimitTriangle
            (fun n : ℕ ↦ DerivedCategory.Q.map
              (((representativeTowers.{c, v, r, a} R A φ L).obj I).map
                (homOfLE (Nat.le_succ n)).op))
            ((globalHomLimit.{c, v, r, a} R A φ L).obj I) p δ ∧
          ∀ n : ℕ, p ≫ Pi.π _ n = DerivedCategory.Q.map
            (limit.π ((representativeTowers.{c, v, r, a} R A φ L).obj I) (op n))) ∧
      ∃ e : ∀ (N : DerivedCategory (Modules.{c, v, max c v r} R)) (q : ℤ),
          ((DerivedCategory.homologyFunctor (ModuleCat.{max c v r} A) q).obj
            ((globalHom.{c, v, r, a, w, z} R A φ E).obj N)) ≃+ (E ⟶ N⟦q⟧),
        (∀ (N N' : DerivedCategory (Modules.{c, v, max c v r} R)) (f : N ⟶ N') (q : ℤ)
          (x : (DerivedCategory.homologyFunctor (ModuleCat.{max c v r} A) q).obj
            ((globalHom.{c, v, r, a, w, z} R A φ E).obj N)),
          e N' q ((DerivedCategory.homologyFunctor (ModuleCat.{max c v r} A) q).map
            ((globalHom.{c, v, r, a, w, z} R A φ E).map f) x) = e N q x ≫ f⟦q⟧') ∧
        (∀ (N : DerivedCategory (Modules.{c, v, max c v r} R)) (q : ℤ) (b : A)
          (x : (DerivedCategory.homologyFunctor (ModuleCat.{max c v r} A) q).obj
            ((globalHom.{c, v, r, a, w, z} R A φ E).obj N)),
          e N q (b • x) = (φ b) • e N q x) := by
  sorry

end CategoryTheory.RingedSiteGlobalRHom
