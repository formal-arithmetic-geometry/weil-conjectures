module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.RingedSiteSectionFunctors
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.Pullback

/-! # Higher direct images of modules as sheafified cohomology presheaves

Source: Stacks Project, Cohomology on Sites, Tag 072W, lemma-higher-direct-images
(blueprint: lem-sfb-ringed-site-higher-image-cohomology-sheafification).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RingedSiteHigherImage

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (u : D ⥤ C) [u.IsContinuous K J]
  {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
  (ρ : B ⟶ (u.sheafPushforwardContinuous CommRingCat.{u} K J).obj A)

/-- The prescribed module direct image, including restriction of scalars along `ρ`.
Source: Stacks Project, Tag 072W
(blueprint: lem-sfb-ringed-site-higher-image-cohomology-sheafification). -/
abbrev directImage :=
  SheafOfModules.pushforward.{u} (RingedSiteSectionFunctors.sectionModuleMap u ρ)

/-- The cohomology presheaf functor: derive the presheaf underlying module direct image.
Its values are the cohomology of the evaluated module injective resolution, its scalar
operation is multiplication through `ρ`, and its restrictions are those of that complex.
Source: Stacks Project, Tag 072W, the two displayed kernel/image quotients in the proof
(blueprint: lem-sfb-ringed-site-higher-image-cohomology-sheafification). -/
abbrev cohomologyPresheaf
    [EnoughInjectives
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))]
    (q : ℕ) :=
  (directImage u ρ ⋙ SheafOfModules.forget _).rightDerived q

/-- Exact sheafification followed by its counit gives the canonical homology map.
Source: Stacks Project, Tag 072W, proof
(blueprint: lem-sfb-ringed-site-higher-image-cohomology-sheafification). -/
def sheafifiedHomologyComparison {E : Type u} [SmallCategory E]
    {L : GrothendieckTopology E} (R : Sheaf L RingCat.{u})
    (X : CochainComplex (ringedSiteModules.{u} R) ℕ) (q : ℕ) :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj
      ((X.sc q).map (SheafOfModules.forget R)).homology ⟶ (X.sc q).homology :=
  let S := PresheafOfModules.sheafification (𝟙 R.obj)
  let ε : SheafOfModules.forget R ⋙ S ⟶ 𝟭 (SheafOfModules.{u} R) :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit
  (((X.sc q).map (SheafOfModules.forget R)).mapHomologyIso S).inv ≫
    ShortComplex.homologyMap ((X.sc q).mapNatTrans ε)

/-- The resolution cocycle map to the higher module direct image.
Source: Stacks Project, Tag 072W, proof
(blueprint: lem-sfb-ringed-site-higher-image-cohomology-sheafification). -/
def resolutionComparison
    [EnoughInjectives
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))]
    (q : ℕ)
    (M : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    (I : InjectiveResolution M) :
    (PresheafOfModules.sheafification
      (𝟙 ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B).obj)).obj
        ((cohomologyPresheaf u ρ q).obj M) ⟶
      ((directImage u ρ).rightDerived q).obj M := by
  let R := (sheafCompose K (forget₂ CommRingCat RingCat)).obj B
  let F := directImage u ρ
  let T := SheafOfModules.forget R
  let S := PresheafOfModules.sheafification (𝟙 R.obj)
  let X := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let Y := (T.mapHomologicalComplex (.up ℕ)).obj X
  let c : (Y.sc q).homology ≅
      (HomologicalComplex.homologyFunctor _ (.up ℕ) q).obj
        (((F ⋙ T).mapHomologicalComplex (.up ℕ)).obj I.cocomplex) :=
    (HomologicalComplex.homologyFunctor _ (.up ℕ) q).mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ T)) (.up ℕ)).app I.cocomplex)
  exact S.map ((I.isoRightDerivedObj (F ⋙ T) q).hom ≫ c.inv) ≫
    sheafifiedHomologyComparison R X q ≫ (I.isoRightDerivedObj F q).inv

/-- The canonical evaluation comparison on a resolution, retaining the derived evaluation
in the module category as its target. Source: Stacks Project, Tag 072W, proof
(blueprint: lem-sfb-ringed-site-higher-image-cohomology-sheafification). -/
def evaluationComparison
    [EnoughInjectives
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))]
    (q : ℕ) (V : D)
    (M : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    (I : InjectiveResolution M) :
    ((cohomologyPresheaf u ρ q ⋙
      PresheafOfModules.toPresheaf
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B).obj ⋙
      (CategoryTheory.evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op V)).obj M) ⟶
    ((RingedSiteSectionFunctors.sectionEvaluation
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (u.obj V)).rightDerived q).obj
        M := by
  let R := (sheafCompose K (forget₂ CommRingCat RingCat)).obj B
  let F := directImage u ρ ⋙ SheafOfModules.forget R
  let E := PresheafOfModules.toPresheaf R.obj ⋙
    (CategoryTheory.evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op V)
  let G := RingedSiteSectionFunctors.sectionEvaluation
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (u.obj V)
  let X := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) q
  let e : F ⋙ E ≅ G := Iso.refl _
  let c := (Functor.mapHomologicalComplexCompIso e (.up ℕ)).app I.cocomplex
  exact E.map (I.isoRightDerivedObj F q).hom ≫
    ((X.sc q).mapHomologyIso E).inv ≫ H.map c.hom ≫
      (I.isoRightDerivedObj G q).inv

/-- Higher module direct images are naturally sheafified module-cohomology presheaves.

Source: Stacks Project, Cohomology on Sites, Tag 072W, statement and proof
(blueprint: lem-sfb-ringed-site-higher-image-cohomology-sheafification).

The first family identifies every presheaf value with the right derived additive evaluation
on module sheaves. Its equality for every resolution fixes the cocycle identification.
The second natural isomorphism is the asserted sheafification comparison; its equality
for every resolution fixes the cocycle-to-cohomology-sheaf map. Naturality in a module
morphism is part of both natural isomorphisms.

Proof: (1) Use nonnegative injective module resolutions as in
lem-weil-pbc-left-exact-injective-resolution-degree-zero. Evaluation and module pushforward
are additive and preserve kernels. Their right derived functors are computed on these
resolutions by lem-weil-pbc-derived-functor-map-via-lift.
(2) Presheaf module kernels and cokernels are objectwise. Their homology is H^q(I(u(V))),
with scalar operation b[z] = [ρ(b)z] and restrictions induced by I; semilinearity follows
from naturality of ρ. Exact evaluation gives `evaluationComparison`.
(3) Apply exact module sheafification
(lem-weil-pbc-ringed-site-module-sheafification-exact). Its homology comparison from
lem-sp-exact-functor-preserves-homology, followed by the sheafification counit on the
module sheaf complex and the resolution isomorphism, is `resolutionComparison`.
This sends an evaluated cocycle class to its cohomology-sheaf section.
(4) Lift each module morphism to a resolution map using
lem-weil-pbc-injective-resolution-lift-exists. The derived-map formula and naturality of
homology comparison show naturality: both composites send [z] to the class of its image.
(5) The same argument for the identity and two resolutions proves independence of the
resolution, hence the formulas hold for every resolution. Scalar restriction never
requires flatness of ρ. Degree zero uses the zero incoming differential. -/
theorem exists_cohomologyPresheaf_sheafificationIso
    [PreservesFiniteLimits (u.sheafPullback (Type u) K J)]
    [EnoughInjectives
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))]
    [EnoughInjectives
      (ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))]
    (q : ℕ) :
    (∀ V : D, ∃ e : cohomologyPresheaf u ρ q ⋙
        PresheafOfModules.toPresheaf
          ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B).obj ⋙
        (CategoryTheory.evaluation Dᵒᵖ AddCommGrpCat.{u}).obj (op V) ≅
      (RingedSiteSectionFunctors.sectionEvaluation
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A) (u.obj V)).rightDerived q,
      ∀ (M : ringedSiteModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
        (I : InjectiveResolution M),
        e.hom.app M = evaluationComparison u ρ q V M I) ∧
    (∃ σ : cohomologyPresheaf u ρ q ⋙ PresheafOfModules.sheafification
        (𝟙 ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B).obj) ≅
        (directImage u ρ).rightDerived q,
      ∀ (M : ringedSiteModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
        (I : InjectiveResolution M),
        σ.hom.app M = resolutionComparison u ρ q M I) := by
  sorry

end CategoryTheory.RingedSiteHigherImage
