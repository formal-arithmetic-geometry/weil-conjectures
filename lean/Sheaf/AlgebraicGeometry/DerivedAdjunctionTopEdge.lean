/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackTopCohomology
public import Sheaf.AlgebraicGeometry.UnboundedDirectImageSectionPresheaf
public import WeilConjectures.AlgebraicGeometry.PinnedDerivedAdjunctionShifts
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.AlgebraicGeometry.RingedSpaceSheafificationCohomology
import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.AlgebraicGeometry.DerivedAdjoint
import Sheaf.AlgebraicGeometry.Picard.CanonicalSingleAdjunctionTranspose

/-! # The top-cohomology edge and the derived adjunction

Source: Stacks Project, cohomology.tex, Tags 0BKJ, 0D5X and 079W; derived.tex,
Tags 08J5, 0149 and 06XS. The adjunct equality is the DAG's agent assembly
(blueprint: lem-weil-pbc-derived-adjunction-top-edge).

All local comparisons below use the existing universal right-derived units on the
same K-injective representative. In particular they retain the local-class normalization.
The theorem specifies the edge by its sheafification equation before identifying adjuncts.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
noncomputable section
namespace AlgebraicGeometry

namespace RingedSpace

variable (X : RingedSpace.{u})
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]

/-- A fixed K-injective representative, using the published functorial resolution.
Source: Stacks, Tag 079V (blueprint: lem-weil-pbc-derived-adjunction-top-edge). -/
abbrev topEdgeResolution (K : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :=
  (CochainComplex.kInjectiveResolutionFunctor.{u} (SheafOfModules.{u} (moduleRings X))).obj
    (DerivedCategory.Q.objPreimage K)

/-- The canonical identification of that representative with K, induced by the resolution
quasi-isomorphism. Source: Stacks, Tag 079V
(blueprint: lem-weil-pbc-derived-adjunction-top-edge). -/
def topEdgeResolutionIso (K : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
    DerivedCategory.Q.obj (topEdgeResolution X K) ≅ K :=
  let r := (CochainComplex.toKInjectiveResolution.{u}
    (SheafOfModules.{u} (moduleRings X))).app (DerivedCategory.Q.objPreimage K)
  letI : QuasiIso r :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ _).2
  (asIso (DerivedCategory.Q.map r)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso K

/-- H^q of local sections computed on the fixed representative. Both isomorphisms are
canonical derived-unit comparisons. Source: Stacks, Tags 0BKJ and 0D5W
(blueprint: lem-weil-pbc-derived-adjunction-top-edge). -/
def topEdgeLocalModel (q : ℤ)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
    (localHypercohomologyPresheaf X q).obj K ≅
      (((localAbelianSections X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (topEdgeResolution X K)).homology q :=
  (localHypercohomologyPresheaf X q).mapIso (topEdgeResolutionIso X K).symm ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso
      ((localAbelianSections X).rightDerivedFunctorOfQuasiIsoResolutionsObjIso
        (localSectionsEnoughKInjectives X) (𝟙 (topEdgeResolution X K))) ≪≫
    (DerivedCategory.homologyFunctorFactors _ q).app _

/-- The canonical local-class map Θ, namely the abelian sheafification unit followed by
its fixed cohomology-sheaf identification. Source: Stacks, Tag 0BKJ
(blueprint: lem-weil-pbc-derived-adjunction-top-edge). -/
def topEdgeLocalClass (q : ℤ)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
    (localHypercohomologyPresheaf X q).obj K ⟶
      (localAbelianSections X).obj ((DerivedCategory.homologyFunctor _ q).obj K) :=
  (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).unit.app _ ≫
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      (localHypercohomologySheafificationAt q K).hom

variable {X} {Y : RingedSpace.{u}}
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))]

/-- Transport between the two published right-derived direct images, by comparing both
units on the same K-injective representative. Source: Stacks, Tags 079V and 0D5W
(blueprint: lem-weil-pbc-derived-adjunction-top-edge). -/
def topEdgeDirectImageComparison (g : X ⟶ Y)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
    (sectionDerivedDirectImage g).obj K ≅ (derivedModuleDirectImage g).obj K :=
  (sectionDerivedDirectImage g).mapIso (topEdgeResolutionIso X K).symm ≪≫
    (moduleDirectImage g).rightDerivedFunctorOfQuasiIsoResolutionsObjIso
      (localSectionsEnoughKInjectives X) (𝟙 (topEdgeResolution X K)) ≪≫
    ((derivedModuleDirectImage g).mapIso (topEdgeResolutionIso X K).symm ≪≫
      (moduleDirectImage g).rightDerivedFunctorObjQIso (topEdgeResolution X K)).symm

/-- The inverse-open local cohomology presheaf computed on the same representative.
Source: Stacks, Tag 0D5X (blueprint: lem-weil-pbc-derived-adjunction-top-edge). -/
def topEdgeInverseModel (g : X ⟶ Y) (q : ℤ)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
    (inverseOpenHypercohomologyPresheaf g q).obj K ≅
      ((((moduleDirectImage g ⋙ localAbelianSections Y).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (topEdgeResolution X K)).homology q) :=
  (inverseOpenHypercohomologyPresheaf g q).mapIso (topEdgeResolutionIso X K).symm ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso
      ((moduleDirectImage g ⋙ localAbelianSections Y).rightDerivedFunctorOfQuasiIsoResolutionsObjIso
          (localSectionsEnoughKInjectives X) (𝟙 (topEdgeResolution X K))) ≪≫
    (DerivedCategory.homologyFunctorFactors _ q).app _

/-- The local derived-sections isomorphism λ, in the direction used by the edge.
The selected presheaf isomorphism is uniquely fixed by its stated hom transformation.
Source: Stacks, Tags 0D5W and 0D5X
(blueprint: lem-weil-pbc-derived-adjunction-top-edge). -/
def topEdgeLocalLeray (g : X ⟶ Y) (q : ℤ)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
    (localHypercohomologyPresheaf Y q).obj ((derivedModuleDirectImage g).obj K) ≅
      (inverseOpenHypercohomologyPresheaf g q).obj K :=
  (localHypercohomologyPresheaf Y q).mapIso (topEdgeDirectImageComparison g K).symm ≪≫
    (Classical.choose (unboundedDirectImage_sectionPresheaf g q)).symm.app K

/-- Θ on inverse-image opens. Exact precomposition commutes with homology; the two
model comparisons then identify H^q(g^-1 V,K) with the corresponding local sections of K.
Source: Stacks, Tags 0BKJ and 0D5X
(blueprint: lem-weil-pbc-derived-adjunction-top-edge). -/
def topEdgeInverseLocalClass (g : X ⟶ Y) (q : ℤ)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
    (inverseOpenHypercohomologyPresheaf g q).obj K ⟶
      (localAbelianSections Y).obj
        ((moduleDirectImage g).obj ((DerivedCategory.homologyFunctor _ q).obj K)) :=
  (topEdgeInverseModel g q K).hom ≫
    (((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj
      (Opens.map g.hom.base).op).mapHomologicalComplexHomologyIso
        (ComplexShape.up ℤ) q).hom.app
          (((localAbelianSections X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (topEdgeResolution X K)) ≫
    ((Functor.whiskeringLeft (Opens Y)ᵒᵖ (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj
      (Opens.map g.hom.base).op).map
        ((topEdgeLocalModel X q K).inv ≫ topEdgeLocalClass X q K)

end RingedSpace

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The inverse of the already recorded canonical top comparison κ.
Source: Stacks, Tag 05TC (blueprint: lem-weil-pbc-derived-adjunction-top-edge). -/
def topEdgePullbackInverse {T S : Scheme.{u}} (g : T ⟶ S)
    (q : ℤ) (C : schemeDerivedCategory S) (hC : C.IsLE q) :=
  letI := (derivedPullback_topCohomology g q C hC).choose_spec.2.1
  inv (derivedPullbackTopCohomology g q C hC)

/-- The pinned derived adjunction induces the ordinary tensor-pullback adjunction in top
cohomology, with precisely the local-class edge e. The existential unique map is the
sheafification of Θλ, expressed by its universal defining equation on every open.
Source: Stacks, cohomology.tex, Tags 0BKJ, 0D5X and 079W; derived.tex, Tags 08J5, 0149,
06XS. The adjunct equality is the agent refinement in the DAG
(blueprint: lem-weil-pbc-derived-adjunction-top-edge).

Proof:
1. Naturality of Θ and λ and module sheafification give the naturality of e. All
section maps are linear via g-sharp. Sheafification makes its defining equation unique.
2. On M[-q], the single direct-image comparison sends m to its resolution cocycle.
The maps λ and Θ send this to the class of that same m; hence e H^q(u)=id.
3. Put A=Lg*C, M=H^q(K), J=τ≥q K. The standard triangles give M[-q]→J→τ≥q+1 J
and τ≤q-1 A→A→H^q(A)[-q], with A≤q by the pullback top-cohomology theorem.
4. Orthogonality and exactness of contravariant Hom factor every A→J through
H^q(A)[-q]; covariant Hom exactness factors the result through M[-q]→J.
5. Shifted full faithfulness of the single functor shows that this factor is the
single of H^q of the original map. Thus maps A→J are determined by H^q.
6. Set a=H^q(d)κ^-1 and let b be its ordinary adjunct. The composite v of Lg* of
the top projection with the pinned single comparison has H^q(v)=κ. Consequently
jd=i a[-q]v, since both sides have the same top cohomology.
7. The normalized single transpose at the identity identifies the pinned comparison
with that of the top-cohomology theorem. The single transpose, pinned adjunction shifts,
pinned counit shifts and adjunction naturality give
Rg*(j)α=Rg*(i) u b[-q] τ_C.
8. Apply H^q and e. Naturality from step 1, normalization from step 2 and the identity
actions of i,j,τ_C on H^q give e H^q(α)=b. This is the displayed equality.
The argument allows arbitrary integer q, non-flat g, zero modules and empty opens. -/
theorem derivedAdjunction_topEdge {T S : Scheme.{u}} (g : T ⟶ S)
    (q : ℤ) (C : schemeDerivedCategory S) (hC : C.IsLE q)
    (K : schemeDerivedCategory T) (_hK : ∃ n : ℤ, K.IsGE n) :
    ∃! e : (DerivedCategory.homologyFunctor.{w, u, u + 1}
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).obj
          ((schemeDerivedDirectImage g).obj K) ⟶
        (Scheme.Modules.pushforward g).obj
          ((DerivedCategory.homologyFunctor.{w, u, u + 1}
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).obj K),
      (∀ V : (Opens S)ᵒᵖ,
        (RingedSpace.topEdgeLocalClass S.toRingedSpace q
          ((schemeDerivedDirectImage g).obj K)).app V ≫
          ((SheafOfModules.toSheaf (moduleRings S.toRingedSpace)).map e).hom.app V =
        (RingedSpace.topEdgeLocalLeray g.toLRSHom.toShHom q K).hom.app V ≫
          (RingedSpace.topEdgeInverseLocalClass g.toLRSHom.toShHom q K).app V) ∧
      (∀ d : (derivedPullback g).obj C ⟶ K,
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).homEquiv _ _
          (topEdgePullbackInverse g q C hC ≫
            (DerivedCategory.homologyFunctor.{w, u, u + 1}
              (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).map d) =
          (DerivedCategory.homologyFunctor.{w, u, u + 1}
            (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).map
              ((@pinnedDerivedAdjunction.{u, w} _
                (fun {_ _} f ↦ Scheme.Modules.canonicalTensorPullbackAdditive.{u, w} f)
                _ _ g).homEquiv C K d) ≫ e) := by
  sorry

end AlgebraicGeometry
