/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackTopCohomology
public import Sheaf.Paper.HigherDirectImagePresheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
import WeilConjectures.AlgebraicGeometry.RingedSpaceSheafificationCohomology
import Sheaf.AlgebraicGeometry.UnboundedDirectImageSectionPresheaf
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
import WeilConjectures.AlgebraicGeometry.ModuleOpenRestrictionInjectives
import WeilConjectures.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial

/-! # Top derived base change on local cohomology classes

Source: Stacks Project, Cohomology, Tags 01E4, 01FB and 08HY, with the top-adjunction
argument specified in the DAG (blueprint: lem-weil-pbc-top-base-change-presheaf).

The chosen fibre product is `pullback g f`, so its projection to X is `pullback.snd g f`.
The class maps use the existing restricted-resolution section identifications. The
adjoint is transported from total-derived cohomology to classical higher direct images
by the canonical total/classical comparison. No map is assumed invertible except κ.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
open Scheme.Modules

/-- Restrict the ordinary tensor-pullback unit to an inverse-image open. The coefficient
is the restriction of the global pulled-back module, using direct-image composition and
restriction adjunctions, so no independently chosen coefficient comparison occurs.
Source: Stacks Project, Tag 01FB and Sheaves, Tags 0096 and 0097
(blueprint: lem-weil-pbc-top-base-change-presheaf). -/
def topBaseChangeRestrictedUnit {Z X : Scheme.{u}} (v : Z ⟶ X)
    (F : X.Modules) (U : X.Opens) :
    (restrictFunctor U.ι).obj F ⟶
      (pushforward (v.resLE U (v ⁻¹ᵁ U) le_rfl)).obj
        ((restrictFunctor (v ⁻¹ᵁ U).ι).obj ((tensorPullback v).obj F)) :=
  ((restrictAdjunction U.ι).homEquiv _ _).symm
    ((tensorPullbackSectionAdjunction v).unit.app F ≫
      (pushforward v).map ((restrictAdjunction (v ⁻¹ᵁ U).ι).unit.app
        ((tensorPullback v).obj F)) ≫
      (pushforwardComp (v ⁻¹ᵁ U).ι v).hom.app
        ((restrictFunctor (v ⁻¹ᵁ U).ι).obj ((tensorPullback v).obj F)) ≫
      ((pushforwardComp (v.resLE U (v ⁻¹ᵁ U) le_rfl) U.ι ≪≫
        pushforwardCongr (v.resLE_comp_ι le_rfl)).inv.app
          ((restrictFunctor (v ⁻¹ᵁ U).ι).obj ((tensorPullback v).obj F))))

/-- The particular cocycle-to-sheafification map θ, on the cohomology of a restricted
module. Every resolution identification preserves its augmentation and its sections.
Source: Stacks Project, Tag 01E4, lemma-describe-higher-direct-images
(blueprint: lem-weil-pbc-top-base-change-presheaf). -/
def topBaseChangeClass {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (I : InjectiveResolution F) (V : S.Opens) (U : X.Opens) (e : U = f ⁻¹ᵁ V)
    (R : RestrictedResolutionSections I U) (q : ℕ) :
    (forget₂ _ AddCommGrpCat.{u}).obj
        ((RingedSpace.moduleCohomology U.toScheme.toRingedSpace q).obj
          ((restrictFunctor U.ι).obj F)) ⟶
      (((pushforward f).rightDerived q).obj F).presheaf.obj (op V) :=
  resolutionSectionClass R.resolution
      (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
      V (R.sections ≪≫ eqToIso (congrArg (fun A ↦
        ((RingedSpace.openModuleSections X.toRingedSpace A).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex) e)) q ≫
    Hom.app (I.isoRightDerivedObj (pushforward f) q).inv V

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The normalized module base-change map δ: the derived mate followed by the pinned
comparison from derived to ordinary pullback on a single module. This is the specified
counit representative of `IsDerivedModuleBaseChangeMap`, on the reversed fibre product.
Source: Stacks Project, Tag 08HY
(blueprint: lem-weil-pbc-top-base-change-presheaf). -/
def topBaseChangeDelta {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (F : X.Modules) :
    (derivedPullback g).obj ((schemeDerivedDirectImage f).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)) ⟶
    (schemeDerivedDirectImage (pullback.fst g f)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (pullback g f).toRingedSpace)) 0).obj
          ((tensorPullback (pullback.snd g f)).obj F)) :=
  schemeDerivedBaseChangeMap f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition.symm ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F) ≫
    (schemeDerivedDirectImage (pullback.fst g f)).map
      (pinnedModulePullbackComparisonAt (pullback.snd g f) 0 F)

/-- The ordinary adjoint of H^q(δ)κ⁻¹, expressed on classical higher direct images
using the canonical total/classical cohomology isomorphisms. The inverse of κ uses the
recorded top-cohomology theorem; δ itself need not be invertible.
Source: Stacks Project, Tags 01E4 and 08HY; top-degree adjunction comparison in the DAG
(blueprint: lem-weil-pbc-top-base-change-presheaf). -/
def topBaseChangeAdjoint {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (F : X.Modules) (q : ℕ)
    (hC : ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)).IsLE (q : ℤ)) :
    ((pushforward f).rightDerived q).obj F ⟶
      (pushforward g).obj (((pushforward (pullback.fst g f)).rightDerived q).obj
        ((tensorPullback (pullback.snd g f)).obj F)) :=
  let C := (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)
  letI : IsIso (derivedPullbackTopCohomology g (q : ℤ) C hC) :=
    (Classical.choose_spec (derivedPullback_topCohomology g (q : ℤ) C hC)).2.1
  (Functor.homologyRightDerivedFunctorObjSingleFunctorIso
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) F q).inv ≫
    (tensorPullbackSectionAdjunction g).homEquiv _ _
      (inv (derivedPullbackTopCohomology g (q : ℤ) C hC) ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings T.toRingedSpace)) (q : ℤ)).map
            (topBaseChangeDelta f g F)) ≫
    (pushforward g).map (Functor.homologyRightDerivedFunctorObjSingleFunctorIso
      (RingedSpace.moduleDirectImage (pullback.fst g f).toLRSHom.toShHom)
      ((tensorPullback (pullback.snd g f)).obj F) q).hom

/-- On every open, the ordinary adjoint of top derived module base change carries the
canonical cocycle class to the cocycle class of pullback along the restricted ordinary
unit. The resolution parameters merely express the specified θ maps and range over all
augmentation-preserving restricted resolutions. There are no geometric finiteness,
flatness, quasi-coherence or base-change-invertibility hypotheses.
Source: Stacks Project, cohomology.tex, Tags 01E4, 01FB and 08HY, with the agent
adjunction identification recorded in the node
(blueprint: lem-weil-pbc-top-base-change-presheaf).

Proof:
1. Put G = v*F and D = Rf_T*(G[0]). Transpose the derived mate. Naturality in its
coefficient comparison replaces the derived unit by Rv*(c_v) after that unit.
The specified single-module transpose normalization identifies this composite with
F[0] → Rv*(G[0]), induced by the ordinary unit. Thus the derived adjunct A is Rf*
of this arrow followed by the normalized direct-image composition comparisons
(def-pc-derived-module-base-change-map, lem-pc-ringed-spaces-derived-adjoint,
lem-pc-derived-direct-image-composition).
2. Sheafify the local derived-sections comparison followed by the canonical local-class
map to obtain e : H^q(Rg*D) → g*H^q(D). Its defining section equation follows from
lem-pc-ringed-space-sheafification-cohomology and
lem-trf-unbounded-direct-image-section-presheaf. The bound hC and the bounded-below
injective resolution of G[0] allow lem-weil-pbc-derived-adjunction-top-edge to identify
the ordinary adjoint with e H^q(A), for precisely the fixed κ.
3. Choose injective resolutions I of F and J of G, an injective replacement ℓ of v*J,
and an augmented lift β from I. Restriction preserves these resolutions. The section
quasi-isomorphism theorem makes Γ(U,ℓ) invertible on cohomology. The restricted unit's
cohomology map is H^qΓ(U,ℓ)⁻¹ H^qΓ(U,β), by def-weil-pbc-module-cohomology-fmap and
its independence theorem. The normalized direct-image composition represents A by
the roof f*I → f*L ← f*v*J, with arrows f*β and f*ℓ. Evaluation on V and the local
derived-sections comparisons give exactly the same cohomology map.
4. On I and J the canonical local-class maps send the same cocycles to their sections
in the cohomology sheaves. They are precisely the θ maps of
lem-weil-pbc-higher-direct-image-presheaf, computed by topBaseChangeClass.
Naturality for A commutes its local cohomology action with its cohomology-sheaf action.
The restriction-unit construction fixes the coefficient as (v*F)|U', equivalently the
ordinary pullback coefficient via lem-pc-module-pullback-identity-composition.
5. Substitute a = e H^q(A) into that naturality equation, apply the defining section
equation of e and the roof calculation from step 3. Cancel the canonical local
comparison isomorphisms. This gives Γ(V,a) θ_V = θ'_W v_V* as displayed, transported
only through the canonical total/classical higher-direct-image comparisons.
No θ component or δ is inverted. -/
theorem top_base_change_presheaf {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (F : X.Modules) (q : ℕ)
    (hC : ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)).IsLE (q : ℤ))
    (V : S.Opens) (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (R : RestrictedResolutionSections I (f ⁻¹ᵁ V))
    (R' : RestrictedResolutionSections J ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V))) :
    topBaseChangeClass f F I V (f ⁻¹ᵁ V) rfl R q ≫
        Hom.app (topBaseChangeAdjoint f g F q hC) V =
      moduleCohomologyFMap ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
          ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl)
        (topBaseChangeRestrictedUnit (pullback.snd g f) F (f ⁻¹ᵁ V)) q ≫
      topBaseChangeClass (pullback.fst g f) ((tensorPullback (pullback.snd g f)).obj F)
        J (g ⁻¹ᵁ V) ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V))
        (flatBaseChangeOpenEquality f g V) R' q := by
  sorry

end AlgebraicGeometry
