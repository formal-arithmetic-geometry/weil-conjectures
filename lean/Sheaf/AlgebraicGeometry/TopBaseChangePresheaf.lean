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
import Sheaf.AlgebraicGeometry.DerivedSquareLocalClasses

/-! # Top derived base change on local cohomology classes

Source: Stacks Project, Cohomology, Tags 01E4, 01FB and 08HY, with the top-adjunction
argument specified in the DAG (blueprint: lem-weil-pbc-top-base-change-presheaf).

The chosen fibre product is `pullback g f`, so its projection to X is `pullback.snd g f`.
The class maps use the existing restricted-resolution section identifications. The
adjoint is transported from total-derived cohomology to classical higher direct images
by the canonical total/classical comparison. No map is assumed invertible except κ.
-/

@[expose] public section
set_option cleanup.letToHave false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
open Scheme.Modules
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local irreducible] Scheme.Modules.tensorPullback
attribute [local irreducible] limit limit.π

private theorem normalized_tensorAdjunction {Y Z : Scheme.{u}} (v : Y ⟶ Z) :
    Classical.choose (exists_tensorPullbackAdjunction v) =
      tensorPullbackSectionAdjunction v := by
  apply (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction v)).2
  intro M U m
  exact (Classical.choose_spec (exists_tensorPullbackAdjunction v)) M (op U) m

attribute [local irreducible] tensorPullbackSectionAdjunction resolutionSectionClass
  moduleCohomologyFMap Functor.rightDerivedFunctor Functor.rightDerived
  Functor.homologyRightDerivedFunctorObjSingleFunctorIso
  InjectiveResolution.isoRightDerivedObj derivedPullbackTopCohomology
  pinnedModulePullbackComparisonAt RingedSpace.topEdgeLocalClass
  RingedSpace.topEdgeLocalLeray RingedSpace.topEdgeInverseLocalClass

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

attribute [local irreducible] topBaseChangeDelta

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem topBaseChangeClass_source {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (I : InjectiveResolution F) (V : S.Opens)
    (R : RestrictedResolutionSections I (f ⁻¹ᵁ V)) (q : ℕ) :
    topBaseChangeClass f F I V (f ⁻¹ᵁ V) rfl R q =
      resolutionSectionClass R.resolution
        (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
        V R.sections q ≫ Hom.app (I.isoRightDerivedObj (pushforward f) q).inv V := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  simp only [topBaseChangeClass, eqToIso_refl, Iso.trans_refl]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem restrictedDirectImageMap_unit {Z X : Scheme.{u}} (v : Z ⟶ X)
    (F : X.Modules) (U : X.Opens) :
    restrictedDirectImageMap v ((tensorPullbackSectionAdjunction v).unit.app F) U =
      topBaseChangeRestrictedUnit v F U := by
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem topBaseChangeClass_eq {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (I : InjectiveResolution F) (V : S.Opens) (U : X.Opens) (e : U = f ⁻¹ᵁ V)
    (R : RestrictedResolutionSections I U) (q : ℕ) :
    topBaseChangeClass f F I V U e R q =
      resolutionSectionClass R.resolution
        (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
        V (R.sections ≪≫ eqToIso (congrArg (fun A ↦
          ((RingedSpace.openModuleSections X.toRingedSpace A).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex) e)) q ≫
      Hom.app (I.isoRightDerivedObj (pushforward f) q).inv V := by
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem topBaseChangeAdjoint_eq {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (F : X.Modules) (q : ℕ)
    (hC : ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)).IsLE (q : ℤ)) :
    topBaseChangeAdjoint f g F q hC =
      (schemeSingleCohomologyComparison f F q).inv ≫
      (tensorPullbackSectionAdjunction g).homEquiv _ _
        (topEdgePullbackInverse g (q : ℤ)
          ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)) hC ≫
          (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) (q : ℤ)).map
              (topBaseChangeDelta f g F)) ≫
      (pushforward g).map (schemeSingleCohomologyComparison (pullback.fst g f)
        ((tensorPullback (pullback.snd g f)).obj F) q).hom := by
  delta schemeSingleCohomologyComparison
  rfl

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem conjugate_comp {D : Type*} [Category D]
    {A B C E H : D} (a : A ⟶ B) (b : E ⟶ H)
    {m : B ⟶ E} {n : B ⟶ C} {p : C ⟶ E} (h : m = n ≫ p) :
    a ≫ m ≫ b = a ≫ n ≫ p ≫ b := by
  rw [h, Category.assoc]

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem transport_class_equation {D : Type*} [Category D]
    {A B C E : D} {s s' : A ⟶ B} {a a' : B ⟶ E}
    {t t' : C ⟶ E} {m m' : A ⟶ C}
    (hs : s = s') (ha : a = a') (ht : t = t') (hm : m = m')
    (h : s' ≫ a' = m' ≫ t') : s ≫ a = m ≫ t := by
  rw [hs, ha, ht, hm]
  exact h

attribute [local irreducible] topBaseChangeClass topBaseChangeRestrictedUnit
  topBaseChangeAdjoint derivedSquareUnitMap derivedSquareRightComparison
  schemeSingleCohomologyComparison

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
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
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let C := (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)
  let G := (tensorPullback (pullback.snd g f)).obj F
  let K := (schemeDerivedDirectImage (pullback.fst g f)).obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings (pullback g f).toRingedSpace)) 0).obj G)
  have hK : K.IsGE 0 := by
    dsimp only [K, schemeDerivedDirectImage, RingedSpace.derivedModuleDirectImage]
    exact Functor.isGE_rightDerivedFunctor_obj_singleFunctor
      (RingedSpace.moduleDirectImage (pullback.fst g f).toLRSHom.toShHom) G
  have hedge :=
    (@derivedAdjunction_topEdge.{u, w} inferInstance T S g (q : ℤ) C hC K ⟨0, hK⟩).exists
  let e := Classical.choose hedge
  have he := (Classical.choose_spec hedge).1
  have ha := (Classical.choose_spec hedge).2
  have hd : (@pinnedDerivedAdjunction.{u, w} _
      (fun {_ _} v ↦ canonicalTensorPullbackAdditive.{u, w} v)
      _ _ g).homEquiv C K (topBaseChangeDelta f g F) =
      derivedSquareUnitMap f (pullback.fst g f) g (pullback.snd g f)
        pullback.condition.symm F G
        ((tensorPullbackSectionAdjunction (pullback.snd g f)).unit.app F) := by
    unfold topBaseChangeDelta
    exact (derivedModuleBaseChange_transpose f (pullback.fst g f) g
      (pullback.snd g f) pullback.condition.symm F).trans
        (congrArg (fun adj : tensorPullback (pullback.snd g f) ⊣
            pushforward (pullback.snd g f) ↦
          derivedSquareUnitMap f (pullback.fst g f) g (pullback.snd g f)
            pullback.condition.symm F G (adj.unit.app F))
          (normalized_tensorAdjunction (pullback.snd g f)))
  have ht := (congrArg (fun adj : tensorPullback g ⊣ pushforward g ↦
      adj.homEquiv _ _
        (topEdgePullbackInverse g (q : ℤ) C hC ≫
          (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) (q : ℤ)).map
              (topBaseChangeDelta f g F))) (normalized_tensorAdjunction g)).symm.trans
                (ha (topBaseChangeDelta f g F))
  have ht' := ht.trans (congrArg (fun z ↦
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (q : ℤ)).map z ≫ e) hd)
  have hlocal := @derivedSquareUnit_localClasses.{u, w} inferInstance
    X S (pullback g f) T f (pullback.fst g f) g
    (pullback.snd g f) pullback.condition.symm F G
    ((tensorPullbackSectionAdjunction (pullback.snd g f)).unit.app F)
    q e he V I J R R'
  have hadj := conjugate_comp
    (schemeSingleCohomologyComparison f F q).inv
    ((pushforward g).map (schemeSingleCohomologyComparison (pullback.fst g f) G q).hom) ht'
  have hadj' := (topBaseChangeAdjoint_eq f g F q hC).trans hadj
  have hm := congrArg (fun φ ↦
    moduleCohomologyFMap ((pullback.snd g f).resLE (f ⁻¹ᵁ V)
      ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) le_rfl) φ q)
      (restrictedDirectImageMap_unit (pullback.snd g f) F (f ⁻¹ᵁ V))
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  exact transport_class_equation (D := AddCommGrpCat.{u})
    (topBaseChangeClass_source f F I V R q)
    (congrArg (fun z ↦ Hom.app z V) hadj')
    (topBaseChangeClass_eq (pullback.fst g f) G J (g ⁻¹ᵁ V)
      ((pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)) (flatBaseChangeOpenEquality f g V) R' q)
    hm.symm hlocal

end AlgebraicGeometry
