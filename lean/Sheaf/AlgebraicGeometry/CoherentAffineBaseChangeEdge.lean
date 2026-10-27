/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import WeilConjectures.AlgebraicGeometry.PinnedSingleBaseChangeShift
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeSquare
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.LerayDegenerateSections
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Sheaf.AlgebraicGeometry.TopDegreeLeraySquare
import Sheaf.AlgebraicGeometry.TensorSingleBaseChangePasting
import Sheaf.AlgebraicGeometry.DerivedPullbackTopCohomology
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.AffineHigherDirectImageCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.ResolutionScalarAction

/-! # Simultaneous affine coherent edge isomorphisms

Source: Stacks Project, Cohomology, Tags 0ATM, 01FB, 01F8 and 01F2.
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality).

The auxiliary maps below spell out the canonical maps in the statement. A single module
in cohomological degree one represents `E[-1]`. The normalization on the top projection
specifies the truncation projection, independently of any local splitting.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback RingedSpace.moduleCohomology
  Functor.homologyRightDerivedFunctorObjSingleFunctorIso

attribute [local instance_reducible] TopCat.Sheaf
set_option allowUnsafeReducibility true in
attribute [local reducible] Scheme.Modules Scheme.Modules.Hom Scheme.Modules.instCategory
  Scheme.Modules.instAbelian

attribute [local instance 2000] topDegreeModuleCategory topDegreeModulePreadditive
  topDegreeModuleAbelian

set_option allowUnsafeReducibility true in
attribute [local reducible] topDegreeModuleCategory topDegreeModulePreadditive
  topDegreeModuleAbelian

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- `Rf_*(G[0])`. Source: Stacks, Tag 01F2
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
abbrev coherentEdgeK {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules) :=
  topDegreeDerivedImage.{u, w} f G

/-- Cohomology of the derived image, in particular `A` in degree zero and `E` in degree one.
Source: Stacks, Tag 01F2
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
abbrev coherentEdgeCohomology {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules) (n : ℤ) :=
  (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) n).obj (coherentEdgeK f G)

/-- The coefficient `G_T = j_T^*G`. Source: Stacks, Tag 0ATM
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
abbrev coherentEdgeCoefficient {X S T : Scheme.{u}}
    (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S) :=
  (Scheme.Modules.tensorPullback (pullback.fst f g)).obj G

/-- The canonical module base change is the existing pinned single-degree composite,
specialized to degree zero and the chosen fibre product.
Source: Stacks, Tag 08HY
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
abbrev coherentEdgeDelta {X S T : Scheme.{u}}
    (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S) :
    (derivedPullback g).obj (coherentEdgeK f G) ⟶
      coherentEdgeK (pullback.snd f g) (coherentEdgeCoefficient f G g) :=
  topDegreeTensorBaseChange f (pullback.snd f g) g (pullback.fst f g)
    pullback.condition G

/-- `H^1(Lg^*tau)` with the specified single-module counit identifying its target with
`g^*E`. Source: Stacks, Tag 05TC, dual truncation argument
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
def coherentEdgeGamma {S T : Scheme.{u}} (g : T ⟶ S) (K : schemeDerivedCategory S)
    (τ : K ⟶ (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1).obj K)) :
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 1).obj ((derivedPullback g).obj K) ⟶
    (Scheme.Modules.tensorPullback g).obj ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1).obj K) :=
  by
  letI := (Classical.choose exists_derivedPullbackComposition) g
  exact (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 1).map
        ((derivedPullback g).map τ ≫ pinnedSingleDegreeTensorComparison g
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1).obj K) 1) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 1).hom.app _

/-- The cocycle Leray edge, with its target expressed as `H^1(Rf_*(G[0]))` using the
canonical comparison between total and classical right derived functors.
The cocycle condition of the selected theorem determines the edge uniquely.
Source: Stacks, Tags 01F4(2) and 01E4
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
abbrev coherentEdgeEpsilon {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules) :
    (forget₂ _ AddCommGrpCat.{u}).obj (topDegreeCohomologyOnBase f G) ⟶
    (forget₂ _ AddCommGrpCat.{u}).obj
      ((RingedSpace.globalSectionsFunctor S.toRingedSpace).obj
        (coherentEdgeCohomology f G 1)) :=
  topDegreeLerayEdge.{u, w} f G

/-- Degree-one cohomology, with scalars restricted along `f_T` to `Gamma(T,O_T)`.
Source: Stacks, Tag 01F2 and the following module-structure remark
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
abbrev coherentEdgeH {X S T : Scheme.{u}}
    (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S) :=
  topDegreeCohomologyOnBase (pullback.snd f g) (coherentEdgeCoefficient f G g)

/-- Section pullback along the normalized ordinary tensor-pullback unit, with the
preimage of the whole space identified with the whole space.
Source: Stacks, Tag 0096
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
abbrev coherentEdgeSectionPullback {T T' : Scheme.{u}} (h : T' ⟶ T) (M : T.Modules)
    (s : (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj M) :
    (RingedSpace.globalSectionsFunctor T'.toRingedSpace).obj
      ((Scheme.Modules.tensorPullback h).obj M) :=
  topDegreeSectionPullback h M s

/-- Section pullback followed by `h^*g^*E ≅ (gh)^*E`.
Source: Stacks, Tags 0096 and 0097
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
def coherentEdgeRho {S T T' : Scheme.{u}} (g : T ⟶ S) (h : T' ⟶ T) (E : S.Modules)
    (s : (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj
      ((Scheme.Modules.tensorPullback g).obj E)) :
    (RingedSpace.globalSectionsFunctor T'.toRingedSpace).obj
      ((Scheme.Modules.tensorPullback (h ≫ g)).obj E) :=
  ((Scheme.Modules.tensorPullbackSectionComp h g).inv.app E).app ⊤
    (coherentEdgeSectionPullback h ((Scheme.Modules.tensorPullback g).obj E) s)

/-- The map `h_X : X_(gh) ⟶ X_g` of the chosen fibre products.
Source: Stacks, Tag 0ATM
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
abbrev coherentEdgeXMap {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (h : T' ⟶ T) : pullback f (h ≫ g) ⟶ pullback f g :=
  baseChangeMap f (Over.homMk h (by rfl) : Over.mk (h ≫ g) ⟶ Over.mk g)

/-- Canonical coefficient identification `h_X^*G_T ≅ G_(gh)` using normalized pullback
composition and the first-projection equation of the fibre product.
Source: Stacks, Tags 0097 and 0ATM
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
def coherentEdgeCoefficientIso {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S) (h : T' ⟶ T) :
    (Scheme.Modules.tensorPullback (coherentEdgeXMap f g h)).obj
        (coherentEdgeCoefficient f G g) ≅ coherentEdgeCoefficient f G (h ≫ g) :=
  ((Scheme.Modules.tensorPullbackSectionComp (coherentEdgeXMap f g h)
      (pullback.fst f g)).symm.app G) ≪≫
    eqToIso (congrArg (fun k ↦ (Scheme.Modules.tensorPullback k).obj G)
      (by simp [coherentEdgeXMap, baseChangeMap]))

/-- The cohomology map with exactly the coefficient identification above.
Source: Stacks, Tags 01FB and 01F8
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
abbrev coherentEdgePullback {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S) (h : T' ⟶ T) :=
  topDegreeCohomologyPullback (pullback.snd f g) (pullback.snd f (h ≫ g))
    (coherentEdgeXMap f g h)
    (coherentEdgeCoefficient f G g) (coherentEdgeCoefficient f G (h ≫ g))
    (coherentEdgeCoefficientIso f G g h).hom

attribute [local instance 3000] SheafOfModules.instCategory SheafOfModules.instPreadditive
attribute [local instance 4000] globalLerayModuleAbelian

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coherentEdge_leray_square
    {Y T Z U : Scheme.{u}} (q : Y ⟶ T) (r : Z ⟶ U) (h : U ⟶ T) (p : Z ⟶ Y)
    (hs : p ≫ q = r ≫ h) (F : Y.Modules) (M : Z.Modules)
    (a : (Scheme.Modules.tensorPullback p).obj F ⟶ M)
    (hC : (coherentEdgeK.{u, w} q F).IsLE 1) :
    let C := coherentEdgeK.{u, w} q F
    let d := topDegreeBaseChangeMap.{u, w} q r h p hs F M a
    let κ := derivedPullbackTopCohomology h 1 C hC
    letI : IsIso κ := (Classical.choose_spec
      (derivedPullback_topCohomology h 1 C hC)).2.1
    ∀ x : topDegreeCohomologyOnBase q F,
      coherentEdgeEpsilon r M (topDegreeCohomologyPullback q r p F M a x) =
        (RingedSpace.globalSectionsFunctor U.toRingedSpace).map
          (inv κ ≫ ((DerivedCategory.homologyFunctor.{w, u, u + 1}
            (SheafOfModules.{u} (moduleRings U.toRingedSpace)) 1)).map d)
            (coherentEdgeSectionPullback h (coherentEdgeCohomology q F 1)
              (coherentEdgeEpsilon q F x)) := by
  have raw := topDegreeLeray_commutativeSquare.{u, w} q r h p hs F M a hC
  simpa only [coherentEdgeEpsilon, coherentEdgeSectionPullback,
    coherentEdgeCohomology, coherentEdgeK] using raw

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
/-- The existing additive group of the specified base cohomology module. -/
local instance (priority := 2000) coherentEdge_baseCohomologyGroup
    {Y T : Scheme.{u}} (q : Y ⟶ T) (F : Y.Modules) :
    AddCommGroup (topDegreeCohomologyOnBase q F) :=
  ModuleCat.isAddCommGroup (topDegreeCohomologyOnBase q F)

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
/-- The existing scalar action of the specified base cohomology module. -/
local instance (priority := 2000) coherentEdge_baseCohomologyModule
    {Y T : Scheme.{u}} (q : Y ⟶ T) (F : Y.Modules) :
    Module Γ(T, ⊤) (topDegreeCohomologyOnBase q F) :=
  ModuleCat.isModule (topDegreeCohomologyOnBase q F)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] Functor.rightDerived

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
local instance coherentEdge_cohomologyModule (T : Scheme.{u}) (n : ℕ)
    (M : SheafOfModules.{u} (moduleRings T.toRingedSpace)) :
    Module Γ(T, ⊤) ((RingedSpace.moduleCohomology T.toRingedSpace n).obj M) :=
  ModuleCat.isModule ((RingedSpace.moduleCohomology T.toRingedSpace n).obj M)

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
local instance coherentEdge_sectionsModule (T : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings T.toRingedSpace)) :
    Module Γ(T, ⊤) ((RingedSpace.globalSectionsFunctor T.toRingedSpace).obj M) :=
  ModuleCat.isModule ((RingedSpace.globalSectionsFunctor T.toRingedSpace).obj M)

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
/-- Module sheaves have enough injectives, with the existing proof for this ringed space. -/
local instance coherentEdge_enoughInjectives (T : Scheme.{u}) : EnoughInjectives T.Modules :=
  (RingedSpace.moduleSheaves_abelian_enoughInjectives T.toRingedSpace).2

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem coherentEdge_semilinear_natTrans
    {R S : Type*} [Ring R] [Ring S] {C : Type*} [Category C]
    (F : C ⥤ ModuleCat R) (G : C ⥤ ModuleCat S)
    (ε : F ⋙ forget₂ _ AddCommGrpCat ⟶ G ⋙ forget₂ _ AddCommGrpCat)
    (M : C) (a : M ⟶ M) (r : S) (t : R)
    (hF : ∀ x : F.obj M, F.map a x = t • x)
    (hG : ∀ y : G.obj M, G.map a y = r • y) (x : F.obj M) :
    ε.app M (t • x) = r • (show G.obj M from ε.app M x) := by
  calc
    _ = ε.app M (F.map a x) := congrArg (fun y ↦ ε.app M y) (hF x).symm
    _ = G.map a (ε.app M x) := CategoryTheory.congr_fun (ε.naturality a) x
    _ = _ := hG _

attribute [local irreducible] Functor.rightDerivedFunctor
  DerivedCategory.homologyFunctor DerivedCategory instCategoryDerivedCategory

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
local instance coherentEdge_pullbackSectionsModule {S T : Scheme.{u}} (g : T ⟶ S)
    (M : SheafOfModules.{u} (moduleRings S.toRingedSpace)) :
    Module Γ(T, ⊤) ((RingedSpace.globalSectionsFunctor T.toRingedSpace).obj
      ((Scheme.Modules.tensorPullback g).obj M)) :=
  coherentEdge_sectionsModule T ((Scheme.Modules.tensorPullback g).obj M)

private theorem coherentEdge_isLE_of_locally_split
    {S : Scheme.{u}} (K : schemeDerivedCategory S) (A E : S.Modules)
    (hsplit : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ Nonempty
      ((schemeOpenRestriction S U).mapDerivedCategory.obj K ≅
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj
            ((schemeOpenRestriction S U).obj A) ⊞
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 1).obj
            ((schemeOpenRestriction S U).obj E))) : K.IsLE 1 := by
  classical
  choose U hU e using hsplit
  have hcover : ⨆ s, U s = ⊤ := by
    apply eq_top_iff.mpr
    intro s _
    exact Opens.mem_iSup.mpr ⟨s, hU s⟩
  apply (DerivedCategory.isLE_iff K 1).mpr
  intro i hi
  apply Scheme.Modules.isZero_of_iSup_eq_top _ U hcover
  intro s
  let R := schemeOpenRestriction S (U s)
  let A₀ := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings (U s).toScheme.toRingedSpace)) 0).obj (R.obj A)
  let E₁ := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings (U s).toScheme.toRingedSpace)) 1).obj (R.obj E)
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (U s).toScheme.toRingedSpace)) i
  let t := DerivedCategory.TStructure.t
    (C := SheafOfModules.{u} (moduleRings (U s).toScheme.toRingedSpace))
  have hsum : (A₀ ⊞ E₁).IsLE 1 :=
    t.isLE₂ (Pretriangulated.binaryBiproductTriangle A₀ E₁)
      (Pretriangulated.binaryBiproductTriangle_distinguished A₀ E₁) 1
      (t.isLE_of_le A₀ 0 1 (by omega)) (by
        change E₁.IsLE 1
        dsimp only [E₁]
        infer_instance)
  have hle : (R.mapDerivedCategory.obj K).IsLE 1 := by
    let := hsum
    exact t.isLE_of_iso (e s).some.symm 1
  let := hle
  have hz : IsZero (H.obj (R.mapDerivedCategory.obj K)) :=
    DerivedCategory.isZero_of_isLE _ 1 i hi
  exact hz.of_iso
    (((R.mapDerivedCategoryHomologyFunctorIso i).app K).symm ≪≫
      (Scheme.Modules.overFunctorEquiv (U s)).app
        ((DerivedCategory.homologyFunctor _ i).obj K)).symm

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem coherentEdge_isLE_of_iso
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
    {K L : DerivedCategory A} (a : K ⟶ L) [IsIso a] (n : ℤ)
    (hK : K.IsLE n) : L.IsLE n := by
  let := hK
  exact (DerivedCategory.TStructure.t (C := A)).isLE_of_iso (asIso a) n

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem coherentEdge_topProjection_normalized
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : DerivedCategory A) (hK : K.IsLE 1) :
    (DerivedCategory.homologyFunctor A 1).map
        (derivedTopTruncationProjection 1 K hK) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso A 1).hom.app _ = 𝟙 _ := by
  let := hK
  have h := (Equiv.ofBijective _
    (DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE
      (X := K) (Y := (DerivedCategory.singleFunctor A 1).obj
        ((DerivedCategory.homologyFunctor A 1).obj K)) 1)).apply_symm_apply
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso A 1).inv.app
            ((DerivedCategory.homologyFunctor A 1).obj K))
  change (DerivedCategory.homologyFunctor A 1).map
    (derivedTopTruncationProjection 1 K hK) = _ at h
  rw [h]
  exact Iso.inv_hom_id_app _ _

private theorem coherentEdgeGamma_eq_top
    {S T : Scheme.{u}} (g : T ⟶ S) (K : schemeDerivedCategory S) (hK : K.IsLE 1) :
    coherentEdgeGamma g K (derivedTopTruncationProjection 1 K hK) =
      derivedPullbackTopCohomology g 1 K hK := by
  simp only [coherentEdgeGamma, derivedPullbackTopCohomology, Functor.map_comp]
  rfl

private theorem coherentEdgeGamma_isIso
    {S T : Scheme.{u}} (g : T ⟶ S) (K : schemeDerivedCategory.{u, w} S)
    (hK : K.IsLE 1) :
    IsIso (coherentEdgeGamma.{u, w} g K (derivedTopTruncationProjection 1 K hK)) := by
  rw [coherentEdgeGamma_eq_top]
  exact (Classical.choose_spec (derivedPullback_topCohomology.{u, w} g 1 K hK)).2.1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coherentEdgeEpsilon_smul
  {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules)
  (r : Γ(S, ⊤)) (x : topDegreeCohomologyOnBase f G) :
  coherentEdgeEpsilon.{u, w} f G (r • x) =
    r • (show (RingedSpace.globalSectionsFunctor S.toRingedSpace).obj
      (coherentEdgeCohomology.{u, w} f G 1) from coherentEdgeEpsilon.{u, w} f G x) := by
  with_unfolding_all
    classical
    let ε := topDegreeClassicalLerayEdge f 1
    let x₀ : (RingedSpace.moduleCohomology X.toRingedSpace 1).obj G := x
    let a := Scheme.Modules.smulHom G (f.appTop r)
    have hn := coherentEdge_semilinear_natTrans
      (RingedSpace.moduleCohomology X.toRingedSpace 1)
      ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived 1 ⋙
        RingedSpace.globalSectionsFunctor S.toRingedSpace)
      ε G a r (f.appTop r)
      (fun y ↦ Scheme.Modules.moduleCohomology_map_smulHom G (injectiveResolution G) 1
        (f.appTop r) y)
      (fun y ↦ by
        have hd := Scheme.Modules.higherDirectImage_map_smulHom f 1 G r
        exact (congrArg (fun k ↦
          (RingedSpace.globalSectionsFunctor S.toRingedSpace).map k y) hd).trans
            (Scheme.Modules.smulHom_app_top_apply _ r y)) x₀
    let b :
        (RingedSpace.globalSectionsFunctor S.toRingedSpace).obj
          (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived 1).obj G) ⟶
        (RingedSpace.globalSectionsFunctor S.toRingedSpace).obj
          (coherentEdgeCohomology.{u, w} f G 1) :=
      (RingedSpace.globalSectionsFunctor S.toRingedSpace).map
        (topDegreeLerayComparison.{u, w} f G).inv
    unfold coherentEdgeEpsilon topDegreeLerayEdge
    change b (ε.app G (f.appTop r • x₀)) = r • b (ε.app G x₀)
    exact (congrArg (fun y ↦ b y) hn).trans (b.hom.map_smul r _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def coherentEdge_linearMap {Y T : Scheme.{u}} (q : Y ⟶ T) (F : Y.Modules) :
    (topDegreeCohomologyOnBase q F) →ₗ[Γ(T, ⊤)]
        (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj
          (coherentEdgeCohomology.{u, w} q F 1) where
  toFun x := coherentEdgeEpsilon.{u, w} q F x
  map_add' x y := (coherentEdgeEpsilon.{u, w} q F).hom.map_add x y
  map_smul' r x := coherentEdgeEpsilon_smul q F r x

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private def coherentEdge_equivOfBijective
    {R A B : Type*} [CommRing R] [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] (l : A →ₗ[R] B) (hl : Function.Bijective l) : A ≃ₗ[R] B :=
  LinearEquiv.ofBijective l hl

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem coherentEdge_equivOfBijective_apply
    {R A B : Type*} [CommRing R] [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] (l : A →ₗ[R] B) (hl : Function.Bijective l) (x : A) :
    coherentEdge_equivOfBijective l hl x = l x := rfl

attribute [local irreducible] coherentEdge_equivOfBijective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def coherentEdge_linearEquiv {Y T : Scheme.{u}} (q : Y ⟶ T) (F : Y.Modules)
    {M : T.Modules} (β : M ≅ coherentEdgeCohomology.{u, w} q F 1)
    (hε : IsIso (coherentEdgeEpsilon.{u, w} q F)) :
    (topDegreeCohomologyOnBase q F) ≃ₗ[Γ(T, ⊤)]
        (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj M := by
  let A : ModuleCat.{u} Γ(T, ⊤) := topDegreeCohomologyOnBase q F
  let B : ModuleCat.{u} Γ(T, ⊤) :=
    (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj
      (coherentEdgeCohomology.{u, w} q F 1)
  let C : ModuleCat.{u} Γ(T, ⊤) :=
    (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj M
  let b : B ⟶ C := (RingedSpace.globalSectionsFunctor T.toRingedSpace).map β.inv
  let l : A →ₗ[Γ(T, ⊤)] C := b.hom.comp (coherentEdge_linearMap q F)
  apply coherentEdge_equivOfBijective l
  change Function.Bijective (fun x : A ↦ b (coherentEdgeEpsilon.{u, w} q F x))
  let : IsIso b := Functor.map_isIso _ _
  let := hε
  exact (ConcreteCategory.bijective_of_isIso b).comp
    (ConcreteCategory.bijective_of_isIso (coherentEdgeEpsilon.{u, w} q F))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coherentEdge_linearEquiv_apply {Y T : Scheme.{u}}
    (q : Y ⟶ T) (F : Y.Modules) {M : T.Modules}
    (β : M ≅ coherentEdgeCohomology.{u, w} q F 1)
    (hε : IsIso (coherentEdgeEpsilon.{u, w} q F))
    (x : topDegreeCohomologyOnBase q F) :
    coherentEdge_linearEquiv q F β hε x =
      (RingedSpace.globalSectionsFunctor T.toRingedSpace).map β.inv
        (coherentEdgeEpsilon.{u, w} q F x) := by
  unfold coherentEdge_linearEquiv
  rw [coherentEdge_equivOfBijective_apply]
  rfl

attribute [local irreducible] coherentEdge_linearMap coherentEdge_linearEquiv

private theorem coherentEdgeEpsilon_isIso
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] [IsAffine S]
    (G : X.Modules) [G.IsQuasicoherent] : IsIso (coherentEdgeEpsilon f G) := by
  with_unfolding_all
    classical
    unfold coherentEdgeEpsilon topDegreeLerayEdge
    apply IsIso.comp_isIso'
    · exact topDegreeClassicalLerayEdge_isIso f G 1
        (fun q p hp ↦ isZero_affine_higherDirectImage_moduleCohomology f G
          inferInstance q p hp)
    · exact Functor.map_isIso _ _

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem coherentEdgeSectionPullback_naturality
    {T T' : Scheme.{u}} (h : T' ⟶ T) {M N : T.Modules} (a : M ⟶ N)
    (s : (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj M) :
    coherentEdgeSectionPullback h N (Scheme.Modules.Hom.app a ⊤ s) =
      Scheme.Modules.Hom.app ((Scheme.Modules.tensorPullback h).map a) ⊤
        (coherentEdgeSectionPullback h M s) := by
  let adj := Scheme.Modules.tensorPullbackSectionAdjunction h
  have hu := congrArg (fun b ↦ Scheme.Modules.Hom.app b ⊤ s) (adj.unit.naturality a)
  change Scheme.Modules.Hom.app (adj.unit.app N) ⊤ (Scheme.Modules.Hom.app a ⊤ s) =
    Scheme.Modules.Hom.app ((Scheme.Modules.tensorPullback h).map a) (h ⁻¹ᵁ ⊤)
      (Scheme.Modules.Hom.app (adj.unit.app M) ⊤ s) at hu
  unfold coherentEdgeSectionPullback topDegreeSectionPullback
  rw [hu]
  exact CategoryTheory.congr_fun
    (((PresheafOfModules.toPresheaf _).map
      ((Scheme.Modules.tensorPullback h).map a).val).naturality
        (eqToHom (congrArg op (Opens.map_top h.base).symm)))
    (Scheme.Modules.Hom.app (adj.unit.app M) ⊤ s) |>.symm

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem coherentEdge_sections_map_apply {T : Scheme.{u}} {M N : T.Modules}
    (a : M ⟶ N) (s : (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj M) :
    (RingedSpace.globalSectionsFunctor T.toRingedSpace).map a s =
      Scheme.Modules.Hom.app a ⊤ s := rfl

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem coherentEdgeRho_eq_sectionsMap
    {S T T' : Scheme.{u}} (g : T ⟶ S) (h : T' ⟶ T) (E : S.Modules)
    (s : (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj
      ((Scheme.Modules.tensorPullback g).obj E)) :
    coherentEdgeRho g h E s =
      (RingedSpace.globalSectionsFunctor T'.toRingedSpace).map
        ((Scheme.Modules.tensorPullbackSectionComp h g).inv.app E)
        (coherentEdgeSectionPullback h ((Scheme.Modules.tensorPullback g).obj E) s) := rfl

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem coherentEdge_sections_square {T T' : Scheme.{u}} (h : T' ⟶ T)
    {M N : T.Modules} {M' N' : T'.Modules} (β : M ≅ N) (β' : M' ≅ N')
    (b : (Scheme.Modules.tensorPullback h).obj N ⟶ N')
    (c : (Scheme.Modules.tensorPullback h).obj M ⟶ M')
    (hb : b ≫ β'.inv = (Scheme.Modules.tensorPullback h).map β.inv ≫ c)
    (z : (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj N)
    (z' : (RingedSpace.globalSectionsFunctor T'.toRingedSpace).obj N')
    (hz : z' = (RingedSpace.globalSectionsFunctor T'.toRingedSpace).map b
      (coherentEdgeSectionPullback h N z)) :
    (RingedSpace.globalSectionsFunctor T'.toRingedSpace).map β'.inv z' =
      (RingedSpace.globalSectionsFunctor T'.toRingedSpace).map c
        (coherentEdgeSectionPullback h M
          ((RingedSpace.globalSectionsFunctor T.toRingedSpace).map β.inv z)) := by
  simp only [coherentEdge_sections_map_apply] at hz ⊢
  rw [hz, coherentEdgeSectionPullback_naturality]
  exact congrArg (fun a ↦ Scheme.Modules.Hom.app a ⊤
    (coherentEdgeSectionPullback h N z)) hb

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem coherentEdgeCoefficient_quasicoherent
    {X S T : Scheme.{u}} (f : X ⟶ S) (G : X.Modules) [G.IsQuasicoherent]
    (g : T ⟶ S) : (coherentEdgeCoefficient f G g).IsQuasicoherent := by
  let e := (Scheme.Modules.tensorPullbackSectionAdjunction (pullback.fst f g)).leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction (pullback.fst f g))
  exact (SheafOfModules.isQuasicoherent (pullback f g).ringCatSheaf).prop_of_iso
    (e.app G).symm (Scheme.Modules.isQuasicoherent_pullback (pullback.fst f g) G)

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem coherentEdge_map_square
    {C D : Type*} [Category C] [Category D] (H : C ⥤ D)
    {A B B' E : C} (a : A ⟶ B) (b : B ⟶ E) (c : A ⟶ B') (d : B' ⟶ E)
    (hp : a ≫ b = c ≫ d) : H.map a ≫ H.map b = H.map c ≫ H.map d :=
  (H.map_comp a b).symm.trans ((congrArg H.map hp).trans (H.map_comp c d))

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem coherentEdge_comparison_inverse
    {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {E F : C} {E' F' : D} (β : E ≅ F) (β' : E' ≅ F')
    (b : P.obj F ⟶ F') (c : P.obj E ⟶ E')
    (hb : P.map β.hom ≫ b = c ≫ β'.hom) :
    b ≫ β'.inv = P.map β.inv ≫ c := by
  apply (cancel_epi (P.map β.hom)).1
  rw [← Category.assoc, hb]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    ← P.map_comp_assoc, Iso.hom_inv_id, P.map_id, Category.id_comp]

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem coherentEdge_comparison_square
    {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {A B E : C} {A' B' C' E' F' : D}
    (k₁ : A' ⟶ P.obj A) (k₂ : B' ⟶ P.obj B) (kg : A ⟶ E) (kgh : C' ⟶ E')
    [IsIso k₁] [IsIso k₂] [IsIso kg]
    (d : A ⟶ B) (d' : C' ⟶ F') (ld : A' ⟶ B') (cc : A' ⟶ C') (m : B' ⟶ F')
    (c : P.obj E ⟶ E') (β : E ≅ B) (β' : E' ≅ F')
    (hβ : kg ≫ β.hom = d) (hβ' : kgh ≫ β'.hom = d')
    (hn : ld ≫ k₂ = k₁ ≫ P.map d)
    (hc : cc ≫ kgh = k₁ ≫ P.map kg ≫ c) (hp : ld ≫ m = cc ≫ d') :
    (inv k₂ ≫ m) ≫ β'.inv = P.map β.inv ≫ c := by
  have hb : P.map β.hom ≫ (inv k₂ ≫ m) = c ≫ β'.hom := by
    apply (cancel_epi (k₁ ≫ P.map kg)).1
    calc
      _ = k₁ ≫ P.map d ≫ inv k₂ ≫ m := by
        simp only [Category.assoc, ← P.map_comp_assoc, hβ]
      _ = ld ≫ m := by rw [← reassoc_of% hn]; simp
      _ = cc ≫ d' := hp
      _ = _ := by rw [← hβ', ← Category.assoc, hc]; simp only [Category.assoc]
  exact coherentEdge_comparison_inverse P β β' (inv k₂ ≫ m) c hb

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private def coherentEdge_comparisonIsoRaw
    {C : Type*} [Category C] {A B E : C}
    (γ : A ⟶ E) (d : A ⟶ B) [IsIso γ] [IsIso d] : E ≅ B :=
  (asIso γ).symm ≪≫ asIso d

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem coherentEdge_comparisonIsoRaw_normalized
    {C : Type*} [Category C] {A B E : C}
    (γ : A ⟶ E) (d : A ⟶ B) [IsIso γ] [IsIso d] :
    γ ≫ (coherentEdge_comparisonIsoRaw γ d).hom = d := by
  simp only [coherentEdge_comparisonIsoRaw, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, asIso_inv, IsIso.hom_inv_id_assoc]

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem coherentEdge_comparisonIso_existsUnique
    {C : Type*} [Category C] {A B E : C}
    (γ : A ⟶ E) (d : A ⟶ B) [IsIso γ] [IsIso d] :
    ∃! β : E ≅ B, γ ≫ β.hom = d := by
  refine ⟨coherentEdge_comparisonIsoRaw γ d,
    coherentEdge_comparisonIsoRaw_normalized γ d, ?_⟩
  intro β hβ
  apply Iso.ext
  apply (cancel_epi γ).1
  exact hβ.trans (coherentEdge_comparisonIsoRaw_normalized γ d).symm

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
/-- The normalized comparison uniquely determines the isomorphism. Existence is
proved by the explicit inverse-and-composition construction above. -/
private def coherentEdge_comparisonIso
    {C : Type*} [Category C] {A B E : C}
    (γ : A ⟶ E) (d : A ⟶ B) [IsIso γ] [IsIso d] : E ≅ B :=
  Classical.choose (coherentEdge_comparisonIso_existsUnique γ d)

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem coherentEdge_comparisonIso_normalized
    {C : Type*} [Category C] {A B E : C}
    (γ : A ⟶ E) (d : A ⟶ B) [IsIso γ] [IsIso d] :
    γ ≫ (coherentEdge_comparisonIso γ d).hom = d := by
  exact (Classical.choose_spec (coherentEdge_comparisonIso_existsUnique γ d)).1

attribute [local irreducible] coherentEdge_comparisonIso

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coherentEdge_pullback_isLE {S T : Scheme.{u}} (g : T ⟶ S)
    (K : schemeDerivedCategory.{u, w} S) (hK : K.IsLE 1) :
    ((derivedPullback.{u, w} g).obj K).IsLE 1 :=
  Classical.choose (derivedPullback_topCohomology.{u, w} g 1 K hK)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coherentEdge_top_isIso {S T : Scheme.{u}} (g : T ⟶ S)
    (K : schemeDerivedCategory.{u, w} S) (hK : K.IsLE 1) :
    IsIso (derivedPullbackTopCohomology.{u, w} g 1 K hK) :=
  (Classical.choose_spec (derivedPullback_topCohomology.{u, w} g 1 K hK)).2.1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coherentEdge_top_naturality {S T : Scheme.{u}} (g : T ⟶ S)
    (C D : schemeDerivedCategory.{u, w} S) (hC : C.IsLE 1) (hD : D.IsLE 1)
    (a : C ⟶ D) :
    ((DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 1)).map
        ((derivedPullback.{u, w} g).map a) ≫
          derivedPullbackTopCohomology.{u, w} g 1 D hD =
      derivedPullbackTopCohomology.{u, w} g 1 C hC ≫
        (Scheme.Modules.tensorPullback g).map
          (((DerivedCategory.homologyFunctor.{w, u, u + 1}
            (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1)).map a) :=
  (Classical.choose_spec
    (derivedPullback_topCohomology.{u, w} g 1 C hC)).2.2.1 D hD a

/-- The existing composition comparison, with its object type fixed before projections.
Its source theorem fixes the hom component by the derived lift formula and hence fixes
this isomorphism uniquely. -/
private def coherentEdge_pullbackComp
    {S T T' : Scheme.{u}} (g : T ⟶ S) (h : T' ⟶ T) :
    derivedPullback.{u, w} g ⋙ derivedPullback.{u, w} h ≅
      derivedPullback.{u, w} (h ≫ g) := by
  letI := @Classical.choose _ _ exists_derivedPullbackComposition.{u, w}
  exact pinnedPullbackComposition h g

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coherentEdge_top_comp
    {S T T' : Scheme.{u}} (g : T ⟶ S) (h : T' ⟶ T)
    (C : schemeDerivedCategory.{u, w} S) (hC : C.IsLE 1) :
    let hbound := Classical.choose (derivedPullback_topCohomology.{u, w} g 1 C hC)
    ((DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) 1)).map
        ((coherentEdge_pullbackComp.{u, w} g h).hom.app C) ≫
        derivedPullbackTopCohomology.{u, w} (h ≫ g) 1 C hC =
      derivedPullbackTopCohomology.{u, w} h 1 ((derivedPullback.{u, w} g).obj C) hbound ≫
        (Scheme.Modules.tensorPullback h).map
          (derivedPullbackTopCohomology.{u, w} g 1 C hC) ≫
        (Scheme.Modules.tensorPullbackSectionComp h g).inv.app
          (((DerivedCategory.homologyFunctor.{w, u, u + 1}
            (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1)).obj C) := by
  exact (Classical.choose_spec
    (derivedPullback_topCohomology.{u, w} g 1 C hC)).2.2.2 T' h


private theorem coherentEdge_typed_pasting
    {X S Y T Z U : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (h : U ⟶ T)
    (p : Y ⟶ X) (q : Y ⟶ T) (t : Z ⟶ Y) (r : Z ⟶ U) (p₀ : Z ⟶ X)
    (hs : p ≫ f = q ≫ g) (hi : t ≫ q = r ≫ h) (hp : t ≫ p = p₀)
    (ho : p₀ ≫ f = r ≫ (h ≫ g)) (G : X.Modules) :
    let e := ((Scheme.Modules.tensorPullbackSectionComp t p).symm.app G) ≪≫
      @eqToIso Z.Modules (@Scheme.Modules.instCategory Z) _ _
        (congrArg (fun k ↦ (Scheme.Modules.tensorPullback k).obj G) hp)
    (derivedPullback.{u, w} h).map (topDegreeTensorBaseChange f q g p hs G) ≫
        topDegreeBaseChangeMap q r h t hi ((Scheme.Modules.tensorPullback p).obj G)
          ((Scheme.Modules.tensorPullback p₀).obj G) e.hom =
      (coherentEdge_pullbackComp g h).hom.app (topDegreeDerivedImage f G) ≫
        topDegreeTensorBaseChange f r (h ≫ g) p₀ ho G := by
  have raw := tensorSingleBaseChange_pasting.{u, w} f g h p q t r p₀ hs hi hp ho G
  simp only [topDegreeBaseChangeMap, topDegreeTensorBaseChange,
    singleDegreeBaseChangeSource, coherentEdge_pullbackComp, pinnedPullbackComposition,
    perfectHomComposition,
    Functor.comp_obj] at raw ⊢
  delta topDegreeDerivedImage globalLerayImage
  try delta singleDegreeBaseChangeTarget at raw
  dsimp only [Functor.comp_obj] at raw ⊢
  exact raw

set_option allowUnsafeReducibility true in
attribute [local irreducible] coherentEdgeDelta coherentEdgeCoefficient coherentEdgeXMap

attribute [local irreducible] coherentEdge_pullbackComp
  derivedPullbackTopCohomology RingedSpace.globalSectionsFunctor
  coherentEdgeGamma coherentEdgeCoefficientIso
  coherentEdgeRho

set_option allowUnsafeReducibility true in
attribute [local reducible] Scheme.Modules Scheme.Modules.Hom

set_option allowUnsafeReducibility true in
attribute [local instance_reducible] Scheme.Modules.instCategory Scheme.Modules.instAbelian

set_option allowUnsafeReducibility true in
attribute [local irreducible] pullback schemeDerivedDirectImage

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coherentEdge_comparisons_exist
    {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules)
    (hK : (coherentEdgeK.{u, w} f G).IsLE 1)
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (coherentEdgeDelta.{u, w} f G g)) :
    ∃ β : ∀ (T : Scheme.{u}) (g : T ⟶ S),
        (Scheme.Modules.tensorPullback g).obj (coherentEdgeCohomology.{u, w} f G 1) ≅
          coherentEdgeCohomology (pullback.snd f g) (coherentEdgeCoefficient f G g) 1,
      ∀ (T : Scheme.{u}) (g : T ⟶ S),
        coherentEdgeGamma g (coherentEdgeK f G)
            (derivedTopTruncationProjection 1 (coherentEdgeK f G) hK) ≫ (β T g).hom =
          ((DerivedCategory.homologyFunctor.{w, u, u + 1}
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 1)).map
              (coherentEdgeDelta.{u, w} f G g) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  first
  | let β (T : Scheme.{u}) (g : T ⟶ S) := by
      let : IsIso (coherentEdgeGamma.{u, w} g (coherentEdgeK.{u, w} f G)
          (derivedTopTruncationProjection 1 (coherentEdgeK f G) hK)) :=
        coherentEdgeGamma_isIso g (coherentEdgeK f G) hK
      let : IsIso (coherentEdgeDelta.{u, w} f G g) := hbc T g
      let H := (DerivedCategory.homologyFunctor.{w, u, u + 1}
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 1)
      let : IsIso (H.map (coherentEdgeDelta.{u, w} f G g)) :=
        @Functor.map_isIso _ _ _ _ _ _ H (coherentEdgeDelta.{u, w} f G g) (hbc T g)
      exact coherentEdge_comparisonIso
        (coherentEdgeGamma.{u, w} g (coherentEdgeK.{u, w} f G)
          (derivedTopTruncationProjection 1 (coherentEdgeK f G) hK))
        (H.map (coherentEdgeDelta.{u, w} f G g))
    refine ⟨β, ?_⟩
    intro T g
    let : IsIso (coherentEdgeGamma.{u, w} g (coherentEdgeK.{u, w} f G)
        (derivedTopTruncationProjection 1 (coherentEdgeK f G) hK)) :=
      coherentEdgeGamma_isIso g (coherentEdgeK f G) hK
    let : IsIso (coherentEdgeDelta.{u, w} f G g) := hbc T g
    let H := (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 1)
    let : IsIso (H.map (coherentEdgeDelta.{u, w} f G g)) :=
        @Functor.map_isIso _ _ _ _ _ _ H (coherentEdgeDelta.{u, w} f G g) (hbc T g)
    exact coherentEdge_comparisonIso_normalized _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coherentEdge_linearEquivs_exist
    {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules)
    (β : ∀ (T : Scheme.{u}) (g : T ⟶ S),
      (Scheme.Modules.tensorPullback g).obj (coherentEdgeCohomology.{u, w} f G 1) ≅
        coherentEdgeCohomology (pullback.snd f g) (coherentEdgeCoefficient f G g) 1)
    (hε : ∀ (T : Scheme.{u}) (g : T ⟶ S) (_ : IsAffine T),
      IsIso (coherentEdgeEpsilon.{u, w} (pullback.snd f g) (coherentEdgeCoefficient f G g))) :
    ∃ e : ∀ (T : Scheme.{u}) (g : T ⟶ S) (_ : IsAffine T),
        coherentEdgeH f G g ≃ₗ[Γ(T, ⊤)]
          (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj
            ((Scheme.Modules.tensorPullback g).obj (coherentEdgeCohomology.{u, w} f G 1)),
      ∀ (T : Scheme.{u}) (g : T ⟶ S) (hT : IsAffine T) (x : coherentEdgeH f G g),
        e T g hT x = (RingedSpace.globalSectionsFunctor T.toRingedSpace).map (β T g).inv
          (coherentEdgeEpsilon.{u, w} (pullback.snd f g) (coherentEdgeCoefficient f G g) x) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  first
  | refine ⟨fun T g hT ↦ coherentEdge_linearEquiv (pullback.snd f g)
      (coherentEdgeCoefficient f G g) (β T g) (hε T g hT), ?_⟩
    intro T g hT x
    exact coherentEdge_linearEquiv_apply _ _ _ _ x

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem coherentEdgePullback_eq {X S T U : Scheme.{u}}
    (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S) (h : U ⟶ T) :
    coherentEdgePullback f G g h = topDegreeCohomologyPullback (pullback.snd f g)
      (pullback.snd f (h ≫ g)) (coherentEdgeXMap f g h)
      (coherentEdgeCoefficient f G g) (coherentEdgeCoefficient f G (h ≫ g))
      (coherentEdgeCoefficientIso f G g h).hom := rfl

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem coherentEdgeXMap_snd {X S T U : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (h : U ⟶ T) :
    coherentEdgeXMap f g h ≫ pullback.snd f g = pullback.snd f (h ≫ g) ≫ h := by
  simp [coherentEdgeXMap, baseChangeMap, pullback.map, pullback.lift_snd]

omit [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] in
private theorem coherentEdgeXMap_fst {X S T U : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (h : U ⟶ T) :
    coherentEdgeXMap f g h ≫ pullback.fst f g = pullback.fst f (h ≫ g) := by
  simp [coherentEdgeXMap, baseChangeMap, pullback.map, pullback.lift_fst]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def coherentEdge_arrowDelta {X S T U : Scheme.{u}}
    (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S) (h : U ⟶ T) :
    (derivedPullback.{u, w} h).obj
        (coherentEdgeK (pullback.snd f g) (coherentEdgeCoefficient f G g)) ⟶
      coherentEdgeK (pullback.snd f (h ≫ g)) (coherentEdgeCoefficient f G (h ≫ g)) :=
  topDegreeBaseChangeMap (pullback.snd f g) (pullback.snd f (h ≫ g)) h
    (coherentEdgeXMap f g h) (coherentEdgeXMap_snd f g h)
    (coherentEdgeCoefficient f G g) (coherentEdgeCoefficient f G (h ≫ g))
    (coherentEdgeCoefficientIso f G g h).hom

private theorem coherentEdge_arrowDelta_eq {X S T U : Scheme.{u}}
    (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S) (h : U ⟶ T) :
    coherentEdge_arrowDelta.{u, w} f G g h =
      topDegreeBaseChangeMap (pullback.snd f g) (pullback.snd f (h ≫ g)) h
        (coherentEdgeXMap f g h) (coherentEdgeXMap_snd f g h)
        (coherentEdgeCoefficient f G g) (coherentEdgeCoefficient f G (h ≫ g))
        (coherentEdgeCoefficientIso f G g h).hom := rfl

attribute [local irreducible] coherentEdge_arrowDelta

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coherentEdge_arrowDelta_pasting {X S T U : Scheme.{u}}
    (f : X ⟶ S) (G : X.Modules) (g : T ⟶ S) (h : U ⟶ T) :
    (derivedPullback.{u, w} h).map (coherentEdgeDelta.{u, w} f G g) ≫
        coherentEdge_arrowDelta f G g h =
      (coherentEdge_pullbackComp g h).hom.app (coherentEdgeK f G) ≫
        coherentEdgeDelta.{u, w} f G (h ≫ g) := by
  have raw := coherentEdge_typed_pasting.{u, w} f g h (pullback.fst f g)
    (pullback.snd f g) (coherentEdgeXMap f g h) (pullback.snd f (h ≫ g))
    (pullback.fst f (h ≫ g)) pullback.condition (coherentEdgeXMap_snd f g h)
    (coherentEdgeXMap_fst f g h) pullback.condition G
  simpa only [coherentEdge_arrowDelta, coherentEdgeDelta, coherentEdgeCoefficientIso,
    coherentEdgeCoefficient, coherentEdgeK] using raw

/-- The existing sheafification adjoints on slice sites, cached for module predicates.
Source: Mathlib concrete sheafification; Stacks, Tag 007X
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
local instance (priority := 2000) coherentEdge_overSheafify (S : Type u) [TopologicalSpace S] :
    ∀ U : Opens S,
      HasWeakSheafify ((Opens.grothendieckTopology S).over U) AddCommGrpCat.{u} :=
  fun U ↦ sheafToPresheaf_isRightAdjoint ((Opens.grothendieckTopology S).over U)
    AddCommGrpCat.{u}

/-- The existing local-bijection criterion on slice sites, cached for module predicates.
Source: Mathlib concrete sheafification; Stacks, Tag 007X
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality). -/
local instance (priority := 2000) coherentEdge_overLocalBijective
    (S : Type u) [TopologicalSpace S] :
    ∀ U : Opens S,
      ((Opens.grothendieckTopology S).over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  fun U ↦
    let J := (Opens.grothendieckTopology S).over U
    letI : ∀ P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u},
        Presheaf.IsLocallyInjective J (toSheafify J P) :=
      fun P ↦ Presheaf.isLocallyInjective_toSheafify' J P
    letI : ∀ P : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{u},
        Presheaf.IsLocallySurjective J (toSheafify J P) :=
      fun P ↦ Presheaf.isLocallySurjective_toSheafify' J P
    GrothendieckTopology.WEqualsLocallyBijective.mk' J AddCommGrpCat.{u}

set_option allowUnsafeReducibility true in
attribute [local reducible] coherentEdge_sectionsModule coherentEdge_pullbackSectionsModule

attribute [local irreducible] derivedTopTruncationProjection
  Scheme.Modules.tensorPullbackSectionComp Scheme.Modules.tensorPullbackSectionAdjunction

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- For a quasi-compact separated map with a universally base-change-compatible derived
image locally split into finite locally free terms in degrees zero and one, the normalized
truncation projection yields simultaneous linear affine Leray isomorphisms compatible
with every arrow of affine base schemes. The identity on degree-one cohomology specifies
its canonical truncation projection; its existence is part of the conclusion.
Source: Stacks Project, Cohomology, Tags 0ATM, 01FB, 01F8 and 01F2.
(blueprint: lem-weil-pbc-coherent-affine-base-change-edge-naturality).

Proof:
1. The local splitting shows the derived image is in D≤1: cohomology above one
vanishes on each splitting open, hence globally. The homology bijection for maps
from D≤1 to a single module in degree one constructs the normalized top projection.
2. The top-cohomology pullback theorem identifies gamma with its canonical comparison
and makes it invertible. The base-change hypothesis then makes beta invertible.
3. Quasi-coherence of the pulled coefficient and qcqs affine higher-image vanishing
make the specified Leray edge invertible. Naturality under scalar multiplication
makes this edge linear over the base ring. Compose it with sections of beta inverse.
4. Normalized tensor single-module horizontal pasting, with the specified coefficient
isomorphism, identifies the composite base-change maps. Naturality and composition
of the top comparison give the corresponding composition equation for beta.
5. The top-degree Leray square identity identifies the action on cohomology classes
with sections of the top derived base-change map after section pullback.
6. Cancel beta on the target and use its composition equation. Naturality of the
normalized pullback unit moves beta inverse across section pullback. The ordinary
composition comparison gives exactly rho, simultaneously for all base arrows. -/
theorem coherent_affine_base_change_edge_naturality
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [IsSeparated f]
    (G : X.Modules) [G.IsQuasicoherent]
    [SheafOfModules.IsFiniteLocallyFree (coherentEdgeCohomology f G 0)]
    [SheafOfModules.IsFiniteLocallyFree (coherentEdgeCohomology f G 1)]
    (hsplit : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ Nonempty
      ((schemeOpenRestriction S U).mapDerivedCategory.obj (coherentEdgeK f G) ≅
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj
            ((schemeOpenRestriction S U).obj (coherentEdgeCohomology f G 0)) ⊞
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 1).obj
            ((schemeOpenRestriction S U).obj (coherentEdgeCohomology f G 1))))
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S),
      IsIso (coherentEdgeDelta f G g)) :
    ∃ τ : coherentEdgeK f G ⟶ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1).obj
          (coherentEdgeCohomology f G 1),
      ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1).map τ ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 1).hom.app
            (coherentEdgeCohomology f G 1) = 𝟙 _) ∧
      (∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (coherentEdgeGamma g (coherentEdgeK f G) τ)) ∧
      ∃ β : ∀ (T : Scheme.{u}) (g : T ⟶ S),
          (Scheme.Modules.tensorPullback g).obj (coherentEdgeCohomology f G 1) ≅
            coherentEdgeCohomology (pullback.snd f g) (coherentEdgeCoefficient f G g) 1,
        (∀ (T : Scheme.{u}) (g : T ⟶ S),
          coherentEdgeGamma g (coherentEdgeK f G) τ ≫ (β T g).hom =
            (DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 1).map
                (coherentEdgeDelta f G g)) ∧
        ∃ e : ∀ (T : Scheme.{u}) (g : T ⟶ S) (_ : IsAffine T),
            coherentEdgeH f G g ≃ₗ[Γ(T, ⊤)]
              (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj
                ((Scheme.Modules.tensorPullback g).obj (coherentEdgeCohomology f G 1)),
          (∀ (T : Scheme.{u}) (g : T ⟶ S) (hT : IsAffine T),
            IsIso (coherentEdgeEpsilon (pullback.snd f g) (coherentEdgeCoefficient f G g)) ∧
            ∀ x : coherentEdgeH f G g,
              e T g hT x = (RingedSpace.globalSectionsFunctor T.toRingedSpace).map
                (β T g).inv
                  (coherentEdgeEpsilon (pullback.snd f g) (coherentEdgeCoefficient f G g) x)) ∧
          ∀ (T T' : Scheme.{u}) (g : T ⟶ S) (h : T' ⟶ T)
            (hT : IsAffine T) (hT' : IsAffine T') (x : coherentEdgeH f G g),
            e T' (h ≫ g) hT' (coherentEdgePullback f G g h x) =
              coherentEdgeRho g h (coherentEdgeCohomology f G 1) (e T g hT x) := by
  classical
  have hK := coherentEdge_isLE_of_locally_split (coherentEdgeK.{u, w} f G)
    (coherentEdgeCohomology.{u, w} f G 0) (coherentEdgeCohomology.{u, w} f G 1) hsplit
  let τ := derivedTopTruncationProjection 1 (coherentEdgeK.{u, w} f G) hK
  have hγ (T : Scheme.{u}) (g : T ⟶ S) :
      IsIso (coherentEdgeGamma.{u, w} g (coherentEdgeK.{u, w} f G) τ) := by
    exact coherentEdgeGamma_isIso g (coherentEdgeK.{u, w} f G) hK
  have hb := coherentEdge_comparisons_exist.{u, w} f G hK hbc
  obtain ⟨β, hβnorm⟩ := hb
  refine ⟨τ, ?_, ?_⟩
  · exact coherentEdge_topProjection_normalized
      (A := SheafOfModules.{u} (moduleRings S.toRingedSpace)) (coherentEdgeK f G) hK
  refine ⟨hγ, β, hβnorm, ?_⟩
  have hε (T : Scheme.{u}) (g : T ⟶ S) (hT : IsAffine T) :
      IsIso (coherentEdgeEpsilon.{u, w} (pullback.snd f g) (coherentEdgeCoefficient f G g)) := by
    let := hT
    let := coherentEdgeCoefficient_quasicoherent f G g
    exact coherentEdgeEpsilon_isIso (pullback.snd f g) (coherentEdgeCoefficient f G g)
  obtain ⟨e, he⟩ := coherentEdge_linearEquivs_exist f G β hε
  refine ⟨e, ?_, ?_⟩
  · intro T g hT
    exact ⟨hε T g hT, he T g hT⟩
  · intro T T' g h hT hT' x
    have hx := he T g hT x
    have hx' := he T' (h ≫ g) hT' (coherentEdgePullback f G g h x)
    let K : schemeDerivedCategory.{u, w} S := coherentEdgeK.{u, w} f G
    let Kg : schemeDerivedCategory.{u, w} T :=
      coherentEdgeK.{u, w} (pullback.snd f g) (coherentEdgeCoefficient f G g)
    let H := (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) 1)
    let P := Scheme.Modules.tensorPullback h
    let m := coherentEdge_arrowDelta.{u, w} f G g h
    have hpaste := coherentEdge_arrowDelta_pasting.{u, w} f G g h
    let hLg := coherentEdge_pullback_isLE g K hK
    have hKg : Kg.IsLE 1 := by
      let : IsIso (coherentEdgeDelta.{u, w} f G g) := hbc T g
      exact coherentEdge_isLE_of_iso
        (A := SheafOfModules.{u} (moduleRings T.toRingedSpace))
        (coherentEdgeDelta.{u, w} f G g) 1 hLg
    let κg := derivedPullbackTopCohomology.{u, w} g 1 K hK
    let κgh := derivedPullbackTopCohomology.{u, w} (h ≫ g) 1 K hK
    let κ₁ := derivedPullbackTopCohomology.{u, w} h 1
      ((derivedPullback.{u, w} g).obj K) hLg
    let κ₂ := derivedPullbackTopCohomology.{u, w} h 1 Kg hKg
    let : IsIso κg := coherentEdge_top_isIso g K hK
    let : IsIso κ₁ := coherentEdge_top_isIso h ((derivedPullback.{u, w} g).obj K) hLg
    let : IsIso κ₂ := coherentEdge_top_isIso h Kg hKg
    let b : P.obj (coherentEdgeCohomology.{u, w} (pullback.snd f g)
        (coherentEdgeCoefficient f G g) 1) ⟶
        coherentEdgeCohomology.{u, w} (pullback.snd f (h ≫ g))
          (coherentEdgeCoefficient f G (h ≫ g)) 1 := inv κ₂ ≫ H.map m
    let c : P.obj ((Scheme.Modules.tensorPullback g).obj
        (coherentEdgeCohomology.{u, w} f G 1)) ⟶
        (Scheme.Modules.tensorPullback (h ≫ g)).obj (coherentEdgeCohomology.{u, w} f G 1) :=
      (Scheme.Modules.tensorPullbackSectionComp h g).inv.app
        (coherentEdgeCohomology.{u, w} f G 1)
    have hnorm (V : Scheme.{u}) (v : V ⟶ S) :
        derivedPullbackTopCohomology.{u, w} v 1 K hK ≫ (β V v).hom =
          (DerivedCategory.homologyFunctor.{w, u, u + 1}
            (SheafOfModules.{u} (moduleRings V.toRingedSpace)) 1).map
              (coherentEdgeDelta.{u, w} f G v) := by
      rw [← coherentEdgeGamma_eq_top v K hK]
      exact hβnorm V v
    let d := (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 1).map
        (coherentEdgeDelta.{u, w} f G g)
    let ld := H.map ((derivedPullback.{u, w} h).map (coherentEdgeDelta.{u, w} f G g))
    let cc := H.map ((coherentEdge_pullbackComp g h).hom.app K)
    have hnat : ld ≫ κ₂ = κ₁ ≫ P.map d :=
      coherentEdge_top_naturality h ((derivedPullback.{u, w} g).obj K)
        Kg hLg hKg (coherentEdgeDelta.{u, w} f G g)
    have hcomp : cc ≫ κgh = κ₁ ≫ P.map κg ≫ c := coherentEdge_top_comp g h K hK
    have hβinv : b ≫ (β T' (h ≫ g)).inv = P.map (β T g).inv ≫ c := by
      exact coherentEdge_comparison_square P κ₁ κ₂ κg κgh d
        (H.map (coherentEdgeDelta.{u, w} f G (h ≫ g))) ld cc (H.map m) c
        (β T g) (β T' (h ≫ g)) (hnorm T g) (hnorm T' (h ≫ g)) hnat hcomp
        (coherentEdge_map_square H _ _ _ _ hpaste)
    have heps' :
        coherentEdgeEpsilon.{u, w} (pullback.snd f (h ≫ g))
            (coherentEdgeCoefficient f G (h ≫ g)) (coherentEdgePullback f G g h x) =
          (RingedSpace.globalSectionsFunctor T'.toRingedSpace).map b
            (coherentEdgeSectionPullback h
              (coherentEdgeCohomology.{u, w} (pullback.snd f g)
                (coherentEdgeCoefficient f G g) 1)
              (coherentEdgeEpsilon.{u, w} (pullback.snd f g)
                (coherentEdgeCoefficient f G g) x)) := by
      dsimp only [b, m]
      rw [coherentEdge_arrowDelta_eq, coherentEdgePullback_eq]
      exact coherentEdge_leray_square.{u, w} (pullback.snd f g)
          (pullback.snd f (h ≫ g)) h (coherentEdgeXMap f g h) (coherentEdgeXMap_snd f g h)
          (coherentEdgeCoefficient f G g) (coherentEdgeCoefficient f G (h ≫ g))
          (coherentEdgeCoefficientIso f G g h).hom hKg x
    have hsec := coherentEdge_sections_square h (β T g) (β T' (h ≫ g)) b c hβinv
      (coherentEdgeEpsilon.{u, w} (pullback.snd f g) (coherentEdgeCoefficient f G g) x)
      (coherentEdgeEpsilon.{u, w} (pullback.snd f (h ≫ g))
        (coherentEdgeCoefficient f G (h ≫ g)) (coherentEdgePullback f G g h x)) heps'
    have hrho := coherentEdgeRho_eq_sectionsMap g h (coherentEdgeCohomology f G 1)
      ((RingedSpace.globalSectionsFunctor T.toRingedSpace).map (β T g).inv
        (coherentEdgeEpsilon (pullback.snd f g) (coherentEdgeCoefficient f G g) x))
    exact hx'.trans ((hsec.trans hrho.symm).trans
      (congrArg (coherentEdgeRho g h (coherentEdgeCohomology f G 1)) hx.symm))

end AlgebraicGeometry
