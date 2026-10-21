/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.QcoherentTensorPullbackSheafMap
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import Sheaf.CategoryTheory.CohomologyPullbackZero
import all Sheaf.AlgebraicGeometry.QcoherentPullbackSectionsNaturality

/-! # Pullback maps and connecting homomorphisms on the two sites

Source: Stacks Project, Tags 01F7, 03AX and 010T.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
attribute [local irreducible] tensorPullback tensorPullbackObj SheafOfModules.toSheaf
attribute [local irreducible] constantSheaf constantSheafAdj
  qcoherentPullbackSheafMap coherentEtaleMap Adjunction.leftAdjointUniq
  CoherentEtale.Coeff Etale.upperStar Etale.upperStarLowerStarAdjunction
  Etale.cohomologyMap Scheme.upperStarConstantSheafIso
  Sheaf.H.map Sheaf.H.mapFunctor Sheaf.H.δSucc Sheaf.H.equiv₀
  qcoherentPullbackSection etaleTensorSectionsRestriction tensorSectionsUnit
attribute [local instance 4000] cohomologyHasSheafify
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

/-- Fix the sheafification proof used by the etale cohomology maps.
Source: Mathlib's small-etale-site sheafification instance.
(blueprint: lem-weil-pbc-qcoherent-pullback-cohomology-maps)

Proof: Use sheafification of abelian presheaves on the small etale site. -/
@[instance 4000]
theorem etalePullback_hasSheafify (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1} := by infer_instance

/-- Fix the small Ext proof used by the etale cohomology maps.
Source: Mathlib's Grothendieck abelian sheaf category.
(blueprint: lem-weil-pbc-qcoherent-pullback-cohomology-maps)

Proof: Abelian sheaves form a Grothendieck abelian category and hence have Ext
in the coefficient universe. -/
@[instance 4000]
theorem etalePullback_hasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) := by infer_instance

/-- Cache the fixed large Ext presentation before specializing the coefficients.
Source: Mathlib's standard large Ext instance.
(blueprint: lem-weil-pbc-qcoherent-pullback-cohomology-maps)

Proof: Apply the standard large Ext construction to the abelian sheaf category. -/
@[instance 4000]
theorem zariskiPullback_hasLargeExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

/-- Cache additivity in the shared abelian preadditive presentation.
Source: exact abelian inverse image in Mathlib.
(blueprint: lem-weil-pbc-qcoherent-pullback-cohomology-maps)

Proof: Use the existing inverse-image additivity instance. -/
@[instance 4000]
theorem zariskiPullback_additive {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (invImage g).Additive := invImage_additive g

/-- Cache etale inverse-image additivity in the shared presentation.
Source: Mathlib's additivity of left adjoints.
(blueprint: lem-weil-pbc-qcoherent-pullback-cohomology-maps)

Proof: Use the existing additivity instance for etale inverse image. -/
@[instance 4000]
theorem etalePullback_additive {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (Etale.upperStar AddCommGrpCat.{u + 1} g).Additive :=
  Etale.additive_upperStar AddCommGrpCat.{u + 1} g

attribute [local semireducible] SheafOfModules.toSheaf

/-- Exact inverse image on the fixed large Zariski abelian cohomology. -/
@[irreducible]
def zariskiPullbackCohomology {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : SheafOfModules.{u} X.ringCatSheaf) (G : SheafOfModules.{u} Y.ringCatSheaf)
    (φ : F ⟶ (pushforward g).obj G) (q : ℕ) :
    CoherentEtale.Source X F q → CoherentEtale.Source Y G q :=
  @Sheaf.cohomologyPullbackMap.{u, u, u, u, u, u + 1}
    _ _ _ _ _ _ (cohomologyHasSheafify X) (cohomologyHasSheafify Y)
    (HasExt.standard _) (HasExt.standard _)
    (invImage g) _ _ _ (constIso g).symm
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)
    ((SheafOfModules.toSheaf Y.ringCatSheaf).obj G) (coeff g φ) q

attribute [local irreducible] SheafOfModules.toSheaf
  TopCat.Sheaf.pullbackPushforwardAdjunction
  Functor.sheafAdjunctionContinuous

/-- Pullback on lifted etale cohomology followed by the structural coefficient map. -/
@[irreducible]
def etalePullbackCohomology {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : SheafOfModules.{u} X.ringCatSheaf) (G : SheafOfModules.{u} Y.ringCatSheaf)
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : (tensorPullback g).obj F ⟶ G) (q : ℕ) :
    Sheaf.H.{u + 1} (liftedCoherentEtaleSheaf F) q →
      Sheaf.H.{u + 1} (liftedCoherentEtaleSheaf G) q :=
  Sheaf.adjointCohomologyPullbackMap.{u + 1, u, u + 1, u, u + 1, u + 1}
    (Etale.upperStar AddCommGrpCat.{u + 1} g)
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).symm.app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (Etale.lowerStar AddCommGrpCat.{u + 1} g)
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g)
    (liftedCoherentEtaleSheaf F) (liftedCoherentEtaleSheaf G)
    (qcoherentPullbackSheafMap g F G ψ) q

/-- The large Zariski pullback commutes with boundaries in a coefficient square.
Source: Stacks Project, Tags 01F7 and 010T.
(blueprint: lem-weil-pbc-qcoherent-pullback-cohomology-maps)

Proof: Apply exact abelian inverse image to the underlying source short exact
sequence. The three adjoint module coefficient maps give a morphism from this
sequence to the underlying target sequence, by adjunction naturality. Exact
functor transport of Ext classes preserves the connecting extension class.
Naturality of that extension class gives the boundary square directly in the
fixed large Ext universe. -/
theorem zariskiPullbackCohomology_boundary {X Y : Scheme.{u}} (g : Y ⟶ X)
    (S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf))
    (R : ShortComplex (SheafOfModules.{u} Y.ringCatSheaf))
    (hS : (S.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf)).ShortExact)
    (hR : (R.map (SheafOfModules.toSheaf.{u} Y.ringCatSheaf)).ShortExact)
    (φ₁ : S.X₁ ⟶ (pushforward g).obj R.X₁)
    (φ₂ : S.X₂ ⟶ (pushforward g).obj R.X₂)
    (φ₃ : S.X₃ ⟶ (pushforward g).obj R.X₃)
    (h₁ : S.f ≫ φ₂ = φ₁ ≫ (pushforward g).map R.f)
    (h₂ : S.g ≫ φ₃ = φ₂ ≫ (pushforward g).map R.g)
    (q : ℕ) (x : CoherentEtale.Source X S.X₃ q) :
    zariskiPullbackCohomology g S.X₁ R.X₁ φ₁ (q + 1)
        (CoherentEtale.sourceBoundary S hS q x) =
      CoherentEtale.sourceBoundary R hR q
        (zariskiPullbackCohomology g S.X₃ R.X₃ φ₃ q x) := by
  let A := S.map (SheafOfModules.toSheaf.{u} X.ringCatSheaf)
  let B := R.map (SheafOfModules.toSheaf.{u} Y.ringCatSheaf)
  let φ : A.map (invImage g) ⟶ B := ShortComplex.homMk
    (coeff g φ₁) (coeff g φ₂) (coeff g φ₃)
    (coeff_naturality g φ₁ φ₂ S.f R.f h₁).symm
    (coeff_naturality g φ₂ φ₃ S.g R.g h₂).symm
  unfold zariskiPullbackCohomology CoherentEtale.sourceBoundary
  exact Sheaf.cohomologyPullbackMap_boundary.{u, u, u, u, u, u + 1}
    (invImage g) (constIso g).symm A B hS hR φ q x

/-- The etale pullback commutes with boundaries in a coefficient square.
Source: Stacks Project, Tags 03AX and 010T.
(blueprint: lem-weil-pbc-qcoherent-pullback-cohomology-maps)

Proof: Exact etale inverse image commutes with connecting homomorphisms.
Structural coefficient naturality gives a morphism from the pulled-back
source coefficient sequence to the target coefficient sequence. Naturality
of the connecting homomorphism for this morphism finishes the proof. -/
theorem etalePullbackCohomology_boundary {X Y : Scheme.{u}} (g : Y ⟶ X)
    (S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf))
    (R : ShortComplex (SheafOfModules.{u} Y.ringCatSheaf))
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    [R.X₁.IsQuasicoherent] [R.X₂.IsQuasicoherent] [R.X₃.IsQuasicoherent]
    (hzS : coherentEtaleMap S.X₁ S.X₂ S.f ≫ coherentEtaleMap S.X₂ S.X₃ S.g = 0)
    (hzR : coherentEtaleMap R.X₁ R.X₂ R.f ≫ coherentEtaleMap R.X₂ R.X₃ R.g = 0)
    (heS : (ShortComplex.mk _ _ hzS).ShortExact)
    (heR : (ShortComplex.mk _ _ hzR).ShortExact)
    (ψ₁ : (tensorPullback g).obj S.X₁ ⟶ R.X₁)
    (ψ₂ : (tensorPullback g).obj S.X₂ ⟶ R.X₂)
    (ψ₃ : (tensorPullback g).obj S.X₃ ⟶ R.X₃)
    (h₁ : (tensorPullback g).map S.f ≫ ψ₂ = ψ₁ ≫ R.f)
    (h₂ : (tensorPullback g).map S.g ≫ ψ₃ = ψ₂ ≫ R.g)
    (q : ℕ) (x : CoherentEtale.Target X S.X₃ q) :
    etalePullbackCohomology g S.X₁ R.X₁ ψ₁ (q + 1)
        (CoherentEtale.targetBoundary
          (fun F G _ _ φ ↦ coherentEtaleMap F G φ) S hzS heS q x) =
      CoherentEtale.targetBoundary
        (fun F G _ _ φ ↦ coherentEtaleMap F G φ) R hzR heR q
        (etalePullbackCohomology g S.X₃ R.X₃ ψ₃ q x) := by
  unfold etalePullbackCohomology CoherentEtale.targetBoundary
  exact Sheaf.adjointCohomologyPullbackMap_boundary.{u + 1, u, u + 1, u, u + 1, u + 1}
    _ _ _ _ _ _ heS heR
    (qcoherentPullbackSheafMap g _ _ ψ₁) (qcoherentPullbackSheafMap g _ _ ψ₂)
    (qcoherentPullbackSheafMap g _ _ ψ₃)
    (qcoherentPullbackSheafMap_naturality g ψ₁ ψ₂ S.f R.f h₁)
    (qcoherentPullbackSheafMap_naturality g ψ₂ ψ₃ S.g R.g h₂) q x

attribute [local semireducible] SheafOfModules.toSheaf

private theorem adjunctionUnit_global_app {X Y : Scheme.{u}} (g : Y ⟶ X)
    (L : X.Modules ⥤ Y.Modules) (adj : L ⊣ pushforward g)
    (F : X.Modules) (G : Y.Modules) (ψ : L.obj F ⟶ G) :
    sectionsUnitOfAdjunction g L adj F ≫ ψ.app ⊤ = (adj.homEquiv F G ψ).app ⊤ := by
  have hi : (homOfLE g.preimage_top.ge).op =
      𝟙 (op (⊤ : TopologicalSpace.Opens Y)) := rfl
  unfold sectionsUnitOfAdjunction
  erw [hi, (L.obj F).presheaf.map_id, Category.comp_id]
  rw [Adjunction.homEquiv_unit, Hom.comp_app, pushforward_map_app]
  simp only [g.preimage_top]
  rfl

/-- The tensor section unit followed by a coefficient map is its adjoint on sections.
Source: Stacks Project, Tag 01FD.
(blueprint: lem-weil-pbc-qcoherent-pullback-cohomology-maps)

Proof: Identify the concrete tensor section unit with the abstract adjunction unit.
The adjunction hom equivalence is composition with this unit; restriction at the
preimage of the top open is the identity. -/
theorem tensorSectionsUnit_adjoint_app {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (G : Y.Modules) (ψ : (tensorPullback g).obj F ⟶ G) :
    tensorSectionsUnit g F ≫ ψ.app ⊤ =
      (((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv F G) ψ).app ⊤ := by
  refine Eq.trans (congrArg (fun k ↦ k ≫ ψ.app ⊤)
    (unit_to_abstract (A := Y) (B := X) g F)) ?_
  exact adjunctionUnit_global_app g (tensorPullback g)
    (Classical.choose (exists_tensorPullbackAdjunction g)) F G ψ


private theorem zariskiConstIso_eq {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (constIso g).symm =
      (Adjunction.leftAdjointUniq
        (((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
            isTerminalTop).comp
          (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base)).ofNatIsoRight
          ((TopologicalSpace.Opens.map g.base).sheafPushforwardContinuousCompSheafSectionsObjIso
            AddCommGrpCat.{u} (Opens.grothendieckTopology X)
            (Opens.grothendieckTopology Y) (op ⊤)))
        (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
          isTerminalTop)).symm.app (AddCommGrpCat.of (ULift.{u} ℤ)) := by
  unfold constIso Functor.constantSheafsheafPullbackIso
    TopCat.Sheaf.pullbackPushforwardAdjunction
  rfl

private theorem etaleConstIso_eq {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).symm.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) =
      (Adjunction.leftAdjointUniq
        (((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
            terminalIsTerminal).comp
          (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g)).ofNatIsoRight
          (Etale.lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} g))
        (constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
          terminalIsTerminal)).symm.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)) := by
  unfold Scheme.upperStarConstantSheafIso
  rfl

/-- Degree-zero Zariski pullback is the adjoint module map on global sections.
Source: Stacks Project, Tags 01F7 and 0096.
(blueprint: lem-weil-pbc-qcoherent-pullback-cohomology-maps)

Proof: Apply the degree-zero adjunction formula to abelian inverse image
and the coefficient morphism. The inverse adjunction in the coefficient
construction cancels with the forward adjunction. The section comparison at
the preimage of the top open is the identity, leaving the underlying module
morphism on global sections, in the same fixed Ext universe. -/
theorem zariskiPullbackCohomology_zero {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : SheafOfModules.{u} X.ringCatSheaf) (G : SheafOfModules.{u} Y.ringCatSheaf)
    (φ : F ⟶ (pushforward g).obj G)
    (x : CoherentEtale.Source X F 0) :
    CoherentEtale.sourceZero Y G (zariskiPullbackCohomology g F G φ 0 x) =
      Hom.app φ ⊤ (CoherentEtale.sourceZero X F x) := by
  unfold CoherentEtale.sourceZero
  let J := Opens.grothendieckTopology X
  let K := Opens.grothendieckTopology Y
  let A := (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj F
  let B := (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).obj G
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base
  let σ := (TopologicalSpace.Opens.map g.base).sheafPushforwardContinuousCompSheafSectionsObjIso
    AddCommGrpCat.{u} J K (op ⊤)
  have h := Sheaf.adjointCohomologyPullbackMap_zero_of_eq.{u, u, u, u, u, u + 1}
    (invImage g) (constIso g).symm _ adj
    isTerminalTop isTerminalTop σ (zariskiConstIso_eq g)
    A B ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) x
  unfold Sheaf.adjointCohomologyPullbackMap at h
  change Sheaf.H.equiv₀.{u + 1} B isTerminalTop
      (Sheaf.cohomologyPullbackMap (invImage g) (constIso g).symm
        A B (coeff g φ) 0 x) =
    Hom.app φ ⊤ (Sheaf.H.equiv₀.{u + 1} A isTerminalTop x) at h
  unfold zariskiPullbackCohomology
  exact h


attribute [local irreducible] SheafOfModules.toSheaf


private theorem etalePullback_zero_general {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : SheafOfModules.{u} X.ringCatSheaf) (G : SheafOfModules.{u} Y.ringCatSheaf)
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : (tensorPullback g).obj F ⟶ G)
    (s : (liftedCoherentEtaleSheaf F).obj.obj (op (⊤_ X.Etale))) :
    Sheaf.H.equiv₀.{u + 1} (liftedCoherentEtaleSheaf G) terminalIsTerminal
      (etalePullbackCohomology g F G ψ 0
        ((Sheaf.H.equiv₀.{u + 1} (liftedCoherentEtaleSheaf F)
          terminalIsTerminal).symm s)) =
      (Etale.lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} g).hom.app
        (liftedCoherentEtaleSheaf G)
        ((qcoherentPullbackSheafMap g F G ψ).hom.app (op (⊤_ X.Etale)) s) := by
  unfold etalePullbackCohomology
  have h := Sheaf.adjointCohomologyPullbackMap_zero_of_eq
    (Etale.upperStar AddCommGrpCat.{u + 1} g)
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).symm.app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (Etale.lowerStar AddCommGrpCat.{u + 1} g)
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g)
    terminalIsTerminal terminalIsTerminal
    (Etale.lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} g)
    (etaleConstIso_eq g) _ _ (qcoherentPullbackSheafMap g F G ψ)
    ((Sheaf.H.equiv₀.{u + 1} (liftedCoherentEtaleSheaf F) terminalIsTerminal).symm s)
  refine h.trans ?_
  exact congrArg (fun t ↦
    (Etale.lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} g).hom.app
      (liftedCoherentEtaleSheaf G)
      ((qcoherentPullbackSheafMap g F G ψ).hom.app (op (⊤_ X.Etale)) t))
    ((Sheaf.H.equiv₀.{u + 1} (liftedCoherentEtaleSheaf F)
      terminalIsTerminal).apply_symm_apply s)

attribute [local semireducible] CoherentEtale.Coeff

private theorem map_unit_square {C D : Type*} [Category* C] [Category* D]
    (L : C ⥤ D) {A B C' D' E F : C}
    (i : A ⟶ B) (k : B ⟶ C') (r : C' ⟶ D')
    (a : A ⟶ E) (b : E ⟶ F) (c : F ⟶ C') (d : F ⟶ D')
    (hi : i ≫ k = a ≫ b ≫ c) (hr : c ≫ r = d) :
    L.map i ≫ L.map (k ≫ r) = L.map (a ≫ b ≫ d) := by
  rw [← L.map_comp, ← Category.assoc, hi]
  simp only [Category.assoc, hr]

private theorem ulift_composite_apply {A B C D : Ab.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (s : A) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.map (a ≫ b ≫ c) (ULift.up s) =
      ULift.up (c (b (a s))) := rfl

private theorem ulift_apply {A B : Ab.{u}} (a : A ⟶ B) (s : A) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.map a (ULift.up s) = ULift.up (a s) := rfl

private theorem native_unit_evaluation {A B C D : AddCommGrpCat.{u + 1}}
    (i : A ⟶ B) (θ : B ⟶ C) (σ : C ⟶ D) (o : A ⟶ D)
    (h : i ≫ θ ≫ σ = o) (s : A) (si : B) (so : D)
    (hi : i s = si) (ho : o s = so) : σ (θ si) = so := by
  rw [← hi, ← ho]
  exact ConcreteCategory.congr_hom h s

private theorem etalePullback_unit_hom {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : SheafOfModules.{u} X.ringCatSheaf) (G : SheafOfModules.{u} Y.ringCatSheaf)
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : (tensorPullback g).obj F ⟶ G) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.map
        (tensorSectionsUnit (⊤_ X.Etale).hom F) ≫
      (qcoherentPullbackSheafMap g F G ψ).hom.app (op (⊤_ X.Etale)) ≫
        (Etale.lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} g).hom.app
          (liftedCoherentEtaleSheaf G) =
      AddCommGrpCat.uliftFunctor.{u + 1, u}.map
        (tensorSectionsUnit g F ≫ ψ.app ⊤ ≫ tensorSectionsUnit (⊤_ Y.Etale).hom G) := by
  let U : X.Etale := ⊤_ X.Etale
  let V := g.Etale.obj U
  let a : (⊤_ Y.Etale) ⟶ V := (PreservesTerminal.iso g.Etale).inv
  let L := AddCommGrpCat.uliftFunctor.{u + 1, u}
  have ht := congrArg (fun f ↦ L.map (tensorSectionsUnit U.hom F) ≫ f)
    (qcoherentPullbackSheafMap_terminal g F G ψ)
  have hs := qcoherentPullbackSection_global_unit g F G ψ U V
    (pullback.fst U.hom g) pullback.condition
  have hr := tensorSectionsUnit_restriction G a
  have hc := map_unit_square L (tensorSectionsUnit U.hom F)
    (qcoherentPullbackSection g F G ψ U V (pullback.fst U.hom g) pullback.condition)
    (etaleTensorSectionsRestriction G a) (tensorSectionsUnit g F) (ψ.app ⊤)
    (tensorSectionsUnit V.hom G) (tensorSectionsUnit (⊤_ Y.Etale).hom G) hs hr
  exact ht.trans hc

private theorem etalePullback_unit {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : SheafOfModules.{u} X.ringCatSheaf) (G : SheafOfModules.{u} Y.ringCatSheaf)
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : (tensorPullback g).obj F ⟶ G) (s : Γ(F, ⊤)) :
    (Etale.lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} g).hom.app
        (liftedCoherentEtaleSheaf G)
        ((qcoherentPullbackSheafMap g F G ψ).hom.app (op (⊤_ X.Etale))
          (ULift.up (tensorSectionsUnit (⊤_ X.Etale).hom F s))) =
      ULift.up (tensorSectionsUnit (⊤_ Y.Etale).hom G
        (ψ.app ⊤ (tensorSectionsUnit g F s))) := by
  let i : AddCommGrpCat.uliftFunctor.{u + 1, u}.obj Γ(F, ⊤) ⟶
      (liftedCoherentEtaleSheaf F).obj.obj (op (⊤_ X.Etale)) :=
    AddCommGrpCat.uliftFunctor.map (tensorSectionsUnit (⊤_ X.Etale).hom F)
  let o : AddCommGrpCat.uliftFunctor.{u + 1, u}.obj Γ(F, ⊤) ⟶
      (liftedCoherentEtaleSheaf G).obj.obj (op (⊤_ Y.Etale)) :=
    AddCommGrpCat.uliftFunctor.map
      (tensorSectionsUnit g F ≫ ψ.app ⊤ ≫ tensorSectionsUnit (⊤_ Y.Etale).hom G)
  refine native_unit_evaluation i
    ((qcoherentPullbackSheafMap g F G ψ).hom.app (op (⊤_ X.Etale)))
    ((Etale.lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} g).hom.app
      (liftedCoherentEtaleSheaf G)) o (etalePullback_unit_hom g F G ψ) (ULift.up s)
      _ _ ?_ ?_
  · exact ulift_apply _ s
  · exact ulift_composite_apply _ _ _ s

/-- Degree-zero etale pullback of a structural global section is structural pullback.
Source: Stacks Project, Tags 03DR, 03AX and 01FD.
(blueprint: lem-weil-pbc-qcoherent-pullback-cohomology-maps)

Proof: The degree-zero adjunction formula evaluates the structural coefficient
map at the terminal etale object of X and restricts its value from its base
change to the terminal etale object of Y. Combining the source section unit
with the coefficient formula gives the unit for g followed by psi and the unit
at that base change. Unit compatibility with etale restriction replaces the
last unit by the unit at the terminal object of Y. -/
theorem etalePullbackCohomology_zero {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : SheafOfModules.{u} X.ringCatSheaf) (G : SheafOfModules.{u} Y.ringCatSheaf)
    [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : (tensorPullback g).obj F ⟶ G) (s : Γ(F, ⊤)) :
    CoherentEtale.targetZero Y G
      (etalePullbackCohomology g F G ψ 0
        ((CoherentEtale.targetZero X F).symm
          (ULift.up (tensorSectionsUnit (⊤_ X.Etale).hom F s)))) =
      ULift.up (tensorSectionsUnit (⊤_ Y.Etale).hom G
        (ψ.app ⊤ (tensorSectionsUnit g F s))) := by
  unfold CoherentEtale.targetZero
  exact (etalePullback_zero_general g F G ψ
    (ULift.up (tensorSectionsUnit (⊤_ X.Etale).hom F s))).trans
      (etalePullback_unit g F G ψ s)



end
end AlgebraicGeometry.Scheme.Modules
