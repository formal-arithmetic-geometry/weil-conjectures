/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceGeometricStalkModels
public import Sheaf.AlgebraicGeometry.SpaceGeometricPointsConservative
public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.DirectSum.Module

/-! # Normalized geometric stalks of étale sum extension

Source: Stacks Project, Modules on Sites, Tags 03DI and 0710;
Spaces and Modules, Tag 08GU, equations stalk-restriction and stalk-j-shriek
(blueprint: lem-sfb-space-etale-sum-stalks).

An adjunction realizing extension determines it up to the unique isomorphism carrying
its unit to the direct-sum generators. We quantify over its realization and retain its
counit. The forward sum map below is characterized on every pointed scheme chart;
its inverse is the stalk isomorphism in the displayed formula of Tag 0710.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}

/-- All geometric lifts with the original algebraically closed field, including an
empty or infinite fibre. Source: Stacks 08GU and 0710
(blueprint: lem-sfb-space-etale-sum-stalks). -/
abbrev EtaleGeometricLift (j : Z ⟶ X) {P : Over S}
    (x : yoneda.obj P ⟶ X.obj.obj) :=
  {z : yoneda.obj P ⟶ Z.obj.obj // z ≫ j.hom.hom = x}

/-- The full pointed-neighbourhood section diagram, with the original module universe.
Source: Stacks 04JY, 0710 (blueprint: lem-sfb-space-etale-sum-stalks). -/
def etaleFullModuleDiagram {P : Over S} (x : yoneda.obj P ⟶ X.obj.obj) (M : X.Modules) :
    (X.PointedEtale x)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (X.pointedEtaleForget x).op ⋙ M.val.presheaf

/-- Passing from the fixed affine basis to all pointed scheme charts preserves the
actual section colimit, and determines its cocone uniquely on affine germs.
Source: Stacks 04JY, 03ED, 0710 (blueprint: lem-sfb-space-etale-sum-stalks).
Proof: every pointed étale scheme chart has an affine neighbourhood of the lifted
point, and a chart in the fixed small affine basis refines this neighbourhood.
Two such refinements admit a common pointed affine refinement; the same argument
equalizes parallel arrows. Thus the affine inclusion is initial, its opposite is
final, and restriction induces the colimit equivalence. Extend the existing germ
cocone along this final functor. Colimit uniqueness gives exactly the asserted
unique cocone and its colimit property, without changing its module or ring. -/
theorem etaleFullGerms_existsUnique {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) (M : X.Modules) :
    ∃! γ : etaleFullModuleDiagram x M ⟶
        (Functor.const _).obj
          ((forget₂ _ AddCommGrpCat).obj ((SingleComplex.stalkModel s x).modules.obj M)),
      Nonempty (IsColimit (Cocone.mk _ γ)) ∧
      ∀ N : SingleComplex.Neighbourhood (Over.mk s) x,
        γ.app (op (StructuredArrow.mk N.hom)) =
          ((SingleComplex.stalkModel s x).germs M).app (op N) := by
  sorry

/-- The full germ cocone is selected by its unique extension of the existing affine
colimit cocone. Source: Stacks 04JY, 0710
(blueprint: lem-sfb-space-etale-sum-stalks). -/
def etaleFullGerms {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) (M : X.Modules) :=
  (etaleFullGerms_existsUnique s x M).choose

/-- Postcomposition sends a pointed chart of a lift to a pointed chart of the base.
Source: Stacks 03LP, 0710 (blueprint: lem-sfb-space-etale-sum-stalks). -/
def etaleLiftNeighbourhood (j : Z ⟶ X) (hj : IsEtale j.hom.hom) {P : Over S}
    (x : yoneda.obj P ⟶ X.obj.obj) (z : EtaleGeometricLift j x)
    (N : Z.PointedEtale z.val) : X.PointedEtale x :=
  StructuredArrow.mk (Y := (etaleMap j hj).obj N.right)
    (CostructuredArrow.homMk N.hom.left
      (by
        change yoneda.map N.hom.left ≫ (N.right.obj.hom ≫ j.hom.hom) = x
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun a ↦ a ≫ j.hom.hom) N.hom.w).trans z.property)))

/-- The canonical map of geometric local rings, with the lift equality transported.
Source: Stacks 03G8 and 08GU (blueprint: lem-sfb-space-etale-sum-stalks). -/
def etaleLiftRingMap (j : Z ⟶ X) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj)
    (z : EtaleGeometricLift j x) :
    SingleComplex.stalkRing s x →+* SingleComplex.stalkRing s z.val :=
  (SingleComplex.stalkMap j s z.val).comp
    (eqToHom (congrArg (SingleComplex.stalkRing s) z.property.symm)).hom

/-- A lifted module stalk regarded as a module over the base local ring by the
canonical structural map. Source: Stacks 08GU and 0710
(blueprint: lem-sfb-space-etale-sum-stalks). -/
def etaleLiftStalk (j : Z ⟶ X) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj)
    (z : EtaleGeometricLift j x) : Z.Modules ⥤ ModuleCat.{u} (SingleComplex.stalkRing s x) :=
  (SingleComplex.stalkModel s z.val).modules ⋙
    ModuleCat.restrictScalars (etaleLiftRingMap j s x z)

/-- Each lifted stalk maps canonically to the stalk of extension, by the germ of
its sectionwise unit. Source: Stacks 03DI, 0710
(blueprint: lem-sfb-space-etale-sum-stalks).
Proof: the unit of the realizing adjunction inserts a section on a Z-chart into
its lift summand. Apply the germ on the same chart over X. Naturality of the unit
makes these maps compatible with refinement. Their scalar equation is the
canonical map of local rings, so the module-colimit property gives the unique
linear map displayed here. In the enlarged localized-site model this is exactly
the inclusion in the direct-sum presheaf followed by module sheafification. -/
theorem etaleSumStalkInjection_existsUnique (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    (L : Z.Modules ⥤ X.Modules) (adj : L ⊣ pullback j hj)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) (z : EtaleGeometricLift j x) (M : Z.Modules) :
    ∃! ι : (etaleLiftStalk j s x z).obj M →ₗ[SingleComplex.stalkRing s x]
        (SingleComplex.stalkModel s x).modules.obj (L.obj M),
      ∀ (N : Z.PointedEtale z.val) (m : M.val.obj (op N.right)),
        ι ((etaleFullGerms s z.val M).app (op N) m) =
          (etaleFullGerms s x (L.obj M)).app
            (op (etaleLiftNeighbourhood j hj x z N))
            ((adj.unit.app M).val.app (op N.right) m) := by
  sorry

/-- The canonical summand injection is chosen from its unique formula on all germs.
Source: Stacks 0710 (blueprint: lem-sfb-space-etale-sum-stalks). -/
def etaleSumStalkInjection (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    (L : Z.Modules ⥤ X.Modules) (adj : L ⊣ pullback j hj)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) (z : EtaleGeometricLift j x) (M : Z.Modules) :=
  (etaleSumStalkInjection_existsUnique j hj L adj s x z M).choose

open Classical in
/-- The direct sum of the germ-normalized injections, with no bound on the lift set.
Source: Stacks 0710 (blueprint: lem-sfb-space-etale-sum-stalks). -/
def etaleSumStalkMap (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    (L : Z.Modules ⥤ X.Modules) (adj : L ⊣ pullback j hj)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) (M : Z.Modules) :=
  DirectSum.toModule (SingleComplex.stalkRing s x) (EtaleGeometricLift j x)
    ((SingleComplex.stalkModel s x).modules.obj (L.obj M))
    (fun z ↦ etaleSumStalkInjection j hj L adj s x z M)

/-- Literal restriction identifies the lifted stalk with the original stalk by
sending each germ on a Z-chart to the same section's germ on its X-chart.
Source: Stacks 08GU, equation-stalk-restriction, and 04K2(4)
(blueprint: lem-sfb-space-etale-sum-stalks).
Proof: localization identifies étale restriction with inverse image. The
geometric-point inverse-image comparison sends the germ of a restricted section
to its original germ and is natural in the module. The local ring comparison is
an isomorphism because pointed charts of Z at a fixed lift are cofinal in pointed
charts of X at its image. This makes the comparison linear over the base ring.
Its germ equation determines it uniquely by the section-colimit property. -/
theorem etaleRestrictionStalk_existsUnique (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) (z : EtaleGeometricLift j x) (F : X.Modules) :
    ∃! e : (etaleLiftStalk j s x z).obj ((pullback j hj).obj F) ≃ₗ[
        SingleComplex.stalkRing s x] (SingleComplex.stalkModel s x).modules.obj F,
      ∀ (N : Z.PointedEtale z.val) (m : F.val.obj (op ((etaleMap j hj).obj N.right))),
        e ((etaleFullGerms s z.val ((pullback j hj).obj F)).app (op N) m) =
          (etaleFullGerms s x F).app (op (etaleLiftNeighbourhood j hj x z N)) m := by
  sorry

/-- The canonical restriction comparison, retaining its unique section normalization.
Source: Stacks 08GU (blueprint: lem-sfb-space-etale-sum-stalks). -/
def etaleRestrictionStalkIso (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) (z : EtaleGeometricLift j x) (F : X.Modules) :=
  (etaleRestrictionStalk_existsUnique j hj s x z F).choose

/-- The normalized copy of F_x in the stalk of j_! j^* F at a chosen lift.
Source: Stacks 08GU, 03DI (blueprint: lem-sfb-space-etale-sum-stalks). -/
def etaleConstantStalkInjection (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    (L : Z.Modules ⥤ X.Modules) (adj : L ⊣ pullback j hj)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) (z : EtaleGeometricLift j x) (F : X.Modules) :=
  (etaleSumStalkInjection j hj L adj s x z ((pullback j hj).obj F)).comp
    (etaleRestrictionStalkIso j hj s x z F).symm.toLinearMap

open Classical in
/-- The sum of the normalized constant-stalk injections.
Source: Stacks 08GU (blueprint: lem-sfb-space-etale-sum-stalks). -/
def etaleConstantSumStalkMap (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    (L : Z.Modules ⥤ X.Modules) (adj : L ⊣ pullback j hj)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) (F : X.Modules) :=
  DirectSum.toModule (SingleComplex.stalkRing s x) (EtaleGeometricLift j x)
    ((SingleComplex.stalkModel s x).modules.obj (L.obj ((pullback j hj).obj F)))
    (fun z ↦ etaleConstantStalkInjection j hj L adj s x z F)

/-- Iterated restriction and composite restriction have the identical chart sections.
Source: Stacks 03LP, 03DI (blueprint: lem-sfb-space-etale-sum-stalks). -/
def etaleSumRestrictionComp (k : Y ⟶ Z) (j : Z ⟶ X)
    (hk : IsEtale k.hom.hom) (hj : IsEtale j.hom.hom) :
    pullback j hj ⋙ pullback k hk ≅
      pullback (k ≫ j) (isEtale_comp k.hom.hom j.hom.hom hk hj) :=
  NatIso.ofComponents (fun F ↦
    (SheafOfModules.fullyFaithfulForget Y.structureSheaf).preimageIso
      (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _)))
    (by intros; ext; rfl)

/-- The map induced by the further restriction counit: transpose the pulled-back
unit of j. Under composition of adjunctions this is j_! of the k-counit.
Source: Stacks 03DI, 08GU (blueprint: lem-sfb-space-etale-sum-stalks). -/
def etaleNestedStalkCounit (k : Y ⟶ Z) (j : Z ⟶ X)
    (hk : IsEtale k.hom.hom) (hj : IsEtale j.hom.hom)
    (L : Z.Modules ⥤ X.Modules) (adj : L ⊣ pullback j hj)
    (L' : Y.Modules ⥤ X.Modules)
    (adj' : L' ⊣ pullback (k ≫ j) (isEtale_comp k.hom.hom j.hom.hom hk hj))
    (F : X.Modules) :
    L'.obj ((pullback (k ≫ j) (isEtale_comp k.hom.hom j.hom.hom hk hj)).obj F) ⟶
      L.obj ((pullback j hj).obj F) :=
  (adj'.homEquiv _ _).symm
    ((etaleSumRestrictionComp k j hk hj).inv.app F ≫
      (pullback k hk).map (adj.unit.app ((pullback j hj).obj F)) ≫
      (etaleSumRestrictionComp k j hk hj).hom.app (L.obj ((pullback j hj).obj F)))

/-- The normalized stalk formula, naturality, counit summation, and compatibility
with further étale restriction. Bijectivity of a linear map is the asserted linear
isomorphism; its inverse sends a sheafified summand germ to the corresponding lift.
Source: Stacks 0710, 03DI and 08GU
(blueprint: lem-sfb-space-etale-sum-stalks).
Proof:
1. Use lem-trf-space-enlarged-etale-ringed-site-model to identify restriction with
   localization. lem-pur-site-restriction-module-adjunction-exact and
   def-weil-extension-by-zero-presheaf describe extension as the sheafification of
   the sum over lifts. lem-sfb-space-sum-extension-geometric-stalk gives the
   canonical linear stalk formula, the ring isomorphism, and its germ formula.
   Its inverse is exactly etaleSumStalkMap, by the defining germ equations above.
2. For a restricted module apply lem-sfb-space-geometric-points-conservative.
   Its inverse-image stalk comparison is etaleRestrictionStalkIso by the same
   germ equation. Substituting in the sum proves the constant-summand formula.
3. In the normalized Hom bijection a map α sends the a-summand section m to
   α_(W,a)(m), and module sheafification extends it uniquely. Conversely restrict
   a map to each summand. The two operations are inverse, naturally in both
   modules. Thus the realizing adjunction, identified with this construction by
   its unit, has counit equal to the identity on each normalized stalk copy.
4. For k followed by j, def-weil-pbc-composite-adjunction identifies the composite
   unit with the two successive summand inclusions. The comparison for left
   adjoints sends a b-generator to the outer kb-summand and inner b-summand.
   Applying j_! to the k-counit evaluates the inner generator without changing
   its section. Its stalk is therefore the identity into the k-image summand,
   exactly the counit-induced map displayed below. Finite support treats infinite lift
   sets and adds components when two lifts have the same image. No separation,
   finiteness, or quasi-compactness is used. -/
theorem space_etale_sum_stalks (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    (L : Z.Modules ⥤ X.Modules) (adj : L ⊣ pullback j hj)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) :
    (∀ z : EtaleGeometricLift j x, Function.Bijective (etaleLiftRingMap j s x z)) ∧
    (∀ M : Z.Modules, Function.Bijective (etaleSumStalkMap j hj L adj s x M)) ∧
    (∀ (M N : Z.Modules) (a : M ⟶ N) (z : EtaleGeometricLift j x)
      (m : (etaleLiftStalk j s x z).obj M),
      (SingleComplex.stalkModel s x).modules.map (L.map a)
          (etaleSumStalkInjection j hj L adj s x z M m) =
        etaleSumStalkInjection j hj L adj s x z N ((etaleLiftStalk j s x z).map a m)) ∧
    (∀ F : X.Modules, Function.Bijective (etaleConstantSumStalkMap j hj L adj s x F)) ∧
    (∀ (F : X.Modules) (z : EtaleGeometricLift j x)
      (m : (SingleComplex.stalkModel s x).modules.obj F),
      (SingleComplex.stalkModel s x).modules.map (adj.counit.app F)
        (etaleConstantStalkInjection j hj L adj s x z F m) = m) ∧
    (∀ (Y : AlgebraicSpace S) (k : Y ⟶ Z) (hk : IsEtale k.hom.hom)
      (L' : Y.Modules ⥤ X.Modules)
      (adj' : L' ⊣ pullback (k ≫ j) (isEtale_comp k.hom.hom j.hom.hom hk hj))
      (F : X.Modules)
      (z' : EtaleGeometricLift (k ≫ j) x) (z : EtaleGeometricLift j x),
      z'.val ≫ k.hom.hom = z.val →
      ∀ m : (SingleComplex.stalkModel s x).modules.obj F,
        (SingleComplex.stalkModel s x).modules.map
          (etaleNestedStalkCounit k j hk hj L adj L' adj' F)
          (etaleConstantStalkInjection (k ≫ j)
            (isEtale_comp k.hom.hom j.hom.hom hk hj) L' adj' s x z' F m) =
          etaleConstantStalkInjection j hj L adj s x z F m) := by
  sorry

open Classical in
/-- The displayed stalk isomorphism, oriented from extension to the sum of lifted
stalks. Its inverse is the sum of the specified unit-germ injections, so its value
on a sheafified summand germ is the germ in that lift's summand.
Source: Stacks 0710 and 08GU (blueprint: lem-sfb-space-etale-sum-stalks). -/
def spaceEtaleSumStalkIso (j : Z ⟶ X) (hj : IsEtale j.hom.hom)
    (L : Z.Modules ⥤ X.Modules) (adj : L ⊣ pullback j hj)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj) (M : Z.Modules) :
    (SingleComplex.stalkModel s x).modules.obj (L.obj M) ≃ₗ[SingleComplex.stalkRing s x]
      DirectSum (EtaleGeometricLift j x) (fun z ↦ (etaleLiftStalk j s x z).obj M) :=
  ({ etaleSumStalkMap j hj L adj s x M,
      Equiv.ofBijective (etaleSumStalkMap j hj L adj s x M)
        ((space_etale_sum_stalks j hj L adj s x).2.1 M) with } :
    DirectSum (EtaleGeometricLift j x) (fun z ↦ (etaleLiftStalk j s x z).obj M) ≃ₗ[
      SingleComplex.stalkRing s x]
      (SingleComplex.stalkModel s x).modules.obj (L.obj M)).symm

end AlgebraicGeometry.AlgebraicSpace
