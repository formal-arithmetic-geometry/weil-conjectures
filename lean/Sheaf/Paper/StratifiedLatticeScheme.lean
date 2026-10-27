/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.ContinuousCoefficientModuleEncoding
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Paper.LatticeSheafBasic
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.Paper.ContinuousRingUniverseRealization
import Sheaf.Topology.ContinuousMapCondensedRingMap
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Sheaf.Paper.LatticeSheafLocallyConstant
import Sheaf.Paper.PadicIntegersInvertEll
import Sheaf.AlgebraicGeometry.WeaklyEtaleStability
import all Sheaf.AlgebraicGeometry.LisseLatticePresentationTransport
import all Sheaf.AlgebraicGeometry.LisseLatticeCoefficientNormalization
import all Sheaf.AlgebraicGeometry.IntegralLatticeCoefficientTransport
import all Sheaf.Paper.LocalSystemAffineDescentPresentation
import Sheaf.AlgebraicGeometry.CoproductFpqcEffectivity
import Sheaf.AlgebraicGeometry.CoproductModelRepresentsSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine

/-! # The scheme representing embedded integral lattices

Source: blueprint main-20261015, sk-lem-stratified-lattice-scheme, (1)--(3).
(blueprint: det-lem-stratified-lattice-scheme).

## Main definitions and statement

* `latticeCondensedField`, `latticeCondensedIntegers`: the actual condensed coefficients.
* `latticeCondensedRingInclusion`, `latticeCondensedInclusion`: their actual inclusion.
* `stratifiedLatticeModule`, `stratifiedLatticeScalarMap`, `stratifiedLatticeSectionRing`:
  the recorded sectionwise encoding of those same internal modules and scalar map.
* `exists_stratifiedLatticeScheme`: the three clauses of the lattice-scheme lemma.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CondensedRing

private def sectionRingIso (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (e : R ≅ S) [IsMonHom e.hom] :
    InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) R ≅
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) S where
  hom := sectionRingMap X e.hom
  inv := sectionRingMap X e.inv
  hom_inv_id := by
    ext T x
    change e.inv.hom.app T (e.hom.hom.app T x) = x
    exact ConcreteCategory.congr_hom (congrArg (fun f : R ⟶ R ↦ f.hom.app T)
      e.hom_inv_id) x
  inv_hom_id := by
    ext T x
    change e.hom.hom.app T (e.inv.hom.app T x) = x
    exact ConcreteCategory.congr_hom (congrArg (fun f : S ⟶ S ↦ f.hom.app T)
      e.inv_hom_id) x

private theorem universeComparison_natural (X : Scheme.{u})
    (T T' : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [TopologicalSpace T'] [CommRing T'] [IsTopologicalRing T']
    (f : T →+* T') (hf : Continuous f) :
    (upperStarFromPoint X).map (Profinite.continuousMapRingObjMapOfUniverse f hf) ≫
        ContinuousRingUniverse.comparison X T' =
      ContinuousRingUniverse.comparison X T ≫
        (sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
            forget₂ RingCat.{u + 1} Ab.{u + 1})).map
            (latticeCoefficientSheafMap X f hf) := by
  let adj := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  apply (adj.homEquiv _ _).injective
  dsimp only [upperStarFromPoint]
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simp only [ContinuousRingUniverse.comparison, adj, Equiv.apply_symm_apply]
  ext S g
  rfl

private def coefficientRealization (X : Scheme.{u}) (T : Type u)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [TotallyDisconnectedSpace T] :
    InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
      (condensedRingObj (Profinite.continuousCoefficientRingObj T) X) ≅
        latticeCoefficientSheaf X T := by
  let J := Scheme.ProEt.topology X
  let R := continuousCoefficientRingSheaf X T
  let A := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  let : IsCommMonObj A := Sheaf.isCommMonObj_sheafCompose_obj J R
    (fun V a b ↦ @mul_comm (ULift.{u + 1} C(V.unop.left, T)) inferInstance a b)
  letI := Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} T
  let := Profinite.isCommMonObj_continuousMapRingObjOfUniverse.{u, u} T
  let := ContinuousRingUniverse.comparison_isIso X T
  let φ := sectionRingIso X (asIso (ContinuousRingUniverse.comparison X T))
  let r : latticeModuleRing X T ≅ R := ObjectProperty.isoMk _
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))
  let j := (fullyFaithfulSheafCompose J
    CommRingCat.fullyFaithfulForget₂ToRingCat.{u + 1}).preimageIso
    (reconstructedRingIso X R ≪≫ r.symm)
  exact φ ≪≫ j

private theorem coefficientRealization_apply (X : Scheme.{u}) (T : Type u)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [TotallyDisconnectedSpace T]
    (U : X.ProEtᵒᵖ)
    (x : (condensedRingObj (Profinite.continuousCoefficientRingObj T) X).obj.obj U) :
    (coefficientRealization X T).hom.hom.app U x =
      (ContinuousRingUniverse.comparison X T).hom.app U x := by
  rfl

attribute [irreducible] coefficientRealization

private def coefficientFreeIso {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) {R S : Sheaf J RingCat.{u + 1}} (e : S ≅ R)
    (n : ℕ) :
    (SheafOfModules.pushforward (F := 𝟭 C) e.hom).obj
        (SheafOfModules.free (R := R) (ULift.{u + 1} (Fin n))) ≅
      SheafOfModules.free (R := S) (ULift.{u + 1} (Fin n)) := by
  let G := SheafOfModules.pushforward (F := 𝟭 C) e.hom
  have := SheafOfModules.isLeftAdjoint_pushforward_of_isIso
    (F := 𝟭 C) (R := R) (S := S) e.hom
  exact (SheafOfModules.mapFreeIso G _ (coefficientUnitIso J e).symm).symm

attribute [irreducible] sectionRingIso coefficientFreeIso

private theorem coefficientPushforwardCancel_apply
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R S : Sheaf J RingCat.{u + 1}} (e : S ≅ R) (M : SheafOfModules.{u + 1} R)
    (V : Cᵒᵖ)
    (x : ((SheafOfModules.pushforward (F := 𝟭 C) e.inv).obj
      ((SheafOfModules.pushforward (F := 𝟭 C) e.hom).obj M)).val.obj V) :
    (coefficientPushforwardCancel J e M).hom.val.app V x = (show M.val.obj V from x) := by
  unfold coefficientPushforwardCancel
  rfl

private theorem coefficientPushforwardCancel_inv_apply
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R S : Sheaf J RingCat.{u + 1}} (e : S ≅ R) (M : SheafOfModules.{u + 1} R)
    (V : Cᵒᵖ) (x : M.val.obj V) :
    (coefficientPushforwardCancel J e M).inv.val.app V x = x := by
  unfold coefficientPushforwardCancel
  rfl

private theorem coefficientTensorPresheafIso_one
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {R S R' S' : Sheaf J CommRingCat.{u + 1}}
    (a : R ⟶ S) (a' : R' ⟶ S') (eR : R' ≅ R) (eS : S' ≅ S)
    (hsquare : a' ≫ eS.hom = eR.hom ≫ a)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R'))
    (V : Cᵒᵖ) (m : M.val.obj V) :
    (coefficientTensorPresheafIso J a a' eR eS hsquare M).hom.app V
      ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (a.hom.app V).hom]
        (show ((SheafOfModules.pushforward (F := 𝟭 C)
          (R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R')
          (S := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
          ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            eR.inv)).obj M).val.obj V from m)) =
      (1 : S'.obj.obj V) ⊗ₜ[R'.obj.obj V, (a'.hom.app V).hom] m := by
  let er := ((sheafToPresheaf J CommRingCat).mapIso eR).app V
  let es := ((sheafToPresheaf J CommRingCat).mapIso eS).app V
  have square : a'.hom.app V ≫ es.hom = er.hom ≫ a.hom.app V :=
    congrArg (fun t : R' ⟶ S ↦ t.hom.app V) hsquare
  have ht := coefficientTensorIso_hom_tmul
    (R.obj.obj V) (S.obj.obj V) (R'.obj.obj V) (S'.obj.obj V)
    (a.hom.app V) (a'.hom.app V) er es square (M.val.obj V) 1 m
  simp only [map_one] at ht
  unfold coefficientTensorPresheafIso
  exact ht

private theorem pushforwardSheafificationIso_unit
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (R S : Sheaf J RingCat.{u + 1}) (φ : S ⟶ R)
    (P : PresheafOfModules.{u + 1} R.obj) :
    (PresheafOfModules.sheafificationAdjunction (R := S) (𝟙 _)).unit.app
        ((PresheafOfModules.pushforward (F := 𝟭 C) φ.hom).obj P) ≫
        (pushforwardSheafificationIso J J (𝟭 C) R S φ P).hom.val =
      (PresheafOfModules.pushforward (F := 𝟭 C) φ.hom).map
        ((PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 _)).unit.app P) := by
  unfold pushforwardSheafificationIso
  let N := (SheafOfModules.pushforward (F := 𝟭 C) (R := R) (S := S) φ).obj
    ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj P)
  change (PresheafOfModules.sheafificationHomEquiv (𝟙 S.obj)
    (P := (PresheafOfModules.pushforward (F := 𝟭 C) φ.hom).obj P) (F := N))
    ((PresheafOfModules.sheafificationHomEquiv (𝟙 S.obj)).symm _) = _
  exact Equiv.apply_symm_apply _ _

private def sheafificationTransport
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (R S : Sheaf J RingCat.{u + 1}) (φ : S ⟶ R)
    (P : PresheafOfModules.{u + 1} S.obj) (P' : PresheafOfModules.{u + 1} R.obj)
    (t : P ≅ (PresheafOfModules.pushforward (F := 𝟭 C) φ.hom).obj P') :
    (PresheafOfModules.sheafification (R := S) (𝟙 _)).obj P ≅
      (SheafOfModules.pushforward (F := 𝟭 C) φ).obj
        ((PresheafOfModules.sheafification (R := R) (𝟙 _)).obj P') :=
  (PresheafOfModules.sheafification (R := S) (𝟙 _)).mapIso t ≪≫
    pushforwardSheafificationIso J J (𝟭 C) R S φ P'

private theorem sheafificationTransport_unit
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (R S : Sheaf J RingCat.{u + 1}) (φ : S ⟶ R)
    (P : PresheafOfModules.{u + 1} S.obj) (P' : PresheafOfModules.{u + 1} R.obj)
    (t : P ≅ (PresheafOfModules.pushforward (F := 𝟭 C) φ.hom).obj P')
    (V : Cᵒᵖ) (x : P.obj V) :
    (sheafificationTransport J R S φ P P' t).hom.val.app V
        (((PresheafOfModules.sheafificationAdjunction (R := S) (𝟙 _)).unit.app P).app V x) =
      ((PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 _)).unit.app P').app V
        (t.hom.app V x) := by
  let adj := PresheafOfModules.sheafificationAdjunction (R := S) (𝟙 S.obj)
  let G := PresheafOfModules.pushforward (F := 𝟭 C)
    (R := R.obj) (S := S.obj) φ.hom
  let g := G.map ((PresheafOfModules.sheafificationAdjunction
    (R := R) (𝟙 R.obj)).unit.app P')
  have hn := adj.unit.naturality t.hom
  have hcomp : adj.unit.app P ≫ (sheafificationTransport J R S φ P P' t).hom.val =
      t.hom ≫ g := by
    dsimp only [sheafificationTransport, Iso.trans_hom, SheafOfModules.comp_val]
    erw [← Category.assoc, ← hn, Category.assoc, pushforwardSheafificationIso_unit]
    rfl
  exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.app V) hcomp) x

attribute [irreducible] sheafificationTransport

/-- Transport the actual pair, retaining its embedded image. The tensor comparison
sends 1 tensor m to 1 tensor m; the sheafification adjunction proves this after sheafifying. -/
private theorem pair_of_coefficient_iso {X : Scheme.{u}}
    {R S R' S' : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (a' : R' ⟶ S') (eR : R' ≅ R) (eS : S' ≅ S)
    (hsquare : a' ≫ eS.hom = eR.hom ≫ a)
    (L : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (L' : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S'))
    (eL : L' ≅ (SheafOfModules.pushforward (F := 𝟭 X.ProEt)
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map eS.hom)).obj L)
    (U : X.ProEt) (P : IntegralLatticePair a' L' U) :
    ∃ Q : IntegralLatticePair a L U, ∀ T : (Over U)ᵒᵖ,
      Q.image T = Set.image (eL.hom.val.app (op T.unop.left)) (P.image T) := by
  let K := Scheme.ProEt.topology X
  let J := K.over U
  let res := (Over.forget U).sheafPushforwardContinuous CommRingCat.{u + 1} J K
  let er := res.mapIso eR
  let es := res.mapIso eS
  let a₀ := latticeScalarMap a U
  let a'₀ := latticeScalarMap a' U
  have square : a'₀ ≫ es.hom = er.hom ≫ a₀ := by
    change res.map a' ≫ res.map eS.hom = res.map eR.hom ≫ res.map a
    simpa only [Functor.map_comp] using congrArg (fun t : R' ⟶ S ↦ res.map t) hsquare
  let forgetRing := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let erRing := forgetRing.mapIso er
  let esRing := forgetRing.mapIso es
  let M := (SheafOfModules.pushforward (F := 𝟭 (Over U)) erRing.inv).obj P.module
  have := P.locallyFree
  have hfree : M.IsFiniteLocallyFree :=
    finiteLocallyFree_restrict J _ _ erRing.symm P.module
  let T₀ := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a'₀ P.module
  let t := coefficientTensorPresheafIso J a₀ a'₀ er es square P.module
  let ψ := SheafOfModules.pushforward (F := 𝟭 (Over U))
    (R := forgetRing.obj (S'.over U)) (S := forgetRing.obj (S.over U)) esRing.inv
  let χ := SheafOfModules.pushforward (F := 𝟭 (Over U))
    (R := forgetRing.obj (S.over U)) (S := forgetRing.obj (S'.over U)) esRing.hom
  let rationalization : SheafOfModules.changeOfRings.{u, u + 1, u + 1} a₀ M ≅
      ψ.obj (SheafOfModules.changeOfRings.{u, u + 1, u + 1} a'₀ P.module) :=
    sheafificationTransport J (forgetRing.obj (S'.over U))
      (forgetRing.obj (S.over U)) esRing.inv _ T₀ t
  let el : L'.over U ≅ χ.obj (L.over U) :=
    (SheafOfModules.overFunctor
      ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S') U).mapIso eL
  let r₄ := coefficientPushforwardCancel J esRing (L.over U)
  let Q : IntegralLatticePair a L U :=
    { module := M, locallyFree := hfree
      rationalization := rationalization ≪≫ ψ.mapIso P.rationalization ≪≫
        ψ.mapIso el ≪≫ r₄ }
  refine ⟨Q, ?_⟩
  intro T
  rw [IntegralLatticePair.image, IntegralLatticePair.image, ← Set.range_comp']
  apply congrArg Set.range
  funext m
  dsimp only [Q, Iso.trans_hom, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  change r₄.hom.val.app T
    (el.hom.val.app T (P.rationalization.hom.val.app T
      (rationalization.hom.val.app T _))) = _
  dsimp only [r₄]
  rw [coefficientPushforwardCancel_apply]
  change eL.hom.val.app (op T.unop.left)
    (P.rationalization.hom.val.app T (rationalization.hom.val.app T _)) = _
  congr 2
  let x : (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a₀ M).obj T :=
    (1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T, (a₀.hom.app T).hom] m
  have ht := sheafificationTransport_unit J (forgetRing.obj (S'.over U))
    (forgetRing.obj (S.over U)) esRing.inv _ T₀ t T x
  refine ht.trans ?_
  have htt := coefficientTensorPresheafIso_one J a₀ a'₀ er es square P.module T m
  exact congrArg (fun z ↦ ((PresheafOfModules.sheafificationAdjunction
    (R := forgetRing.obj (S'.over U)) (𝟙 _)).unit.app T₀).app T z) htt


/-- Transport the presentation through the image-preserving pair construction in both
directions. The image criterion supplies its kernel and restriction compatibility. -/
private theorem presentation_of_coefficient_iso {X : Scheme.{u}}
    {R S R' S' : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (a' : R' ⟶ S') (eR : R' ≅ R) (eS : S' ≅ S)
    (hsquare : a' ≫ eS.hom = eR.hom ≫ a)
    (ha : ∀ T, Function.Injective ((a.hom.app T).hom))
    (ha' : ∀ T, Function.Injective ((a'.hom.app T).hom))
    (L : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 2)))
    (c' : ∀ U : X.ProEt, IntegralLatticePair a'
      ((SheafOfModules.pushforward (F := 𝟭 X.ProEt)
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map eS.hom)).obj L) U →
        F.obj.obj (op U))
    (hc' : IsLatticeClassPresentation a' _ F c') :
    ∃ c : ∀ U : X.ProEt, IntegralLatticePair a L U → F.obj.obj (op U),
      IsLatticeClassPresentation a L F c := by
  classical
  let J := Scheme.ProEt.topology X
  let fr := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let L' := (SheafOfModules.pushforward (F := 𝟭 X.ProEt) (fr.map eS.hom)).obj L
  have hsquare' : a ≫ eS.inv = eR.inv ≫ a' := by
    apply (cancel_mono eS.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hsquare, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have forward (U : X.ProEt) (P : IntegralLatticePair a L U) :
      ∃ Q : IntegralLatticePair a' L' U, ∀ T : (Over U)ᵒᵖ, Q.image T = P.image T := by
    obtain ⟨Q, hQ⟩ := pair_of_coefficient_iso a' a eR.symm eS.symm hsquare' L' L
      (coefficientPushforwardCancel J (fr.mapIso eS) L).symm U P
    refine ⟨Q, ?_⟩
    intro T
    have ht := hQ T
    rw [ht]
    change Set.image (fun x ↦ (coefficientPushforwardCancel J (fr.mapIso eS) L).inv.val.app
      (op T.unop.left) x) (P.image T) = P.image T
    simp only [coefficientPushforwardCancel_inv_apply]
    exact Set.image_id _
  have backward (U : X.ProEt) (Q : IntegralLatticePair a' L' U) :
      ∃ P : IntegralLatticePair a L U, ∀ T : (Over U)ᵒᵖ, P.image T = Q.image T := by
    obtain ⟨P, hP⟩ := pair_of_coefficient_iso a a' eR eS hsquare L L' (Iso.refl _) U Q
    refine ⟨P, ?_⟩
    intro T
    have ht := hP T
    change P.image T = Set.image id (Q.image T) at ht
    simpa only [Set.image_id] using ht
  let d (U : X.ProEt) (P : IntegralLatticePair a L U) := (forward U P).choose
  have hd (U : X.ProEt) (P : IntegralLatticePair a L U) (T : (Over U)ᵒᵖ) :
      (d U P).image T = P.image T := (forward U P).choose_spec T
  refine ⟨fun U P ↦ c' U (d U P), ?_, ?_, ?_⟩
  · intro U x
    obtain ⟨Q, hQ⟩ := hc'.1 U x
    obtain ⟨P, hP⟩ := backward U Q
    refine ⟨P, ?_⟩
    rw [← hQ]
    apply (hc'.2.1 U _ _).2
    exact (IntegralLatticePair.equivalent_iff_image_eq a' L' U
      (fun T ↦ ha' (op T.unop.left)) _ _).2 (fun T ↦ (hd U P T).trans (hP T))
  · intro U P Q
    rw [hc'.2.1, IntegralLatticePair.equivalent_iff_image_eq a' L' U
      (fun T ↦ ha' (op T.unop.left)), IntegralLatticePair.equivalent_iff_image_eq a L U
      (fun T ↦ ha (op T.unop.left))]
    simp only [hd]
  · intro U V f P Q
    rw [hc'.2.2]
    simp only [hd]

/-- Shrink the lattice-class sheaf, apply affine coproduct fpqc descent, and transport
the representing bijections back. The identity section gives the universal pair. -/
private theorem latticeClass_representable {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (L : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 2)))
    (c : ∀ U : X.ProEt, IntegralLatticePair a L U → F.obj.obj (op U))
    (hc : IsLatticeClassPresentation a L F c)
    (A : Type u) [Nonempty A]
    (I : Type (u + 1)) (U : I → X.ProEt)
    (hcover : (Scheme.ProEt.topology X).CoversTop U)
    (hconst : ∀ i, Nonempty (F.over (U i) ≅
      (constantSheaf ((Scheme.ProEt.topology X).over (U i)) (Type (u + 2))).obj
        (ULift.{u + 2} A))) :
    ∃ Q : X.ProEt, IsSeparated Q.hom ∧ Etale Q.hom ∧ Surjective Q.hom ∧
      ∃ ρ : F.obj ≅
        ((Scheme.ProEt.forget X).op ⋙ yoneda.obj (Over.mk Q.hom)) ⋙ uliftFunctor.{u + 2},
        ∃ M : IntegralLatticePair a L Q,
          (ρ.hom.app (op Q) (c Q M)).down = 𝟙 (Over.mk Q.hom) := by
  classical
  obtain ⟨F₀, e, he⟩ := small_latticeClass_sheaf a L F c hc
  have htriv (i : I) : Nonempty
      ((Scheme.proEtaleSetRestriction X (U i)).obj F₀ ≅
        (constantSheaf (Scheme.ProEt.topology (U i).left) (Type (u + 1))).obj
          (ULift.{u + 1} A)) := by
    exact ⟨constant_slice_smallSite F₀ (U i) _
      (small_constant_slice F F₀ e he (U i) A (hconst i).some.symm)⟩
  let T : X.ProEt := Scheme.ProEt.mk (𝟙 X)
  obtain ⟨P, hP, hle⟩ := Scheme.ProEt.mem_topology_iff.mp (hcover T)
  obtain ⟨J, W, π, rfl⟩ := P.exists_eq_ofArrows
  have hw (j : J) := hle _ _ ⟨j⟩
  choose α hfα using hw
  let f := fun j ↦ (hfα j).some
  have hW : Presieve.ofArrows (fun j ↦ (W j).left) (fun j ↦ (W j).hom) ∈
      Scheme.proetalePrecoverage X := by
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at hP
    change Presieve.ofArrows (fun j ↦ (W j).left) (fun j ↦ (π j).left) ∈
      Scheme.proetalePrecoverage X at hP
    have hwπ (j : J) : (π j).left = (W j).hom := by
      have hh := MorphismProperty.Over.w (π j)
      change (π j).left ≫ 𝟙 X = (W j).hom at hh
      exact (Category.comp_id _).symm.trans hh
    simpa only [hwπ] using hP
  have htw (j : J) : Nonempty
      ((Scheme.proEtaleSetRestriction X (W j)).obj F₀ ≅
        (constantSheaf (Scheme.ProEt.topology (W j).left) (Type (u + 1))).obj
          (ULift.{u + 1} A)) := by
    exact Scheme.ProEt.restriction_trivialization X F₀ A (U (α j)) (W j) (f j)
      (htriv (α j)).some
  obtain ⟨n, B, β, refinement, V, ι, hB, hι, hcol, hV, hf, hs, hq,
    hfp, hp, ψ, k, hk, hlabel, hclopen, D, hD, hδ⟩ :=
    Scheme.ProEt.localSystem_affine_descent_presentation X A F₀ J W hW
      (fun j ↦ (htw j).some)
  let : IsAffine V.left := hV
  let : Flat V.hom := hf
  let : Surjective V.hom := hs
  let : QuasiCompact V.hom := hq
  let : IsAffine ((𝟭 Scheme).obj V.left) := hV
  obtain ⟨Y, q, hpb, hqinv⟩ := (coproduct_fpqc_effectivity V.hom hfp A D).2
  let η : (Over.pullback V.hom).obj Y ≅ Scheme.ProEt.localSystemCopies V.left A :=
    Over.isoMk hpb.isoPullback.symm (by simp [Scheme.ProEt.localSystemCopies])
  let b (Z : V.left.ProEt) :
      F₀.obj.obj (op ((MorphismProperty.Over.map ⊤ V.prop).obj Z)) ≃
        (Over.mk Z.hom ⟶ Over.mk (coproductModelProjection V.left A)) :=
    ((((sheafToPresheaf _ _).mapIso ψ ≪≫ k).app (op Z)).toEquiv).trans Equiv.ulift
  have hb (Z Z' : V.left.ProEt) (g : Z' ⟶ Z)
      (s : F₀.obj.obj (op ((MorphismProperty.Over.map ⊤ V.prop).obj Z))) :
      b Z' (F₀.obj.map ((MorphismProperty.Over.map ⊤ V.prop).map g).op s) =
        Over.homMk g.left (MorphismProperty.Over.w g) ≫ b Z s := by
    have hh := congrArg (fun m ↦ m s)
      ((ψ.hom.hom ≫ k.hom).naturality g.op)
    exact congrArg ULift.down hh
  have hd (Z : Scheme.{u}) (f₁ f₂ : Z ⟶ V.left)
      (hf₁ : WeaklyEtale f₁) (hf₂ : WeaklyEtale f₂) (h : f₁ ≫ V.hom = f₂ ≫ V.hom)
      (s : F₀.obj.obj (op ((MorphismProperty.Over.map ⊤ V.prop).obj
        (@Scheme.ProEt.mk _ _ f₁ hf₁)))) :
      D.transport f₁ f₂ h (b (@Scheme.ProEt.mk _ _ f₁ hf₁) s) =
        b (@Scheme.ProEt.mk _ _ f₂ hf₂)
          (F₀.obj.map (MorphismProperty.Over.homMk (𝟙 Z) (by
            exact (Category.id_comp _).trans h)).op s) := by
    let := hf₁
    let := hf₂
    let Z₁ : V.left.ProEt := Scheme.ProEt.mk f₁
    let Z₂ : V.left.ProEt := Scheme.ProEt.mk f₂
    have hi (Z' : V.left.ProEt) (t : F₀.obj.obj
        (op ((MorphismProperty.Over.map ⊤ V.prop).obj Z'))) :
        ψ.inv.hom.app (op Z') (k.inv.app (op Z') (ULift.up (b Z' t))) = t := by
      exact ConcreteCategory.congr_hom
        (((sheafToPresheaf _ _).mapIso ψ ≪≫ k).hom_inv_id_app (op Z')) t
    have ht := hD Z f₁ f₂ h (b Z₁ s)
    rw [hi] at ht
    have hm := Scheme.ProEt.map_identity_heq X Z F₀
      (f₂ ≫ V.hom) (f₁ ≫ V.hom) h.symm s
    have ht' := eq_of_heq (ht.trans hm.symm)
    have hz := congrArg (fun t ↦ b Z₂ t) ht'
    have hcancel (z : (Scheme.ProEt.localSystemCopiesHom V.left A).obj (op Z₂)) :
        b Z₂ (ψ.inv.hom.app (op Z₂) (k.inv.app (op Z₂) z)) = z.down := by
      exact congrArg ULift.down (ConcreteCategory.congr_hom
        (((sheafToPresheaf _ _).mapIso ψ ≪≫ k).inv_hom_id_app (op Z₂)) z)
    exact (hcancel _).symm.trans hz
  have hη (Z : Scheme.{u}) (f₁ f₂ : Z ⟶ V.left) (h : f₁ ≫ V.hom = f₂ ≫ V.hom)
      (z : Over.mk f₁ ⟶ Over.mk (coproductModelProjection V.left A)) :
      (D.transport f₁ f₂ h z).left ≫ η.inv.left ≫ pullback.fst Y.hom V.hom =
        z.left ≫ η.inv.left ≫ pullback.fst Y.hom V.hom := by
    simpa [η] using hqinv f₁ f₂ h z
  obtain ⟨hsep, het, hsurj, hY, hTA, bY, hbY, huniq⟩ :=
    coproductModel_represents_sheaf V.hom hfp A F₀ b hb D hd Y.hom η hη
  let Q : X.ProEt := @Scheme.ProEt.mk _ _ Y.hom hY
  let ρ : F.obj ≅
      ((Scheme.ProEt.forget X).op ⋙ yoneda.obj (Over.mk Q.hom)) ⋙
        uliftFunctor.{u + 2} :=
    NatIso.ofComponents (fun Z ↦ ((e Z.unop).trans ((bY Z.unop).trans
      Equiv.ulift.symm)).toIso) (by
        intro Z Z' g
        ext x
        exact congrArg ULift.up ((congrArg (bY Z'.unop) (he _ _ g.unop x)).trans
          (hbY.1 _ _ g.unop _)))
  obtain ⟨M, hM⟩ := hc.1 Q ((e Q).symm ((bY Q).symm (𝟙 (Over.mk Q.hom))))
  refine ⟨Q, hsep, het, hsurj inferInstance, ρ, M, ?_⟩
  change bY Q (e Q (c Q M)) = 𝟙 (Over.mk Q.hom)
  rw [hM, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The rational condensed coefficient ring, with the canonical extension topology.
Source: blueprint sk-lem-stratified-lattice-scheme, coefficient convention.
(blueprint: det-lem-stratified-lattice-scheme). -/
abbrev latticeCondensedField (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
  Profinite.continuousCoefficientRingObj (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))

/-- The integral condensed coefficient ring uses the induced valuation-ring topology.
Source: blueprint sk-lem-stratified-lattice-scheme, coefficient convention.
(blueprint: det-lem-stratified-lattice-scheme). -/
abbrev latticeCondensedIntegers (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
  Profinite.continuousCoefficientRingObj (latticeCoefficientIntegers l E)

/-- Inclusion of integral continuous functions into rational continuous functions.
Source: blueprint sk-lem-stratified-lattice-scheme, coefficient convention.
(blueprint: det-lem-stratified-lattice-scheme). -/
def latticeCondensedRingInclusion (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Profinite.continuousCoefficientRingSheaf (latticeCoefficientIntegers l E) ⟶
      Profinite.continuousCoefficientRingSheaf
        (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) :=
  ⟨{ app := fun S ↦ RingCat.ofHom
      (ULift.ringEquiv.symm.toRingHom.comp
        (((latticeCoefficientIntegers l E).subtype.compLeftContinuous S.unop
          continuous_subtype_val).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The actual condensed coefficient inclusion as a bundled morphism of ring objects.
Source: blueprint sk-lem-stratified-lattice-scheme, coefficient convention.
(blueprint: det-lem-stratified-lattice-scheme). -/
def latticeCondensedInclusion (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Mon.mk (latticeCondensedIntegers l E) ⟶ Mon.mk (latticeCondensedField l E) :=
  Mon.ofHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (latticeCondensedRingInclusion l E))

/-- The sectionwise presentation of the given internal rational module, using the
recorded equivalence, whose underlying abelian sheaf and restrictions are unchanged.
Source: blueprint sk-lem-stratified-lattice-scheme, module-object convention.
(blueprint: det-lem-stratified-lattice-scheme). -/
abbrev stratifiedLatticeModule (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (latticeCondensedField l E) X)) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
    (condensedRingObj (latticeCondensedField l E) X)).functor.obj L

/-- The integral-to-rational scalar map in the recorded section-ring reconstruction.
Source: blueprint sk-lem-stratified-lattice-scheme, module-object convention.
(blueprint: det-lem-stratified-lattice-scheme). -/
abbrev stratifiedLatticeScalarMap (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :=
  sectionRingMap X (coefficientMap (latticeCondensedInclusion l E).hom X)

/-- The rational section ring of the same internal coefficient object.
Source: blueprint sk-lem-stratified-lattice-scheme, module-object convention.
(blueprint: det-lem-stratified-lattice-scheme). -/
abbrev stratifiedLatticeSectionRing (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
      (condensedRingObj (latticeCondensedField l E) X))

/-- The lattice functor is a sheaf, is locally the constant lattice-coset sheaf,
and is represented by a separated surjective etale scheme carrying its universal lattice.
Source: blueprint main-20261015, sk-lem-stratified-lattice-scheme, (1)--(3).
(blueprint: det-lem-stratified-lattice-scheme).

Proof: the canonical continuous-ring comparison identifies reconstructed integral and
rational coefficients. Its inverse-image adjunction shows that the coefficient square
commutes. Transport lattice pairs along this square: the tensor comparison sends
1 tensor m to 1 tensor m, and naturality of sheafification preserves their embedded
images. The image criterion transports the exact lattice-class presentation, including
restriction maps. Transport finite free charts and apply the local lattice-classification
theorem to obtain the constant-coset descriptions.

Shrink the class sheaf using its presentation by subobjects of a fixed module. Refine
the given covering family to a precoverage family and apply the affine local-system
descent-presentation theorem. Its coproduct scheme and descent datum are effective by
coproduct fpqc effectivity. The representing-sheaf theorem gives natural representing
bijections and a separated, etale, surjective structure map. Compose those bijections
with the size-change bijections to recover the required representing isomorphism.
The inverse image of the identity has a lattice-pair representative by surjectivity of
the class presentation; the inverse identities give the displayed universal equation.
Rank zero and empty bases are included throughout. -/
theorem exists_stratifiedLatticeScheme (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (r : ℕ)
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (latticeCondensedField l E) X))
    (_hL : ∃ (I : Type (u + 1)) (U : I → X.ProEt),
      (Scheme.ProEt.topology X).CoversTop U ∧ ∀ i : I,
      Nonempty ((stratifiedLatticeModule l E X L).over (U i) ≅
        SheafOfModules.free (R := (stratifiedLatticeSectionRing l E X).over (U i))
          (ULift.{u + 1} (Fin r)))) :
    ∃ (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 2)))
      (c : ∀ U : X.ProEt,
        IntegralLatticePair (stratifiedLatticeScalarMap l E X)
          (stratifiedLatticeModule l E X L) U → F.obj.obj (op U)),
      IsLatticeClassPresentation (stratifiedLatticeScalarMap l E X)
        (stratifiedLatticeModule l E X L) F c ∧
      (∀ (V : X.ProEt)
        (_t : (stratifiedLatticeModule l E X L).over V ≅
          SheafOfModules.free (R := (stratifiedLatticeSectionRing l E X).over V)
            (ULift.{u + 1} (Fin r))),
        Nonempty (F.over V ≅
          (constantSheaf ((Scheme.ProEt.topology X).over V) (Type (u + 2))).obj
            (ULift.{u + 2} (integralMatrixCosets (latticeCoefficientIntegers l E) r)))) ∧
      ∃ Q : X.ProEt, IsSeparated Q.hom ∧ Etale Q.hom ∧ Surjective Q.hom ∧
        ∃ ρ : F.obj ≅
          ((Scheme.ProEt.forget X).op ⋙ yoneda.obj (Over.mk Q.hom)) ⋙ uliftFunctor.{u + 2},
          ∃ M : IntegralLatticePair (stratifiedLatticeScalarMap l E X)
              (stratifiedLatticeModule l E X L) Q,
            (ρ.hom.app (op Q) (c Q M)).down = 𝟙 (Over.mk Q.hom) := by
  classical
  let K := WithAbs (Padic.coefficientExtensionAbsoluteValue l E)
  let A := latticeCoefficientIntegers l E
  let : IsUltrametricDist K :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm (by
      intro x y
      exact isNonarchimedean_spectralNorm (K := ℚ_[l]) (L := E) x.ofAbs y.ofAbs)
  let : TotallyDisconnectedSpace K := inferInstance
  let : TotallyDisconnectedSpace A := inferInstance
  let J := Scheme.ProEt.topology X
  let fr := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let a := stratifiedLatticeScalarMap l E X
  let a' := integralLatticeCoefficientMap X l E
  let eA := coefficientRealization X A
  let eK := coefficientRealization X K
  have square₀ : a ≫ eK.hom = eA.hom ≫ a' := by
    ext T x
    change eK.hom.hom.app T (a.hom.app T x) = a'.hom.app T (eA.hom.hom.app T x)
    dsimp only [eK, eA]
    rw [coefficientRealization_apply, coefficientRealization_apply]
    have hn := universeComparison_natural X A K A.subtype continuous_subtype_val
    have hh := congrArg (fun f ↦ f.hom.app T) hn
    exact ConcreteCategory.congr_hom hh x
  have square : a' ≫ eK.inv = eA.inv ≫ a := by
    apply (cancel_mono eK.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [square₀, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have ha' (T : X.ProEtᵒᵖ) : Function.Injective ((a'.hom.app T).hom) := by
    intro x y h
    apply ULift.ext
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    exact congrArg (fun t ↦ t.down z) h
  have ha (T : X.ProEtᵒᵖ) : Function.Injective ((a.hom.app T).hom) := by
    intro x y h
    apply (((sheafToPresheaf J CommRingCat).mapIso eA).app T).commRingCatIsoToRingEquiv.injective
    apply ha' T
    have hx := ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.hom.app T) square₀) x
    have hy := ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.hom.app T) square₀) y
    exact hx.symm.trans ((congrArg (fun t ↦ eK.hom.hom.app T t) h).trans hy)
  let M := stratifiedLatticeModule l E X L
  obtain ⟨I, U, hcover, hframes⟩ := _hL
  let : M.IsFiniteLocallyFree :=
    SheafOfModules.isFiniteLocallyFree_of_exists_over_iso_free U hcover
      (fun _ ↦ ULift.{u + 1} (Fin r)) hframes
  let M' := (SheafOfModules.pushforward (F := 𝟭 X.ProEt) (fr.map eK.inv)).obj M
  let : M'.IsFiniteLocallyFree := finiteLocallyFree_restrict J _ _ (fr.mapIso eK.symm) M
  have frame (V : X.ProEt)
      (t : M.over V ≅ SheafOfModules.free
        (R := (stratifiedLatticeSectionRing l E X).over V) (ULift.{u + 1} (Fin r))) :
      M'.over V ≅ latticeFreeSheaf X K V r := by
    let res := (Over.forget V).sheafPushforwardContinuous RingCat.{u + 1} (J.over V) J
    let e := res.mapIso (fr.mapIso eK.symm)
    let G := SheafOfModules.pushforward (F := 𝟭 (Over V))
      (R := (stratifiedLatticeSectionRing l E X).over V)
      (S := (latticeModuleRing X K).over V) e.hom
    exact G.mapIso t ≪≫ coefficientFreeIso (J.over V) e r
  obtain ⟨F, c', hc', hlocal⟩ := integralLatticeSheaf_locallyConstant X l E M'
  obtain ⟨c, hc⟩ := presentation_of_coefficient_iso a a' eA.symm eK.symm square
    ha ha' M F c' hc'
  have hconst (V : X.ProEt)
      (t : M.over V ≅ SheafOfModules.free
        (R := (stratifiedLatticeSectionRing l E X).over V) (ULift.{u + 1} (Fin r))) :
      Nonempty (F.over V ≅ (constantSheaf (J.over V) (Type (u + 2))).obj
        (ULift.{u + 2} (integralMatrixCosets A r))) :=
    ⟨(hlocal V r (frame V t)).choose.symm⟩
  refine ⟨F, c, hc, hconst, ?_⟩
  exact latticeClass_representable a M F c hc (integralMatrixCosets A r) I U hcover
    (fun i ↦ hconst (U i) (hframes i).some)

end AlgebraicGeometry.ProEtale.CondensedRing
