/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Sheaf.Paper.ProEtaleFiniteModelStalks
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.LeftExact

/-! # Rigidity of constant models at an overlap point

Source: Weil blueprint main-20261015, finite-local-systems-type proof,
Models are locally unique; Stacks Tag 099Y
(blueprint: lem-pe-constant-module-model-rigidity-universes).
-/

@[expose] public section
set_option autoImplicit false
universe t u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def scalarRestriction
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    (A : Type*) [CommRing A] (R : Sheaf J RingCat)
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶ R.obj) :
    SheafOfModules R ⥤ Sheaf J (ModuleCat A) where
  obj F := by
    let P := (PresheafOfModules.restrictScalars α).obj F.val
    let G : Cᵒᵖ ⥤ ModuleCat A :=
      { obj := P.obj
        map f := P.map f
        map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
        map_comp f g := by
          ext x
          exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
    exact ⟨G, Presheaf.isSheaf_of_isSheaf_comp J G
      (forget₂ (ModuleCat A) AddCommGrpCat) F.isSheaf⟩
  map f := { hom :=
    { app U := (ModuleCat.restrictScalars (α.app U).hom).map (f.val.app U)
      naturality _ _ g := by
        ext x
        exact PresheafOfModules.naturality_apply f.val g x } }

private noncomputable def constantModelFiberIso
    (X : Scheme.{t}) (Λ : Type u) [CommRing Λ] (U : X.ProEt)
    (Φ : ((ProEt.topology X).over U).Point.{t + 1})
    (M : ModuleCat.{max u (t + 1)} (ULift.{t + 1, u} Λ)) :
    let J := ProEt.topology X
    let R := (sheafCompose J
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
        ((constantSheaf J CommRingCat.{max u (t + 1)}).obj
          (CommRingCat.of (ULift.{t + 1, u} Λ)))
    let α := Functor.whiskerLeft (Over.forget U).op
      (Functor.whiskerRight (toSheafify J
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, u} Λ))))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}))
    Φ.sheafFiber.obj ((scalarRestriction (J.over U) (ULift.{t + 1, u} Λ)
      (R.over U) α).obj (proEtaleConstantModuleSheafOverOfUniverses X Λ U M)) ≅ M := by
  let : PreservesFilteredColimitsOfSize.{t + 1, t + 1}
      (CategoryTheory.forget (ModuleCat.{max u (t + 1)} (ULift.{t + 1, u} Λ))) :=
    preservesFilteredColimitsOfSize_shrink.{t + 1, u, t + 1, u} _
  let : PreservesFilteredColimitsOfSize.{t + 1, t + 1}
      (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)}) :=
    preservesFilteredColimitsOfSize_shrink.{t + 1, u, t + 1, u} _
  let J := ProEt.topology X
  let R := (sheafCompose J
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      ((constantSheaf J CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1, u} Λ)))
  let α := Functor.whiskerLeft (Over.forget U).op
    (Functor.whiskerRight (toSheafify J
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, u} Λ))))
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)}))
  let : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  let : HasSheafify (J.over U) AddCommGrpCat.{max u (t + 1)} :=
    instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover.{
      max u (t + 1), max u (t + 1) + 1, t, t + 1, max u (t + 1)} _ _
  let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  have := (proEtaleConstantRingUnit_over_locallyBijectiveOfUniverses X Λ U).1
  have := (proEtaleConstantRingUnit_over_locallyBijectiveOfUniverses X Λ U).2
  let P := proEtaleConstantModulePresheafOfUniverses (Over U) Λ M
  let η := (PresheafOfModules.sheafificationAdjunction
    (J := J.over U) (R := R.over U) α).unit.app P
  let G := (scalarRestriction (J.over U) (ULift.{t + 1, u} Λ) (R.over U) α).obj
    (proEtaleConstantModuleSheafOverOfUniverses X Λ U M)
  let η' : (Functor.const (Over U)ᵒᵖ).obj M ⟶ G.obj :=
    { app := η.app
      naturality _ _ f := by ext x; exact PresheafOfModules.naturality_apply η f x }
  have : Presheaf.IsLocallyInjective (J.over U) η' := by
    constructor
    intro T x y h
    exact Presheaf.equalizerSieve_mem (J.over U) (toSheafify (J.over U) P.presheaf) x y h
  have : Presheaf.IsLocallySurjective (J.over U) η' := by
    constructor
    intro T x
    exact Presheaf.imageSieve_mem (J.over U) (toSheafify (J.over U) P.presheaf) x
  have : IsIso (Φ.presheafFiber.map η') := by
    rw [← isIso_iff_of_reflects_iso _ (CategoryTheory.forget (ModuleCat (ULift.{t + 1, u} Λ))),
      isIso_iff_bijective]
    exact Φ.toPresheafFiber_map_bijective η'
  exact (asIso (Φ.presheafFiber.map η')).symm ≪≫ Φ.presheafFiberConstIso M

private noncomputable def moduleFiberOverIso
    (X : Scheme.{t}) (Φ : (ProEt.topology X).Point.{t + 1})
    {U : X.ProEt} (z : Φ.fiber.obj U) (A : Type u) [CommRing A]
    (F : Sheaf (ProEt.topology X) (ModuleCat.{max u (t + 1)} A)) :
    (Φ.over z).sheafFiber.obj (F.over U) ≅ Φ.sheafFiber.obj F :=
  Functor.Final.colimitIso
    ((FunctorToTypes.fromOverFunctorElementsEquivalence Φ.fiber z).functor ⋙
      Over.forget (Φ.fiber.elementsMk U z)).op
    ((CategoryOfElements.π Φ.fiber).op ⋙ F.obj)

/-- Two local constant models above the same base point are isomorphic.
Source: Weil blueprint main-20261015, finite-local-systems-type proof,
Models are locally unique, expanded using geometric fibres as in Stacks Tag 099Y
(blueprint: lem-pe-constant-module-model-rigidity-universes).

Proof: the equality of the two images gives a point of the scheme fibre product
of U and V. Choose an algebraic closure of its residue field and the resulting
geometric point. The pointed weakly-etale neighbourhood functor is a point of the
small pro-etale site: every fpqc weakly-etale covering lifts this geometric point,
as follows by splitting a nonempty weakly-etale scheme over an algebraically
closed field. Restrict that point to the two slices. The geometric fibre of a
constant module sheaf is its coefficient module, because sheafification preserves
this fibre and the pointed neighbourhood category is filtered and nonempty.
The slice fibre of F equals its original fibre by finality of the over-category
forgetful functor. Apply the two fibre functors to the given trivializations.
Their composites identify M and N with the same fibre of F. Constant scalar germ
maps identify the scalar actions with those of the original lifted coefficient
ring, so the resulting additive isomorphism is linear. This proof does not need
finite presentation, connectedness, or conservativity of geometric fibres. -/
theorem proEtaleConstantModule_model_rigidity (X : Scheme.{t}) (Λ : Type u) [CommRing Λ]
    (F : SheafOfModules.{max u (t + 1)}
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
          ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj
            (CommRingCat.of (ULift.{t + 1, u} Λ)))))
    (U V : X.ProEt)
    (M N : ModuleCat.{max u (t + 1)} (ULift.{t + 1, u} Λ))
    (eM : Nonempty (F.over U ≅ proEtaleConstantModuleSheafOverOfUniverses X Λ U M))
    (eN : Nonempty (F.over V ≅ proEtaleConstantModuleSheafOverOfUniverses X Λ V N))
    (x : U.left) (y : V.left) (hxy : U.hom x = V.hom y) : Nonempty (M ≅ N) := by
  let J := ProEt.topology X
  let R := (sheafCompose J
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
      ((constantSheaf J CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1, u} Λ)))
  let α := Functor.whiskerRight (toSheafify J
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1, u} Λ))))
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  let H := scalarRestriction J (ULift.{t + 1, u} Λ) R α
  let HU := scalarRestriction (J.over U) (ULift.{t + 1, u} Λ) (R.over U)
    (Functor.whiskerLeft (Over.forget U).op α)
  let HV := scalarRestriction (J.over V) (ULift.{t + 1, u} Λ) (R.over V)
    (Functor.whiskerLeft (Over.forget V).op α)
  obtain ⟨eM⟩ := eM
  obtain ⟨eN⟩ := eN
  let eMU : (H.obj F).over U ≅ HU.obj
      (proEtaleConstantModuleSheafOverOfUniverses X Λ U M) := HU.mapIso eM
  let eNV : (H.obj F).over V ≅ HV.obj
      (proEtaleConstantModuleSheafOverOfUniverses X Λ V N) := HV.mapIso eN
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  let Ω := AlgebraicClosure ((pullback U.hom V.hom).residueField z)
  let q : Spec (.of Ω) ⟶ pullback U.hom V.hom := (SpecToEquivOfField Ω _).2
    ⟨z, CommRingCat.ofHom (algebraMap ((pullback U.hom V.hom).residueField z) Ω)⟩
  let qX := q ≫ pullback.fst U.hom V.hom ≫ U.hom
  let Φ := AlgebraicGeometry.ProEtale.geometricPoint qX
  let zM : Φ.fiber.obj U := ⟨Over.homMk (q ≫ pullback.fst U.hom V.hom) rfl⟩
  let zN : Φ.fiber.obj V := ⟨Over.homMk (q ≫ pullback.snd U.hom V.hom)
    (by change (q ≫ pullback.snd U.hom V.hom) ≫ V.hom =
          q ≫ pullback.fst U.hom V.hom ≫ U.hom
        rw [Category.assoc, ← pullback.condition])⟩
  let sM := moduleFiberOverIso X Φ zM (ULift.{t + 1, u} Λ) (H.obj F)
  let sN := moduleFiberOverIso X Φ zN (ULift.{t + 1, u} Λ) (H.obj F)
  exact ⟨(constantModelFiberIso X Λ U (Φ.over zM) M).symm ≪≫
    ((Φ.over zM).sheafFiber.mapIso eMU).symm ≪≫ sM ≪≫ sN.symm ≪≫
    (Φ.over zN).sheafFiber.mapIso eNV ≪≫
    constantModelFiberIso X Λ V (Φ.over zN) N⟩

end AlgebraicGeometry.Scheme
