/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Comma.Arrow
import Sheaf.AlgebraicGeometry.ProperFlatOpenSquareMateIso
import Sheaf.AlgebraicGeometry.NewBaseOpenMateFactorization
import Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeHbeta
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap

/-! # One-open compatibility of right-adjoint mates

Source: Stacks Project, duality.tex, Remark 48.6.1 (Tag 0E9S).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

-- Compare exact restriction and derived pullback via their left-derived universal properties.
private theorem open_pullback_restriction_iso (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))] :
    Nonempty ((schemeOpenRestriction X U).mapDerivedCategory ≅ derivedPullback U.ι) :=
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in by
  classical
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    T, hT, hTmap, hTadd, ε, hL, htri, hK⟩ :=
      Classical.choose_spec (exists_derivedPullback U.ι)
  have ht : T = Scheme.Modules.tensorPullback U.ι :=
    CategoryTheory.Functor.ext hT (fun _ _ φ ↦ hTmap φ)
  subst T
  let R := schemeOpenRestriction X U
  have : R.Additive := inferInstance
  have : (Scheme.Modules.tensorPullback U.ι).Additive := hTadd
  let θ : R ≅ Scheme.Modules.tensorPullback U.ι :=
    Scheme.Modules.overFunctorEquiv U ≪≫
      ((Scheme.Modules.nonempty_tensorPullbackAdjunction U.ι).some.leftAdjointUniq
        (Scheme.Modules.restrictAdjunction U.ι)).symm
  let θh : R.mapHomotopyCategory (.up ℤ) ≅
      (Scheme.Modules.tensorPullback U.ι).mapHomotopyCategory (.up ℤ) :=
    { hom := θ.hom.mapHomotopyCategory (.up ℤ)
      inv := θ.inv.mapHomotopyCategory (.up ℤ)
      hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp
      inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp]; simp }
  let e := R.mapDerivedCategoryFactorsh ≪≫ Functor.isoWhiskerRight θh DerivedCategory.Qh
  let S := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)
  have : R.mapDerivedCategory.IsLeftDerivedFunctor e.hom S :=
    Functor.isLeftDerivedFunctor_of_inverts S _ e
  have : (derivedPullback U.ι).IsLeftDerivedFunctor ε S := hL
  have : R.mapDerivedCategory.IsRightKanExtension e.hom :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension _ _ S
  have : (derivedPullback U.ι).IsRightKanExtension ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension _ _ S
  exact ⟨Functor.rightKanExtensionUnique R.mapDerivedCategory e.hom (derivedPullback U.ι) ε⟩

set_option maxHeartbeats 800000 in
-- The two QCoh lifts and iterated pullbacks require additional definitional-equality checks.
/-- Compatibility of the canonical mate with an open in the new base alone.
There is no open in the old base and no second local right adjoint.
Source: Stacks Project, duality.tex, Remark 48.6.1 (Tag 0E9S),
Lemma 48.5.2 (Tag 0ATR), and Tag 0E4J.
(blueprint: lem-sc-right-adjoint-mate-new-base-open)

Proof: Paste the square for W -> Y' with X' = X times_Y Y'. The projection
identities characterize the supplied isomorphism r from f' inverse(W) to
X times_Y W. Exact open restriction agrees with derived pullback. Identify
restriction of a' with the supplied c: apply proper-flat open-unit invertibility
to f', then use direct-image composition, the open counit and uniqueness of
right adjoints. The source comparison is pullback composition; the target
comparison is this restriction identification followed by pullback composition.
Expand the mate as the unit, inverse conjugate of ordinary base change, and
counit. Horizontally paste the W square. Composition of units and counits and
the triangle identities identify its mate with the mate of the pasted square;
ordinary base change and its inverse conjugate respect the same comparisons.
Thus the two endpoint isomorphisms commute with the mates. They yield an arrow
isomorphism, without assuming either mate is invertible. For an empty W all
comparisons lie in the zero derived category, so the same argument applies.
-/
theorem rightAdjoint_mate_newBase_open
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X Y Y' : Scheme.{u}}
    [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Y'] [QuasiSeparatedSpace Y']
    (g : Y' ⟶ Y) (f : X ⟶ Y) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (a' : schemeDerivedQCohCategory Y' ⥤ schemeDerivedQCohCategory (pullback f g))
    (adjf : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint X Y
          (QuasiCompact.compactSpace_of_compactSpace f)
          (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _ f _ _).fst E.obj E.property) ⊣ a)
    (adjf' : (schemeDerivedQCohProperty Y').lift
      ((schemeDerivedQCohProperty (pullback f g)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f g)) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f g)) _ _ _ _
          (pullback.snd f g) _ _).fst E.obj E.property) ⊣ a')
    (hβ : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition E.obj))
    (K : schemeDerivedQCohCategory Y)
    (W : Y'.Opens) [IsAffine W.toScheme]
    (c : schemeDerivedQCohCategory W.toScheme ⥤
      schemeDerivedQCohCategory (pullback f (W.ι ≫ g)))
    (adjc : (schemeDerivedQCohProperty W.toScheme).lift
      ((schemeDerivedQCohProperty (pullback f (W.ι ≫ g))).ι ⋙
        schemeDerivedDirectImage (pullback.snd f (W.ι ≫ g))) (fun E ↦
        (@schemeDerivedDirectImage_qcqs_hasRightAdjoint _ _ _
          (quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (W.ι ≫ g))) _ _ _ _
          (pullback.snd f (W.ι ≫ g)) _ _).fst E.obj E.property) ⊣ c)
    (hβW : ∀ E : schemeDerivedQCohCategory X,
      IsIso (schemeDerivedBaseChangeMap f (pullback.snd f (W.ι ≫ g)) (W.ι ≫ g)
        (pullback.fst f (W.ι ≫ g)) pullback.condition E.obj))
    (r : ((pullback.snd f g) ⁻¹ᵁ W).toScheme ⟶ pullback f (W.ι ≫ g))
    [IsIso r]
    (hr₁ : r ≫ pullback.fst f (W.ι ≫ g) =
      ((pullback.snd f g) ⁻¹ᵁ W).ι ≫ pullback.fst f g)
    (hr₂ : r ≫ pullback.snd f (W.ι ≫ g) ≫ W.ι =
      ((pullback.snd f g) ⁻¹ᵁ W).ι ≫ pullback.snd f g) :
    Nonempty (Arrow.mk
      ((schemeOpenRestriction (pullback f g) ((pullback.snd f g) ⁻¹ᵁ W)).mapDerivedCategory.map
        ((schemeDerivedQCohProperty (pullback f g)).ι.map
          (@dualityEquationBaseChangeMap _ X Y Y'
            (QuasiCompact.compactSpace_of_compactSpace f)
            (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
            f g a a' adjf adjf' hβ K))) ≅
      Arrow.mk ((derivedPullback r).map
        ((schemeDerivedQCohProperty (pullback f (W.ι ≫ g))).ι.map
          (@dualityEquationBaseChangeMap _ X Y W.toScheme
            (QuasiCompact.compactSpace_of_compactSpace f)
            (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _
            f (W.ι ≫ g) a c adjf adjc hβW K)))) := by
  classical
  let f' := pullback.snd f g
  let P := pullback f' W.ι
  have : CompactSpace (pullback f g : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace f'
  have : QuasiSeparatedSpace (pullback f g : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated f'
  have : QuasiSeparatedSpace P := quasiSeparatedSpace_of_quasiSeparated (pullback.snd f' W.ι)
  let F := (schemeDerivedQCohProperty W.toScheme).lift
    ((schemeDerivedQCohProperty P).ι ⋙ schemeDerivedDirectImage (pullback.snd f' W.ι))
    (fun E ↦ (schemeDerivedDirectImage_qcqs_hasRightAdjoint P W.toScheme
      (pullback.snd f' W.ι)).fst E.obj E.property)
  have : F.IsLeftAdjoint :=
    (schemeDerivedDirectImage_qcqs_hasRightAdjoint P W.toScheme
      (pullback.snd f' W.ι)).choose_spec
  let d := F.rightAdjoint
  let adjd := Adjunction.ofIsLeftAdjoint F
  have hβO := proper_flat_rightAdjoint_baseChange_hβ W.ι f'
  let q := (isPullback_morphismRestrict f' W).flip.isoPullback.hom
  have hq₁ : q ≫ pullback.fst f' W.ι = (f' ⁻¹ᵁ W).ι :=
    (isPullback_morphismRestrict f' W).flip.isoPullback_hom_fst
  have hq₂ : q ≫ pullback.snd f' W.ι = f' ∣_ W :=
    (isPullback_morphismRestrict f' W).flip.isoPullback_hom_snd
  obtain ⟨δ₀⟩ := open_pullback_restriction_iso (pullback f g) (f' ⁻¹ᵁ W)
  obtain ⟨_, _, _, comp, _⟩ := exists_derivedPullbackComposition.{u, w}
  let δ : (schemeOpenRestriction (pullback f g) (f' ⁻¹ᵁ W)).mapDerivedCategory ≅
      derivedPullback (pullback.fst f' W.ι) ⋙ derivedPullback q :=
    δ₀ ≪≫ eqToIso (congrArg (fun k ↦ derivedPullback k) hq₁.symm) ≪≫
      (comp q (pullback.fst f' W.ι)).symm
  obtain ⟨e⟩ := newBase_open_mate_factorization g f a a' adjf adjf' hβ K W
    c adjc hβW r hr₁ hr₂ d adjd hβO q hq₁ hq₂ δ
  let K' := ((schemeDerivedQCohProperty Y').lift
    ((schemeDerivedQCohProperty Y).ι ⋙ derivedPullback g)
    (fun E ↦ (derivedPullback_tensor_preserve_QCoh g).1 E.obj E.property)).obj K
  let μO := @dualityEquationBaseChangeMap _ (pullback f g) Y' W.toScheme
    (QuasiCompact.compactSpace_of_compactSpace f')
    (quasiSeparatedSpace_of_quasiSeparated f') _ _ _ _
    f' W.ι a' d adjf' adjd hβO K'
  have : IsIso μO := proper_flat_openSquare_mate_isIso W f' a' d adjf' adjd hβO K'
  let t := δ.hom.app _ ≫ (derivedPullback q).map
    ((schemeDerivedQCohProperty P).ι.map μO)
  have : IsIso t := by dsimp only [t]; infer_instance
  let μ := (schemeOpenRestriction (pullback f g) ((pullback.snd f g) ⁻¹ᵁ W)).mapDerivedCategory.map
    ((schemeDerivedQCohProperty (pullback f g)).ι.map
      (@dualityEquationBaseChangeMap _ X Y Y'
        (QuasiCompact.compactSpace_of_compactSpace f)
        (quasiSeparatedSpace_of_quasiSeparated f) _ _ _ _ f g a a' adjf adjf' hβ K))
  have e₀ : Arrow.mk μ ≅ Arrow.mk (μ ≫ t) :=
    Arrow.isoMk (Iso.refl _) (asIso t) (by simp)
  exact ⟨e₀ ≪≫ e⟩


end AlgebraicGeometry
