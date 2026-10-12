module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Adjunction.Basic
import Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange
import Sheaf.AlgebraicGeometry.DerivedQCohStandardAdjunction
import all Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- Right-adjoint base change on the self-product at a quasi-coherent complex,
for the three specified derived-category localizations.
Source: Stacks Project, Tag 0AAB, specialized to the self-product square in Tag 0E2P.
(blueprint: lem-sc-self-product-right-adjoint-base-change-local).
Proof: choose the standard localizations for all schemes and compare the specified
localizations for S, X and their self-product using the localization universal
property. These equivalences commute with direct image and derived pullback: the
right- and left-derived universal properties respectively give the comparisons.
Transport the two given adjunctions; uniqueness of right adjoints identifies the
transported functors with the choices in proper_flat_rightAdjoint_baseChange.
Noetherian schemes are qcqs, and flatness gives Tor independence for the
self-product. Apply that theorem with g=f and evaluate its invertible canonical
base-change map at the transported K. Transport back along the three equivalences
and invert the map to obtain b(Lf*K) ≅ Lpr₁*a(K). Proof irrelevance identifies the
quasi-coherent membership witnesses. This step makes no identification of Lf*K
with a structure sheaf; K may be zero or unbounded and schemes may be empty. -/
theorem proper_flat_selfProduct_rightAdjoint_baseChange_local
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Limits.pullback f f).toRingedSpace))]
    (hRf : ∀ E : schemeDerivedQCohCategory X,
      schemeDerivedQCohProperty S ((schemeDerivedDirectImage f).obj E.obj))
    (hRpr₂ : ∀ E : schemeDerivedQCohCategory (Limits.pullback f f),
      schemeDerivedQCohProperty X
        ((schemeDerivedDirectImage (pullback.snd f f)).obj E.obj))
    (hLpr₁ : ∀ E : schemeDerivedQCohCategory X,
      schemeDerivedQCohProperty (Limits.pullback f f)
        ((derivedPullback (pullback.fst f f)).obj E.obj))
    (a : schemeDerivedQCohCategory S ⥤ schemeDerivedQCohCategory X)
    (b : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory (Limits.pullback f f))
    (adjA : (schemeDerivedQCohProperty S).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) hRf ⊣ a)
    (adjB : (schemeDerivedQCohProperty X).lift
      ((schemeDerivedQCohProperty (Limits.pullback f f)).ι ⋙
        schemeDerivedDirectImage (pullback.snd f f)) hRpr₂ ⊣ b)
    (K : schemeDerivedQCohCategory S)
    (hLfK : schemeDerivedQCohProperty X ((derivedPullback f).obj K.obj)) :
    Nonempty
      (b.obj ⟨(derivedPullback f).obj K.obj, hLfK⟩ ≅
        ((schemeDerivedQCohProperty (Limits.pullback f f)).lift
          ((schemeDerivedQCohProperty X).ι ⋙ derivedPullback (pullback.fst f f))
          hLpr₁).obj (a.obj K)) := by
  classical
  let hx : HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := inferInstance
  let hs : HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) := inferInstance
  let hp : HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (pullback f f).toRingedSpace)) := inferInstance
  let d (Z : Scheme.{u}) := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace))
  let P := pullback f f
  let qP := @schemeDerivedQCohProperty P hp
  let pX := @schemeDerivedQCohProperty X (d X)
  let pP := @schemeDerivedQCohProperty P (d P)
  let Lfs := @derivedPullback X S f (d S) (d X)
  let Lps := @derivedPullback P X (pullback.fst f f) (d X) (d P)
  obtain ⟨eS, hRfs, aS, ⟨adjAS⟩, ⟨ιS⟩, ⟨α⟩⟩ :=
    @derivedQCoh_standardAdjunction X S f hx hs hRf a adjA
  obtain ⟨eX, hRps, bS, ⟨adjBS⟩, ⟨ιX⟩, ⟨γ⟩⟩ :=
    @derivedQCoh_standardAdjunction P X (pullback.snd f f) hp hx hRpr₂ b adjB
  obtain ⟨tf⟩ := pullback_transport f hx hs (d X) (d S)
  obtain ⟨tp⟩ := pullback_transport (pullback.fst f f) hp hx (d P) (d X)
  let M : @schemeDerivedQCohCategory X hx := ⟨(@derivedPullback X S f hs hx).obj K.obj, hLfK⟩
  let K' := eS.functor.obj K
  have hLfs : pX (Lfs.obj K'.obj) := by
    let := d S
    let := d X
    exact (derivedPullback_tensor_preserve_QCoh f).1 K'.obj K'.property
  let M' : @schemeDerivedQCohCategory X (d X) := ⟨Lfs.obj K'.obj, hLfs⟩
  let ε : eX.functor.obj M ≅ M' := pX.isoMk
    (ιX.app M ≪≫ tf.app K.obj ≪≫ Lfs.mapIso (ιS.app K).symm)
  have hLps : ∀ E : @schemeDerivedQCohCategory X (d X), pP (Lps.obj E.obj) := by
    let := d X
    let := d P
    exact fun E ↦ (derivedPullback_tensor_preserve_QCoh (pullback.fst f f)).1
      E.obj E.property
  let LP := pP.lift (pX.ι ⋙ Lps) hLps
  have η : Nonempty (LP.obj (aS.obj K') ≅ bS.obj M') := by
    let : ∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1}
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) := d
    obtain ⟨hβ, hθ⟩ := proper_flat_rightAdjoint_baseChange f f aS bS adjAS adjBS
    let θ := dualityEquationBaseChangeMap f f aS bS adjAS adjBS hβ K'
    have : IsIso θ := hθ K'
    exact ⟨asIso θ⟩
  obtain ⟨η⟩ := η
  let N := (qP.lift
    ((@schemeDerivedQCohProperty X hx).ι ⋙
      @derivedPullback P X (pullback.fst f f) hx hp)
      hLpr₁).obj (a.obj K)
  let ζ : (@schemeDerivedStandardEquivalence P hp).functor.obj (b.obj M).obj ≅
      (@schemeDerivedStandardEquivalence P hp).functor.obj N.obj :=
    (γ.app M).symm ≪≫ pP.ι.mapIso (bS.mapIso ε) ≪≫ pP.ι.mapIso η.symm ≪≫
      Lps.mapIso (α.app K) ≪≫ (tp.app (a.obj K).obj).symm
  exact ⟨qP.fullyFaithfulι.preimageIso
    ((@schemeDerivedStandardEquivalence P hp).functor.preimageIso ζ)⟩

end AlgebraicGeometry
