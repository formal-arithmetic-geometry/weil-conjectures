module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Adjunction.Basic
import Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange

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
  sorry

end AlgebraicGeometry
