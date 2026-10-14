/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Degree
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
import WeilConjectures.AlgebraicGeometry.Picard.RationalPoint
import Sheaf.AlgebraicGeometry.PicardFpqcSeparated

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- The uniqueness part of fpqc descent for the fppf sheafification of a fixed fibrewise-degree
subfunctor. Two amalgamations of one compatible family over an fpqc sieve agree. Pull both
amalgamations back to the finite separable residue-field extension supplied by a closed point of
the smooth geometrically integral curve. After the rational-point normalization, their local
trivializations can be chosen compatibly with the given family. The uniqueness of normalized
transition maps forces the two descended invertible modules and all overlap morphisms to agree,
so the two pulled-back amalgamations are equal. Equality of sections of the fppf sheafification
is reflected by this finite fppf cover, hence the original amalgamations are equal over the
starting sieve. Fibrewise degree is unchanged by the residue-field extension, so both sections
remain in the specified degree subfunctor throughout. Source: Stacks Project, Tags 0D28, 0D2B
and 023T.
(blueprint: lem-pd-degree-picard-sheaf-fpqc-uniqueness) -/
theorem unique_amalgamation_fpqc_sheafify_picardDegree
    {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIntegral f]
    (d : ℤ) (S : Subfunctor (picardPresheaf f))
    (hS : ∀ (T : Over (Spec (.of k))) (L : (picardPresheaf f).obj (op T)),
      L ∈ S.obj (op T) ↔ ∀ t, picardPresheafDegree f L t = d)
    {T : Over (Spec (.of k))} (R : Sieve T)
    (hR : R ∈ (Scheme.fpqcTopology.over (Spec (.of k))) T)
    (x : Presieve.FamilyOfElements
      ((presheafToSheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type (u + 1))).obj
        S.toFunctor).obj R.arrows)
    (hx : x.Compatible) {t₁ t₂ : _}
    (h₁ : x.IsAmalgamation t₁) (h₂ : x.IsAmalgamation t₂) :
    t₁ = t₂ := by
  -- Universal triviality of the direct image makes the entire Picard sheaf fpqc-separated.
  -- Left exact sheafification embeds the degree subfunctor into that sheaf.
  have _ := hS
  have _ := hx
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) := by
    change SmoothOfRelativeDimension 1 f
    infer_instance
  have : IsProper (C ↘ Spec (.of k)) := by
    change IsProper f
    infer_instance
  have : GeometricallyIntegral (C ↘ Spec (.of k)) := by
    change GeometricallyIntegral f
    infer_instance
  have hf (Y : Over (Spec (.of k))) :
      IsIso (pushforwardUnitMap (pullback.snd f Y.hom)) :=
    isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral (X := C) Y
  let J := Scheme.fppfTopology.over (Spec (.of k))
  let φ := sheafifyMap J S.ι
  have : Mono φ := inferInstance
  exact ((isSeparated_fpqc_picardFunctor f hf) R hR).of_mono φ x t₁ t₂ h₁ h₂

end AlgebraicGeometry
