/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Support preservation by the right adjoint of proper flat direct image

Source: Stacks Project, duality.tex, Lemma 48.4.4, case (1), Tag 0E4G, using
perfect.tex, Tags 0A1H and 0A9C(i) for the unbounded strengthening in the node
(blueprint: lem-sc-proper-flat-right-adjoint-open-support).
-/

@[expose] public section

universe uT wXT wYT

open CategoryTheory

namespace AlgebraicGeometry

/-- The right adjoint of proper, flat, finitely presented derived direct image preserves
support on the complement of a quasi-compact open. `F` is the restriction of `Rf_*` to
`D_QCoh`, identified with the recorded ambient direct image by the natural isomorphism
`hF`. Support means vanishing of every cohomology stalk on the open.
Source: Stacks Project, duality.tex, Tag 0E4G, Lemma 48.4.4, case (1); the unbounded
version uses perfect.tex, Tags 0A1H and 0A9C(i).
(blueprint: lem-sc-proper-flat-right-adjoint-open-support).

Proof:
1. Put T = Y minus V and U = f⁻¹(V). If a(Q)|U is nonzero, perfect generation
   (lem-pc-derived-qcoh-perfect-generation) detects it by a nonzero map P_U → a(Q)|U.
   The lifting lemma lem-sc-perfect-support-map-lift, with closed subset X, lifts it
   to β : P → a(Q), with P perfect and β|U nonzero, since P_U is a compatible summand.
2. The adjunction identifies β with a map Rf_*P → Q.
3. Properness, flatness and finite presentation, and
   lem-pc-proper-support-perfect-direct-image with G = O_X[0], make Rf_*P perfect.
   Case (i) of lem-sc-pseudo-coherent-support-annihilation supplies a perfect I and
   I → O_Y, an isomorphism over V, killing the composite I ⊗ᴸ Rf_*P → Rf_*P → Q.
4. The projection formula lem-pc-projection-formula identifies its source with
   Rf_*(Lf^*I ⊗ᴸ P). Adjunction makes Lf^*I ⊗ᴸ P → P → a(Q) zero.
5. Over U the map Lf^*I → O_X is invertible, contradicting β|U being nonzero.
   Thus every cohomology stalk of a(Q) vanishes on U. -/
theorem proper_flat_rightAdjoint_open_support
    {X Y : Scheme.{uT}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [HasDerivedCategory.{wXT} (SheafOfModules.{uT} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wYT} (SheafOfModules.{uT} (moduleRings Y.toRingedSpace))]
    (F : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (hF : F ⋙ ObjectProperty.ι (schemeDerivedQCohProperty Y) ≅
      ObjectProperty.ι (schemeDerivedQCohProperty X) ⋙ schemeDerivedDirectImage f)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X) (adj : F ⊣ a)
    (V : Y.Opens) (hV : IsCompact (V : Set Y)) (Q : schemeDerivedQCohCategory Y)
    (hQ : ∀ (n : ℤ) (y : Y), y ∈ V →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{uT} (moduleRings Y.toRingedSpace)) n).obj Q.obj).val.presheaf y))) :
    ∀ (n : ℤ) (x : X), x ∈ f ⁻¹ᵁ V →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{uT} (moduleRings X.toRingedSpace)) n).obj
          (a.obj Q).obj).val.presheaf x)) := by
  sorry

end AlgebraicGeometry
