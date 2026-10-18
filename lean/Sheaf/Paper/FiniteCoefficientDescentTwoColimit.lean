/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
public import Sheaf.Paper.CoefficientFiniteDescentLisse
import Sheaf.CategoryTheory.FlatScalarTowerCoherence
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import Sheaf.Paper.CoefficientFiniteDescentHom
import Sheaf.Paper.CoefficientFiniteDescentObjects
import Sheaf.Paper.CoefficientHeart
import WeilConjectures.CategoryTheory.FilteredTwoColimit
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility

/-!
# Finite coefficient descent and the rational coefficient two-colimit

Source: Weil blueprint main-20261015, sec-six-functors-basics,
sk-thm-sfb-qlbar-two-colimit/_section.md, assertions (1)--(4)
(blueprint: sk-thm-sfb-qlbar-two-colimit).

The shifted Hom-colimit isomorphism is expressed by its representative and eventual
equality conditions. We write the shifted target as T(D[r]); exact scalar extension
canonically identifies this with (TD)[r]. Every transition and evaluation is the
specified scalar-extension map, conjugated by canonical tensor transitivity.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The canonical derived scalar comparison for three finite coefficient fields.
Source: blueprint sk-thm-sfb-qlbar-two-colimit, definition of C_F and proof (4),
tensor transitivity (blueprint: sk-thm-sfb-qlbar-two-colimit).
This is the existing exact-functor comparison applied to the ordinary tensor comparison.
-/
def finiteDescentDerivedComp (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E F H : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) (a : F ≤ H) :
    derivedExtendScalarsSubfield X ℓ (h.trans a) ≅
      derivedExtendScalarsSubfield X ℓ h ⋙ derivedExtendScalarsSubfield X ℓ a :=
  Functor.leftDerivedFunctorNatIso _ (lisseFiniteExtensionCompIso X ℓ h a) ≪≫
    Functor.leftDerivedFunctorCompIso _ _

/-- Evaluate a finite-field derived Hom representative in the algebraic closure.
Source: blueprint sk-thm-sfb-qlbar-two-colimit, displayed isomorphism (2)
(blueprint: sk-thm-sfb-qlbar-two-colimit). -/
def finiteDescentDerivedHomToAlgCl (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    {C D : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))}
    (f : (derivedExtendScalarsSubfield X ℓ h).obj C ⟶
      (derivedExtendScalarsSubfield X ℓ h).obj D) :
    (derivedExtendScalarsToPadicAlgCl X ℓ E).obj C ⟶
      (derivedExtendScalarsToPadicAlgCl X ℓ E).obj D :=
  (derivedExtendScalarsCompIso X ℓ h).inv.app C ≫
    (derivedExtendScalarsToPadicAlgCl X ℓ F).map f ≫
      (derivedExtendScalarsCompIso X ℓ h).hom.app D

/-- The transition between finite-field Hom representatives, using tensor transitivity.
Source: blueprint sk-thm-sfb-qlbar-two-colimit, displayed colimit (2) and proof (4)
(blueprint: sk-thm-sfb-qlbar-two-colimit). -/
def finiteDescentDerivedHomTransition (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E F H : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) (a : F ≤ H)
    {C D : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E))}
    (f : (derivedExtendScalarsSubfield X ℓ h).obj C ⟶
      (derivedExtendScalarsSubfield X ℓ h).obj D) :
    (derivedExtendScalarsSubfield X ℓ (h.trans a)).obj C ⟶
      (derivedExtendScalarsSubfield X ℓ (h.trans a)).obj D :=
  (finiteDescentDerivedComp X ℓ h a).hom.app C ≫
    (derivedExtendScalarsSubfield X ℓ a).map f ≫
      (finiteDescentDerivedComp X ℓ h a).inv.app D

/-- All four finite coefficient descent assertions, including the rational identification
and the ordinary-category filtered two-colimit.
Source: blueprint main-20261015, sk-thm-sfb-qlbar-two-colimit, assertions (1)--(4)
(blueprint: sk-thm-sfb-qlbar-two-colimit).

Proof following the node's fourteen steps:
1. The standing separated finite-type scheme is qcqs: finite type is quasi-compact,
the separated diagonal is a closed immersion and quasi-compact, and qcqs permanence
applies over the affine Spec k. No extra Noetherianity hypothesis is needed.
2. The two coefficient extensions preserve finite limits by lem-sfb-subfield-flat
and lem-sfb-qlbar-flat, and finite colimits by sk-def-sfb-change-of-scalars.
They are exact, so sk-def-sfb-derived-categories identifies their derived functors
with termwise scalar extension.
3. Apply det-lem-coefficient-finite-descent-lisse (1) on this qcqs scheme.
4. Apply det-lem-coefficient-finite-descent-hom (3) for every integer shift.
The canonical maps are additive, so bijectivity is an isomorphism of groups.
5. Apply det-lem-coefficient-finite-descent-objects for bounded constructible objects.
It also preserves the finite-field models after enlarging their coefficient field.
6. The rational case of sk-lem-coefficient-heart identifies Dctf, Dbc and Dcons.
Fullness identifies their Hom sets with ambient derived Hom sets; take r = 0.
7. The ambient extensions are the recorded def-sfb-derived-extend-subfield and
def-sfb-derived-extend-to-qlbar over pulled-back condensed rings, not discrete rings.
8. The two constructibility-preservation lemmas restrict them to the full categories
of def-sfb-dcons-subfield and def-sfb-dcons-qlbar, giving the recorded functors.
9. lem-sfb-flat-scalar-tower-coherence gives the canonical tensor comparisons and
all identity and tower equations. The ordinary comparison sends 1 tensor (1 tensor m)
to 1 tensor m, so lem-weil-pbc-conjugate-iso-unit-equation identifies it with the
adjunction comparison of def-sfb-derived-extend-comp-iso. Restrict to obtain the cocone.
10. def-weil-finite-subextension-directed-set gives a common finite compositum,
including above any fixed E. Tensor coherence makes these actual Hom transitions.
11. Object descent proves the Obj clause of sk-def-sfb-filtered-two-colimit.
12. Move two source fields to a common H. The shifted Hom bijection at r = 0 and
lem-weil-pbc-filtered-colimit-sets-elementwise provide a finite-stage representative.
13. Conjugate it by the tensor comparisons. Their tower equation gives exactly the
Hom-surj equation of the canonical cocone.
14. Injectivity of the Hom-colimit map and eventual equality of representatives give
Hom-inj. The identity comparison includes representatives at E itself. Obj, Hom-surj
and Hom-inj give the displayed filtered two-colimit, with its same-field Hom bijection.
-/
theorem finiteCoefficientDescentTwoColimit
    (k : Type u) [Field k] (p ℓ : ℕ) [CharP k p] [Fact ℓ.Prime]
    (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    (∀ L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ),
      IsLisseCoefficientModule (Profinite.padicAlgClRingObj ℓ) L →
      ∃ (E : PadicAlgCl.FiniteIntermediateField ℓ)
        (L_E : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (padicSubfieldRingObj X ℓ E)),
        IsLisseCoefficientModule (Profinite.continuousMapRingObj E) L_E ∧
          Nonempty ((Mod.extendScalars (padicSubfieldRingObjToPadicAlgCl X ℓ E)).obj L_E ≅ L)) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (C D : ConstantModelBoundedConstructible (Profinite.continuousMapRingObj E) X) (r : ℤ),
      (∀ ψ : (derivedExtendScalarsToPadicAlgCl X ℓ E).obj C.obj ⟶
          (derivedExtendScalarsToPadicAlgCl X ℓ E).obj (D.obj⟦r⟧),
        ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
          (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
            (derivedExtendScalarsSubfield X ℓ h).obj (D.obj⟦r⟧)),
          finiteDescentDerivedHomToAlgCl X ℓ h f = ψ) ∧
      (∀ (F G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F) (a : E ≤ G)
        (f : (derivedExtendScalarsSubfield X ℓ h).obj C.obj ⟶
          (derivedExtendScalarsSubfield X ℓ h).obj (D.obj⟦r⟧))
        (g : (derivedExtendScalarsSubfield X ℓ a).obj C.obj ⟶
          (derivedExtendScalarsSubfield X ℓ a).obj (D.obj⟦r⟧)),
        finiteDescentDerivedHomToAlgCl X ℓ h f = finiteDescentDerivedHomToAlgCl X ℓ a g →
        ∃ (H : PadicAlgCl.FiniteIntermediateField ℓ) (b : F ≤ H) (c : G ≤ H),
          finiteDescentDerivedHomTransition X ℓ h b f =
            finiteDescentDerivedHomTransition X ℓ a c g)) ∧
    (∀ K : ConstantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X,
      ∃ (E : PadicAlgCl.FiniteIntermediateField ℓ)
        (K_E : ConstantModelBoundedConstructible (Profinite.continuousMapRingObj E) X),
        Nonempty ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K_E.obj ≅ K.obj)) ∧
    ((∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
        constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X =
          boundedConstructible (padicSubfieldRingObj X ℓ E) ∧
        (constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X ⊓
          DerivedCategory.finiteTorAmplitude _) =
            constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X) ∧
      (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X =
        boundedConstructible (padicAlgClRingObj X ℓ) ∧
      (constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X ⊓
        DerivedCategory.finiteTorAmplitude _) =
          constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X) ∧
      (constructibleCocone X ℓ).IsFilteredTwoColimit) :=
  sorry

end AlgebraicGeometry.ProEtale
