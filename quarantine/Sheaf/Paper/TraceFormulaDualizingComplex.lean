/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.SixFunctors.FiniteDualizing

/-!
# Dualizing complexes and Verdier duality for the trace formula

Source: Weil conjectures blueprint, `main-20261015`,
`sec-six-functors/sk-thm-sf-kunneth-verdier/def-trf-dualizing-complex.md`
(blueprint: def-trf-dualizing-complex).

The ambient category and its internal Hom are the recorded intrinsic constant-ring
constructions. The Verdier functor has the full finite-Tor constructible category as
source and the ambient derived category as target. Evaluation is defined by transposing
its identity using the recorded evaluation-normalized finite tensor--Hom adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The ambient derived category on the small pro-etale site, with the recorded coefficients.
Source: blueprint `def-trf-dualizing-complex` (blueprint: def-trf-dualizing-complex). -/
abbrev traceFormulaDerivedCategory
    (T : TraceFormulaCoefficientConventions.{u}) (Y : Scheme.{u}) :=
  proEtaleDerivedCategory Y T.coefficientRing

/-- The full bounded constructible finite-Tor subcategory, for an arbitrary `Y` over `k`.
Source: blueprint `def-trf-dualizing-complex` (blueprint: def-trf-dualizing-complex). -/
abbrev traceFormulaFiniteTorCategory
    (T : TraceFormulaCoefficientConventions.{u}) (Y : Scheme.{u}) :=
  finiteTorConstructibleCategory T.coefficients.l T.coefficientField T.level T.level_pos Y

/-- The recorded finite internal Hom, at the positive level selected by the conventions.
Source: blueprint `def-trf-dualizing-complex` (blueprint: def-trf-dualizing-complex). -/
def traceFormulaDerivedInternalHom
    (T : TraceFormulaCoefficientConventions.{u}) (Y : Scheme.{u}) :
    (traceFormulaDerivedCategory T Y)ᵒᵖ × traceFormulaDerivedCategory T Y ⥤
      traceFormulaDerivedCategory T Y := by
  exact derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology Y)
    ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1, u} T.coefficientRing)))

/-- The recorded closed structure, whose K-flat models normalize the ordinary evaluation.
Reindexing `n` as `(n-1)+1` changes no positive coefficient level.
Source: blueprint `def-trf-dualizing-complex`, tensor--Hom adjunction;
Stacks Tags 08J9 and 08JA (blueprint: def-trf-dualizing-complex). -/
def traceFormulaClosed
    (T : TraceFormulaCoefficientConventions.{u}) (Y : Scheme.{u}) :
    CoefficientClosedStructure (traceFormulaDerivedInternalHom T Y) := by
  unfold traceFormulaDerivedInternalHom traceFormulaDerivedCategory
    TraceFormulaCoefficientConventions.coefficientRing
  rw [← Nat.sub_add_cancel T.level_pos]
  exact finiteIntrinsicClosed T.coefficients.l T.coefficientField Y (T.level - 1)

/-- The dualizing complex `ω_{Y,A} = Ra_Y^! A_s`.
This specializes the existing `integralDualizingFiniteTerm`, at positive level `n` rather
than its index `n-1`. Its intrinsic exceptional functor is the recorded `Rν_*`, etale
exceptional inverse image and exact `ν^*`, in canonical constant-ring coordinates, applied
to the regular coefficient module in degree zero. Compactifiability follows from separated
finite type and is not an additional hypothesis. Exceptional admissibility names the constructible
restriction of this functor; no ambient pro-etale right adjoint is chosen.
Source: blueprint `def-trf-dualizing-complex` (blueprint: def-trf-dualizing-complex). -/
def traceFormulaDualizingComplex
    (T : TraceFormulaCoefficientConventions.{u})
    (Y : Over (Spec (CommRingCat.of T.datum.k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] :
    traceFormulaDerivedCategory T Y.left := by
  unfold traceFormulaDerivedCategory TraceFormulaCoefficientConventions.coefficientRing
  rw [← Nat.sub_add_cancel T.level_pos]
  exact @integralDualizingFiniteTerm T.coefficients.l inferInstance T.coefficientField
    inferInstance inferInstance inferInstance T.datum Y.left ⟨Y.hom⟩
    (inferInstance : LocallyOfFiniteType Y.hom) (inferInstance : QuasiCompact Y.hom)
    (inferInstance : IsSeparated Y.hom) (T.level - 1)

/-- The contravariant Verdier functor `M ↦ RHom_A(M, ω_{Y,A})`.
Its source is exactly `D^b_ctf(Y,A)` and its target is the ambient derived category.
On `u : M → N`, the map is `RHom_A(u, id_ω)` by the first argument of `flip`.
Source: blueprint `def-trf-dualizing-complex` (blueprint: def-trf-dualizing-complex). -/
def traceFormulaVerdierDual
    (T : TraceFormulaCoefficientConventions.{u})
    (Y : Over (Spec (CommRingCat.of T.datum.k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] :
    (traceFormulaFiniteTorCategory T Y.left)ᵒᵖ ⥤ traceFormulaDerivedCategory T Y.left :=
  (finiteTorConstructible T.coefficients.l T.coefficientField T.level T.level_pos Y.left).ι.op ⋙
    (Functor.curry.obj (traceFormulaDerivedInternalHom T Y.left)).flip.obj
      (traceFormulaDualizingComplex T Y)

/-- The displayed tensor--Hom bijection, with its recorded evaluation normalization.
The finite closed structure is characterized on K-flat tensor representatives; its Hom
bijection is the external form of currying and the global derived-Hom identification.
Source: blueprint `def-trf-dualizing-complex`, displayed adjunction;
Stacks Tags 08J9 and 08JA (blueprint: def-trf-dualizing-complex). -/
def traceFormulaVerdierHomEquiv
    (T : TraceFormulaCoefficientConventions.{u})
    (Y : Over (Spec (CommRingCat.of T.datum.k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (M : traceFormulaFiniteTorCategory T Y.left) :
    ((traceFormulaClosed T Y.left).tensor.obj
        ((traceFormulaVerdierDual T Y).obj (op M), M.obj) ⟶
      traceFormulaDualizingComplex T Y) ≃
    ((traceFormulaVerdierDual T Y).obj (op M) ⟶
      (traceFormulaDerivedInternalHom T Y.left).obj
        (op M.obj, traceFormulaDualizingComplex T Y)) :=
  (traceFormulaClosed T Y.left).transpose _ M.obj (traceFormulaDualizingComplex T Y)

/-- The canonical evaluation `D_Y M ⊗^L_A M → ω_{Y,A}`: the transpose of the identity.
It uses the same derived internal Hom and normalized derived tensor as the functor above.
Source: blueprint `def-trf-dualizing-complex`, evaluation paragraph
(blueprint: def-trf-dualizing-complex). -/
def traceFormulaVerdierEvaluation
    (T : TraceFormulaCoefficientConventions.{u})
    (Y : Over (Spec (CommRingCat.of T.datum.k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (M : traceFormulaFiniteTorCategory T Y.left) :
    (traceFormulaClosed T Y.left).tensor.obj
        ((traceFormulaVerdierDual T Y).obj (op M), M.obj) ⟶
      traceFormulaDualizingComplex T Y :=
  (traceFormulaVerdierHomEquiv T Y M).symm (𝟙 _)

end WeilConjectures
