/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.Paper.CommonStageCurveWeilMiddleExtension
public import Sheaf.Paper.CommonStageLisse
public import Sheaf.Paper.FourierTraceFormula
public import WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension

/-! # Geometric constituent exclusion in the common-stage heart

Source: main-20261015, def-a1-constituent-nonexceptional; rem-dl-a1-conventions
(blueprint: def-a1-constituent-nonexceptional).

A rank-one geometric constituent is expressed as a lisse subquotient in the
actual geometric heart. The Artin--Schreier line is constructed at completed
integral coefficients for the function ax, with a in the full algebraic closure.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

/-- A dense open of the standard affine line, retaining its finite-field model.
Finite type, quasi-compactness and separatedness follow for every such open from
Noetherianity of the line; they do not restrict its possible domains.
Source: blueprint constituent convention (blueprint: def-a1-constituent-nonexceptional). -/
structure SfAffineLineOpen (F : FourierSetting.{u}) where
  U : Over (Spec (.of F.field.k₀))
  j : U ⟶ fourierAffineModel F PUnit.{u + 1}
  [finiteType : LocallyOfFiniteType U.hom]
  [quasiCompact : QuasiCompact U.hom]
  [separated : IsSeparated U.hom]
  [openImmersion : IsOpenImmersion j.left]
  dense : DenseRange j.left.base

attribute [instance] SfAffineLineOpen.finiteType SfAffineLineOpen.quasiCompact
  SfAffineLineOpen.separated SfAffineLineOpen.openImmersion

variable (F : FourierSetting.{u})

/-- Every base-field additive character has a unique trace-pairing coefficient
relative to a fixed nontrivial prime-field character. This retains arbitrary psi,
not just the character Psi composed with the unscaled trace.
Source: def-fd-additive-character and the function ax convention
(blueprint: def-a1-constituent-nonexceptional).
Proof: values of characters are pth roots of unity. A nontrivial character of Fp
identifies its additive group with those roots. Thus psi is an Fp-linear functional
on k0. Nondegeneracy of the field-trace pairing gives its unique coefficient b.
The same argument includes the trivial psi, whose coefficient is zero. -/
theorem sfFourierCharacterScale_existsUnique
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (hΨ : Ψ ≠ 1)
    (ψ : AddChar F.field.k₀ F.coefficients.Qbar) :
    ∃! b : F.field.k₀, ∀ x : F.field.k₀,
      ψ x = fourierTraceBaseCharacter F Ψ (b * x) := by
  sorry

/-- The uniquely specified trace-pairing coefficient of the given psi.
Source: definition's function ax convention (blueprint: def-a1-constituent-nonexceptional). -/
def sfFourierCharacterScale
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (hΨ : Ψ ≠ 1)
    (ψ : AddChar F.field.k₀ F.coefficients.Qbar) : F.field.k₀ :=
  (sfFourierCharacterScale_existsUnique F Ψ hΨ ψ).exists.choose

/-- The affine line is a smooth curve of pure dimension one.
Source: rem-dl-a1-conventions (blueprint: def-a1-constituent-nonexceptional).
Proof: the polynomial algebra in one variable is smooth over the field. Its
prime spectrum has dimension one and its unique irreducible component is itself. -/
theorem sfAffineLine_curve :
    Smooth (fourierAffineModel F PUnit.{u + 1}).hom ∧
      (fourierAffineModel F PUnit.{u + 1}).left.IsPureDimension 1 := by
  sorry

/-- The same dense-open datum in the recorded ordinary-middle-extension interface.
Source: rem-dl-a1-conventions (blueprint: def-a1-constituent-nonexceptional). -/
def SfAffineLineOpen.curve (A : SfAffineLineOpen F) : Scheme.MiddleExtensionCurve F.field :=
  { U := A.U
    C := fourierAffineModel F PUnit.{u + 1}
    j := A.j
    dense := A.dense
    smooth := (sfAffineLine_curve F).1
    pureDimension := (sfAffineLine_curve F).2 }

variable (A : SfAffineLineOpen F)

/-- The geometric dense open is Noetherian of characteristic p, also when it is
all of the line. Density excludes the empty scheme.
Source: rem-dl-a1-conventions (blueprint: def-a1-constituent-nonexceptional).
Proof: the geometric open is an open of Spec k[x], hence Noetherian. It is
nonempty by density and the line is integral, so its global sections are a
nonzero k-algebra, of the same characteristic p. -/
theorem sfAffineOpen_geometry :
    IsNoetherian (F.field.geometricFiber A.U).left ∧
      CharP Γ((F.field.geometricFiber A.U).left, ⊤) F.field.p := by
  sorry

/-- The function ax on the geometric open; a ranges over k, not only k0.
The x coordinate is pulled from the arithmetic line and a from the geometric base.
Source: definition's final paragraph (blueprint: def-a1-constituent-nonexceptional). -/
def sfAffineOpenLinearFunction (a : F.field.k) :
    Γ((F.field.geometricFiber A.U).left, ⊤) :=
  (F.field.geometricFiber A.U).hom.appTop
      ((Scheme.ΓSpecIso (.of F.field.k)).inv.hom a) *
    (fourierModelProjection F A.U ≫ A.j.left).appTop
      (AffineSpace.coord (Spec (.of F.field.k₀)) PUnit.unit)

/-- The geometric character line, with its explicit completed integral representative.
The character Psi induces psi by composition with the finite-field trace.
Source: def-fd-artin-schreier-sheaf, function ax
(blueprint: def-a1-constituent-nonexceptional). -/
def sfAffineLinearArtinSchreierComplex
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (a : F.field.k) :
    generalAlgebraicallyClosedConstructibleCategory F.coefficients.l F.coefficients.Qbar
      (F.field.geometricFiber A.U).left :=
  letI := (sfAffineOpen_geometry F A).1
  letI := (sfAffineOpen_geometry F A).2
  ⟨fourierCoefficientStage F,
    (sfRationalConstructibleLocalization F.coefficients.l (fourierCoefficient F)
      (F.field.geometricFiber A.U).left).obj
      ⟨fourierAdicArtinSchreier F (F.field.geometricFiber A.U).left Ψ
          (sfAffineOpenLinearFunction F A a),
        fourierAdicArtinSchreier_mem F (F.field.geometricFiber A.U).left Ψ
          (sfAffineOpenLinearFunction F A a)⟩⟩

/-- The explicit rank-one character complex is in the standard heart.
Source: Artin--Schreier covering paragraph (blueprint: def-a1-constituent-nonexceptional).
Proof: the finite etale torsor trivializes its character summand. Over that cover
the completed sheaf is free of rank one in degree zero. Its reductions are finite
free in degree zero. Hence good truncation, rationalization and common-stage
inclusion put it in both standard halves. This also treats a=0 and trivial Psi. -/
theorem sfAffineLinearArtinSchreier_mem
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (a : F.field.k) :
    sfCommonStageHeartProperty F.coefficients.l (F.field.geometricFiber A.U).left
      F.coefficients.Qbar (sfAffineLinearArtinSchreierComplex F A Ψ a) := by
  sorry

/-- The character line as an actual geometric heart object, with no Weil structure
required when a is outside k0.
Source: definition's final paragraph (blueprint: def-a1-constituent-nonexceptional). -/
def sfAffineLinearArtinSchreier
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (a : F.field.k) :
    sfCommonStageHeart F.coefficients.l (F.field.geometricFiber A.U).left
      F.coefficients.Qbar :=
  ⟨sfAffineLinearArtinSchreierComplex F A Ψ a, sfAffineLinearArtinSchreier_mem F A Ψ a⟩

/-- No geometric irreducible constituent is a linear Artin--Schreier character.
A character line is rank one and irreducible, so occurrence as a Jordan--Hoelder
constituent means exactly occurrence as a quotient of a lisse geometric subsheaf.
The arrows and mono/epi conditions below are in the geometric standard heart,
not the derived category or the Weil heart. The scalar zero is included. The trace-pairing
coefficient converts the prime-field construction into the specified base-field character psi.
Source: def-a1-constituent-nonexceptional, both paragraphs
(blueprint: def-a1-constituent-nonexceptional). -/
def SfIsConstituentNonexceptional
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar) (hΨ : Ψ ≠ 1)
    (ψ : AddChar F.field.k₀ F.coefficients.Qbar)
    (M : sfCommonStageWeilSheaf F.field F.coefficients.l F.coefficients.different
      A.U F.coefficients.Qbar) : Prop :=
  ∀ a : F.field.k, ¬ ∃
    (G : sfCommonStageHeart F.coefficients.l (F.field.geometricFiber A.U).left
      F.coefficients.Qbar)
    (i : G ⟶ (qbarCurveWeilHeartForget F.field F.coefficients.l
      F.coefficients.different F.coefficients.Qbar A.U).obj M)
    (p : G ⟶ sfAffineLinearArtinSchreier F A Ψ
      (algebraMap F.field.k₀ F.field.k (sfFourierCharacterScale F Ψ hΨ ψ) * a)),
    HasCommonStageLisseLattice F.coefficients.l F.coefficients.Qbar
      (F.field.geometricFiber A.U).left G.obj ∧ Mono i ∧ Epi p

end WeilConjectures
