/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction
public import Sheaf.AlgebraicGeometry.RelativeProjExists
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore
import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

/-! # Relative projective space with its relative-Proj charts

Source: blueprint, Nagata compactification, Conrad sketch, order 203
(blueprint: def-nagata-relative-projective-space).

The algebra is the constructed symmetric algebra of the free module. Its grading is fixed
by the monomial inclusions. Only uniquely specified algebra data and the universal relative
Proj realization are selected; no chart isomorphisms are selected separately.

## Main definitions

* `RelativeProjectiveSpace.algebra`: the symmetric algebra with symmetric-degree grading.
* `RelativeProjectiveSpace.construction`: its relative-Proj realization.
* `RelativeProjectiveSpace.scheme`, `RelativeProjectiveSpace.π`: the scheme over the base.
* `RelativeProjectiveSpace.standardOpen`: its standard homogeneous-coordinate opens.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry.RelativeProjectiveSpace

variable (X : Scheme.{u}) (r : ℕ)

/-- The free module with ordered basis indexed by `0, ..., r`.
Source: blueprint, order 203 (blueprint: def-nagata-relative-projective-space). -/
def freeModule : X.Modules :=
  SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (r + 1)))

/-- The degree-one generator `j_F(e_i)` on an arbitrary open.
Source: blueprint, order 203 (blueprint: def-nagata-relative-projective-space). -/
def generator (U : X.Opens) (i : Fin (r + 1)) :
    (SymmetricAlgebraSheaf.algebra (freeModule X r)).right.obj.obj (op U) :=
  (SymmetricAlgebraSheaf.inclusion (freeModule X r)).val.app (op U)
    ((SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up i)).val.app (op U)
      (1 : X.ringCatSheaf.obj.obj (op U)))

/-- The indexing set of monomials of symmetric degree `n`.
Source: blueprint, order 203 (blueprint: def-nagata-relative-projective-space). -/
def monomials (n : ℕ) := ULift.{u} {a : Fin (r + 1) → ℕ // ∑ i, a i = n}

/-- The degree-`n` monomial evaluated in the constructed symmetric algebra.
Source: blueprint, order 203 (blueprint: def-nagata-relative-projective-space). -/
def monomial (n : ℕ) (a : monomials.{u} r n) (U : X.Opens) :
    (SymmetricAlgebraSheaf.algebra (freeModule X r)).right.obj.obj (op U) :=
  ∏ i : Fin (r + 1), generator X r U i ^ a.down.val i

/-- The linear maps sending 1 to a fixed monomial commute with restriction.
Source: blueprint, order 203 (blueprint: def-nagata-relative-projective-space).
Proof: the free-basis inclusions and the symmetric-algebra inclusion are sheaf morphisms.
Their naturality gives restriction of each generator; restriction is a ring homomorphism,
so it preserves the finite product and powers. Module restriction preserves scalars. -/
theorem monomial_naturality (n : ℕ) (a : monomials.{u} r n)
    {U V : X.Opensᵒᵖ} (f : U ⟶ V) :
    (SheafOfModules.unit X.ringCatSheaf).val.map f ≫
        (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map f).hom).map
          (ModuleCat.ofHom (LinearMap.toSpanSingleton (X.ringCatSheaf.obj.obj V)
            ((SymmetricAlgebraSheaf.algebra (freeModule X r)).toModule.val.obj V)
            (monomial X r n a V.unop))) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton (X.ringCatSheaf.obj.obj U)
          ((SymmetricAlgebraSheaf.algebra (freeModule X r)).toModule.val.obj U)
          (monomial X r n a U.unop)) ≫
        (SymmetricAlgebraSheaf.algebra (freeModule X r)).toModule.val.map f := by
  sorry

/-- The monomial map from a copy of the structure module into the symmetric algebra.
Source: blueprint, order 203 (blueprint: def-nagata-relative-projective-space). -/
def monomialUnit (n : ℕ) (a : monomials.{u} r n) :
    SheafOfModules.unit X.ringCatSheaf ⟶
      (SymmetricAlgebraSheaf.algebra (freeModule X r)).toModule where
  val :=
    { app U := ModuleCat.ofHom
        (Y := (SymmetricAlgebraSheaf.algebra (freeModule X r)).toModule.val.obj U)
        (LinearMap.toSpanSingleton (X.ringCatSheaf.obj.obj U)
        ((SymmetricAlgebraSheaf.algebra (freeModule X r)).toModule.val.obj U)
        (monomial X r n a U.unop))
      naturality f := monomial_naturality X r n a f }

/-- The homogeneous monomial inclusion, extended from the free monomial basis.
Source: blueprint, order 203 (blueprint: def-nagata-relative-projective-space). -/
def monomialMap (n : ℕ) :
    SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r n) ⟶
      (SymmetricAlgebraSheaf.algebra (freeModule X r)).toModule :=
  Sigma.desc (fun a ↦ monomialUnit X r n a)

/-- The exact characterization of the symmetric-degree relative-Proj input. The pieces
are the free monomial sheaves and their inclusions are evaluation of those monomials.
`HEq` compares maps whose endpoints are identified by the preceding equalities.
Source: blueprint, order 203 (blueprint: def-nagata-relative-projective-space). -/
def IsSymmetricInput (A : RelativeProjAlgebra X) : Prop :=
  A.algebra.obj = SymmetricAlgebraSheaf.algebra (freeModule X r) ∧
    A.piece = (fun n ↦ SheafOfModules.free (R := X.ringCatSheaf) (monomials.{u} r n)) ∧
    ∀ n : ℕ, HEq (Sigma.ι A.piece n ≫ A.decomposition.hom) (monomialMap X r n)

/-- There is exactly one relative-Proj algebra structure with these fixed pieces,
algebra sheaf and monomial inclusions; thus selecting it does not select unknown data.
Source: blueprint, order 203 (blueprint: def-nagata-relative-projective-space).
Proof: the free module is quasi-coherent. The constructed symmetric algebra has the
universal property by lem-weil-pbc-quasi-coherent-symmetric-algebra-core. Uniqueness of
universal pairs identifies it with the quasi-coherent pair of
lem-weil-pbc-quasi-coherent-symmetric-algebra, giving quasi-coherence and the canonical
affine-section identification. On an affine open, use the standard free basis and
SymmetricAlgebra.equivMvPolynomial. Monomials are a basis; grouping them by total degree
agrees with lem-weil-pbc-symmetric-algebra-graded. These identifications commute with
restriction, so they give the homogeneous free sheaves, their multiplication and unit,
and the decomposition isomorphism. Multiplication and unit satisfy the algebra laws
on every affine open, hence globally. For uniqueness the fixed monomial inclusions fix
the decomposition by the coproduct property. They are monomorphisms, so `mul_eq` and
`unit_eq` uniquely determine every homogeneous multiplication and the unit. All remaining
fields are propositions. This proves uniqueness as equality of the entire input datum. -/
theorem existsUnique_symmetricInput : ∃! A : RelativeProjAlgebra X, IsSymmetricInput X r A := by
  sorry

/-- The uniquely specified symmetric algebra input, with its symmetric-degree grading.
Source: blueprint, order 203 (blueprint: def-nagata-relative-projective-space). -/
def algebra : RelativeProjAlgebra X := (existsUnique_symmetricInput X r).exists.choose

/-- Relative Proj with all its compatible affine restriction isomorphisms. The existence
theorem determines this realization up to the unique chart-preserving isomorphism.
Source: blueprint, order 203 (blueprint: def-nagata-relative-projective-space). -/
def construction : RelativeProjData (algebra X r) := (exists_relativeProjData (algebra X r)).choose

/-- Relative projective `r`-space over `X`, using symmetric-algebra relative Proj.
Source: blueprint, order 203 (blueprint: def-nagata-relative-projective-space). -/
def scheme : Scheme.{u} := (construction X r).proj

/-- The structural morphism of relative projective space.
Source: blueprint, order 203 (blueprint: def-nagata-relative-projective-space). -/
def π : scheme X r ⟶ X := (construction X r).π

/-- The specified equality with the constructed symmetric algebra sheaf.
Source: blueprint, order 203 (blueprint: def-nagata-relative-projective-space).
Proof: take the first clause of the specification of existsUnique_symmetricInput. -/
theorem algebra_eq : (algebra X r).algebra.obj =
    SymmetricAlgebraSheaf.algebra (freeModule X r) := by
  sorry

/-- The coordinate section in the actual graded section ring used for local Proj.
Source: blueprint, order 203 (blueprint: def-nagata-relative-projective-space). -/
def coordinate (V : X.affineOpens) (i : Fin (r + 1)) : (algebra X r).sections V :=
  (eqToHom (algebra_eq X r).symm).right.hom.app (op V.1) (generator X r V.1 i)

/-- Each coordinate is homogeneous of degree one.
Source: blueprint, order 203 (blueprint: def-nagata-relative-projective-space).
Proof: the monomial with exponent 1 at i and zero elsewhere is a basis section of the
first piece. The monomial-inclusion clause identifies its image with this coordinate. -/
theorem coordinate_mem (V : X.affineOpens) (i : Fin (r + 1)) :
    coordinate X r V i ∈ (algebra X r).sectionGrade V 1 := by
  sorry

/-- On an affine base the polynomial identification is uniquely determined by its
coefficients and its ordered degree-one generators.
Source: blueprint, order 203 (blueprint: def-nagata-relative-projective-space).
Proof: identify the sections of the finite free module with the free module on its
standard basis. The universal-property comparison with the quasi-coherent symmetric
algebra gives its canonical affine-section isomorphism. Compose its inverse with
SymmetricAlgebra.equivMvPolynomial for that basis and invert. This gives the displayed
coefficient and generator equations. Polynomial extensionality proves uniqueness. -/
theorem existsUnique_affinePolynomialEquiv (V : X.affineOpens) :
    ∃! e : MvPolynomial (Fin (r + 1)) (X.presheaf.obj (op V.1)) ≃+*
        (algebra X r).sections V,
      (∀ a : X.presheaf.obj (op V.1),
        e (MvPolynomial.C a) = (algebra X r).algebra.obj.hom.hom.app (op V.1) a) ∧
      (∀ i : Fin (r + 1), e (MvPolynomial.X i) = coordinate X r V i) := by
  sorry

/-- The canonical polynomial identification, preserving coefficients and coordinates.
Source: blueprint, order 203 (blueprint: def-nagata-relative-projective-space). -/
def affinePolynomialEquiv (V : X.affineOpens) :
    MvPolynomial (Fin (r + 1)) (X.presheaf.obj (op V.1)) ≃+* (algebra X r).sections V :=
  (existsUnique_affinePolynomialEquiv X r V).exists.choose

/-- Symmetric degree is polynomial total degree in the standard coordinates.
Source: blueprint, order 203 (blueprint: def-nagata-relative-projective-space).
Proof: the fixed degree-n monomial inclusions identify the nth piece with the span of
monomials of total degree n. The polynomial equivalence sends each such monomial to
that same monomial in the coordinates. The monomial basis proves both inclusions. -/
theorem affinePolynomial_homogeneous (V : X.affineOpens) (n : ℕ)
    (p : MvPolynomial (Fin (r + 1)) (X.presheaf.obj (op V.1))) :
    affinePolynomialEquiv X r V p ∈ (algebra X r).sectionGrade V n ↔
      p ∈ MvPolynomial.homogeneousSubmodule (Fin (r + 1))
        (X.presheaf.obj (op V.1)) n := by
  sorry

/-- The standard open on an affine local model, using the actual coordinate section.
Source: blueprint, order 203 (blueprint: def-nagata-relative-projective-space). -/
def localStandardOpen (V : X.affineOpens) (i : Fin (r + 1)) :
    ((algebra X r).localProj V).Opens :=
  Proj.basicOpen ((algebra X r).sectionGrade V) (coordinate X r V i)

/-- The global standard open is the union of the specified opens over all affine bases.
There is no independent choice of opens or charts.
Source: blueprint, order 203 (blueprint: def-nagata-relative-projective-space). -/
def standardOpen (i : Fin (r + 1)) : (scheme X r).Opens :=
  ⨆ V : X.affineOpens,
    ((π X r ⁻¹ᵁ V.1).ι.opensFunctor.obj
      ((TopologicalSpace.Opens.map ((construction X r).restrictionIso V).hom.base).obj
        (localStandardOpen X r V i)))

/-- The standard chart identification is exactly the affine Proj identification, with
degree-zero homogeneous localization, not a newly chosen isomorphism.
Source: blueprint, order 203 (blueprint: def-nagata-relative-projective-space). -/
def localChart (V : X.affineOpens) (i : Fin (r + 1)) :
    (localStandardOpen X r V i).toScheme ≅
      Spec (CommRingCat.of (HomogeneousLocalization.Away
        ((algebra X r).sectionGrade V) (coordinate X r V i))) :=
  Proj.basicOpenIsoSpec ((algebra X r).sectionGrade V)
    (coordinate X r V i) (coordinate_mem X r V i) Nat.one_pos

/-- The global standard open restricts to the specified local standard open on every
affine base. The chart map is therefore the inherited relative-Proj chart map.
Source: blueprint, order 203 (blueprint: def-nagata-relative-projective-space).
Proof: restriction of a coordinate is the same coordinate. The restriction transition
maps of relative Proj are the canonical graded section-restriction maps, which pull
back D_+(T_i) to D_+(T_i). Use restriction_compatibility, and cover overlaps by affine
refinements. Taking the union defining standardOpen gives the asserted equality. -/
theorem standardOpen_restrict (V : X.affineOpens) (i : Fin (r + 1)) :
    (TopologicalSpace.Opens.map (π X r ⁻¹ᵁ V.1).ι.base).obj (standardOpen X r i) =
      (TopologicalSpace.Opens.map ((construction X r).restrictionIso V).hom.base).obj
        (localStandardOpen X r V i) := by
  sorry

end AlgebraicGeometry.RelativeProjectiveSpace
