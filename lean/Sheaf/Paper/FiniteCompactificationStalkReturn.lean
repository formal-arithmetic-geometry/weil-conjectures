/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K7
-/
module

public import Sheaf.Paper.WeilCompactSupportCohomology
public import Sheaf.Paper.AdicPunctualWeights
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.Paper.ZlFiniteAdicDirectImage
import Sheaf.Paper.A1FiniteWeilSectionsDecomposition
import Sheaf.Paper.WeilPullbackLocalFrobenius
import Sheaf.Paper.ZlImmersionWeilLocalBehavior
import Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison
import Sheaf.Paper.QbarCompactSupportBaseChange
import Sheaf.AlgebraicGeometry.ClosedPointField

/-! # Finite-stalk evaluations and Frobenius return

Source: Stacks 03QP(1); Deligne, Weil II (1.1.10)--(1.1.14);
blueprint main-20261015, lem-zl-finite-pushforward.proof.md.
(blueprint: lem-zl-finite-compactification-stalk-return).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The scalar-extended degree-zero stalk of a specified finite Weil presentation.
Source: local Frobenius convention (blueprint: def-weil-punctual-weights). -/
abbrev sfFinitePresentationStalk
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (L : Padic.FiniteCoefficientFields l Ω)
    (K : sfWeilComplex D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (ι : X₀.left.residueField x.val →+* D.k)
    (hι : ι.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :=
  (ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Ω L)).obj
    ((DerivedCategory.coefficientFdCohomology _ 0).obj
      (localPointComplex l _ D hl X₀ K (localClosedPoint D X₀ x ι hι)))

/-- The actual scalar-extended local operator on that stalk.
Source: local Frobenius convention (blueprint: def-weil-punctual-weights). -/
abbrev sfFinitePresentationFrobenius
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (L : Padic.FiniteCoefficientFields l Ω)
    (K : sfWeilComplex D l hl X₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (ι : X₀.left.residueField x.val →+* D.k)
    (hι : ι.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k) :
    Module.End Ω (sfFinitePresentationStalk D l hl Ω X₀ L K x ι hι) :=
  ((ModuleCat.extendScalars (sfAdicCoefficientEmbedding.{u} l Ω L)).map
    (localClosedFrobeniusCohomology l _ D hl X₀ K x ι hι 0)).hom

variable {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The finite-stalk formula, retaining its jointly injective evaluation maps and
its return operators. The maps target actual source stalks with finite Weil
presentations. Neither eigenvalues nor weights occur in this geometric data.
Source: Stacks 03QP(1); Deligne (1.1.10)--(1.1.14)
(blueprint: lem-zl-finite-compactification-stalk-return). -/
structure SfFiniteCompactificationStalkReturn
    (f₀ : X₀ ⟶ Y₀) (F : sfCommonStageWeilSheaf D l hl X₀ Ω)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (L : Padic.FiniteCoefficientFields l Ω)
    (K : sfWeilComplex D l hl Y₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) where
  Index : Type (max u v)
  [finite : Finite Index]
  point : Index → {x : X₀.left // x ∈ closedPoints X₀.left}
  mapsTo : ∀ i, f₀.left (point i).val = y.val
  degree : Index → ℕ
  degree_ne_zero : ∀ i, degree i ≠ 0
  cardinality : ∀ i, Nat.card (X₀.left.residueField (point i).val) =
    Nat.card (Y₀.left.residueField y.val) ^ degree i
  stage : Index → Padic.FiniteCoefficientFields l Ω
  source : ∀ i, sfWeilComplex D l hl X₀
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω (stage i))
  source_iso : ∀ i, Nonempty (F.obj ≅ sfWeilStageObject D l hl X₀ Ω (stage i) (source i))
  embedding : ∀ i, X₀.left.residueField (point i).val →+* D.k
  compatible : ∀ i, (embedding i).comp (X₀.hom.residueFieldAlgebraMap (point i).val) =
    algebraMap D.k₀ D.k
  evaluation : ∀ i, sfFinitePresentationStalk D l hl Ω Y₀ L K y ι hι →ₗ[Ω]
    sfFinitePresentationStalk D l hl Ω X₀ (stage i) (source i)
      (point i) (embedding i) (compatible i)
  jointly_injective : Function.Injective (fun v i ↦ evaluation i v)
  return_formula : ∀ i v,
    evaluation i ((sfFinitePresentationFrobenius D l hl Ω Y₀ L K y ι hι ^ degree i) v) =
      sfFinitePresentationFrobenius D l hl Ω X₀ (stage i) (source i)
        (point i) (embedding i) (compatible i) (evaluation i v)

/-- Finite-image stalk evaluation separates vectors and satisfies the local
Frobenius return formula, on every finite Weil presentation of the specified image.

Source: Stacks 03QP(1); Deligne, Weil II (1.1.10)--(1.1.14); blueprint
main-20261015, `lem-zl-finite-pushforward.proof.md`, finite-stalk formula and return
sentence (blueprint: lem-zl-finite-compactification-stalk-return).

Proof: choose an affine target open containing y. Its finite inverse image in the
compactification is affine, and the source open is separated and finite type.
Use framework/PBC open exchange, with its prescribed mates and Frobenius
naturality, to restrict the actual compact-support operation. The normalized
finite-adic stalk formula identifies its stalk with the finite sum of geometric
stalks of j!F. Open extension has zero stalk outside X and the original stalk,
including its local operator, inside X. Discard the zero summands: evaluation
on the remaining geometric lifts is still jointly injective.

Regroup these lifts into Frobenius cycles over each closed x above y. A cycle
has positive length e=[κ(x):κ(y)], and a residue-field basis gives
#κ(x)=#κ(y)^e. The finite Weil-sections decomposition over κ(y) gives that the
e-th power of F_y followed by each evaluation equals evaluation followed by
F_x. The pullback/local-Frobenius comparison identifies this return operator
with the one on X, since the residue fields agree; e iterations of the
κ(y)-Weil arrow are [κ(x):k₀] iterations of the original arrow.

Choose finite Weil presentations of F and of the output simultaneously with
the supplied presentation K, their inverse isomorphisms and all equations.
Scalar extension and coefficient-stage transport carry the canonical germs and
return identities to precisely the operators displayed here, not arbitrary
operators on isomorphic vector spaces. The scalar-extended finite sum is still
injective. Closedness of x follows from finiteness of κ(x) over k₀, even when the
ambient scheme is not separated. Empty fibres have a zero output stalk and an
empty evaluation family; nonreduced fibres cause no change to geometric stalks.
All choices are witnesses in a theorem; no global object is defined from them. -/
theorem sfFiniteCompactificationStalkReturn
    [QuasiSeparated Y₀.hom] (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left)
    [IsFinite c.g] (F : sfCommonStageWeilSheaf D l hl X₀ Ω)
    (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
    (L : Padic.FiniteCoefficientFields l Ω)
    (K : sfWeilComplex D l hl Y₀ (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L))
    (hK : Nonempty ((zlWeilHigherShriek D l hl Ω f₀ c 0 F).obj ≅
      sfWeilStageObject D l hl Y₀ Ω L K))
    (ι : Y₀.left.residueField y.val →+* D.k)
    (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k) :
    Nonempty (SfFiniteCompactificationStalkReturn D l hl Ω f₀ F y L K ι hι) := by
  sorry

end WeilConjectures
