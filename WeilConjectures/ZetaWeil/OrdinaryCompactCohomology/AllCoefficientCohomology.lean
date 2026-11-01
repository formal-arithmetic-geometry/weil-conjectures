/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleTensorPreservation
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Determinant
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

/-! # Ordinary and compact cohomology for all four condensed coefficient rings

Source: latest blueprint, sec-six-functors-basics/sk-thm-existence/
def-weil-ordinary-compact-cohomology.md
(blueprint: def-weil-ordinary-compact-cohomology).

The ambient coefficient complexes use the recorded geometric fibre, with scalars
`condensedScalarRing Λ = Λ(*)`. The bounded restrictions below land in the existing
`scalarFiniteCohomology` category. Finite cardinality, finite generation and finite
vector-space dimension are its respective interpretations for the four coefficient rings.
The four point equivalences themselves are `direct_coefficient_point`, publicly imported.

Twisted coefficient objects are inputs to the same ambient functors: use the existing
`coefficientTwistFunctor` with `coefficientFiniteTwistOne`,
`coefficientIntegralTwistOne`, or `coefficientRationalTwistOne`, and `tateTwistFunctor`
for the finite-subextension-valued algebraic closure. No coefficient object, twist,
linear-algebra invariant or Weil category is constructed a second time here.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.OrdinaryCompactCohomology

/-- The four actual coefficient rings, in the order A_E,n, O_E, E, Qbar.
This finite indexing only packages the already recorded condensed rings.
Source: the first paragraph of def-weil-ordinary-compact-cohomology
(blueprint: def-weil-ordinary-compact-cohomology). -/
def coefficientRings (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (pi : PadicAlgCl.integers ell E)
    (n : ℕ) (j : Fin 4) : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  match j.val with
  | 0 => ⟨CondensedGeometricPoint.residueRingObj ell E pi n⟩
  | 1 => ⟨Profinite.padicIntegersRingObj ell E⟩
  | 2 => ⟨Profinite.continuousMapRingObj E⟩
  | _ => ⟨Profinite.padicAlgClRingObj ell⟩

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (D : FiniteFieldDatum.{u}) (Y : Over (Spec (.of D.k)))

/-- RΓ(Y,K) = Fib_s(Ra_Y* K), on the ambient category, so that constants,
Tate twists and forgotten Weil complexes are all admissible inputs.
Source: first displayed definition of coefficient complexes
(blueprint: def-weil-ordinary-compact-cohomology). -/
def ordinary :
    DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj Λ Y.left)) ⥤
    @DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ)) _ _
      (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _) :=
  CondensedRing.moduleObjectDerivedPushforward Λ Y.hom ⋙
    CondensedGeometricPoint.fiber Λ D.k

/-- RΓ_c(Y,K) = Fib_s(Ra_Y! K), using exact extension by zero and proper
pushforward for the chosen compactification.
Source: second displayed definition of coefficient complexes
(blueprint: def-weil-ordinary-compact-cohomology). -/
def compact (c : Compactification Y.hom) :
    DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj Λ Y.left)) ⥤
    @DerivedCategory (ModuleCat.{u + 1} (condensedScalarRing Λ)) _ _
      (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _) :=
  CondensedRing.rightDerivedLowerShriekOfCompactification Λ c ⋙
    CondensedGeometricPoint.fiber Λ D.k

/-- H^i(Y,K), with i any integer, using ordinary scalar-module cohomology.
Source: displayed definition of H^i (blueprint: def-weil-ordinary-compact-cohomology). -/
def ordinaryH (i : ℤ) :=
  ordinary Λ D Y ⋙ @DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (condensedScalarRing Λ)) _ _
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _) i

/-- H_c^i(Y,K), with i any integer.
Source: displayed definition of H_c^i (blueprint: def-weil-ordinary-compact-cohomology). -/
def compactH (c : Compactification Y.hom) (i : ℤ) :=
  compact Λ D Y c ⋙ @DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (condensedScalarRing Λ)) _ _
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _) i

/-- The well-definedness condition for the two coefficient complexes to belong to
D^b_fin, D^b_fg or D^b_fd, as appropriate. It only certifies the fixed functors' values.
Source: the four coefficient-complex target categories
(blueprint: def-weil-ordinary-compact-cohomology). -/
def finiteValues (c : Compactification Y.hom) : Prop :=
  ∀ K : BoundedConstructible (condensedRingObj Λ Y.left),
    CondensedGeometricPoint.scalarFiniteCohomology Λ ((ordinary Λ D Y).obj K.obj) ∧
    CondensedGeometricPoint.scalarFiniteCohomology Λ ((compact Λ D Y c).obj K.obj)

omit Λ in
/-- The displayed coefficient complexes have bounded finite scalar cohomology for
all four coefficients. This is the membership proof used by the bounded restrictions.
Source: def-weil-ordinary-compact-cohomology, the coefficient-complex formulas and
four target categories (blueprint: def-weil-ordinary-compact-cohomology).

Proof: Apply lem-sfb-dc-lower-star-preserves to a_Y for ordinary sections. For compact
sections apply lem-sfb-dc-open-lower-shriek-preserves to the open factor and then
lem-sfb-dc-lower-star-preserves to the proper factor of c. The ambient composites
are exactly the recorded total derived module pushforward and factorwise lower shriek.
Finally apply def-weil-finite-coefficient-point: exact evaluation at s sends bounded
constructible complexes to bounded finite scalar cohomology. Over A_E,n finite
generation is finite cardinality; over O_E it is finite generation; over either
field it is finite dimension. The finite quotient is killed by ell^n since ell
belongs to the maximal ideal generated by pi. No completeness or finite Tor
amplitude is imposed on K.
-/
theorem all_coefficient_finiteValues [IsSeparated Y.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (pi : PadicAlgCl.integers ell E)
    (_hpi : Ideal.span {pi} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E))
    (n : ℕ) (_hn : 1 ≤ n) (c : Compactification Y.hom) (j : Fin 4) :
    finiteValues (coefficientRings.{u} ell E pi n j).X D Y c := by
  sorry

/-- RΓ restricted to the specified bounded constructible domain and finite-cohomology
codomain. The proof parameter affects only full-subcategory membership, never its data.
Source: RΓ and the displayed coefficient categories
(blueprint: def-weil-ordinary-compact-cohomology). -/
def ordinaryBounded (c : Compactification Y.hom) (h : finiteValues Λ D Y c) :
    BoundedConstructible (condensedRingObj Λ Y.left) ⥤
      (CondensedGeometricPoint.scalarFiniteCohomology Λ).FullSubcategory :=
  (CondensedGeometricPoint.scalarFiniteCohomology Λ).lift
    ((boundedConstructible (condensedRingObj Λ Y.left)).ι ⋙ ordinary Λ D Y)
    (fun K => (h K).1)

/-- RΓ_c with the same bounded domain and finite-cohomology codomain.
Source: RΓ_c and the displayed coefficient categories
(blueprint: def-weil-ordinary-compact-cohomology). -/
def compactBounded (c : Compactification Y.hom) (h : finiteValues Λ D Y c) :
    BoundedConstructible (condensedRingObj Λ Y.left) ⥤
      (CondensedGeometricPoint.scalarFiniteCohomology Λ).FullSubcategory :=
  (CondensedGeometricPoint.scalarFiniteCohomology Λ).lift
    ((boundedConstructible (condensedRingObj Λ Y.left)).ι ⋙ compact Λ D Y c)
    (fun K => (h K).2)

omit Λ in
/-- The two bounded coefficient-complex functors, for any of the four coefficients.
All finiteness witnesses are supplied by the preceding named theorem; no finiteness
assumption on the chosen complex is added beyond bounded constructibility.
Source: the two coefficient-complex definitions and their four target categories
(blueprint: def-weil-ordinary-compact-cohomology). -/
def sections [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (pi : PadicAlgCl.integers ell E)
    (hpi : Ideal.span {pi} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (c : Compactification Y.hom) (j : Fin 4) :=
  (ordinaryBounded (coefficientRings.{u} ell E pi n j).X D Y c
      (all_coefficient_finiteValues D Y ell hell E pi hpi n hn c j),
    compactBounded (coefficientRings.{u} ell E pi n j).X D Y c
      (all_coefficient_finiteValues D Y ell hell E pi hpi n hn c j))

/-- The coefficient sheaf Λ_Y, as the regular module in degree zero.
Its bounded constructibility is the existing tensor-unit theorem.
Source: the coefficient-sheaf paragraph
(blueprint: def-weil-ordinary-compact-cohomology). -/
def coefficientObject [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] : BoundedConstructible (condensedRingObj Λ Y.left) :=
  ⟨𝟙_ _, CondensedRing.boundedConstructible_tensor_unit Λ Y⟩

/-- H^i(Y,Λ) abbreviates evaluation on Λ_Y.
Source: constant-coefficient abbreviations
(blueprint: def-weil-ordinary-compact-cohomology). -/
def ordinaryConstant (i : ℤ) :=
  (ordinaryH Λ D Y i).obj (𝟙_ _)

/-- H_c^i(Y,Λ) abbreviates evaluation on Λ_Y.
Source: constant-coefficient abbreviations
(blueprint: def-weil-ordinary-compact-cohomology). -/
def compactConstant (c : Compactification Y.hom) (i : ℤ) :=
  (compactH Λ D Y c i).obj (𝟙_ _)

/-- Twisted constant coefficients: first tensor Λ_Y with the signed Tate line
in degree zero, then take H^i. This helper is specialized to the corresponding
canonical coefficient line by the four definitions below.
Source: H^i(Y,Λ(m)) = H^i(Y,Λ_Y(m))
(blueprint: def-weil-ordinary-compact-cohomology). -/
def ordinaryTwistedConstantWithLine
    (L : Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj Λ Y.left)) (m i : ℤ) :=
  (ordinaryH Λ D Y i).obj
    ((coefficientTwistFunctor Y.left (condensedRingObj Λ Y.left) L m).obj (𝟙_ _))

/-- The identical twisted coefficient convention for compact supports.
Source: H_c^i(Y,Λ(m)) = H_c^i(Y,Λ_Y(m))
(blueprint: def-weil-ordinary-compact-cohomology). -/
def compactTwistedConstantWithLine (c : Compactification Y.hom)
    (L : Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj Λ Y.left)) (m i : ℤ) :=
  (compactH Λ D Y c i).obj
    ((coefficientTwistFunctor Y.left (condensedRingObj Λ Y.left) L m).obj (𝟙_ _))

omit Λ in
/-- Both cohomology groups of the canonical finite twisted coefficient object.
The exponent is n+1, so all positive levels occur. The line and the quotient,
including its fixed uniformizer, are exactly those of the twist dependency.
Source: finite-coefficient Tate abbreviations
(blueprint: def-weil-ordinary-compact-cohomology). -/
def finiteTwistedConstant (ell : ℕ) [Fact ell.Prime]
    (E : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (m i : ℤ) (c : Compactification Y.hom) :=
  (ordinaryTwistedConstantWithLine (twistFiniteRing ell E n) D Y
      (coefficientFiniteTwistOne ell E Y.left n) m i,
    compactTwistedConstantWithLine (twistFiniteRing ell E n) D Y c
      (coefficientFiniteTwistOne ell E Y.left n) m i)

omit Λ in
/-- Both cohomology groups of the canonical integral Tate coefficient object,
using the recorded inverse limit of the finite root lines.
Source: integral-coefficient Tate abbreviations
(blueprint: def-weil-ordinary-compact-cohomology). -/
def integralTwistedConstant (ell : ℕ) [Fact ell.Prime]
    (E : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (m i : ℤ) (c : Compactification Y.hom) :=
  (ordinaryTwistedConstantWithLine (twistIntegralRing ell E) D Y
      (coefficientIntegralTwistOne ell E Y.left) m i,
    compactTwistedConstantWithLine (twistIntegralRing ell E) D Y c
      (coefficientIntegralTwistOne ell E Y.left) m i)

omit Λ in
/-- Both cohomology groups of the canonical rational Tate coefficient object.
The choice E = Q_ell includes the source's Q_ell(m) convention.
Source: rational-coefficient Tate abbreviations
(blueprint: def-weil-ordinary-compact-cohomology). -/
def rationalTwistedConstant (ell : ℕ) [Fact ell.Prime]
    (E : Type u) [Field E] [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (m i : ℤ) (c : Compactification Y.hom) :=
  (ordinaryTwistedConstantWithLine (twistRationalRing ell E) D Y
      (coefficientRationalTwistOne ell E Y.left) m i,
    compactTwistedConstantWithLine (twistRationalRing ell E) D Y c
      (coefficientRationalTwistOne ell E Y.left) m i)

omit Λ in
/-- Both cohomology groups of the canonical algebraic-closure Tate coefficient
object, using the existing finite-subextension-valued condensed ring and twist.
Source: algebraic-closure Tate abbreviations
(blueprint: def-weil-ordinary-compact-cohomology). -/
def algebraicTwistedConstant (ell : ℕ) [Fact ell.Prime]
    (m i : ℤ) (c : Compactification Y.hom) :=
  ((ordinaryH (Profinite.padicAlgClRingObj ell) D Y i).obj
      ((tateTwistFunctor Y.left ell m).obj (𝟙_ _)),
    (compactH (Profinite.padicAlgClRingObj ell) D Y c i).obj
      ((tateTwistFunctor Y.left ell m).obj (𝟙_ _)))

omit Y in
/-- The canonical Weil structure on the coefficient sheaf, from the monoidal
unit comparison of the actual Frobenius pullback.
Source: the Weil coefficient-sheaf paragraph
(blueprint: def-weil-ordinary-compact-cohomology). -/
def coefficientWeilModule (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :
    condensedWeilModules Λ (D.geometricFrobenius Y₀).hom :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk (𝟙_ _)
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ (D.geometricFrobenius Y₀).hom)).symm

/-- For a Weil complex, ordinary coefficient complexes are obtained by For.
Source: the final Weil-complex convention
(blueprint: def-weil-ordinary-compact-cohomology). -/
def ordinaryWeil (g : Y.left ⟶ Y.left) [IsIso g] :=
  condensedWeilForget Λ g ⋙ (boundedConstructible (condensedRingObj Λ Y.left)).ι ⋙
    ordinary Λ D Y

/-- For a Weil complex, compact coefficient complexes are obtained by For.
Source: the final Weil-complex convention
(blueprint: def-weil-ordinary-compact-cohomology). -/
def compactWeil (c : Compactification Y.hom) (g : Y.left ⟶ Y.left) [IsIso g] :=
  condensedWeilForget Λ g ⋙ (boundedConstructible (condensedRingObj Λ Y.left)).ι ⋙
    compact Λ D Y c

/-- Ordinary cohomology of For(K), for a Weil complex K.
Source: the final Weil-complex convention
(blueprint: def-weil-ordinary-compact-cohomology). -/
def ordinaryWeilH (g : Y.left ⟶ Y.left) [IsIso g] (i : ℤ) :=
  ordinaryWeil Λ D Y g ⋙
    @DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (condensedScalarRing Λ)) _ _
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _) i

/-- Compact cohomology of For(K), for a Weil complex K.
Source: the final Weil-complex convention
(blueprint: def-weil-ordinary-compact-cohomology). -/
def compactWeilH (c : Compactification Y.hom) (g : Y.left ⟶ Y.left) [IsIso g]
    (i : ℤ) :=
  compactWeil Λ D Y c g ⋙
    @DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (condensedScalarRing Λ)) _ _
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _) i

end WeilConjectures.OrdinaryCompactCohomology
