/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCoefficientTwists
public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Determinant

/-! # Ordinary and compact cohomology at the geometric point

Source: latest blueprint, sec-six-functors-basics/sk-thm-existence/
def-weil-ordinary-compact-cohomology.md
(blueprint: def-weil-ordinary-compact-cohomology).

## Main definitions

* `OrdinaryCompactCoefficient` selects exactly the four condensed coefficient rings.
* `OrdinaryCompactCoefficient.pointFiber` is the existing geometric-point evaluation.
* `OrdinaryCompactCoefficient.pointEquivalence` states its four finite-cohomology equivalences.
* `OrdinaryCompactCohomology.ordinaryCoefficientComplex` and `compactCoefficientComplex`
  are respectively `Fib_s Ra_*` and `Fib_s Ra_!`, with `s = Spec D.k`.
* `ordinaryCohomology` and `compactCohomology` are their integer homology functors.
* The constant, twisted, and Weil variants below apply these same functors, without
  introducing a second cohomology construction for any coefficient.

The coefficient scalars are the ordinary rings `Λ(*)`, as in the recorded point convention.
The finite extension is explicitly lifted to the scheme universe when calling the recorded
coefficient-twist API. This is only `ULift E`, with its canonical equivalence to the chosen
finite subextension of `PadicAlgCl ell`; it imposes no universe equality. The finite index
`n : ℕ` always denotes exponent `n + 1`, so every positive uniformizer level is included.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- Exactly the four coefficient choices; `finite E n` means `O_E / π_E^(n+1)`.
Source: the coefficient list (blueprint: def-weil-ordinary-compact-cohomology). -/
inductive OrdinaryCompactCoefficient (ell : ℕ) [Fact ell.Prime]
  | finite (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ)
  | integral (E : PadicAlgCl.FiniteIntermediateField ell)
  | rational (E : PadicAlgCl.FiniteIntermediateField ell)
  | qbar

namespace OrdinaryCompactCoefficient

variable {ell : ℕ} [Fact ell.Prime]

/-- The recorded condensed coefficients, including the discrete uniformizer quotient.
Source: the coefficient list (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev ring : OrdinaryCompactCoefficient ell →
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  | .finite E n => twistFiniteRing ell (ULift.{u} E) n
  | .integral E => twistIntegralRing ell (ULift.{u} E)
  | .rational E => twistRationalRing ell (ULift.{u} E)
  | .qbar => Profinite.padicAlgClRingObj ell

/-- The coefficient multiplication is the existing pointwise ring multiplication.
Source: the condensed coefficient convention (blueprint: def-weil-ordinary-compact-cohomology). -/
instance ringMonObj (c : OrdinaryCompactCoefficient ell) : MonObj c.ring.{u} := by
  cases c <;> dsimp [ring, twistFiniteRing, twistIntegralRing, twistRationalRing] <;>
    infer_instance

/-- Each of the four condensed coefficient rings is commutative.
Source: the coefficient list (blueprint: def-weil-ordinary-compact-cohomology). -/
instance ringCommMonObj (c : OrdinaryCompactCoefficient ell) : IsCommMonObj c.ring.{u} := by
  cases c <;> dsimp [ring, twistFiniteRing, twistIntegralRing, twistRationalRing] <;>
    infer_instance

/-- `Λ_Y = p_Y^* Λ` on the actual small pro-etale site.
Source: the coefficient-sheaf paragraph (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev coefficientRing (c : OrdinaryCompactCoefficient ell) (Y : Scheme.{u}) :=
  condensedRingObj c.ring Y

/-- The ambient ordinary derived category of condensed `Λ_Y`-modules.
Source: the `D^b_c` convention (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev ambient (c : OrdinaryCompactCoefficient ell) (Y : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (c.coefficientRing Y))

/-- The cohomologically bounded constructible full subcategory, without finite-Tor restrictions.
Source: the `D^b_c` convention (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev boundedConstructible (c : OrdinaryCompactCoefficient ell) (Y : Scheme.{u}) :=
  ProEtale.BoundedConstructible (c.coefficientRing Y)

/-- The ordinary scalar ring is `Λ(*)`, the singleton section ring of the condensed coefficient.
Source: the four point categories (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev scalarRing (c : OrdinaryCompactCoefficient ell) : CommRingCat.{u + 1} :=
  condensedScalarRing c.ring.{u}

/-- Use the same small derived localization as the recorded scalar fiber.
Source: the ordinary coefficient category (blueprint: def-weil-ordinary-compact-cohomology). -/
instance scalarHasDerived (c : OrdinaryCompactCoefficient ell) :
    HasDerivedCategory.{u + 1, u + 1, u + 2} (ModuleCat.{u + 1} c.scalarRing.{u}) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

/-- The ordinary unbounded derived category over `Λ(*)`.
Source: the four point categories (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev scalarDerived (c : OrdinaryCompactCoefficient ell) :=
  DerivedCategory.{u + 1, u + 1, u + 2} (ModuleCat.{u + 1} c.scalarRing.{u})

/-- The recorded bounded finite-cohomology predicate: finite modules for the finite quotient,
finitely generated modules for the integers, and finite-dimensional modules for the fields.
Source: the four point categories (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev finiteCohomology (c : OrdinaryCompactCoefficient ell) :
    ObjectProperty c.scalarDerived.{u} :=
  CondensedGeometricPoint.scalarFiniteCohomology c.ring.{u}

/-- Evaluation at the geometric point `s = Spec D.k`, in each of the four coefficients.
This is the existing derived singleton evaluation after the canonical point-topos equivalence.
Source: the four `Fib_s` displays (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev pointFiber (D : FiniteFieldDatum.{u}) (c : OrdinaryCompactCoefficient ell) :
    c.ambient (Spec (.of D.k)) ⥤ c.scalarDerived.{u} :=
  CondensedGeometricPoint.fiber c.ring D.k

/-- Restriction of that fixed functor; the argument certifies membership and supplies no data.
Source: the four `Fib_s` displays (blueprint: def-weil-ordinary-compact-cohomology). -/
def boundedPointFiber (D : FiniteFieldDatum.{u}) (c : OrdinaryCompactCoefficient ell)
    (h : ∀ K : c.boundedConstructible (Spec (.of D.k)),
      c.finiteCohomology.{u} ((c.pointFiber D).obj K.obj)) :=
  c.finiteCohomology.{u}.lift
    ((ProEtale.boundedConstructible (c.coefficientRing (Spec (.of D.k)))).ι ⋙ c.pointFiber D) h

/-- The four canonical evaluation equivalences, with the cohomological constructibility
predicate of the node, rather than a finite-Tor or completed subcategory.
Source: the four `Fib_s` displays (blueprint: def-weil-ordinary-compact-cohomology).
Proof: the algebraically closed point has the condensed point topos. Every cover of its final
object splits, so singleton evaluation is exact. The scalar-extension/evaluation adjunction
has invertible unit. A constructible module is globally finitely presented, because a
trivializing cover splits; conversely, scalar realization of a finite presentation is
constructible. Thus the heart counit is invertible on exactly these objects. Exactness gives
the derived adjunction and identifies cohomology on both sides; boundedness then makes its
counit invertible on precisely the two displayed full subcategories. The finite quotient is
a finite ring, so finite generation means finite cardinality, and over either field it means
finite dimension. The same argument identifies the constant-model and cohomological
constructibility predicates at the point. No finite-Tor hypothesis is used. -/
theorem pointEquivalence (D : FiniteFieldDatum.{u}) (_hell : ell ≠ D.p)
    (c : OrdinaryCompactCoefficient ell) :
    ∃ h : ∀ K : c.boundedConstructible (Spec (.of D.k)),
      c.finiteCohomology.{u} ((c.pointFiber D).obj K.obj),
      (c.boundedPointFiber D h).IsEquivalence := by
  sorry

/-- The constant coefficient object is the regular pulled-back module in degree zero.
For the finite branch its underlying ring sheaf is the constant discrete quotient sheaf.
Source: the `Λ_Y` and constant abbreviations (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev constantObject (c : OrdinaryCompactCoefficient ell) (Y : Scheme.{u}) : c.ambient Y :=
  (DerivedCategory.singleFunctor _ 0).obj (Mod.regular (c.coefficientRing Y))

/-- The finite coefficient sheaf is the constant sheaf of the discrete uniformizer quotient.
Source: the finite-coefficient sentence (blueprint: def-weil-ordinary-compact-cohomology).
Proof: continuous maps into the finite discrete ring are locally constant. The resulting
condensed sheaf is its constant sheaf, and pulling it to the small pro-etale site preserves
constant sheaves. The uniformizer quotient is finite at every positive exponent. -/
theorem finiteCoefficient_constant (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ)
    (Y : Scheme.{u}) :
    Nonempty (Mon.mk ((OrdinaryCompactCoefficient.finite E n).coefficientRing Y) ≅
      Mon.mk ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          ((constantSheaf (Scheme.ProEt.topology Y) RingCat.{u + 1}).obj
            (RingCat.of (ULift.{u + 1}
              (Padic.coefficientExtensionRing ell (ULift.{u} E) (n + 1))))))) := by
  sorry

/-- Twisting uses precisely the recorded coefficient-twist functors, in all integer degrees.
Source: the Tate-twist paragraph (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev twistFunctor (c : OrdinaryCompactCoefficient ell) (Y : Scheme.{u}) (m : ℤ) :
    c.ambient Y ⥤ c.ambient Y :=
  match c with
  | .finite E n => coefficientFiniteTwistFunctor ell (ULift.{u} E) Y n m
  | .integral E => coefficientIntegralTwistFunctor ell (ULift.{u} E) Y m
  | .rational E => coefficientRationalTwistFunctor ell (ULift.{u} E) Y m
  | .qbar => tateTwistFunctor Y ell m

/-- `Λ_Y(m) = Λ_Y ⊗^L_Λ Λ(m)_Y`, using the recorded signed coefficient line.
Source: the Tate-twist paragraph (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev twistedConstantObject (c : OrdinaryCompactCoefficient ell) (Y : Scheme.{u}) (m : ℤ) :=
  (c.twistFunctor Y m).obj (c.constantObject Y)

/-- The two field coefficients for which the node asserts a canonical Weil structure.
Source: the Weil-sheaf paragraph (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev ofWeilCoefficient : WeilCoefficient ell → OrdinaryCompactCoefficient ell
  | .finite E => .rational E
  | .qbar => .qbar

/-- The down map from the spectral-norm coordinate field to the given finite subfield is
continuous. This fixes the coefficient transport, rather than choosing an unspecified isomorphism.
Source: the choice of finite coefficient field (blueprint: def-weil-ordinary-compact-cohomology).
Proof: equip the lifted field with its spectral normed-space structure over Q_ell. The down
map is Q_ell-linear between finite-dimensional normed spaces, and is therefore continuous. -/
theorem rationalCoordinateDown_continuous (E : PadicAlgCl.FiniteIntermediateField ell) :
    letI nf := spectralNorm.normedField ℚ_[ell] (ULift.{u} E)
    letI : TopologicalSpace (ULift.{u} E) :=
      nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Continuous (ULift.down : ULift.{u} E → E) := by
  sorry

/-- The up map is the inverse continuous coordinate map.
Source: the choice of finite coefficient field (blueprint: def-weil-ordinary-compact-cohomology).
Proof: the inverse linear equivalence is continuous for the same finite-dimensional reason;
its codomain has the spectral norm topology and its domain the inherited subfield topology. -/
theorem rationalCoordinateUp_continuous (E : PadicAlgCl.FiniteIntermediateField ell) :
    letI nf := spectralNorm.normedField ℚ_[ell] (ULift.{u} E)
    letI : TopologicalSpace (ULift.{u} E) :=
      nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Continuous (ULift.up : E → ULift.{u} E) := by
  sorry

/-- The explicit ring-sheaf isomorphism removes the twist API's coefficient-universe lift.
Every component postcomposes functions with `ULift.down`; the inverse uses `ULift.up`.
Source: the same coefficient E in all conventions
(blueprint: def-weil-ordinary-compact-cohomology). -/
def rationalCoordinateRingIso (E : PadicAlgCl.FiniteIntermediateField ell) :
    letI nf := spectralNorm.normedField ℚ_[ell] (ULift.{u} E)
    letI : TopologicalSpace (ULift.{u} E) :=
      nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Profinite.continuousCoefficientRingSheaf (ULift.{u} E) ≅
      Profinite.continuousMapRingSheaf.{u} E := by
  letI nf := spectralNorm.normedField ℚ_[ell] (ULift.{u} E)
  letI : TopologicalSpace (ULift.{u} E) :=
    nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let e (S : Profinite.{u}) : C(S, ULift.{u} E) ≃+* C(S, E) :=
    { toFun := fun f ↦ ⟨fun x ↦ (f x).down,
        (rationalCoordinateDown_continuous E).comp f.continuous⟩
      invFun := fun f ↦ ⟨fun x ↦ ULift.up (f x),
        (rationalCoordinateUp_continuous E).comp f.continuous⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  refine
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e S.unop).toRingHom.comp ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e S.unop).symm.toRingHom.comp ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · ext S f
    rfl
  · ext S f
    rfl

/-- Canonical coefficient coordinates between the recorded Weil category and twist API.
For Qbar this is the identity; for E it is the explicit up/down ring-sheaf isomorphism.
Source: the same coefficient E in the Weil and twist clauses
(blueprint: def-weil-ordinary-compact-cohomology). -/
def weilCoefficientCoordinates (c : WeilCoefficient ell) :
    (Mon.mk (ofWeilCoefficient c).ring.{u} : Profinite.CondensedRing.{u}) ≅
      Mon.mk (WeilCoefficient.ab c) := by
  cases c with
  | finite E =>
    let F := sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})
    let e : twistRationalRing ell (ULift.{u} E) ≅
        Profinite.continuousMapRingObj.{u} E :=
      F.mapIso (rationalCoordinateRingIso E)
    have : IsMonHom e.hom :=
      Sheaf.isMonHom_sheafCompose_map _ (rationalCoordinateRingIso E).hom
    change Mon.mk (twistRationalRing ell (ULift.{u} E)) ≅
      Mon.mk (Profinite.continuousMapRingObj.{u} E)
    exact Mon.mkIso' e
  | qbar => exact Iso.refl _

/-- The canonical Weil structure on `Λ_Y` is the inverse of the monoidal unit comparison.
Its carrier is exactly the regular pulled-back coefficient module, for `E` and `Qbar` only.
Source: the Weil-sheaf paragraph (blueprint: def-weil-ordinary-compact-cohomology). -/
def constantWeilModule (D : FiniteFieldDatum.{u}) (_hell : ell ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (c : WeilCoefficient ell) :
    condensedWeilModules (WeilCoefficient.ab c) (D.geometricFrobenius Y₀).hom :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk
    (Mod.regular (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber Y₀).left))
    (Functor.Monoidal.εIso
      (CondensedRing.upperStar (WeilCoefficient.ab c) (D.geometricFrobenius Y₀).hom)).symm

/-- The canonical coefficient Weil module is a constructible Weil sheaf.
Source: the Weil-sheaf paragraph (blueprint: def-weil-ordinary-compact-cohomology).
Proof: the coefficient module is free of rank one over itself on the single stratum `Y`.
The canonical Weil isomorphism is pullback's unit comparison, so adding it leaves the
constructibility of the carrier unchanged. -/
theorem constantWeilModule_constructible (D : FiniteFieldDatum.{u}) (hell : ell ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom] (c : WeilCoefficient ell) :
    IsConstructibleModuleObject (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber Y₀).left)
      (constantWeilModule D hell Y₀ c).carrier := by
  sorry

/-- The coefficient sheaf with its canonical Weil structure, as an actual Weil sheaf.
Source: the Weil-sheaf paragraph (blueprint: def-weil-ordinary-compact-cohomology). -/
def constantWeilSheaf (D : FiniteFieldDatum.{u}) (hell : ell ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom] (c : WeilCoefficient ell) :
    condensedConstructibleWeilSheaves (WeilCoefficient.ab c) (D.geometricFrobenius Y₀).hom :=
  ⟨constantWeilModule D hell Y₀ c, constantWeilModule_constructible D hell Y₀ c⟩

end OrdinaryCompactCoefficient

/-- The finite-field datum, distinct coefficient prime, and separated finite-type geometric
scheme required throughout the cohomology convention. Keeping them as data retains every
hypothesis in every public cohomology signature.
Source: the setup paragraph (blueprint: def-weil-ordinary-compact-cohomology). -/
structure OrdinaryCompactCohomologyDatum where
  datum : FiniteFieldDatum.{u}
  ell : ℕ
  [prime : Fact ell.Prime]
  different : ell ≠ datum.p
  Y : Over (Spec (.of datum.k))
  [finite_type : LocallyOfFiniteType Y.hom]
  [quasi_compact : QuasiCompact Y.hom]
  [separated : IsSeparated Y.hom]

attribute [instance] OrdinaryCompactCohomologyDatum.prime
  OrdinaryCompactCohomologyDatum.finite_type OrdinaryCompactCohomologyDatum.quasi_compact
  OrdinaryCompactCohomologyDatum.separated

namespace OrdinaryCompactCohomology

variable (T : OrdinaryCompactCohomologyDatum.{u}) (c : OrdinaryCompactCoefficient T.ell)

/-- The existing field-base compactification supplies the compact-support presentation.
Source: the separated finite-type hypothesis (blueprint: def-weil-ordinary-compact-cohomology). -/
def compactification : Compactification T.Y.hom :=
  NagataCompactification T.Y.hom

/-- `RΓ(Y,K) = Fib_s(Ra_{Y*} K)` for the specified geometric point `s`.
Source: the first coefficient-complex display (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev ordinaryCoefficientComplex : c.ambient T.Y.left ⥤ c.scalarDerived.{u} :=
  (CondensedRing.lowerStar c.ring T.Y.hom).rightDerivedFunctor ⋙ c.pointFiber T.datum

/-- `RΓ_c(Y,K) = Fib_s(Ra_{Y!} K)` for the same `s` and the same coefficient.
Source: the second coefficient-complex display (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev compactCoefficientComplex (T : OrdinaryCompactCohomologyDatum.{u})
    (c : OrdinaryCompactCoefficient T.ell) : c.ambient T.Y.left ⥤ c.scalarDerived.{u} :=
  CondensedRing.rightDerivedLowerShriekOfCompactification c.ring (compactification T) ⋙
    c.pointFiber T.datum

/-- The ordinary coefficient complex restricted to exactly `D^b_c(Y,Λ)`.
Source: the `K ∈ D^b_c` clause (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev ordinaryBoundedCoefficientComplex : c.boundedConstructible T.Y.left ⥤ c.scalarDerived.{u} :=
  (ProEtale.boundedConstructible (c.coefficientRing T.Y.left)).ι ⋙ ordinaryCoefficientComplex T c

/-- The compact coefficient complex restricted to exactly `D^b_c(Y,Λ)`.
Source: the `K ∈ D^b_c` clause (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev compactBoundedCoefficientComplex : c.boundedConstructible T.Y.left ⥤ c.scalarDerived.{u} :=
  (ProEtale.boundedConstructible (c.coefficientRing T.Y.left)).ι ⋙ compactCoefficientComplex T c

/-- `H^i(Y,K) = H^i(RΓ(Y,K))`, for every integer `i`.
Source: the cohomology display (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev ordinaryCohomology (i : ℤ) :=
  ordinaryCoefficientComplex T c ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u + 1} c.scalarRing.{u}) i

/-- `H_c^i(Y,K) = H^i(RΓ_c(Y,K))`, for every integer `i`.
This is the single compact-cohomology definition, including the Qbar branch.
Source: the cohomology display (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev compactCohomology (i : ℤ) :=
  compactCoefficientComplex T c ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u + 1} c.scalarRing.{u}) i

/-- The constant coefficient object is bounded constructible for each of the four rings.
Source: the constant-coefficient abbreviations (blueprint: def-weil-ordinary-compact-cohomology).
Proof: the regular module is free of rank one and hence constructible on the single stratum.
Its single complex has cohomology only in degree zero, so it is cohomologically bounded. -/
theorem constantObject_mem :
    ProEtale.boundedConstructible (c.coefficientRing T.Y.left) (c.constantObject T.Y.left) := by
  sorry

/-- The two coefficient complexes have bounded finite cohomology over the ordinary ring `Λ(*)`.
Source: applying the displayed `Fib_s` equivalences
(blueprint: def-weil-ordinary-compact-cohomology).
Proof: finite-type direct image and compact-support direct image preserve bounded
constructible complexes for these coefficients. Apply the four point equivalences to the
two images. Proper direct image and open extension in the compactification give the same
compact-support image, independently of its presentation. -/
theorem coefficientComplexes_finite (K : c.boundedConstructible T.Y.left) :
    c.finiteCohomology.{u} ((ordinaryCoefficientComplex T c).obj K.obj) ∧
    c.finiteCohomology.{u} ((compactCoefficientComplex T c).obj K.obj) := by
  sorry

/-- The constant-coefficient abbreviation `H^i(Y,Λ)`.
Source: the first constant abbreviation (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev ordinaryConstantCohomology (i : ℤ) :=
  (ordinaryCohomology T c i).obj (c.constantObject T.Y.left)

/-- The constant-coefficient abbreviation `H_c^i(Y,Λ)`.
Source: the second constant abbreviation (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev compactConstantCohomology (i : ℤ) :=
  (compactCohomology T c i).obj (c.constantObject T.Y.left)

/-- `H^i(Y,Λ(m))`, with both integers unrestricted.
Source: the twist abbreviation (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev ordinaryTwistedCohomology (i m : ℤ) :=
  (ordinaryCohomology T c i).obj (c.twistedConstantObject T.Y.left m)

/-- `H_c^i(Y,Λ(m))`, with both integers unrestricted.
Source: the twist abbreviation (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev compactTwistedCohomology (i m : ℤ) :=
  (compactCohomology T c i).obj (c.twistedConstantObject T.Y.left m)

section Weil

variable (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom] (w : WeilCoefficient ell)

/-- The geometric base change supplies the datum used by all four Weil abbreviations.
Source: the `Y = Y₀ × k` clause (blueprint: def-weil-ordinary-compact-cohomology). -/
def geometricDatum : OrdinaryCompactCohomologyDatum.{u} where
  datum := D
  ell := ell
  different := hell
  Y := D.geometricFiber Y₀
  finite_type := inferInstanceAs (LocallyOfFiniteType
    (pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  quasi_compact := inferInstanceAs (QuasiCompact
    (pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  separated := inferInstanceAs (IsSeparated
    (pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- The recorded `For(K)` on actual condensed Weil complexes for either field coefficient.
Source: the Weil-complex clause (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev forgetWeil :=
  condensedWeilForget (WeilCoefficient.ab w) (D.geometricFrobenius Y₀).hom ⋙
    (ProEtale.boundedConstructible
      (condensedRingObj (WeilCoefficient.ab w) (D.geometricFiber Y₀).left)).ι ⋙
    (Mod.comap (coefficientMap
      (OrdinaryCompactCoefficient.weilCoefficientCoordinates w).hom.hom
        (D.geometricFiber Y₀).left)).mapDerivedCategory

/-- For a Weil complex, ordinary sections mean the same construction applied to `For(K)`.
Source: the Weil-complex clause (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev ordinaryWeilCoefficientComplex :=
  forgetWeil D ell Y₀ w ⋙ ordinaryCoefficientComplex (geometricDatum D ell hell Y₀)
    (OrdinaryCompactCoefficient.ofWeilCoefficient w)

/-- For a Weil complex, compact sections mean the same construction applied to `For(K)`.
Source: the Weil-complex clause (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev compactWeilCoefficientComplex :=
  forgetWeil D ell Y₀ w ⋙ compactCoefficientComplex (geometricDatum D ell hell Y₀)
    (OrdinaryCompactCoefficient.ofWeilCoefficient w)

/-- Integer ordinary cohomology of a Weil complex is `H^i(RΓ(Y,For(K)))`.
Source: the Weil-complex clause (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev ordinaryWeilCohomology (i : ℤ) :=
  ordinaryWeilCoefficientComplex D ell hell Y₀ w ⋙ DerivedCategory.homologyFunctor
    (ModuleCat.{u + 1} (OrdinaryCompactCoefficient.ofWeilCoefficient w).scalarRing.{u}) i

/-- Integer compact cohomology of a Weil complex is `H^i(RΓ_c(Y,For(K)))`.
Source: the Weil-complex clause (blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev compactWeilCohomology (i : ℤ) :=
  compactWeilCoefficientComplex D ell hell Y₀ w ⋙ DerivedCategory.homologyFunctor
    (ModuleCat.{u + 1} (OrdinaryCompactCoefficient.ofWeilCoefficient w).scalarRing.{u}) i

end Weil
end OrdinaryCompactCohomology
end WeilConjectures
