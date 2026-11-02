/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.CurrentExceptionalAdjointAdmissibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientTwistAnnihilator
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSmoothTraceUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.SixFunctors.Coefficient.CoefficientDuality
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.GroupScheme.FrobeniusCoefficientReduction.DirectFrobeniusCohomologyTransport
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

/-! # Condensed Poincare duality conventions

Source: current blueprint, under
part-duality-trace-formula/sec-smooth-purity/sec-sp-grp-trace/sec-the-trace-map/
sk-cor-sp-all-coefficients/def-pod-conventions.md (blueprint: def-pod-conventions).

All categories and operations below use actual pulled-back condensed coefficients.
The exceptional inverse image is the explicit normalized smooth right adjoint
from purity. Its identification with any specified Brown right adjoint is the
counit-preserving comparison in the recorded purity theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- The four coefficient labels are presentation indices, not new rings.
Source: the displayed list of coefficients (blueprint: def-pod-conventions). -/
inductive PoincareCoefficient
  | finite
  | integral
  | rational
  | qbar

/-- The global finite-field, coefficient and geometric setting. A compactification
presents the compact-support functor, and its finite-ring admissibility is the
recorded predicate. No properness of the smooth model is imposed.
Source: the opening paragraph (blueprint: def-pod-conventions). -/
structure CondensedPoincareDualityConventions where
  datum : FiniteFieldDatum.{u}
  ell : ℕ
  [prime : Fact ell.Prime]
  different : ell ≠ datum.p
  extension : PadicAlgCl.FiniteIntermediateField ell
  level : ℕ
  level_pos : 1 ≤ level
  X₀ : Over (Spec (.of datum.k₀))
  [finite_type : LocallyOfFiniteType X₀.hom]
  [quasi_compact : QuasiCompact X₀.hom]
  [separated : IsSeparated X₀.hom]
  dimension : ℕ
  [smooth : SmoothOfRelativeDimension dimension X₀.hom]
  [geometrically_connected : GeometricallyConnected X₀.hom]
  admissibility : ∀ (A : Type u) [CommRing A] [Finite A],
    IsExceptionalAdjointAdmissibleAtFiniteRing A
      ((AlgebraicGeometry.NagataCompactification X₀.hom).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap datum.k₀ datum.k))))

attribute [instance] CondensedPoincareDualityConventions.prime
  CondensedPoincareDualityConventions.finite_type
  CondensedPoincareDualityConventions.quasi_compact
  CondensedPoincareDualityConventions.separated
  CondensedPoincareDualityConventions.smooth
  CondensedPoincareDualityConventions.geometrically_connected

namespace CondensedPoincareDualityConventions

/-- The four actual coefficient presentations. The finite exponent is only the
annihilator certificate required by the existing presentation; the ring is
exactly O_E/(pi_E^level), also in ramified extensions.
Source: coefficient paragraph (blueprint: def-pod-conventions). -/
def presentation (P : CondensedPoincareDualityConventions.{u}) :
    PoincareCoefficient → Coefficient P.ell
  | .finite => .finite
      (.of (Padic.coefficientExtensionRing P.ell P.extension P.level))
      (Padic.finite_coefficientExtensionRing P.ell P.extension P.level P.level_pos)
      (P.level - 1) (by
        have h := coefficientFiniteTwist_annihilator P.ell P.extension (P.level - 1)
        rw [Nat.sub_add_cancel P.level_pos] at h
        simpa only [Nat.sub_add_cancel P.level_pos, Nat.cast_pow] using h)
  | .integral => .integral P.extension
  | .rational => .rational P.extension
  | .qbar => .closure

/-- Geometric fibre, point, and structure morphism from the recorded base change.
Source: X, s and a_X in the opening paragraph (blueprint: def-pod-conventions). -/
abbrev X (P : CondensedPoincareDualityConventions.{u}) : Scheme.{u} :=
  (P.datum.geometricFiber P.X₀).left

abbrev s (P : CondensedPoincareDualityConventions.{u}) : Scheme.{u} :=
  Spec (.of P.datum.k)

abbrev structureMap (P : CondensedPoincareDualityConventions.{u}) : P.X ⟶ P.s :=
  (P.datum.geometricFiber P.X₀).hom

/-- The chosen model compactification transported to the geometric fibre. -/
abbrev compactification (P : CondensedPoincareDualityConventions.{u}) :
    Compactification P.structureMap :=
  (AlgebraicGeometry.NagataCompactification P.X₀.hom).baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap P.datum.k₀ P.datum.k)))

/-- Ambient derived categories and the two full bounded constructible categories,
on either X or the point. In particular ctf at the point is not defined by
perfect scalar complexes.
Source: the category displays and point paragraph (blueprint: def-pod-conventions). -/
abbrev ambient (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient)
    (T : Scheme.{u}) := (P.presentation c).derived P.ell T

abbrev bc (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient)
    (T : Scheme.{u}) :=
  ConstantModelBoundedConstructible ((P.presentation c).obj P.ell) T

abbrev ctf (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient)
    (T : Scheme.{u}) := (P.presentation c).ctf P.ell T

/-- Derived inverse image on the pulled-back condensed coefficients.
Source: the six-operation convention (blueprint: def-pod-conventions). -/
abbrev pullback (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient)
    {T U : Scheme.{u}} (f : T ⟶ U) :=
  moduleObjectDerivedPullback ((P.presentation c).obj P.ell) f

/-- Derived direct image on the pulled-back condensed coefficients.
Source: the six-operation convention (blueprint: def-pod-conventions). -/
abbrev directImage (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient)
    {T U : Scheme.{u}} (f : T ⟶ U) :=
  moduleObjectDerivedPushforward ((P.presentation c).obj P.ell) f

/-- The ambient relative derived tensor, without a scalar-model replacement.
Source: the six-operation convention (blueprint: def-pod-conventions). -/
abbrev tensor (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient)
    (T : Scheme.{u}) (K L : P.ambient c T) : P.ambient c T := K ⊗ L

/-- The ambient relative derived internal Hom.
Source: the six-operation convention (blueprint: def-pod-conventions). -/
abbrev internalHom (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient)
    (T : Scheme.{u}) := derivedHom ((P.presentation c).obj P.ell) T

/-- Ordinary and compact derived sections are the recorded condensed functors.
Source: the RΓ and RΓ_c paragraph (blueprint: def-pod-conventions). -/
def ordinarySections (P : CondensedPoincareDualityConventions.{u})
    (c : PoincareCoefficient) :=
  condensedRingOrdinaryCoefficientComplex ((P.presentation c).obj P.ell) P.structureMap

def compactSections (P : CondensedPoincareDualityConventions.{u})
    (c : PoincareCoefficient) :=
  condensedRingCompactCoefficientComplex ((P.presentation c).obj P.ell) P.compactification

/-- Ordinary cohomology in degree `i`, with the actual scalar action. -/
def ordinaryCohomology (P : CondensedPoincareDualityConventions.{u})
    (c : PoincareCoefficient) (i : ℤ) :=
  letI := HasDerivedCategory.ofIsGrothendieckAbelian
    (ModuleCat.{u + 1} (MonObj.Γ ((P.presentation c).obj P.ell)))
  P.ordinarySections c ⋙ DerivedCategory.homologyFunctor _ i

/-- Compactly supported cohomology in degree `i`, with the actual scalar action. -/
def compactCohomology (P : CondensedPoincareDualityConventions.{u})
    (c : PoincareCoefficient) (i : ℤ) :=
  letI := HasDerivedCategory.ofIsGrothendieckAbelian
    (ModuleCat.{u + 1} (MonObj.Γ ((P.presentation c).obj P.ell)))
  P.compactSections c ⋙ DerivedCategory.homologyFunctor _ i

/-- The actual root-tower first Tate line is extended along the integral coefficient
map. Signed powers and their derived tensor are the recorded signed-twist operation.
Source: Tate-twist paragraph (blueprint: def-pod-conventions). -/
def twist (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient)
    (T : Scheme.{u}) (K : P.ambient c T) (m : ℤ) : P.ambient c T :=
  spInternalComplexTwist T (condensedRingObj ((P.presentation c).obj P.ell) T)
    ((P.presentation c).firstLine P.ell T) K m

/-- The geometric index for smooth purity; every instance is inherited by base change.
Source: the smooth pure-dimension hypothesis (blueprint: def-pod-conventions). -/
def smoothIndex (P : CondensedPoincareDualityConventions.{u}) : SmoothDatum P.datum where
  X := P.datum.geometricFiber P.X₀
  Y := Over.mk (𝟙 P.s)
  xFinite := by
    change LocallyOfFiniteType (pullback.snd P.X₀.hom _)
    infer_instance
  xQuasiCompact := by
    change QuasiCompact (pullback.snd P.X₀.hom _)
    infer_instance
  xSeparated := by
    change IsSeparated (pullback.snd P.X₀.hom _)
    infer_instance
  yFinite := by change LocallyOfFiniteType (𝟙 P.s); infer_instance
  yQuasiCompact := by change QuasiCompact (𝟙 P.s); infer_instance
  ySeparated := by change IsSeparated (𝟙 P.s); infer_instance
  map := P.structureMap
  isOver := ⟨by change P.structureMap ≫ 𝟙 P.s = P.structureMap; simp⟩
  separated := by
    change IsSeparated (pullback.snd P.X₀.hom _)
    infer_instance
  finiteType := by
    change LocallyOfFiniteType (pullback.snd P.X₀.hom _)
    infer_instance
  quasiCompact := by
    change QuasiCompact (pullback.snd P.X₀.hom _)
    infer_instance
  dim := P.dimension
  smooth := by
    change SmoothOfRelativeDimension P.dimension (pullback.snd P.X₀.hom _)
    infer_instance
  compactification := P.compactification

/-- Compact support and its explicit smooth right adjoint on Dctf.
The latter is the normalized representative of Ra_X^!: it is uniquely
counit-isomorphic to every specified Brown restriction.
Source: the exceptional-adjoint paragraph (blueprint: def-pod-conventions). -/
def support (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient) :=
  PurityTransport.support P.ell (P.presentation c) P.compactification
    (P.normalizedAdjunction c).support_closed

def exceptionalInverse (P : CondensedPoincareDualityConventions.{u})
    (c : PoincareCoefficient) :=
  source P.ell (P.presentation c) P.structureMap P.dimension
    (P.normalizedAdjunction c).source_closed

def exceptionalAdjunction (P : CondensedPoincareDualityConventions.{u})
    (c : PoincareCoefficient) : P.support c ⊣ P.exceptionalInverse c :=
  (P.normalizedAdjunction c).adjunction

/-- The coefficient unit at the point as an object of the same geometric Dctf.
Source: the point-category paragraph (blueprint: def-pod-conventions). -/
def pointUnit (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient) :
    P.ctf c P.s :=
  ⟨𝟙_ _, smoothTraceUnit_mem P.ell (P.presentation c) P.s⟩

/-- The dualizing object is Ra_X^! of the point unit, not an independently chosen object.
Source: the omega display (blueprint: def-pod-conventions). -/
def omega (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient) :
    P.ctf c P.X :=
  (P.exceptionalInverse c).obj (P.pointUnit c)

/-- The canonical orientation of this normalized smooth right-adjoint presentation.
The source unitor is evaluated at the coefficient unit; its counit is exactly the
integration-normalized counit fixed above.
Source: the eta_X display (blueprint: def-pod-conventions). -/
def orientation (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient) :
    (P.omega c).obj ≅ (P.presentation c).derivedLine P.ell P.X P.dimension :=
  smoothTraceUnitSource P.ell (P.presentation c) P.datum P.smoothIndex

/-- Verdier dual and coefficient dual in the ambient derived module category.
Source: the two final displays (blueprint: def-pod-conventions). -/
def verdierDual (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient)
    (K : P.ctf c P.X) : P.ambient c P.X :=
  ((derivedHom ((P.presentation c).obj P.ell) P.X).obj (Opposite.op K.obj)).obj
    (P.omega c).obj

/-- The coefficient dual, internally using the coefficient unit. -/
def coefficientDual (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient)
    (K : P.ctf c P.X) : P.ambient c P.X :=
  ((derivedHom ((P.presentation c).obj P.ell) P.X).obj (Opposite.op K.obj)).obj (𝟙_ _)

/-- Scalar coefficient dual, on the ordinary complex obtained at the point.
Source: the C-dual display (blueprint: def-pod-conventions). -/
def pointDual (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient) :=
  letI := HasDerivedCategory.ofIsGrothendieckAbelian
    (ModuleCat.{u + 1} (MonObj.Γ ((P.presentation c).obj P.ell)))
  coefficientDerivedDual (MonObj.Γ ((P.presentation c).obj P.ell))

/-- The strict Weil category uses the recorded finite-Tor pair category and the
actual geometric Frobenius automorphism, without a derived-Weil equivalence.
Source: the strict Weil datum paragraph (blueprint: def-pod-conventions). -/
abbrev strictWeil (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient) :=
  StrictWeilCondensed.Complex ((P.presentation c).obj P.ell)
    ⟨(P.datum.geometricFrobenius P.X₀).hom, (P.datum.geometricFrobenius P.X₀).inv,
      (P.datum.geometricFrobenius P.X₀).hom_inv_id,
      (P.datum.geometricFrobenius P.X₀).inv_hom_id⟩

/-- The signed Tate line with its recorded root-normalized strict Weil structure.
Its point scalar is `q^(-m)`, by `StrictWeilCondensed.tatePull_scalar`; the
negative twist therefore has scalar `q^m`.
Source: the Tate-normalization paragraph (blueprint: def-pod-conventions). -/
def tateWeil (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient)
    (m : ℤ) : P.strictWeil c := by
  letI : ∀ x : P.X, Invertible (P.ell : P.X.residueField x) := fun x ↦ by
    apply IsUnit.invertible
    simpa using (primeUnit P.datum P.ell P.different).map
      (P.structureMap.residueFieldAlgebraMap x)
  exact StrictWeilCondensed.tateComplex P.ell (P.presentation c)
    ⟨(P.datum.geometricFrobenius P.X₀).hom, (P.datum.geometricFrobenius P.X₀).inv,
      (P.datum.geometricFrobenius P.X₀).hom_inv_id,
      (P.datum.geometricFrobenius P.X₀).inv_hom_id⟩ m

/-- The specified scalar `q^(-m)`, using the inverse of multiplication by `q`.
Source: the Tate-normalization paragraph (blueprint: def-pod-conventions). -/
def tateScalar (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient)
    (m : ℤ) :=
  StrictWeilCondensed.cardinalScalar P.ell (P.presentation c) P.datum P.different P.s m

/-- The ordinary and compact-support geometric Frobenius endomorphisms.
The first factor is the canonical condensed point transport; the second is the
same transport through the chosen base compactification. The strict Weil
isomorphism supplies the final map from the pulled-back complex to the complex.
Source: the two composites in def-weil-global-geometric-frobenius
(blueprint: def-pod-conventions). -/
def frobenius (P : CondensedPoincareDualityConventions.{u})
    (c : PoincareCoefficient) (K : P.strictWeil c) :
    End ((P.ordinarySections c).obj K.carrier.obj) ×
      End ((P.compactSections c).obj K.carrier.obj) := by
  let Λ := Mon.mk ((P.presentation c).obj P.ell)
  let g := (P.datum.geometricFrobenius P.X₀).hom
  let θ := (leftDerivedUpperStarIsoMapDerivedCategory Λ.X g).hom.app K.carrier.obj ≫
    K.str.hom.hom
  let ordinary := (CondensedFrobeniusTransport.ordinaryTransport
    P.datum P.X₀ Λ (AlgebraicGeometry.NagataCompactification P.X₀.hom)).app K.carrier.obj
  let compact := (CondensedFrobeniusTransport.compactTransport
    P.datum P.X₀ Λ (AlgebraicGeometry.NagataCompactification P.X₀.hom)).app K.carrier.obj
  exact ⟨ordinary ≫ (P.ordinarySections c).map θ,
    compact ≫ (P.compactSections c).map θ⟩

/-- The induced actions in every integer cohomological degree.
Source: def-weil-global-geometric-frobenius, final sentence
(blueprint: def-pod-conventions). -/
def frobeniusOnCohomology (P : CondensedPoincareDualityConventions.{u})
    (c : PoincareCoefficient) (K : P.strictWeil c) (i : ℤ) :=
  letI := HasDerivedCategory.ofIsGrothendieckAbelian
    (ModuleCat.{u + 1} (MonObj.Γ ((P.presentation c).obj P.ell)))
  ((DerivedCategory.homologyFunctor _ i).map (P.frobenius c K).1,
    (DerivedCategory.homologyFunctor _ i).map (P.frobenius c K).2)

/-- The iterates of the global Frobenius actions, including the zeroth identity.
Source: def-trf-frobenius-operators, iterated Weil structure convention
(blueprint: def-pod-conventions). -/
def frobeniusIterate (P : CondensedPoincareDualityConventions.{u})
    (c : PoincareCoefficient) (K : P.strictWeil c) (m : ℕ) :
    End ((P.ordinarySections c).obj K.carrier.obj) ×
      End ((P.compactSections c).obj K.carrier.obj) :=
  ((P.frobenius c K).1 ^ m, (P.frobenius c K).2 ^ m)


/-- Nonfinite coefficients have no additional finite-Tor restriction.
Source: category paragraph of def-pod-conventions, lem-integral-ctf-equals-bc
(blueprint: def-pod-conventions).
Proof in words. X and s are qcqs. Apply the final equality of
integral_ctf_equals_bc to O_E, E and Qbar on each of these two schemes.
This identifies the intersection predicate with bounded constructibility.
The finite coefficient case is excluded, exactly as in the source. -/
theorem nonfiniteCategoriesAgree (P : CondensedPoincareDualityConventions.{u})
    (c : PoincareCoefficient) (_hc : c ≠ .finite) :
    ((constantModelBoundedConstructible ((P.presentation c).obj P.ell) P.X ⊓
        DerivedCategory.finiteTorAmplitude _) =
      constantModelBoundedConstructible ((P.presentation c).obj P.ell) P.X) ∧
    ((constantModelBoundedConstructible ((P.presentation c).obj P.ell) P.s ⊓
        DerivedCategory.finiteTorAmplitude _) =
      constantModelBoundedConstructible ((P.presentation c).obj P.ell) P.s) := by
  sorry

/-- Point evaluation identifies the geometrically defined Dctf with perfect
scalar complexes, preserving the canonical tensor, unit and closed comparison.
Source: point paragraph of def-pod-conventions, sk-lem-finite
(blueprint: def-pod-conventions).
Proof in words. k is algebraically closed of characteristic p with ell distinct
from p. Apply geometric-point perfectness to the four specified coefficient
rings. The fixed fibre functor is the actual point pullback equivalence followed
by derived singleton evaluation. Its restriction is the asserted exact symmetric
monoidal equivalence, and its closed comparison gives the scalar dual formula.
No equivalence is substituted into the definition of the point category. -/
theorem pointPerfect (P : CondensedPoincareDualityConventions.{u})
    (c : PoincareCoefficient) :
    CondensedGeometricPoint.Statement ((P.presentation c).obj P.ell) P.datum.k := by
  sorry

/-- The finite, integral and field scalar descriptions of the point categories.
Source: point paragraph of def-pod-conventions (blueprint: def-pod-conventions).
Proof in words. A is finite and Noetherian, so bounded finite cohomology and
finite Tor amplitude are equivalent to a bounded finite-projective model.
O_E is a DVR: a finite presentation has finite-free kernel, giving a two-term
finite-free resolution. Assemble the finitely many cohomology resolutions by
truncation triangles. Over E and Qbar finite bases and cohomology splitting
give finite-free models. Conversely such models have bounded finite cohomology,
and the finite coefficient model also has the asserted finite Tor interval. -/
theorem pointScalarDescription (P : CondensedPoincareDualityConventions.{u})
    (c : PoincareCoefficient) :
    letI := HasDerivedCategory.ofIsGrothendieckAbelian
      (ModuleCat.{u + 1} (MonObj.Γ ((P.presentation c).obj P.ell)))
    ∀ C : DerivedCategory (ModuleCat.{u + 1} (MonObj.Γ ((P.presentation c).obj P.ell))),
      DerivedCategory.IsPerfectRingComplex C ↔
        boundedFiniteCoefficientComplex (MonObj.Γ ((P.presentation c).obj P.ell)) C ∧
          (c = .finite → DerivedCategory.finiteTorAmplitude _ C) := by
  sorry

/-- Each Qbar point object descends to one finite coefficient extension.
Source: point paragraph of def-pod-conventions, sk-thm-sfb-qlbar-two-colimit (2)
(blueprint: def-pod-conventions).
Proof in words. Apply finite coefficient-field descent at Spec k, which is
separated of finite type over k. It supplies an object with bounded constructible
cohomology over one finite subextension and an isomorphism after scalar extension.
The field case of integral_ctf_equals_bc makes the descended object finite Tor,
without changing its underlying object or the given ambient isomorphism. -/
theorem pointFiniteDescent (P : CondensedPoincareDualityConventions.{u})
    (K : P.ctf .qbar P.s) :
    ∃ E : PadicAlgCl.FiniteIntermediateField P.ell,
      ∃ L : (Coefficient.rational E).ctf P.ell P.s,
        Nonempty ((derivedExtendScalarsToPadicAlgCl P.s P.ell E).obj L.obj ≅ K.obj) := by
  sorry

end CondensedPoincareDualityConventions
end WeilConjectures
