module

public import Sheaf.AlgebraicGeometry.RelativeAssassin
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.AlgebraicGeometry.Fiber
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import Sheaf.TraceFormula.ValuationClosedFibreNoetherian
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleStalkFinite
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-! # Valuation specialization stalk model

Source: Stacks Project, More on Morphisms, Tag 0GSI, third proof paragraph
(blueprint: lem-trf-valuation-specialization-stalk-model).

The auxiliary abbreviations expose the actual quotient and localization constructions.
The generic module is `(B ⊗[A] K) ⊗[B] N`, canonically `N ⊗[A] K` by tensor cancellation
and symmetry. All comparisons are normalized on original germs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.ValuationSpecialization

/-- The canonical scalar map from an affine base to a stalk of its scheme.
Source: Stacks 0GSI, third paragraph (blueprint: lem-trf-valuation-specialization-stalk-model). -/
abbrev baseMap {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (x : X) : A →+* X.presheaf.stalk x :=
  (f.stalkMap x).hom.comp (StructureSheaf.toStalk A (f x)).hom

/-- The actual module stalk, with its structure-sheaf scalar action.
Source: Stacks 01HV (blueprint: lem-trf-valuation-specialization-stalk-model). -/
abbrev stalk {X : Scheme.{u}} (F : X.Modules) (x : X) :=
  (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F

/-- The ideal `m_A B` in the stalk.
Source: Stacks 0GSI (blueprint: lem-trf-valuation-specialization-stalk-model). -/
abbrev closedIdeal {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (x : X) :=
  (IsLocalRing.maximalIdeal A).map (baseMap f x)

/-- The closed-fibre quotient ring `R`.
Source: Stacks 0GSI (blueprint: lem-trf-valuation-specialization-stalk-model). -/
abbrev closedRing {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (x : X) := X.presheaf.stalk x ⧸ closedIdeal f x

/-- The quotient `L = N / m_A N`, with the quotient-ring action transported through
Mathlib's quotient-tensor equivalence. No module data is chosen from an existence theorem.
Source: Stacks 00DF and 0GSI (blueprint: lem-trf-valuation-specialization-stalk-model). -/
def closedModule {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (F : X.Modules) (x : X) : ModuleCat (closedRing f x) :=
  let e := TensorProduct.quotTensorEquivQuotSMul (stalk F x) (closedIdeal f x)
  letI := e.symm.toAddEquiv.module (closedRing f x)
  ModuleCat.of (closedRing f x)
    (stalk F x ⧸ (closedIdeal f x • (⊤ : Submodule (X.presheaf.stalk x) (stalk F x))))

/-- The generic scalar extension `B_K = B ⊗[A] Frac(A)`.
Source: Stacks 0GSI (blueprint: lem-trf-valuation-specialization-stalk-model). -/
abbrev genericRing {A : Type u} [CommRing A] [IsDomain A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (x : X) :=
  letI := (baseMap f x).toAlgebra
  X.presheaf.stalk x ⊗[A] FractionRing A

/-- The inclusion `B → B_K` sends `b` to `b ⊗ 1`.
Source: Stacks 0GSI (blueprint: lem-trf-valuation-specialization-stalk-model). -/
abbrev genericInclusion {A : Type u} [CommRing A] [IsDomain A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (x : X) : X.presheaf.stalk x →+* genericRing f x :=
  letI := (baseMap f x).toAlgebra
  Algebra.TensorProduct.includeLeftRingHom

/-- The generic module, in the canonically equivalent scalar-extension encoding
`B_K ⊗[B] N = N ⊗[A] K`.
Source: Stacks 00DK, 0GSI (blueprint: lem-trf-valuation-specialization-stalk-model). -/
abbrev genericModule {A : Type u} [CommRing A] [IsDomain A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (F : X.Modules) (x : X) : ModuleCat (genericRing f x) :=
  (ModuleCat.extendScalars (genericInclusion f x)).obj (stalk F x)

/-- The actual localized module at a prime of `B_K`.
Source: Stacks 00E3, 0GSI (blueprint: lem-trf-valuation-specialization-stalk-model). -/
abbrev genericLocalizedModule {A : Type u} [CommRing A] [IsDomain A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (F : X.Modules) (x : X)
    (qK : PrimeSpectrum (genericRing f x)) : ModuleCat (Localization.AtPrime qK.asIdeal) :=
  letI := LocalizedModule.moduleOfIsLocalization (S := qK.asIdeal.primeCompl)
    (M := genericModule f F x) (T := Localization.AtPrime qK.asIdeal)
  ModuleCat.of _ (LocalizedModule qK.asIdeal.primeCompl (genericModule f F x))

/-- Germ of the pullback of a section on the point's own fibre, using the canonical
sectionwise tensor-pullback unit.
Source: Stacks 0096, 0098 (blueprint: lem-trf-valuation-specialization-stalk-model). -/
abbrev fibreGerm {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (F : X.Modules) (x : X)
    (U : X.Opens) (hx : x ∈ U) (m : F.val.obj (op U)) :
    stalk ((Scheme.Modules.tensorPullback (f.fiberι (f x))).obj F) (f.asFiber x) :=
  TopCat.Presheaf.germ
    ((Scheme.Modules.tensorPullback (f.fiberι (f x))).obj F).val.presheaf
    ((f.fiberι (f x)) ⁻¹ᵁ U) (f.asFiber x)
    (Eq.mpr (congrArg (fun z : X ↦ z ∈ U) (f.fiberι_asFiber x)) hx)
    (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
      (f.fiberι (f x)))).unit.app F).val.app (op U) m)

/-- Source: Stacks Project, Tag 0GSI, third proof paragraph
(blueprint: lem-trf-valuation-specialization-stalk-model).

Proof:
1. Choose a finite-type affine chart about `x`. Its local ring is a prime localization,
so `A → B` is essentially finite type and local; finite type of `F` makes `N` finite
(affine-open-stalk-localization, finite-type-module-stalk-finite).
2. The local-spectrum embedding identifies the generalization `y` with a unique prime `q`.
Its contraction is zero since `f(y)` is generic (spec-local-ring-canonical-morphism).
3. Fibre-stalk-quotient and module-stalk-pullback identify the closed-fibre stalks with
`R` and `L`; tensor-over-quotient gives the quotient-module comparison on germs.
4. Valuation-closed-fibre-noetherian makes `R` Noetherian; images of generators make `L` finite.
5. On the affine chart the closure is `Spec(C/q0)`, so `x` is minimal over `q0 + m_A C`.
Minimal-prime-localization-radical gives the required radical equality in `B`.
6. Affine-module-germ-localization identifies the localizations `B_q`, `N_q` with the
stalks at `y`; the double-localization maps send `(b/u)/(c/v)` to `vb/(uc)` and likewise
for module fractions, with inverse `b/c ↦ (b/1)/(c/1)`.
7. Localization-tensor-over-base identifies generic base change with localization away
from zero in `A`. Since `q` contracts to zero its extension is prime. Localizing there
recovers `B_q`, `N_q`. The base generic stalk has zero maximal ideal, so the fibre-stalk
quotient and pullback formulas identify these with the generic-fibre stalks, on germs.
8. The relative-assassin definition and annihilator-associated-primes definition give
the two association equivalences: compatible ring and module isomorphisms preserve
maximal ideals and element annihilators. -/
theorem valuation_specialization_stalk_model
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (F : X.Modules) (hF : F.IsQuasiCoherentFiniteType) (y x : X)
    (hy : (f y).asIdeal = ⊥) (hx : f x = IsLocalRing.closedPoint A)
    (hcomponent : ∃ (C : Set (((Scheme.IdealSheafData.vanishingIdeal
        ⟨closure {y}, isClosed_closure⟩).subschemeι ≫ f).fiber (IsLocalRing.closedPoint A)))
      (z : ((Scheme.IdealSheafData.vanishingIdeal
        ⟨closure {y}, isClosed_closure⟩).subschemeι ≫ f).fiber (IsLocalRing.closedPoint A)),
      C ∈ irreducibleComponents (((Scheme.IdealSheafData.vanishingIdeal
        ⟨closure {y}, isClosed_closure⟩).subschemeι ≫ f).fiber (IsLocalRing.closedPoint A)) ∧
      IsGenericPoint z C ∧
      (Scheme.IdealSheafData.vanishingIdeal ⟨closure {y}, isClosed_closure⟩).subschemeι
        (((Scheme.IdealSheafData.vanishingIdeal
          ⟨closure {y}, isClosed_closure⟩).subschemeι ≫ f).fiberι
            (IsLocalRing.closedPoint A) z) = x) :
    IsLocalHom (baseMap f x) ∧ (baseMap f x).EssFiniteType ∧
    Module.Finite (X.presheaf.stalk x) (stalk F x) ∧
    ∃ q : PrimeSpectrum (X.presheaf.stalk x),
      (X.fromSpecStalk x) q = y ∧ q.asIdeal.comap (baseMap f x) = ⊥ ∧
      (q.asIdeal ⊔ closedIdeal f x).radical = IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
      IsNoetherianRing (closedRing f x) ∧ Module.Finite (closedRing f x) (closedModule f F x) ∧
      ∃ (eR : closedRing f x ≃+* (f.fiber (f x)).presheaf.stalk (f.asFiber x))
        (eL : closedModule f F x ≃+
          stalk ((Scheme.Modules.tensorPullback (f.fiberι (f x))).obj F) (f.asFiber x)),
        (∀ b, eR (Ideal.Quotient.mk (closedIdeal f x) b) =
          ((X.presheaf.stalkCongr (.of_eq (f.fiberι_asFiber x))).inv ≫
            (f.fiberι (f x)).stalkMap (f.asFiber x)).hom b) ∧
        (∀ r m, eL (r • m) = eR r • eL m) ∧
        (∀ (U : X.Opens) (hxU : x ∈ U) (m : F.val.obj (op U)),
          eL (Submodule.Quotient.mk (TopCat.Presheaf.germ F.val.presheaf U x hxU m)) =
            fibreGerm f F x U hxU m) ∧
        (x ∈ Scheme.Modules.relativeAssassin f F ↔
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map
            (Ideal.Quotient.mk (closedIdeal f x)) ∈
            RingTheory.annihilatorAssociatedPrimes (closedRing f x) (closedModule f F x)) ∧
        ∃ qK : PrimeSpectrum (genericRing f x),
          qK.asIdeal = q.asIdeal.map (genericInclusion f x) ∧
          ∃ (eT : Localization.AtPrime qK.asIdeal ≃+*
              (f.fiber (f y)).presheaf.stalk (f.asFiber y))
            (eP : genericLocalizedModule f F x qK ≃+
              stalk ((Scheme.Modules.tensorPullback (f.fiberι (f y))).obj F) (f.asFiber y)),
            (∀ r m, eP (r • m) = eT r • eP m) ∧
            (∀ (U : X.Opens) (hxU : x ∈ U) (hyU : y ∈ U) (b : Γ(X, U)),
              eT (algebraMap (genericRing f x) (Localization.AtPrime qK.asIdeal)
                (genericInclusion f x (X.presheaf.germ U x hxU b))) =
                  ((X.presheaf.stalkCongr (.of_eq (f.fiberι_asFiber y))).inv ≫
                    (f.fiberι (f y)).stalkMap (f.asFiber y)).hom
                    (X.presheaf.germ U y hyU b)) ∧
            (∀ (U : X.Opens) (hxU : x ∈ U) (hyU : y ∈ U) (m : F.val.obj (op U)),
              eP (LocalizedModule.mk
                ((1 : genericRing f x) ⊗ₜ[X.presheaf.stalk x, genericInclusion f x]
                  (TopCat.Presheaf.germ F.val.presheaf U x hxU m)) 1) =
                fibreGerm f F y U hyU m) ∧
            (y ∈ Scheme.Modules.relativeAssassin f F ↔
              IsLocalRing.maximalIdeal (Localization.AtPrime qK.asIdeal) ∈
                RingTheory.annihilatorAssociatedPrimes (Localization.AtPrime qK.asIdeal)
                  (genericLocalizedModule f F x qK)) := by
  sorry

end AlgebraicGeometry.ValuationSpecialization
