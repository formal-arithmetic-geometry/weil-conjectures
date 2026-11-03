/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.EllPowerCoefficientStages
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement

/-! # Canonical encoding of the finite quotient coefficient rings

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-setup/sec-the-purity-statement/sk-thm-purity-transport/
sk-lem-sp-field-extension/sk-lem-sp-field-extension-towers.md and .proof.md,
clause (1) and proof (1): the finite rings `O_E/ℓ^(n+1)` of the reductions
(blueprint: det-sp-finite-quotient-canonical-encoding).

* `FiniteDiscreteOrdinary.canonicalRingIso`: the sheafification extension of the
  constant-section ring map, normalized by constant sections;
* `FiniteDiscreteOrdinary.canonicalEncoding`: an encoding whose ring isomorphism and
  ordinary functor are the canonical ones (shared by every encoding);
* `CondensedIntegralTower.finiteEncoding`, `finiteDerived`: the encodings of `O_E/ℓ^(n+1)`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The canonical ring isomorphism: the sheafification extension of the constant-section
ring map. Source: (blueprint: det-sp-finite-quotient-canonical-encoding), step 1. -/
@[no_expose] def canonicalRingIso [Finite A] [DiscreteTopology A] (T : Scheme.{u}) :
    realizationRing (Scheme.ProEt.topology T) (ULift.{u + 1} A) ≅ sectionRing A T :=
  haveI := canonicalRingMap_isIso A T
  asIso (canonicalRingMap A T)

/-- The canonical ring isomorphism is normalized by constant sections.
Source: (blueprint: det-sp-finite-quotient-canonical-encoding), step 1.
Proof: it is the extension of the constant-section map along `toSheafify`. -/
theorem canonicalRingIso_normalization [Finite A] [DiscreteTopology A] (T : Scheme.{u})
    (U : T.ProEtᵒᵖ) (a : ULift.{u + 1} A) :
    (canonicalRingIso A T).hom.hom.app U
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app U a) =
    (canonicalAbelianMap A T).hom.app U
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a) :=
  canonicalRingMap_normalization A T U a

/-- The ring isomorphism of every encoding is the canonical one: a map out of the
sheafified constant ring is fixed by its values on constant sections.
Source: (blueprint: det-sp-finite-quotient-canonical-encoding), uniqueness.
Proof: both ring isomorphisms satisfy the same constant-section normalization; the
sheafification universal property (uniqueness of the extension along `toSheafify`) then
identifies their underlying morphisms. -/
theorem encoding_ringIso_eq [Finite A] [DiscreteTopology A] {T : Scheme.{u}}
    (e e' : Encoding A T) : e.ringIso = e'.ringIso := by
  apply Iso.ext
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology T) _ _ (sectionRing A T).property
  ext U a
  exact (e.normalization U a).trans (e'.normalization U a).symm

/-- The canonical finite-discrete encoding. Its ring isomorphism is the canonical
sheafification extension of the constant-section ring map (`canonicalEncoding_ringIso`)
and its ordinary functor is section action followed by scalar restriction along it
(`canonicalEncoding_ordinary_functor`); both are shared by every encoding, so the derived
encoding `Encoding.ordinaryDerived`, which depends only on the ordinary functor, is canonical.
Source: (blueprint: det-sp-finite-quotient-canonical-encoding), steps 1--3;
Stacks 00YV and 03CY. -/
def canonicalEncoding [Finite A] [DiscreteTopology A] (T : Scheme.{u}) : Encoding A T :=
  Classical.choice (encoding_exists A T)

/-- The ring isomorphism of the canonical encoding is the canonical ring isomorphism.
Source: (blueprint: det-sp-finite-quotient-canonical-encoding), step 1.
Proof: both are normalized on constant sections; use uniqueness of the extension along
sheafification. -/
theorem canonicalEncoding_ringIso [Finite A] [DiscreteTopology A] (T : Scheme.{u}) :
    (canonicalEncoding A T).ringIso = canonicalRingIso A T := by
  apply Iso.ext
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology T) _ _ (sectionRing A T).property
  ext U a
  exact ((canonicalEncoding A T).normalization U a).trans
    (canonicalRingIso_normalization A T U a).symm

/-- The ordinary functor of the canonical encoding is the section encoding along the
canonical ring isomorphism.
Source: (blueprint: det-sp-finite-quotient-canonical-encoding), step 2.
Proof: the `ordinary_functor` field and `canonicalEncoding_ringIso`. -/
theorem canonicalEncoding_ordinary_functor [Finite A] [DiscreteTopology A] (T : Scheme.{u}) :
    (canonicalEncoding A T).ordinary.functor = sectionEncoding A T (canonicalRingIso A T) := by
  rw [(canonicalEncoding A T).ordinary_functor, canonicalEncoding_ringIso]

/-- Every encoding has the canonical ordinary functor.
Source: (blueprint: det-sp-finite-quotient-canonical-encoding), uniqueness.
Proof: both functors are `sectionEncoding` along their ring isomorphisms, which agree. -/
theorem encoding_ordinary_functor_eq [Finite A] [DiscreteTopology A] {T : Scheme.{u}}
    (e : Encoding A T) : e.ordinary.functor = (canonicalEncoding A T).ordinary.functor := by
  rw [e.ordinary_functor, (canonicalEncoding A T).ordinary_functor,
    encoding_ringIso_eq A e (canonicalEncoding A T)]

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The finite quotient `O_E/ℓ^(n+1)` of the condensed finite coefficient ring.
Source: (blueprint: det-sp-finite-quotient-canonical-encoding), A_n. -/
abbrev finiteQuotient (n : ℕ) : Type u :=
  Padic.coefficientExtensionIntegers l E ⧸ ellIdeal l E ^ (n + 1)

/-- Its quotient topology from the spectral norm, as in `finiteRingSheaf`.
Source: (blueprint: det-sp-finite-quotient-canonical-encoding), A_n. -/
instance finiteQuotientTopology (n : ℕ) : TopologicalSpace (finiteQuotient l E n) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  inferInstance

/-- The quotient topology is a ring topology.
Source: (blueprint: det-sp-finite-quotient-canonical-encoding), A_n. -/
instance finiteQuotientTopologicalRing (n : ℕ) : IsTopologicalRing (finiteQuotient l E n) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  inferInstance

/-- The quotient is finite (ell-power coefficient stages).
Source: (blueprint: det-sp-finite-quotient-canonical-encoding), A_n. -/
instance finiteQuotientFinite (n : ℕ) : Finite (finiteQuotient l E n) :=
  (ellPowerCoefficientStages l E n).1

/-- The quotient topology is discrete (ell-power coefficient stages).
Source: (blueprint: det-sp-finite-quotient-canonical-encoding), A_n. -/
instance finiteQuotientDiscrete (n : ℕ) : DiscreteTopology (finiteQuotient l E n) :=
  (ellPowerCoefficientStages l E n).2.1

/-- The continuous coefficient sheaf of `finiteQuotient` is the native finite ring.
Source: (blueprint: det-sp-finite-quotient-canonical-encoding), A_n.
Proof: both are the underlying abelian sheaf of the same continuous coefficient ring. -/
theorem coefficient_finiteQuotient (n : ℕ) :
    FiniteDiscreteOrdinary.coefficient (finiteQuotient l E n) = finiteRing l E n := rfl

/-- The canonical encoding of `O_E/ℓ^(n+1)`.
Source: (blueprint: det-sp-finite-quotient-canonical-encoding). -/
def finiteEncoding (n : ℕ) (T : Scheme.{u}) :
    FiniteDiscreteOrdinary.Encoding (finiteQuotient l E n) T :=
  FiniteDiscreteOrdinary.canonicalEncoding (finiteQuotient l E n) T

/-- Its termwise derived equivalence onto the ordinary pro-étale derived category.
Source: (blueprint: det-sp-finite-quotient-canonical-encoding), step 4; Stacks 015F. -/
def finiteDerived (n : ℕ) (T : Scheme.{u}) :
    DerivedCategory (FiniteDiscreteOrdinary.Internal (finiteQuotient l E n) T) ≌
      Scheme.proEtaleDerivedCategory T (finiteQuotient l E n) :=
  (finiteEncoding l E n T).ordinaryDerived

end AlgebraicGeometry.ProEtale.CondensedIntegralTower
