/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Completed integral coefficient sheaves

Source: Weil conjectures blueprint, `sec-smooth-purity`, `sk-def-sf-operations`, order 1455
(blueprint: def-weil-completed-integral-coefficients).

The natural-number index `n` stands for the positive exponent `n + 1`. Coefficients are
lifted into a universe containing the small pro-etale site. The completion is a limit
of ring sheaves, not the discrete constant sheaf of the valuation ring.

## Main definitions

- `integralCoefficientSheafSystem`: the inverse sequence of finite constant ring sheaves.
- `completedIntegralCoefficientSheaf`: its limit in sheaves of rings.
- `completedIntegralCoefficientProjection`: the limit projections.
- `completedIntegralModuleSheaves` and `completedIntegralDerivedCategory`: module categories.
- `completedIntegralCohomology`: cohomology objects of cochain complexes.
- `completedIntegralRestrictScalars`: restriction along each limit projection.
-/

@[expose] public section

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

/-- Transport ring sheafification through a small model in the coefficient universe.
This is the existing Mathlib transport, with `essentiallySmallSelf` supplying the size.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable instance integralCoefficientRingSheafify (Y : AlgebraicGeometry.Scheme.{t}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt Y) :=
    essentiallySmallSelf _
  hasSheafifyEssentiallySmallSite _ _

/-- Transport abelian-group sheafification through a small model in the coefficient universe.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable instance integralCoefficientAbSheafify (Y : AlgebraicGeometry.Scheme.{t}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y) AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt Y) :=
    essentiallySmallSelf _
  hasSheafifyEssentiallySmallSite _ _

/-- The locally bijective description is transported from the same small model.
It supplies Mathlib's abelian instance for module sheaves without an added hypothesis.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable instance integralCoefficientAbLocallyBijective
    (Y : AlgebraicGeometry.Scheme.{t}) :
    (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (AlgebraicGeometry.Scheme.ProEt Y) :=
    essentiallySmallSelf _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})

/-- The constant ring sheaf with coefficient ring `A_{E,n+1}`. This is precisely the
constant commutative-ring sheaf, with commutativity forgotten, used by the dependency's
`proEtaleDerivedCategory`; `ULift` only changes size.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable def integralCoefficientSheaf (n : ℕ) :
    Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) RingCat.{max u (t + 1)} :=
  (sheafCompose _
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
    ((constantSheaf _ CommRingCat.{max u (t + 1)}).obj
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))

/-- Sheafification sends the quotient reduction to the reduction of constant ring sheaves.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable def integralCoefficientSheafTransition (n : ℕ) :
    integralCoefficientSheaf l E Y (n + 1) ⟶ integralCoefficientSheaf l E Y n :=
  (sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
    ((constantSheaf _ CommRingCat.{max u (t + 1)}).map
      (CommRingCat.ofHom
        ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
          ((Padic.coefficientExtensionTransition l E (n + 1)).comp
            (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))))

/-- The inverse sequence of constant finite quotient ring sheaves, starting at exponent one.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable def integralCoefficientSheafSystem :
    ℕᵒᵖ ⥤ Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) RingCat.{max u (t + 1)} :=
  Functor.ofOpSequence (integralCoefficientSheafTransition l E Y)

/-- The completed coefficient sheaf without an auxiliary finite-field datum.
This is the same inverse limit used below; the finite-field convention is irrelevant
for its construction. Source: blueprint order 1455; Stacks Tag 03CO
(blueprint: def-weil-completed-integral-coefficients). -/
noncomputable def completedIntegralCoefficientSheafUnrestricted :
    Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) RingCat.{max u (t + 1)} :=
  limit (integralCoefficientSheafSystem l E Y)

variable (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/-- The completed integral coefficient sheaf is the inverse limit in sheaves of rings.
The global datum and `hl` impose the blueprint's coefficient convention `l ≠ p`.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable def completedIntegralCoefficientSheaf (D : FiniteFieldDatum.{d})
    (_hl : l ≠ D.p) :
    Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) RingCat.{max u (t + 1)} :=
  completedIntegralCoefficientSheafUnrestricted l E Y

/-- The limit projection to exponent `n+1`; no surjectivity theorem is assumed here.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable def completedIntegralCoefficientProjection (n : ℕ) :
    completedIntegralCoefficientSheaf l E Y D hl ⟶ integralCoefficientSheaf l E Y n :=
  limit.π (integralCoefficientSheafSystem l E Y) (op n)

/-- Sheaves of modules over the completed ring sheaf, with Mathlib's abelian structure.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable abbrev completedIntegralModuleSheaves :=
  CategoryTheory.ringedSiteModules.{max u (t + 1)}
    (completedIntegralCoefficientSheaf l E Y D hl)

/-- The localization of cochain complexes of completed-coefficient module sheaves at
quasi-isomorphisms, using the standard derived-category localization.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable abbrev completedIntegralDerivedCategory :=
  @DerivedCategory (completedIntegralModuleSheaves l E Y D hl) _ _
    (HasDerivedCategory.standard _)

/-- Cohomology of a cochain complex in completed-coefficient module sheaves, computed
as the abelian-category homology object `ker d / im d` in degree `r`.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable abbrev completedIntegralCohomology
    (K : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ) (r : ℤ) :=
  K.homology r

/-- Restriction of scalars along the limit projection at exponent `n+1`.
Exactness is intentionally a separate theorem.
Source: blueprint order 1455 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable def completedIntegralRestrictScalars (n : ℕ) :
    SheafOfModules.{max u (t + 1)} (integralCoefficientSheaf l E Y n) ⥤
      completedIntegralModuleSheaves l E Y D hl :=
  SheafOfModules.restrictScalars (completedIntegralCoefficientProjection l E Y D hl n)

/-- The completed coefficient ring is commutative on every site object.
Source: Bhatt--Scholze, Section 6.5, setup before Definition 6.5.1
(blueprint: def-weil-completed-integral-coefficients).
Proof: evaluate the inverse limit of ring sheaves on U. Evaluation preserves limits,
and each finite quotient constant ring sheaf is commutative. The limit projections
are jointly injective on sections. The images of a*b and b*a agree under every
projection, by commutativity in the finite quotient sheaves; hence a*b = b*a. -/
theorem completedIntegralCoefficient_mul_commUnrestricted
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (a b : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U) :
    a * b = b * a := by
  let D := integralCoefficientSheafSystem l E Y
  let ev := sheafToPresheaf (AlgebraicGeometry.Scheme.ProEt.topology Y)
      RingCat.{max u (t + 1)} ⋙
    (evaluation (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ RingCat.{max u (t + 1)}).obj U
  apply Concrete.isLimit_ext (D ⋙ ev)
    (isLimitOfPreserves ev (limit.isLimit D)) (a * b) (b * a)
  intro j
  obtain ⟨n⟩ := j
  change ((limit.π D (op n)).hom.app U) (a * b) =
    ((limit.π D (op n)).hom.app U) (b * a)
  rw [map_mul, map_mul]
  exact @mul_comm
    (((constantSheaf (AlgebraicGeometry.Scheme.ProEt.topology Y)
      CommRingCat.{max u (t + 1)}).obj
        (CommRingCat.of (ULift.{t + 1}
          (Padic.coefficientExtensionRing l E (n + 1))))).obj.obj U) _ _ _

/-- The commutative structure on the existing completed ring, with unchanged ring data.
Source: Bhatt--Scholze, Section 6.5 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable abbrev completedIntegralCoefficientCommRingUnrestricted
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ) :
    CommRing ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U) :=
  { RingCat.ring _ with
    mul_comm := completedIntegralCoefficient_mul_commUnrestricted l E Y U }

/-- The completed coefficient presheaf, retaining its commutative structure.
Source: Bhatt--Scholze, Section 6.5 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable def completedIntegralCommRingPresheafUnrestricted :
    (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ ⥤ CommRingCat.{max u (t + 1)} where
  obj U := @CommRingCat.of ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U)
    (completedIntegralCoefficientCommRingUnrestricted l E Y U)
  map {U V} f :=
    letI := completedIntegralCoefficientCommRingUnrestricted l E Y U
    letI := completedIntegralCoefficientCommRingUnrestricted l E Y V
    CommRingCat.ofHom ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map f).hom
  map_id U := (forget₂ CommRingCat RingCat).map_injective
    ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map_id U)
  map_comp f g := (forget₂ CommRingCat RingCat).map_injective
    ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map_comp f g)

/-- The same completed sheaf with commutativity retained. Forgetting commutativity
recovers the recorded completed ring sheaf definitionally.
Source: Bhatt--Scholze, Section 6.5 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable def completedIntegralCommRingSheafUnrestricted :
    Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)} :=
  ⟨completedIntegralCommRingPresheafUnrestricted l E Y,
    Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat RingCat)
      (completedIntegralCoefficientSheafUnrestricted l E Y).property⟩

/-- The completed coefficient ring is commutative on every site object.
Source: Bhatt--Scholze, Section 6.5, setup before Definition 6.5.1
(blueprint: def-weil-completed-integral-coefficients).
Proof: evaluate the inverse limit of ring sheaves on U. Evaluation preserves limits,
and each finite quotient constant ring sheaf is commutative. The limit projections
are jointly injective on sections. The images of a*b and b*a agree under every
projection, by commutativity in the finite quotient sheaves; hence a*b = b*a. -/
theorem completedIntegralCoefficient_mul_comm
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
    (a b : (completedIntegralCoefficientSheaf l E Y D hl).obj.obj U) :
    a * b = b * a := by
  exact completedIntegralCoefficient_mul_commUnrestricted l E Y U a b

/-- The commutative structure on the existing completed ring, with unchanged ring data.
Source: Bhatt--Scholze, Section 6.5 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable abbrev completedIntegralCoefficientCommRing
    (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ) :
    CommRing ((completedIntegralCoefficientSheaf l E Y D hl).obj.obj U) :=
  completedIntegralCoefficientCommRingUnrestricted l E Y U

/-- The completed coefficient presheaf, retaining its commutative structure.
Source: Bhatt--Scholze, Section 6.5 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable def completedIntegralCommRingPresheaf (D : FiniteFieldDatum.{d})
    (hl : l ≠ D.p) :
    (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ ⥤ CommRingCat.{max u (t + 1)} :=
  let _ := hl
  completedIntegralCommRingPresheafUnrestricted l E Y

/-- The same completed sheaf with commutativity retained. Forgetting commutativity
recovers the recorded completed ring sheaf definitionally.
Source: Bhatt--Scholze, Section 6.5 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable def completedIntegralCommRingSheaf (D : FiniteFieldDatum.{d})
    (hl : l ≠ D.p) :
    Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)} :=
  let _ := hl
  completedIntegralCommRingSheafUnrestricted l E Y

/-- The finite quotient coefficient sheaf with commutativity retained.
Source: Bhatt--Scholze, Section 6.5 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable def integralCoefficientCommRingSheaf (n : ℕ) :
    Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)} :=
  (constantSheaf _ CommRingCat.{max u (t + 1)}).obj
    (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))

/-- The completed coefficient projection without the finite-field convention.
It is the coordinate map of the same limit, with commutativity retained.
Source: blueprint order 1455; Stacks Tag 03CO
(blueprint: def-weil-completed-integral-coefficients). -/
noncomputable def completedIntegralCommRingProjectionUnrestricted (n : ℕ) :
    completedIntegralCommRingSheafUnrestricted l E Y ⟶
      integralCoefficientCommRingSheaf l E Y n where
  hom :=
    { app := fun U ↦
        letI := completedIntegralCoefficientCommRingUnrestricted l E Y U
        CommRingCat.ofHom
          ((limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app U).hom
      naturality := fun _U _V f ↦ (forget₂ CommRingCat RingCat).map_injective
        ((limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.naturality f) }

/-- The existing limit projection as a morphism of commutative ring sheaves.
Source: Bhatt--Scholze, Section 6.5 (blueprint: def-weil-completed-integral-coefficients). -/
noncomputable def completedIntegralCommRingProjection (n : ℕ) :
    completedIntegralCommRingSheaf l E Y D hl ⟶ integralCoefficientCommRingSheaf l E Y n :=
  completedIntegralCommRingProjectionUnrestricted l E Y n

end WeilConjectures
