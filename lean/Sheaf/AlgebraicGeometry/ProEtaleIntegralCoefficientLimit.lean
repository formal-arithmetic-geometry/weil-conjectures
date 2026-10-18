/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.AlgebraicGeometry.ProEtalePointPullback
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.NumberTheory.Padics.IntegersProfiniteTower
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Sheaf.Paper.ProfiniteTestObjectFunctor
import Sheaf.AlgebraicGeometry.Sites.ProetaleSiteProperties
import Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects
import Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Sheaf.Topology.ProfiniteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!
# Integral pulled-back coefficients as the limit of finite constant coefficients

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-prop-sfb-qlbar-colimit-x-integral-limit`, clauses 1--3
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit).

Finite representability is natural in the finite label set. The integral comparison is
normalized by its adjunction mate on every profinite test object and every continuous
function into the integer ring. Thus its finite projections specify the canonical map.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures

namespace AlgebraicGeometry.ProEtale

/-- The constant set sheaves with finite labels, regarded as presheaves.
Source: blueprint main-20261015, integral-limit clause 1
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit). -/
noncomputable def sfbFiniteConstantSets (X : Scheme.{u}) :
    FintypeCat.{u} ⥤ X.ProEtᵒᵖ ⥤ Type (u + 1) :=
  forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1} ⋙
    constantSheaf (Scheme.ProEt.topology X) (Type (u + 1)) ⋙
      sheafToPresheaf _ _

/-- The presheaves represented by the relative finite test schemes, namely the coproducts
of copies of X by `profinite_test_object_functor`.
Source: blueprint main-20261015, integral-limit clause 1
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit). -/
noncomputable def sfbFiniteRepresentables (X : Scheme.{u}) :
    FintypeCat.{u} ⥤ X.ProEtᵒᵖ ⥤ Type (u + 1) :=
  FintypeCat.toProfinite ⋙ profiniteToProEtOf X ⋙ uliftYoneda.{u + 1}

/-- The finite quotient at exponent n+1, bundled using its recorded finiteness theorem.
Source: blueprint main-20261015, integral-limit clause 1
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit). -/
noncomputable def sfbIntegralFiniteLevel (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ) : FintypeCat.{u} :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.le_add_left 1 n)
  FintypeCat.of (Padic.coefficientExtensionRing l E (n + 1))

/-- The finite quotient tower with exactly the specified reduction maps.
Source: blueprint main-20261015, integral-limit clause 1
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit). -/
noncomputable def sfbIntegralFiniteTower (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : ℕᵒᵖ ⥤ FintypeCat.{u} :=
  Functor.ofOpSequence (fun n ↦
    FintypeCat.homMk (X := sfbIntegralFiniteLevel l E (n + 1))
      (Y := sfbIntegralFiniteLevel l E n) (Padic.coefficientExtensionTransition l E (n + 1)))

/-- The integers with their extending absolute-value topology, bundled as a profinite set.
Source: blueprint main-20261015, integral-limit clause 1; integers-profinite-tower
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit). -/
noncomputable def sfbIntegralProfinite (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : Profinite.{u} :=
  letI := Padic.coefficientExtensionIntegersTopology l E
  letI := (Padic.coefficientExtension_integers_profinite_tower.{u, u} l E).2.1
  letI := (Padic.coefficientExtension_integers_profinite_tower.{u, u} l E).2.2.1
  letI := (Padic.coefficientExtension_integers_profinite_tower.{u, u} l E).2.2.2.1
  Profinite.of (Padic.coefficientExtensionIntegers l E)

/-- The condensed integer ring, using its actual continuous-function sections.
Source: blueprint main-20261015, integral-limit clauses 2--3
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit). -/
noncomputable def sfbCondensedIntegers (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  letI := spectralNorm.normedField (Padic l) E
  letI : MonObj (Profinite.continuousMapRingObjOfUniverse.{u, u}
      (Padic.coefficientExtensionIntegers l E)) :=
    Sheaf.monObj_sheafCompose_obj (coherentTopology Profinite.{u})
      (Profinite.continuousMapRingSheafOfUniverse (Padic.coefficientExtensionIntegers l E))
  Mon.mk (Profinite.continuousMapRingObjOfUniverse (Padic.coefficientExtensionIntegers l E))

/-- The existing completed ring sheaf, as an abelian sheaf with its ring-object structure.
Source: blueprint main-20261015, integral-limit clause 3
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit). -/
noncomputable abbrev sfbCompletedIntegersAb (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (completedIntegralCoefficientSheafUnrestricted l E X)

/-- The canonical adjunction whose unit specifies sections pulled back from the point.
Source: blueprint main-20261015, integral-limit proof Step 3
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit). -/
noncomputable def sfbIntegralPointAdjunction (X : Scheme.{u}) :
    sfbPullbackFromPoint X ⊣ sfbPullbackFromPointRightAdjoint X :=
  pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))

/-- The finite-level set representation, including the canonical comparison between
constant ring sheaves and constant set sheaves.
Source: blueprint main-20261015, integral-limit proof Steps 1 and 4
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit). -/
noncomputable def sfbIntegralFiniteRepresentation (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X) (n : ℕ) :
    (integralCoefficientSheaf l E X n).obj ⋙ forget RingCat.{u + 1} ≅
      uliftYoneda.{u + 1}.obj
        ((profiniteToProEtOf X).obj (FintypeCat.toProfinite.obj (sfbIntegralFiniteLevel l E n))) :=
  (sheafToPresheaf _ _).mapIso
    ((constantCommuteCompose (Scheme.ProEt.topology X) (forget CommRingCat.{u + 1})).app
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ≪≫
    a.app (sfbIntegralFiniteLevel l E n)

/-- Finite constants and integral pulled-back coefficients have the stated representations;
the ring comparison is the unique one with the prescribed reduction projections.

Source: blueprint main-20261015, `sk-prop-sfb-qlbar-colimit-x-integral-limit`, clauses 1--3
(blueprint: det-prop-sfb-qlbar-colimit-x-integral-limit).

Proof: (1) A map into the finite coproduct of copies of X is a clopen labelled partition.
The summands cover it in the pro-etale topology. Glue constant sections on these pieces;
uniqueness on overlaps proves the sheafification universal property, naturally in labels.
For the empty label set use the empty covering of the empty object.
(2) The integers-profinite-tower theorem identifies the integer ring with its positive
finite quotients and makes those quotients cofinal among its finite quotients. Apply the
relative profinite test functor to this limit cone. Yoneda and sectionwise sheaf limits
identify its represented presheaf with the limit of finite constants.
(3) The left-exact site inverse image sends the sheaf represented by a profinite set S
to the sheaf represented by X[S]: use its adjunction, restriction on test objects, and
Yoneda, naturally in S. The adjunction lifts to abelian and ring objects, identifying
this underlying-set inverse image with the prescribed monoidal coefficient pullback.
This gives the representation in clause 2 and the displayed normalization by the unit.
(4) Addition, multiplication, negation, zero and one are computed on finite clopen labels.
The reductions preserve them. Their compatible coordinatewise values give the ring
structure on the limit; the limit projections jointly distinguish sections. The
represented comparison is therefore a ring isomorphism. Its adjunction mate on each
continuous function is exactly its reduction followed by finite-label representation.
This determines every projection, hence determines the comparison uniquely.
-/
theorem sfb_integral_coefficient_limit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    ∃ a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X,
      ∃ (c : Cone (sfbIntegralFiniteTower l E ⋙ FintypeCat.toProfinite))
        (j : sfbIntegralProfinite l E ≅ c.pt),
        (∀ (n : ℕ) (x : Padic.coefficientExtensionIntegers l E),
          (j.hom ≫ c.π.app (op n)) x =
            Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x) ∧
        Nonempty (IsLimit c) ∧
        Nonempty (IsLimit ((profiniteToProEtOf X ⋙ Scheme.ProEt.forget X ⋙
          Over.forget X).mapCone c)) ∧
        Nonempty (((sfbPullbackFromPoint X).obj (sfbCondensedIntegers l E).X).obj ⋙
          forget Ab.{u + 1} ≅
            uliftYoneda.{u + 1}.obj ((profiniteToProEtOf X).obj (sfbIntegralProfinite l E))) ∧
        Nonempty ((completedIntegralCoefficientSheafUnrestricted l E X).obj ⋙
          forget RingCat.{u + 1} ≅
            uliftYoneda.{u + 1}.obj ((profiniteToProEtOf X).obj (sfbIntegralProfinite l E))) ∧
        ∃! e : (coefficientRing X (sfbCondensedIntegers l E)).X ≅
            sfbCompletedIntegersAb l E X,
          IsMonHom e.hom ∧ IsMonHom e.inv ∧
          ∀ (S : Profinite.{u}) (f : S ⟶ sfbIntegralProfinite l E) (n : ℕ),
            (sfbIntegralFiniteRepresentation l E X a n).hom.app
                (op ((profiniteToProEtOf X).obj S))
              (((limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app
                  (op ((profiniteToProEtOf X).obj S)))
                ((e.hom.hom.app (op ((profiniteToProEtOf X).obj S)))
                  (((sfbIntegralPointAdjunction X).unit.app (sfbCondensedIntegers l E).X).hom.app
                    (op S) (ULift.up f.hom.hom)))) =
              ULift.up ((profiniteToProEtOf X).map (f ≫ j.hom ≫ c.π.app (op n))) := by
  sorry

end AlgebraicGeometry.ProEtale
