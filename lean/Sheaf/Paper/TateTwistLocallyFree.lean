/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
public import Sheaf.Paper.IntrinsicCoefficientTwists
public import Sheaf.Paper.PurInverseImageTensorHom

import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
import Sheaf.Paper.PadicIntegersInvertEll

/-! # Tate twists are well defined and locally free of rank one

Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.md`, clauses (1)--(3)
(blueprint: det-def-sp-tate-twist-locally-free).

The helpers specialize the recorded constant sheaf, root module, scalar extension,
signed line and tensor functors. All positive root levels are indexed by `n + 1`.
The theorem includes one common cover, normalized generators, canonical Kummer
independence, signed invertible lines and equivalences with the negative twists.

## Main definitions

* `TateSignedLine` states rank one, same-cover triviality and the tensor inverse.
* `TateRationalSignedLine` and `TateQbarSignedLine` express the same clauses in the
  recorded integral-representative categories, with the canonical restriction functors.
* `TateInverseTwists` fixes the actual functor and negative inverse of an equivalence.

## Main statements

* `tateTwist_locallyFree` states all three source clauses for all four coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u v d c h

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.Scheme

/-- The constant commutative coefficient sheaf in clause (2).
Source: blueprint clause (2) (blueprint: det-def-sp-tate-twist-locally-free). -/
abbrev tateFiniteCoefficient (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A)

/-- Apply the canonical quotient coefficient homomorphism to constant sheaves.
Source: blueprint clause (2) (blueprint: det-def-sp-tate-twist-locally-free). -/
def tateFiniteScalar (X : Scheme.{u}) (ℓ : ℕ) (A : Type (u + 1)) [CommRing A]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) :
    purTwistFiniteRing X ℓ n ⟶ tateFiniteCoefficient X A :=
  (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (a.comp ULift.ringEquiv.toRingHom))

/-- The finite A-line is exactly the recorded roots module tensored with A_X.
Source: blueprint clauses (2)--(3) (blueprint: det-def-sp-tate-twist-locally-free). -/
def tateFiniteLine (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type (u + 1)) [CommRing A] (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (tateFiniteScalar X ℓ A n a) (purTwistRootsModule X ℓ n)

/-- The normalized pure tensor used to specify the Kummer-induced morphism.
Source: blueprint clause (2) (blueprint: det-def-sp-tate-twist-locally-free). -/
def tateFiniteTensor (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type (u + 1)) [CommRing A] (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A)
    (V : X.ProEt) (b : (tateFiniteCoefficient X A).obj.obj (op V))
    (x : (proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))).obj.obj (op V)) :
    (tateFiniteLine X ℓ A n a).val.obj (op V) :=
  purScalarSection (purTwistFiniteRing X ℓ n) (tateFiniteCoefficient X A)
    (tateFiniteScalar X ℓ A n a) (purTwistRootsModule X ℓ n) V b x

/-- Signed line clauses on a specified cover: rank one, the same-cover trivializations,
and the positive/negative tensor pairing. All powers and duals are the recorded ones.
Source: blueprint clause (3) (blueprint: det-def-sp-tate-twist-locally-free). -/
def TateSignedLine (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (L : SheafOfModules.{u + 1} (purTwistRing X R))
    {I : Type (u + 1)} (U : I → X.ProEt) : Prop :=
  (∀ m : ℤ, (coefficientTwistLine X (R := R) L m).IsFiniteLocallyFreeOfRank 1 ∧
    ∀ i : I, Nonempty ((coefficientTwistLine X (R := R) L m).over (U i) ≅
      (SheafOfModules.unit (purTwistRing X R)).over (U i))) ∧
  ∀ n : ℕ, Nonempty
    ((SheafOfModules.siteSheafTensorRight (A := R)
      (coefficientTwistLine X L (-(n : ℤ)))).obj (coefficientTwistLine X L n) ≅
        SheafOfModules.unit (purTwistRing X R))

/-- The recorded exact tensor model of K(m), now also for an arbitrary finite A-line.
Source: blueprint clause (3), final paragraph
(blueprint: det-def-sp-tate-twist-locally-free). -/
def tateComplexTwist (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (L : SheafOfModules.{u + 1} (purTwistRing X R))
    (hL : L.IsFiniteLocallyFreeOfRank 1) (m : ℤ) :
    DerivedCategory (SheafOfModules.{u + 1} (purTwistRing X R)) ⥤
      DerivedCategory (SheafOfModules.{u + 1} (purTwistRing X R)) :=
  letI := hL
  letI := (coefficientTwistLine_exact X L m).1
  letI := (coefficientTwistLine_exact X L m).2.1
  letI := (coefficientTwistLine_exact X L m).2.2
  (SheafOfModules.siteSheafTensorRight (A := R) (coefficientTwistLine X L m)).mapDerivedCategory

/-- Fixing the right input of a published tensor bifunctor retains its full arrow action.
Source: blueprint K(m) formula (blueprint: det-def-sp-tate-twist-locally-free). -/
def tateTensorRight {C : Type c} [Category.{h} C] (T : C × C ⥤ C) (L : C) : C ⥤ C :=
  (𝟭 C).prod' ((Functor.const C).obj L) ⋙ T

/-- An equivalence whose actual functor and inverse are the two prescribed twists.
Source: blueprint clause (3), final sentence
(blueprint: det-def-sp-tate-twist-locally-free). -/
def TateInverseTwists {C : Type c} [Category.{h} C] (F G : C ⥤ C) : Prop :=
  ∃ e : C ≌ C, e.functor = F ∧ e.inverse = G

/-- The canonical bounded integral twist uses the recorded intrinsic coefficient line.
Source: blueprint clause (3), integral case
(blueprint: det-def-sp-tate-twist-locally-free). -/
def tateIntegralTwist (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hD : ℓ ≠ D.p) (E : Type u) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E] (X : Scheme.{u})
    [∀ x : X, Invertible (ℓ : X.residueField x)] (m : ℤ) :=
  tateTensorRight (constructibleIntegralTensor ℓ E X)
    (intrinsicIntegralCoefficientTwist D ℓ hD E X m)

/-- The rational twist tensors with the localization of the same integral representative.
Source: blueprint clause (3), rational case
(blueprint: det-def-sp-tate-twist-locally-free). -/
def tateRationalTwist (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hD : ℓ ≠ D.p) (E : Type u) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E] (X : Scheme.{u})
    [∀ x : X, Invertible (ℓ : X.residueField x)] (m : ℤ) :=
  tateTensorRight (rationalDerivedTensor ℓ E X)
    ((sfRationalConstructibleLocalization ℓ E X).obj
      (intrinsicIntegralCoefficientTwist D ℓ hD E X m))

/-- Transport invertibility along the actual residue-field homomorphism.
Source: the cover in blueprint clause (3)
(blueprint: det-def-sp-tate-twist-locally-free). -/
@[instance_reducible] def tatePullbackInvertible (ℓ : ℕ) {Y X : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (ℓ : X.residueField x)] :
    ∀ y : Y, Invertible (ℓ : Y.residueField y) :=
  fun y ↦ (map_natCast (f.residueFieldMap y).hom ℓ) ▸
    Invertible.map (f.residueFieldMap y).hom (ℓ : X.residueField (f y))

/-- The rational signed lines, interpreted in the recorded rational category:
every signed degree-zero line restricts to the coefficient unit on this cover,
and the positive/negative tensor product is the coefficient unit globally.
The integral representative of the coefficient unit is the published zero twist.
Source: blueprint clause (3), rational interpretation via def-coefficient-twists-detailed
(blueprint: det-def-sp-tate-twist-locally-free). -/
def TateRationalSignedLine (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hD : ℓ ≠ D.p) (E : Type u) [Field E] [Algebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E] (X : Scheme.{u})
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    {I : Type (u + 1)} (U : I → X.ProEt) : Prop :=
  (∀ (m : ℤ) (i : I),
    letI := tatePullbackInvertible ℓ (U i).hom
    Nonempty ((rationalDerivedPullback ℓ E (U i).hom).obj
      ((sfRationalConstructibleLocalization ℓ E X).obj
        (intrinsicIntegralCoefficientTwist D ℓ hD E X m)) ≅
      (sfRationalConstructibleLocalization ℓ E (U i).left).obj
        (intrinsicIntegralCoefficientTwist D ℓ hD E (U i).left 0))) ∧
  ∀ n : ℕ, Nonempty ((rationalDerivedTensor ℓ E X).obj
    ((sfRationalConstructibleLocalization ℓ E X).obj
      (intrinsicIntegralCoefficientTwist D ℓ hD E X n),
      (sfRationalConstructibleLocalization ℓ E X).obj
        (intrinsicIntegralCoefficientTwist D ℓ hD E X (-(n : ℤ)))) ≅
    (sfRationalConstructibleLocalization ℓ E X).obj
      (intrinsicIntegralCoefficientTwist D ℓ hD E X 0))

/-- The same signed local-line and tensor-inverse clauses in the recorded literal
common-stage category. Both restriction and tensor are the canonical published functors;
the coefficient unit is the least-stage zero twist, not an arbitrarily chosen object.
Source: blueprint clause (3), Qbar interpretation via def-coefficient-twists-detailed
(blueprint: det-def-sp-tate-twist-locally-free). -/
def TateQbarSignedLine (D : FiniteFieldDatum.{d}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hD : ℓ ≠ D.p) (X : Scheme.{u})
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    (Ω : Type v) [Field Ω] [Algebra (Padic ℓ) Ω] [IsAlgClosure (Padic ℓ) Ω]
    {I : Type (u + 1)} (U : I → X.ProEt) : Prop :=
  (∀ (m : ℤ) (i : I),
    letI := tatePullbackInvertible ℓ (U i).hom
    Nonempty ((commonStageDerivedPullback ℓ Ω (U i).hom).obj
      (intrinsicQbarCoefficientTwist D ℓ hD X Ω m) ≅
      intrinsicQbarCoefficientTwist D ℓ hD (U i).left Ω 0)) ∧
  ∀ n : ℕ, Nonempty ((commonStageDerivedTensor ℓ Ω X).obj
    (intrinsicQbarCoefficientTwist D ℓ hD X Ω n,
      intrinsicQbarCoefficientTwist D ℓ hD X Ω (-(n : ℤ))) ≅
    intrinsicQbarCoefficientTwist D ℓ hD X Ω 0)

/-- One common covering trivializes the compatible root generators and all coefficient
lines; Kummer transitions induce the canonical A-linear isomorphisms; every signed twist
is a line, with positive and negative twist functors inverse on the specified categories.

Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.md`, all three clauses
(blueprint: det-def-sp-tate-twist-locally-free).

Proof:
1. By lem-pur-twist-sheaf-locally-free (2), trivialize the inverse-limit Z_ell line
   on one pro-etale cover. Project the image of 1 to every positive root level.
   The tower projections commute, so the resulting ζ satisfy the power-transition
   equation. The quotient isomorphisms identify the coefficient unit with ζ; their
   module maps are exactly a ↦ a • ζ after every slice restriction.
2. Annihilation supplies the unique unital quotient map Z/ell^(r+1) → A.
   For n ≥ r, compose it with coefficient reduction. On the root-generator cover,
   the Kummer map carries ζ_n to ζ_r; hence the induced map on scalar tensors
   b tensor x is b tensor Kummer(x), the identity under the two A-trivializations.
   It is an isomorphism locally, and therefore globally. The pure-tensor formula
   pins down its canonical map, independently of the annihilating level.
3. The finite A-line is trivial on that cover. Refine it by the integral line's
   trivializing cover from lem-pur-twist-sheaf-locally-free (3). The compatible
   sections and their quotient isomorphisms pull back to this common refinement.
   The integral-limit comparison det-prop-sfb-qlbar-colimit-x-integral-limit
   identifies the completed coefficient sheaf with its finite inverse limit.
   The localization comparison det-prop-sfb-qlbar-colimit-x-invert-ell identifies
   its localization with E_X and gives flatness. Thus integral trivializations
   base-change to rational trivializations. The common-stage coefficient
   construction of def-coefficient-twists-detailed gives the same trivialization
   over Qbar at any common finite coefficient stage.
4. On this same cover every signed tensor power and internal dual of the line is
   the coefficient unit. Rank one descends. Evaluation identifies the tensor of
   the d-th power and its dual with the unit (also for d = 0).
5. Lines are flat, so the exact ordinary tensor model computes derived tensor
   even on unbounded A-complexes. The two evaluation identifications give both
   inverse composites for d and -d. Restrict to the bounded complete integral
   category, localize Hom scalars to E, and pass to the common-stage Hom colimit
   for Qbar. These use the recorded tensor functors and retain the same inverse
   identifications. Their triangle identities hold locally for the free unit,
   hence globally, and give the displayed equivalences with specified inverses.
-/
theorem tateTwist_locallyFree
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (Ω : Type v) [Field Ω] [Algebra (Padic ℓ) Ω] [IsAlgClosure (Padic ℓ) Ω]
    (ι : E →ₐ[Padic ℓ] Ω) :
    ∃ (I : Type (u + 1)) (U : I → X.ProEt)
      (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 X))
      (ζ : ∀ (n : ℕ) (i : I), (purTwistRootsModule X ℓ n).val.obj (op (U i)))
      (e : ∀ (n : ℕ) (i : I),
        (SheafOfModules.unit (purTwistRing X (purTwistFiniteRing X ℓ n))).over (U i) ≅
          (purTwistRootsModule X ℓ n).over (U i)),
      Presieve.ofArrows U f ∈ (ProEt.precoverage X).coverings _ ∧
      (∀ (n : ℕ) (i : I),
        (proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).hom.app (op (U i))
            (ζ (n + 1) i) = ζ n i) ∧
      (∀ (n : ℕ) (i : I) (V : (Over (U i))ᵒᵖ)
        (a : ((purTwistRing X (purTwistFiniteRing X ℓ n)).over (U i)).obj.obj V),
        (e n i).hom.val.app V a =
          a • (purTwistRootsModule X ℓ n).val.map V.unop.hom.op (ζ n i)) ∧
      (∀ (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ),
        (∀ a : A, (ℓ ^ (r + 1)) • a = 0) →
        ∃ a : ZMod (ℓ ^ (r + 1)) →+* A,
          (∀ (n : ℕ) (hrn : r ≤ n),
            ∃ k : tateFiniteLine X ℓ A n
                (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
                  (ZMod (ℓ ^ (r + 1))))) ⟶ tateFiniteLine X ℓ A r a,
              IsIso k ∧
              ∀ (V : X.ProEt) (b : (tateFiniteCoefficient X A).obj.obj (op V))
                (x : (proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))).obj.obj (op V)),
                k.val.app (op V)
                  (tateFiniteTensor X ℓ A n
                    (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
                      (ZMod (ℓ ^ (r + 1))))) V b x) =
                  tateFiniteTensor X ℓ A r a V b
                    ((proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
                      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
                      (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))).hom.app (op V) x)) ∧
          (∃ hL : (tateFiniteLine X ℓ A r a).IsFiniteLocallyFreeOfRank 1,
            TateSignedLine X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) U ∧
            ∀ n : ℕ, TateInverseTwists
              (tateComplexTwist X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) hL n)
              (tateComplexTwist X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) hL
                (-(n : ℤ))))) ∧
      TateSignedLine X (completedIntegralCommRingSheafUnrestricted ℓ E X)
        (purTwistIntegralModule X ℓ E) U ∧
      ∀ (D : FiniteFieldDatum.{d}) (hD : ℓ ≠ D.p),
        TateRationalSignedLine D ℓ hD E X U ∧
        TateQbarSignedLine D ℓ hD X Ω U ∧
        ∀ n : ℕ, TateInverseTwists (tateIntegralTwist D ℓ hD E X n)
          (tateIntegralTwist D ℓ hD E X (-(n : ℤ))) ∧
        TateInverseTwists (tateRationalTwist D ℓ hD E X n)
          (tateRationalTwist D ℓ hD E X (-(n : ℤ))) ∧
        TateInverseTwists (intrinsicQbarComplexTwistFunctor D ℓ hD X Ω n)
          (intrinsicQbarComplexTwistFunctor D ℓ hD X Ω (-(n : ℤ))) := by
  sorry

end AlgebraicGeometry.Scheme
