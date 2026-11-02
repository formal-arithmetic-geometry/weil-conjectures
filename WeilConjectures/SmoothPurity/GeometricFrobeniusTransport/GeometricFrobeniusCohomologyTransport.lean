/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Cohomology transport for the finite-field geometric Frobenius

Source: latest blueprint, def-weil-global-geometric-frobenius, the first arrow of each
of its two displayed composites (blueprint: lem-weil-condensed-isomorphism-cohomology-transport).

The point functor here is exactly the one in def-weil-ordinary-compact-cohomology.
The canonical mates L, R, C and ordinary are imported, not redeclared or owned here.
The theorem is restricted to the geometric fibre, geometric Frobenius, and E/Omega.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport
open scoped CategoryTheory.Obj

namespace WeilConjectures.GeometricFrobeniusTransport

local instance (D : FiniteFieldDatum.{u}) : IsAlgClosed D.k :=
  IsAlgClosure.isAlgClosed D.k₀

local instance (D : FiniteFieldDatum.{u}) (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :
    QuasiCompact (D.geometricFiber Y₀).hom := by
  change QuasiCompact (pullback.snd Y₀.hom _)
  infer_instance

/-- The recorded point functor, with coefficients in the ring Γ Λ, not a different
terminal-section scalar model. Source: def-weil-ordinary-compact-cohomology, Fib_s
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport). -/
abbrev pointSections (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (s : Scheme.{u}) :=
  (condensedRingCoefficientSections Λ s).rightDerivedFunctor

/-- Restriction along b at the final object, followed by the corresponding-object and
coefficient identifications. The canonical point pullback comparison is derived first,
then whiskered with the recorded sections functor. Thus both sides use Γ Λ scalars.
Source: latest blueprint, the specified insertion before the two exchanges
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport). -/
def pointInsertion (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {k : Type u} [Field k] [IsAlgClosed k]
    (b : Spec (.of k) ⟶ Spec (.of k)) :
    pointSections Λ (Spec (.of k)) ≅ L Λ b ⋙ pointSections Λ (Spec (.of k)) :=
  (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ b ≪≫
      Functor.mapDerivedCategoryNatIso (upperStarIsoIdOfIsSepClosed Λ b) ≪≫
      Functor.mapDerivedCategoryIdIso _).symm) _

/-- The geometric base automorphism is Spec of inverse arithmetic Frobenius.
Source: latest blueprint, gamma and the semilinear structure map square
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport). -/
def baseAutomorphism (D : FiniteFieldDatum.{u}) : Spec (.of D.k) ≅ Spec (.of D.k) :=
  let _ : Fintype D.k₀ := Fintype.ofFinite D.k₀
  Scheme.Spec.mapIso
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).toRingEquiv.toCommRingCatIso.op

/-- Normalized compact-support data. Proper-refinement units determine comparisons;
the open-adjunction mate determines exchanges. This extracts those fixed maps from the
published existence theorem, without exporting its arbitrary-square Laws as a conclusion.
Source: latest blueprint, the proper/open construction of the first compact arrow
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport). -/
def compactData (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (c : WeilCoefficient ell) :
    CompactData (WeilCoefficient.ab c) (Spec (.of D.k)) := by
  let _ : Fact D.p.Prime := ⟨D.prime⟩
  let _ : Fintype D.k₀ := Fintype.ofFinite D.k₀
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (f := D.a)
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  have hChar : ringChar D.k ≠ ell := by
    rw [← Algebra.ringChar_eq D.k₀ D.k, ringChar.eq D.k₀ D.p]
    exact hEll.symm
  cases c with
  | finite E => exact (condensedCohomologyTransport D.k ell hChar E false).2.2.choose
  | qbar =>
      let E : PadicAlgCl.FiniteIntermediateField ell := ⟨⊥, inferInstance⟩
      exact (condensedCohomologyTransport D.k ell hChar E true).2.2.choose

/-- The first ordinary arrow on the cohomology node's actual coefficient complex:
point insertion, then the unit/compositor/counit exchange for g;a = a;b.
Source: latest blueprint, first displayed composite, first arrow
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport). -/
def ordinaryTransport (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (c : WeilCoefficient ell)
    (M : CohomologyTransport.D (WeilCoefficient.ab c) (D.geometricFiber Y₀).left) :
    (condensedRingOrdinaryCoefficientComplex (WeilCoefficient.ab c)
      (D.geometricFiber Y₀).hom).obj M ⟶
    (condensedRingOrdinaryCoefficientComplex (WeilCoefficient.ab c)
      (D.geometricFiber Y₀).hom).obj
      ((L (WeilCoefficient.ab c) (D.geometricFrobenius Y₀).hom).obj M) := by
  let _ : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let a := (D.geometricFiber Y₀).hom
  let g := (D.geometricFrobenius Y₀).hom
  let b := (baseAutomorphism D).hom
  have w : g ≫ a = a ≫ b :=
    (D.galoisMap_projections Y₀.hom
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)).2
  exact (pointInsertion (WeilCoefficient.ab c) b).hom.app ((R (WeilCoefficient.ab c) a).obj M) ≫
    (pointSections (WeilCoefficient.ab c) (Spec (.of D.k))).map
      ((ordinary (WeilCoefficient.ab c) g a a b w).app M)

/-- The first compact arrow on the cohomology node's actual compact coefficient complex.
Use the normalized proper/open exchange, then compare the reindexed compactification
with the chosen target presentation. Source: latest blueprint, second display, first arrow
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport). -/
def compactTransport (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (c : WeilCoefficient ell)
    (c₀ c₁ : Compactification (D.geometricFiber Y₀).hom)
    (M : (boundedConstructible
      (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber Y₀).left)).FullSubcategory)
    (hM : boundedConstructible (condensedRingObj (WeilCoefficient.ab c)
      (D.geometricFiber Y₀).left)
      ((L (WeilCoefficient.ab c) (D.geometricFrobenius Y₀).hom).obj M.obj)) :
    (condensedRingCompactCoefficientComplex (WeilCoefficient.ab c) c₀).obj M.obj ⟶
    (condensedRingCompactCoefficientComplex (WeilCoefficient.ab c) c₁).obj
      ((L (WeilCoefficient.ab c) (D.geometricFrobenius Y₀).hom).obj M.obj) := by
  let _ : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let a := (D.geometricFiber Y₀).hom
  let g := (D.geometricFrobenius Y₀).hom
  let b := (baseAutomorphism D).hom
  have w : g ≫ a = a ≫ b :=
    (D.galoisMap_projections Y₀.hom
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)).2
  exact (pointInsertion (WeilCoefficient.ab c) b).hom.app
      ((C (WeilCoefficient.ab c) c₀).obj M.obj) ≫
    (pointSections (WeilCoefficient.ab c) (Spec (.of D.k))).map
      (compact (WeilCoefficient.ab c) (compactData D ell hEll c) a a b g w c₀ c₁ M hM)

/-- Precisely the Frobenius transport assertions, with no arbitrary-square, inverse or
identity law. Naturality and compactification independence use the specified maps above.
Source: latest blueprint, both first arrows and their cohomology transports
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport). -/
structure FrobeniusTransportLaws (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (c : WeilCoefficient ell) : Prop where
  pull_constructible : ∀ (M : (boundedConstructible
      (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber Y₀).left)).FullSubcategory),
    boundedConstructible (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber Y₀).left)
      ((L (WeilCoefficient.ab c) (D.geometricFrobenius Y₀).hom).obj M.obj)
  transport_iso : ∀ (c₀ c₁ : Compactification (D.geometricFiber Y₀).hom)
    (M : (boundedConstructible
      (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber Y₀).left)).FullSubcategory),
    IsIso (ordinaryTransport D ell Y₀ c M.obj) ∧
      IsIso (compactTransport D ell hEll Y₀ c c₀ c₁ M (pull_constructible M))
  ordinary_naturality : ∀ (M N : (boundedConstructible
      (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber Y₀).left)).FullSubcategory)
    (f : M ⟶ N),
    (condensedRingOrdinaryCoefficientComplex (WeilCoefficient.ab c)
        (D.geometricFiber Y₀).hom).map f.hom ≫ ordinaryTransport D ell Y₀ c N.obj =
      ordinaryTransport D ell Y₀ c M.obj ≫
        (condensedRingOrdinaryCoefficientComplex (WeilCoefficient.ab c)
          (D.geometricFiber Y₀).hom).map
          ((L (WeilCoefficient.ab c) (D.geometricFrobenius Y₀).hom).map f.hom)
  compact_naturality : ∀ (c₀ c₁ : Compactification (D.geometricFiber Y₀).hom)
    (M N : (boundedConstructible
      (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber Y₀).left)).FullSubcategory)
    (f : M ⟶ N),
    (condensedRingCompactCoefficientComplex (WeilCoefficient.ab c) c₀).map f.hom ≫
        compactTransport D ell hEll Y₀ c c₀ c₁ N (pull_constructible N) =
      compactTransport D ell hEll Y₀ c c₀ c₁ M (pull_constructible M) ≫
        (condensedRingCompactCoefficientComplex (WeilCoefficient.ab c) c₁).map
          ((L (WeilCoefficient.ab c) (D.geometricFrobenius Y₀).hom).map f.hom)
  compactification_independent : ∀ (c₀ d₀ c₁ d₁ : Compactification (D.geometricFiber Y₀).hom)
    (M : (boundedConstructible
      (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber Y₀).left)).FullSubcategory),
    (pointSections (WeilCoefficient.ab c) (Spec (.of D.k))).map
        (((compactData D ell hEll c).compare (D.geometricFiber Y₀).hom c₀ d₀).hom.app M) ≫
        compactTransport D ell hEll Y₀ c d₀ d₁ M (pull_constructible M) =
      compactTransport D ell hEll Y₀ c c₀ c₁ M (pull_constructible M) ≫
        (pointSections (WeilCoefficient.ab c) (Spec (.of D.k))).map
          (((compactData D ell hEll c).compare (D.geometricFiber Y₀).hom c₁ d₁).hom.app
            ⟨(L (WeilCoefficient.ab c) (D.geometricFrobenius Y₀).hom).obj M.obj,
              pull_constructible M⟩)
  homology_iso : ∀ (c₀ c₁ : Compactification (D.geometricFiber Y₀).hom)
    (M : (boundedConstructible
      (condensedRingObj (WeilCoefficient.ab c) (D.geometricFiber Y₀).left)).FullSubcategory)
    (i : ℤ),
    IsIso ((DerivedCategory.homologyFunctor _ i).map (ordinaryTransport D ell Y₀ c M.obj)) ∧
      IsIso ((DerivedCategory.homologyFunctor _ i).map
        (compactTransport D ell hEll Y₀ c c₀ c₁ M (pull_constructible M)))

/-- On the specified geometric fibre with E or finite-subextension-valued Omega, the
normalized first arrows are natural linear isomorphisms, independent of compactification,
and induce isomorphisms in every integer cohomology degree. Pullback preserves D^b_c.

Source: latest blueprint, def-weil-global-geometric-frobenius, first arrow of each display;
proof steps 1--5 of lem-weil-condensed-isomorphism-cohomology-transport.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport)

Proof: the inverse arithmetic Frobenius gives the specified commuting isomorphism square.
Exact isomorphism pullback preserves bounded constructible complexes. Take the right
adjunction mate of the pullback compositor for ordinary exchange. For compact support,
reindex the compactification, use ordinary exchange on its proper part and the inverse
open-adjunction mate, then the unique proper-refinement-normalized comparison. These
constructions are natural, and common refinements give the comparison-commutation square.
At the algebraically closed point, the coefficient-preserving corresponding-object
comparison identifies inverse-image terminal sections with sections over (s,b); restriction
along the invertible site arrow gives pointInsertion. Whisker this identification with the
recorded coefficient sections functor and localize, using exact point evaluation. The
composites are the two specified transports in the recorded coefficient derived category.
Applying H^i preserves their inverse identities for every integer i. -/
theorem geometricFrobeniusCohomologyTransport (D : FiniteFieldDatum.{u}) (ell : ℕ)
    [Fact ell.Prime] (hEll : ell ≠ D.p) (Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (c : WeilCoefficient ell) : FrobeniusTransportLaws D ell hEll Y₀ c := by
  sorry

end WeilConjectures.GeometricFrobeniusTransport
