/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Dense lisse open for a condensed Weil module

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
`sec-deligne-laumon-general/sec-reduction-to-the-relative-affine-line/`
`sk-prop-wgen-relative-line/thm-zl-relative-line-stratification.proof.md`,
paragraphs 1 and 4 (blueprint: lem-zl-condensed-weil-dense-lisse-open).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The restriction of a Weil isomorphism `θ : Φ^* M ≅ M` to a Frobenius-stable open:
for `j : U ⟶ X` and `φ : U ⟶ U` with `φ ≫ j = j ≫ Φ`, the composite
`φ^* j^* M ≅ (φ ≫ j)^* M = (j ≫ Φ)^* M ≅ j^* Φ^* M ≅ j^* M` of the pullback compositors,
the square and `j^* θ`.
Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
`sec-deligne-laumon-general/sec-reduction-to-the-relative-affine-line/`
`sk-prop-wgen-relative-line/thm-zl-relative-line-stratification.proof.md`,
paragraph 4, restriction of the Weil structure
(blueprint: lem-zl-condensed-weil-dense-lisse-open). -/
def restrictedWeilIso (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U X : Scheme.{u}} {j : U ⟶ X} {φ : U ⟶ U} {Φ : X ⟶ X}
    (h : φ ≫ j = j ≫ Φ)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (θ : (CondensedRing.upperStar Λ Φ).obj M ≅ M) :
    (CondensedRing.upperStar Λ φ).obj ((CondensedRing.upperStar Λ j).obj M) ≅
      (CondensedRing.upperStar Λ j).obj M :=
  (CondensedRing.upperStarComp Λ φ j).symm.app M ≪≫
    eqToIso (congrArg (fun g ↦ (CondensedRing.upperStar Λ g).obj M) h) ≪≫
    (CondensedRing.upperStarComp Λ j Φ).app M ≪≫ (CondensedRing.upperStar Λ j).mapIso θ

/-- A constructible condensed Weil module is lisse on a dense open descending to the
finite-field model, and its Weil isomorphism restricts to that open.
Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
`sec-deligne-laumon-general/sec-reduction-to-the-relative-affine-line/`
`sk-prop-wgen-relative-line/thm-zl-relative-line-stratification.proof.md`,
paragraphs 1 and 4 (blueprint: lem-zl-condensed-weil-dense-lisse-open).

The pullback `pullback j₀ p` is the geometric base change of the open immersion
`j₀ : U₀ ⟶ T₀`; its second projection is the open immersion `j : U ⟶ T`.
The morphism `φ` records the induced geometric Frobenius on this pullback by its
commuting square with the geometric Frobenius of `T`. The square `hφ` is exactly
the datum of `restrictedWeilIso`: the restricted Weil isomorphism of the node is
`restrictedWeilIso Λ hφ θ : φ^* j^* M ≅ j^* M`, the restriction of the given `θ`
(not an arbitrary isomorphism).

Proof: (1) A finite lisse stratification gives an open containing every generic
point: near a component generic point, remove the other components from the open
part of its locally closed stratum. Their union is dense and lisse.
(2) This quasi-compact open descends to a finite constant extension by Galois
descent of quasi-compact opens (Stacks Tag 04KU).
(3) Intersect its finitely many Frobenius conjugates. The Weil isomorphism
identifies the conjugate restrictions, so the intersection remains lisse; it
still contains every generic point and is Galois invariant.
(4) Descend its invariant closed complement (Stacks Tag 038B), obtaining an open
over the finite field.
(5) Surjectivity of geometric base change and generalization to component generic
points show the descended open is dense. For the empty model take the empty open.
(6) The Frobenius open square is Cartesian. Restrict theta and use the pullback
compositors: this is `restrictedWeilIso Λ hφ θ`.
-/
theorem exists_dense_lisse_open_of_constructible_weil
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ D.p)
    (Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom] [IsReduced Y₀.left]
    (M : Mod (Sheaf (Scheme.ProEt.topology (D.geometricFiber Y₀).left) Ab.{u + 1})
      ((coefficientRing (D.geometricFiber Y₀).left
        (Mon.mk (Profinite.padicAlgClRingObj ℓ))).X))
    (_hM : IsConstantModelConstructible
      ((Mon.mk (Profinite.padicAlgClRingObj ℓ)).X)
      (D.geometricFiber Y₀).left M)
    (θ : (CondensedRing.upperStar ((Mon.mk (Profinite.padicAlgClRingObj ℓ)).X)
      (D.geometricFrobenius Y₀).hom).obj M ≅ M) :
    ∃ (U₀ : Scheme.{u}) (j₀ : U₀ ⟶ Y₀.left),
      IsOpenImmersion j₀ ∧ Dense (Set.range j₀.base) ∧
      IsOpenImmersion (pullback.snd j₀ (pullback.fst Y₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))) ∧
      ∃ φ : pullback j₀ (pullback.fst Y₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) ⟶
          pullback j₀ (pullback.fst Y₀.hom
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))),
        IsIso φ ∧
        ∃ hφ : φ ≫ pullback.snd j₀ (pullback.fst Y₀.hom
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) =
          pullback.snd j₀ (pullback.fst Y₀.hom
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) ≫
            (D.geometricFrobenius Y₀).hom,
        IsLisseCoefficientModule ((Mon.mk (Profinite.padicAlgClRingObj ℓ)).X)
          ((CondensedRing.upperStar ((Mon.mk (Profinite.padicAlgClRingObj ℓ)).X)
            (pullback.snd j₀ (pullback.fst Y₀.hom
              (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))).obj M) := by
  sorry

end AlgebraicGeometry.ProEtale
