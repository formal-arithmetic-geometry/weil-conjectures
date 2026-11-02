/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.RelativeCurve.RelativeCurvePunctual
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek

/-!
# Relative smooth-proper purity

Source: latest blueprint, `sec-zeta-weil/sk-prop-smooth-proper-purity/`
`prop-zl-smooth-proper-relative-purity.md` and its eight-step proof
(blueprint: prop-zl-smooth-proper-relative-purity).

The lower shriek uses the chosen compactification, not the identity compactification.
Its Weil structure is Ex_!, computed with the proper/open exchange on a model
compactification and transported by the canonical compactification-independence comparison.
The ordinary direct image uses Ex_* independently. Clause (a) tests the canonical proper
comparison between these two specified structures.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures
namespace RelativeSmoothProperPurity
open CondensedRing

section Lifts
variable (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The Ex_! lift on the canonical, chosen-compactification lower shriek.

The supplied exchange is the proper/open compact-support exchange on the presentation `c`.
The sole transport is from that presentation to `boundedConstructibleLowerShriek ell f`,
through the published compactification-independence comparison. In particular no ordinary
pushforward or proper-coincidence isomorphism enters this construction. Geometric Galois
Frobenius is semilinear over `k`, so the exchange is the proper/open recipe on the
base-changed model compactification, `RelativeCurve.exchange`.
Source: `prop-weil-operations`, Ex_! formula, and Step 1 of the relative-purity proof
(blueprint: prop-zl-smooth-proper-relative-purity). -/
def exShriekLift (c : Compactification f.left)
    {gX : X.left ⟶ X.left} {gY : Y.left ⟶ Y.left} [IsIso gX] [IsIso gY]
    (ex : rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ell) c ⋙
        (upperStar (Profinite.padicAlgClRingObj ell) gY).mapDerivedCategory ≅
      (upperStar (Profinite.padicAlgClRingObj ell) gX).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ell) c)
    (K : Endofunctor.IsoAlgebra
      (upperStar (Profinite.padicAlgClRingObj ell) gX).mapDerivedCategory)
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left)
      K.carrier) :
    Endofunctor.IsoAlgebra
      (upperStar (Profinite.padicAlgClRingObj ell) gY).mapDerivedCategory :=
  let A : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left) :=
    ⟨K.carrier, hK⟩
  let e := (Functor.isoWhiskerRight
    (boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl ell
      (compactificationOverField f) c) (boundedConstructible _).ι ≪≫
        boundedConstructibleLowerShriekOfCompactificationCompatibility ell c).app A
  let P := (upperStar (Profinite.padicAlgClRingObj ell) gY).mapDerivedCategory
  Endofunctor.IsoAlgebra.mk ((boundedConstructibleLowerShriek ell f).obj A).obj
    (P.mapIso e ≪≫ ex.app K.carrier ≪≫
      (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj ell) c).mapIso
        K.str ≪≫ e.symm)

/-- The independent Ex_* lift on the restricted ordinary direct image, normalized by the
published inclusion comparison. Its exchange is the right-adjoint mate of the Frobenius
pullback square, not a transport from the lower-shriek lift.
Source: `prop-weil-operations`, Ex_* formula, and relative-purity Step 1
(blueprint: prop-zl-smooth-proper-relative-purity). -/
def exStarLift (gX : X.left ≅ X.left) (gY : Y.left ≅ Y.left)
    (sq : CommSq gX.hom f.left f.left gY.hom)
    (K : Endofunctor.IsoAlgebra
      (upperStar (Profinite.padicAlgClRingObj ell) gX.hom).mapDerivedCategory)
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left)
      K.carrier) :
    Endofunctor.IsoAlgebra
      (upperStar (Profinite.padicAlgClRingObj ell) gY.hom).mapDerivedCategory :=
  let A : BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell) X.left) :=
    ⟨K.carrier, hK⟩
  let e := (boundedConstructibleLowerStarCompatibility ell f).app A
  let P := (upperStar (Profinite.padicAlgClRingObj ell) gY.hom).mapDerivedCategory
  letI : IsIso (RelativeCurve.properExchange ell f.left gX gY sq) :=
    Adjunction.isIso_exchangeRight_of_isEquivalence _ _ _
  Endofunctor.IsoAlgebra.mk ((boundedConstructibleLowerStar ell f).obj A).obj
    (P.mapIso e ≪≫ (asIso (RelativeCurve.properExchange ell f.left gX gY sq)).app K.carrier ≪≫
      (lowerStar (Profinite.padicAlgClRingObj ell) f.left).rightDerivedFunctor.mapIso K.str ≪≫
      e.symm)

end Lifts
end RelativeSmoothProperPurity

open CondensedRing

/-- Relative smooth-proper purity for the pulled-back condensed Qbar coefficients.

Source: latest blueprint, `prop-zl-smooth-proper-relative-purity.md`, clauses (a), (b),
and the absolute specialization (blueprint: prop-zl-smooth-proper-relative-purity).

Proof (postponed). (1) Independence of compactification identifies the chosen lower shriek
with its identity-compactification presentation. The proper/open definition of Ex_! becomes
Ex_* under this identification; hence the canonical proper comparison is a Weil morphism.
(2) Descend the lisse coefficient to a finite extension, and use the smooth-fibre lattice
neighbourhood lemma etale locally on the base. (3) Finite proper base change and smooth
specialization make the finite-level higher direct images locally constant. (4) Integral
constructibility, completeness and Milnor identify the limit with finite constant local
models. (5) Flat extension to the finite coefficient field and then Qbar gives lissity and
the Frobenius-equivariant geometric-fibre formula. (6) The shriek weight bound gives the
upper bound w+i. (7) The lisse coefficient dual twisted by d has weight -w-2d. (8) The
invariant perfect pairing on each smooth proper closed fibre inverts the complementary
eigenvalues, giving the reverse bound and equality. The constant coefficient has weight
zero, yielding the absolute specialization. Empty fibres, rank zero, disconnected fibres
and every integer degree are included.
-/
theorem relative_smooth_proper_purity_statement
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (X₀ Y₀ : Over (Spec (.of D.k₀)))
    [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated Y₀.hom] [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsProper f₀.left] (d : ℕ)
    [SmoothOfRelativeDimension d f₀.left] (ι : PadicAlgCl ell →+* ℂ)
    {M : NativeL2.WeilModule D ell X₀}
    (hM : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) M.carrier)
    {w : ℝ} (hw : NativeL2.Pure D ell X₀ M ι w) (i : ℤ) :
    letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
    letI : Fact D.p.Prime := ⟨D.prime⟩
    letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
    letI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
    letI : Fact (ringChar D.k).Prime := ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
    letI : Fact (ringChar D.k ≠ ell) := ⟨(ringChar.eq D.k D.p).symm ▸ hEll.symm⟩
    letI : LocallyOfFiniteType (D.geometricFiber X₀).hom :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
    letI : QuasiCompact (D.geometricFiber X₀).hom :=
      inferInstanceAs (QuasiCompact (pullback.snd X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
    letI : IsSeparated (D.geometricFiber X₀).hom :=
      inferInstanceAs (IsSeparated (pullback.snd X₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
    letI : LocallyOfFiniteType (D.geometricFiber Y₀).hom :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd Y₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
    letI : QuasiCompact (D.geometricFiber Y₀).hom :=
      inferInstanceAs (QuasiCompact (pullback.snd Y₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
    letI : IsSeparated (D.geometricFiber Y₀).hom :=
      inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
    let Λ := Profinite.padicAlgClRingObj ell
    let f : D.geometricFiber X₀ ⟶ D.geometricFiber Y₀ := (Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀
    letI : IsProper f.left := MorphismProperty.overPullbackMap
      (P := @IsProper) (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀ inferInstance
    let gX := D.geometricFrobenius X₀
    let gY := D.geometricFrobenius Y₀
    let sq : CommSq gX.hom f.left f.left gY.hom :=
      ⟨(D.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.1⟩
    let K := (Endofunctor.IsoAlgebra.mapOfNatIso
      ((CondensedRing.upperStar Λ gX.hom).mapDerivedCategorySingleFunctor 0)).obj M
    ∃ hK : boundedConstructible (condensedRingObj Λ (D.geometricFiber X₀).left) K.carrier,
      let A : BoundedConstructible (condensedRingObj Λ (D.geometricFiber X₀).left) :=
        ⟨K.carrier, hK⟩
      let c₀ := CondensedRing.compactificationOverField f₀
      let C := RelativeSmoothProperPurity.exShriekLift ell f
        (RelativeCurve.geometricCompactification D f₀ c₀)
        (RelativeCurve.exchange D ell f₀ c₀) K hK
      let S := RelativeSmoothProperPurity.exStarLift ell f gX gY sq K hK
      let H := Endofunctor.IsoAlgebra.mapOfNatIso
        ((CondensedRing.upperStar Λ gY.hom).mapDerivedCategoryHomologyFunctorIso i)
      let N! := H.obj C
      let N := H.obj S
      let a := (DerivedCategory.homologyFunctor _ i).map
        (((CondensedRing.boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ell f).hom.app
          A).hom)
      (CondensedRing.upperStar Λ gY.hom).map a ≫ N.str.hom = N!.str.hom ≫ a ∧
        IsIso a ∧ IsLisseCoefficientModule Λ N.carrier ∧
        NativeL2.Pure D ell Y₀ N ι (w + (i : ℝ)) := by
  sorry

end WeilConjectures
