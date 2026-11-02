/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeoAffineLocal
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothExceptionalBaseChange
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.TensorRightUnitor
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The exceptional inverse image of a smooth morphism

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/
sec-the-exceptional-inverse-image-of-a-smooth-morphism-and-base-change/
sk-prop-cohsm/_section.md, clauses (1)--(3), and sk-prop-cohsm.proof.md, (7.11)--(7.14)
(blueprint: sk-prop-cohsm).

We use the finite classical comparison coordinates supplied by `geoAffineLocal`.
An input is an arbitrary object of `ClassicalD`, without a boundedness, constructibility
or Tor-amplitude condition. Its etale representative is the inverse of the specified
comparison equivalence. All output maps are sent through the native comparison functor.
Thus the tensor map is the coefficient-first projection/counit transpose, and the
exceptional exchange is the inverse compact-support-exchange/counit transpose.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry.ProEtale

/-- The compact-support comparison for a chart, using the two canonical compositors and
its equation over the base. Source: the chart paragraph of sk-prop-cohsm.proof.md, (7.14)
(blueprint: sk-prop-cohsm). -/
def cohsmChartSupportIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X P S : Scheme.{u}} (u : U ⟶ X) (f : X ⟶ S) (e : U ⟶ P) (p : P ⟶ S)
    [QuasiCompact u] [QuasiCompact f] [QuasiCompact e] [QuasiCompact p]
    [HasCompactification u] [HasCompactification f] [HasCompactification e]
    [HasCompactification p] [HasCompactification (u ≫ f)] [HasCompactification (e ≫ p)]
    (h : u ≫ f = e ≫ p) :
    Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) u ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ≅
      Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) p :=
  Etale.unboundedEtaleLowerShriekCompIso A u f ≪≫
    Etale.unboundedEtaleLowerShriekCongr A h ≪≫
    (Etale.unboundedEtaleLowerShriekCompIso A e p).symm

/-- The etale adjunction with its actual sum-over-fibres counit, transported by the
canonical compactification comparison and the exact/left-derived inverse-image comparison.
Source: chart counit in clause (1) (blueprint: sk-prop-cohsm). -/
def cohsmEtaleAdjunction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    [HasCompactification e] :
    Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ⊣
      (Etale.upperStar (ModuleCat.{u + 1} A) e).leftDerivedFunctor :=
  ((Etale.derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
      inferInstance).ofNatIsoLeft
        (Etale.canonicalEtaleCompactSupportComparison A e
          (HasCompactification.compactification e)).symm).ofNatIsoRight
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).symm

/-- The specified affine trace adjunction in the affine-space coordinates of the chart.
The right normal form is the explicit `towerENormalForm` used in
`affineTraceRight_normalForm`, not an independently chosen isomorphism. The left comparison
is the ordered compact-support comparison. The final transport is along the canonical
coordinate-tower/affine-space isomorphism and the specified Tate pullback comparisons.
Consequently its counit at the unit is the transport of `affineTraceCounit`.
The projective data argument includes the Kummer Chern and counit normalization equations.
Source: sk-prop-cohsm clause (1), affine counit; def-amb-affine-trace-construction and
lem-amb-affine-trace-right-normal-form (blueprint: sk-prop-cohsm). -/
def cohsmAffineTraceAdjunction
    (A : Type (u + 1)) [CommRing A] [Finite A] (ell r : ℕ)
    (hpos : 0 < ell ^ r) (hA : ((ell ^ r : ℕ) : A) = 0)
    (tt : Etale.OrdinaryFiniteTwistTransport A (ell ^ r) hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((ell ^ r : ℕ) : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A (ell ^ r) hA tt T hT)
    (S : Scheme.{u}) (hnoeth : IsNoetherian S)
    (hS : IsUnit ((ell ^ r : ℕ) : Γ(S, ⊤))) (d : ℕ)
    [HasCompactification (AffineSpace (ULift.{u} (Fin d)) S ↘ S)] :
    Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin d)) S ↘ S) ⊣
      etaleAffineRight (AffineSpace (ULift.{u} (Fin d)) S) S
        (AffineSpace (ULift.{u} (Fin d)) S ↘ S) A ell r d hA := by
  letI := hnoeth
  let B := ModuleCat.{u + 1} A
  let n := ell ^ r
  let T := affineTraceTower S d
  let P := AffineSpace (ULift.{u} (Fin d)) S
  let g := affineTraceProjection S d
  let p : P ⟶ S := P ↘ S
  let a : P ≅ T := (affineTraceAffineSpaceIso S d).symm
  have ha : a.inv ≫ p = g := AffineSpace.homOfVector_over _ _
  have ha' : a.hom ≫ g = p := by rw [← ha]; simp
  letI := affineTraceNoetherian S d
  let E := fun (Y : Scheme.{u}) (j : ℕ) ↦ Scheme.finiteEtaleTateSheaf A n Y hA (j : ℤ)
  let tp := Scheme.finiteEtaleTwistPullbackData A n hpos hA
  let tc := fun {Y Z : Scheme.{u}} (v : Y ⟶ Z)
    (hZ : IsUnit (n : Γ(Z, ⊤))) (j : ℕ) ↦
      tp.c v hZ (affineTracePullbackInvertible n v hZ) j
  let flat : ∀ (Y : Scheme.{u}), IsUnit (n : Γ(Y, ⊤)) → ∀ j, ObjectProperty.flat (E Y j) := by
    intro Y hY j
    have hs : ∀ y : Y, IsUnit (n : Y.presheaf.stalk y) := by
      intro y
      simpa only [map_natCast] using hY.map (Y.presheaf.germ ⊤ y (by trivial)).hom
    exact (ObjectProperty.flat_iff_preservesFiniteLimits _).2
      (Scheme.finite_etale_torsion_twist_line Y n hpos hs A hA j).2.2.1
  let prod := fun (Y : Scheme.{u}) (hY : IsUnit (n : Γ(Y, ⊤))) (j : ℕ) ↦
    tp.p Y hY j 1 ≪≫ eqToIso
      (congrArg (Scheme.finiteEtaleTateSheaf A n Y hA) (by omega : (j : ℤ) + 1 = (j + 1 : ℕ)))
  let nf := Etale.towerENormalForm B n E tc (fun Y ↦ Iso.refl (E Y 0)) flat prod S hS d
  let adj := Etale.affineTraceAdjunction A n hA tt D S hS d
  let adjT := (adj.ofNatIsoLeft
    (Etale.affineTraceUnboundedCompactComparison A S d)).ofNatIsoRight nf
  let adjP := (cohsmEtaleAdjunction A a.hom).comp adjT
  let l := Etale.unboundedEtaleLowerShriekCompIso A a.hom g ≪≫
    Etale.unboundedEtaleLowerShriekCongr A ha'
  let k := Etale.tensorEPullback B n E tc a.hom
    (affineTraceInvertible n S hS d) d (2 * (d : ℤ))
  let rr := Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Etale.ordinaryFinitePullback A g) k ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Etale.leftDerivedUpperStarComp B a.hom g p ha'.symm).symm _
  exact (adjP.ofNatIsoLeft l).ofNatIsoRight rr

variable (ell : ℕ) [hprime : Fact ell.Prime]
variable (k : Type u) [Field k] [hchar : Fact (ringChar k ≠ ell)]
variable (hbase : Finite k ∨ IsAlgClosed k)
variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable [TopologicalSpace A] [DiscreteTopology A]
variable (r : ℕ) (hr : 1 ≤ r) (hAr : ((ell ^ r : ℕ) : A) = 0)
variable {X S : Scheme.{u}} [hXover : X.Over (Spec (CommRingCat.of k))]
variable [hSover : S.Over (Spec (CommRingCat.of k))]
variable [hXsep : IsSeparated (X ↘ Spec (CommRingCat.of k))]
variable [hXlft : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
variable [hXqc : QuasiCompact (X ↘ Spec (CommRingCat.of k))]
variable [hSsep : IsSeparated (S ↘ Spec (CommRingCat.of k))]
variable [hSlft : LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k))]
variable [hSqc : QuasiCompact (S ↘ Spec (CommRingCat.of k))]
variable (f : X ⟶ S) [hfover : f.IsOver (Spec (CommRingCat.of k))]
variable [hfsep : IsSeparated f] [hflft : LocallyOfFiniteType f] [hfqc : QuasiCompact f]
variable [HasCompactification f] (d : ℕ) [hfsmooth : SmoothOfRelativeDimension d f]

include hprime hchar hbase hr hXsep hXlft hXqc hSsep hSlft hSqc hfover hfsep hflft hfqc hfsmooth in
/-- Clause (1), with its actual trace-normalized chart counit.
`cohsmAffineTraceAdjunction` is the fixed transport of `affineTraceAdjunction`; there is
no existential affine adjunction or normal-form isomorphism. The existential projective
data carry their Kummer Chern/decomposition/counit equations, so changing the adjunction
by a scalar while retaining those equations is impossible.

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/
sec-the-exceptional-inverse-image-of-a-smooth-morphism-and-base-change/
sk-prop-cohsm/_section.md, clause (1), and sk-prop-cohsm.proof.md (7.14)
(blueprint: sk-prop-cohsm).

Proof: the standing finite-type field hypotheses give Noetherianity and invertibility of
ell^r, and primality gives positivity. Use the normalized projective-line datum constructed
by exists_ordinaryFiniteP1Adjunction. Restrict the classical exceptional adjunction along the
open chart using geoAffineLocal clause (2). Compose the actual etale sum adjunction with the
specified ordered affine trace adjunction, transported through the explicit Tate normal form
and coordinate isomorphism in cohsmAffineTraceAdjunction. Identify compact supports by
cohsmChartSupportIso. Right-adjoint uniqueness now supplies the chart identification relative
to this fixed trace counit. Evaluate at K for the first formula, and at the coefficient unit
using canonical unit and Tate pullback comparisons for the dualizing formula.
-/
theorem cohomologicalSmoothness_chart
    (CS : ClassicalComparisonData S A) (N : ClassicalD S A)
    {U : Scheme.{u}} (u : U ⟶ X) [IsOpenImmersion u] [QuasiCompact u]
    [HasCompactification u] [HasCompactification (u ≫ f)]
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) S) [Etale e] [IsSeparated e]
    [QuasiCompact e] [HasCompactification e]
    [HasCompactification (e ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S))]
    (h : u ≫ f = e ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S)) :
    let P := AffineSpace (ULift.{u} (Fin d)) S
    let p : P ⟶ S := P ↘ S
    let K := CS.equivalence.inverse.obj N
    ∃ (hnoeth : IsNoetherian S) (hpos : 0 < ell ^ r)
      (hS : IsUnit ((ell ^ r : ℕ) : Γ(S, ⊤)))
      (tt : Etale.OrdinaryFiniteTwistTransport A (ell ^ r) hAr)
      (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((ell ^ r : ℕ) : Γ(T, ⊤))),
        Etale.OrdinaryFiniteP1Datum A (ell ^ r) hAr tt T hT),
      ∃ t : Etale.rightDerivedUpperShriek A f ⋙
          (Etale.upperStar (ModuleCat.{u + 1} A) u).leftDerivedFunctor ≅
        etaleAffineRight P S p A ell r d hAr ⋙
          (Etale.upperStar (ModuleCat.{u + 1} A) e).leftDerivedFunctor,
        ((((cohsmEtaleAdjunction A u).comp
          (Etale.rightDerivedUpperShriekAdjunction A f)).ofNatIsoLeft
            (cohsmChartSupportIso A u f e p h)).ofNatIsoRight t) =
          (cohsmEtaleAdjunction A e).comp
            (cohsmAffineTraceAdjunction A ell r hpos hAr tt D S hnoeth hS d) ∧
        Nonempty
          ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj
              ((Etale.upperStar (ModuleCat.{u + 1} A) u).leftDerivedFunctor.obj
                ((Etale.rightDerivedUpperShriek A f).obj K)) ≅
            (comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj
              (((etaleAffineRight P S p A ell r d hAr ⋙
                (Etale.upperStar (ModuleCat.{u + 1} A) e).leftDerivedFunctor).obj K))) ∧
        Nonempty
          ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj
              ((Etale.upperStar (ModuleCat.{u + 1} A) u).leftDerivedFunctor.obj
                (Etale.dualizingComplex A f)) ≅
            ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj
              ((DerivedCategory.singleFunctor _ 0).obj
                (Scheme.finiteEtaleTateTwist U (ell ^ r) A hAr d)))⟦2 * (d : ℤ)⟧) := by
  sorry

include hprime hchar hbase hr hAr hXsep hXlft hXqc hSsep hSlft hSqc hfover
  hfsep hflft hfqc hfsmooth in
/-- Clauses (1)--(3): the shifted dualizing object is a locally constant free line; the
specified tensor map is invertible on every classical input; arbitrary base change is
invertible, identifies dualizing objects, and satisfies the coefficient-first tensor square.
The chart and its specified counit are recorded in cohomologicalSmoothness_chart.

Source: current sk-prop-cohsm and sk-prop-cohsm.proof.md, (7.11)--(7.14)
(blueprint: sk-prop-cohsm).

Proof, following the current unit and DAG steps:
1. Use finite classical comparison to represent the unrestricted classical N by K. Transfer
the ordinary compact-support adjunction with its counit; comparison of the two adjunction
Hom bijections identifies all maps below with the classical transposes.
2. Smooth charts are etale over affine space, after open restriction of the base if needed.
Apply geoAffineLocal and the counit-normalized chart identification above. At the unit this
gives a single cohomology sheaf in degree -2d, locally a free rank-one coefficient sheaf.
3. Define the tensor map by inverse projection followed by the counit at the coefficient
unit. In the projective-line model its transpose is the normalized trace formula. Restrict
to the affine line and compose along the ordered affine tower and the etale factor. The
projection-composition and tensor-associativity equations identify it with the actual chart
identification, including d = 0. Exact restriction on a covering family detects isomorphisms.
4. Define exceptional exchange by transposing inverse compact-support exchange followed by
the pulled-back counit. Projective trace base change and etale sum base change identify this
map with pullback/twist exchange in the models. Compact-support composition and mate pasting
give the same result on the affine tower and covering charts after arbitrary change of base.
Restriction to those charts detects invertibility. There is no flatness condition on g.
5. At the coefficient unit, normalize by the inverse-image unit isomorphism to obtain beta.
Transpose the two paths in the final displayed equation under the primed adjunction.
Projection/exchange coherence identifies their projection factors; the defining transpose
of beta identifies their counit factors. Adjunction injectivity proves equality of maps.
Transport the rank-one shape and every specified arrow through the finite classical
comparison. This preserves the full unbounded input, not only the constructible objects.
-/
theorem cohomologicalSmoothness
    (CS : ClassicalComparisonData S A) (N : ClassicalD S A) :
    let K := CS.equivalence.inverse.obj N
    (∃ L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A),
      Nonempty
        (((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
          (Etale.dualizingComplex A f))⟦-(2 * (d : ℤ))⟧ ≅
            (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
              ((DerivedCategory.singleFunctor _ 0).obj L)) ∧
      ∃ cover : Scheme.Cover.{u} Scheme.etalePrecoverage X,
        ∀ i : cover.I₀,
          Nonempty (L.over (cover.etalePrecoverageToEtale i) ≅
            (constantSheaf (X.smallEtaleTopology.over (cover.etalePrecoverageToEtale i))
              (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))) ∧
    IsIso ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
      (Etale.smoothTensorDualityMap A f (Etale.isIso_projectionMap_of_finite A f) K)) ∧
    (∀ (S' : Scheme.{u}) [S'.Over (Spec (CommRingCat.of k))]
      [IsSeparated (S' ↘ Spec (CommRingCat.of k))]
      [LocallyOfFiniteType (S' ↘ Spec (CommRingCat.of k))]
      [QuasiCompact (S' ↘ Spec (CommRingCat.of k))]
      (g : S' ⟶ S) [g.IsOver (Spec (CommRingCat.of k))],
      let V := (comparisonUpperStar (ModuleCat.{u + 1} A) (pullback f g)).mapDerivedCategory
      IsIso (V.map (Etale.smoothExceptionalBaseChangeMap A f g K)) ∧
      IsIso (V.map (Etale.smoothDualizingBaseChangeMap A f g)) ∧
      V.map
        ((Etale.upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor.map
            (Etale.smoothTensorDualityMap A f (Etale.isIso_projectionMap_of_finite A f) K) ≫
          Etale.smoothExceptionalBaseChangeMap A f g K) =
        V.map
          ((Etale.smoothDualityTensorBaseChangeIso A f g K).hom ≫
            ((Etale.derivedTensor (ModuleCat.{u + 1} A) (pullback f g)).obj
              ((Etale.upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor.obj
                ((Etale.upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K))).map
              (Etale.smoothDualizingBaseChangeMap A f g) ≫
            Etale.smoothTensorDualityMap A (pullback.snd f g)
              (Etale.isIso_projectionMap_of_finite A (pullback.snd f g))
              ((Etale.upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K))) := by
  sorry

end AlgebraicGeometry.ProEtale
