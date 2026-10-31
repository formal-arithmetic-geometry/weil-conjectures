/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedWeilEquivarianceParent
public import WeilConjectures.AlgebraicGeometry.CondensedPurityTateDatum
public import WeilConjectures.SixFunctors.CondensedOperationComparisons
public import WeilConjectures.AlgebraicGeometry.CondensedPurityCoefficientChange
public import WeilConjectures.SixFunctors.CondensedFrobeniusComparisonCoherence
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index

/-! # Condensed Weil equivariance and its four compatibilities

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
prop-pur-weil-equivariance-compatibilities.md, order 3548, and its entire proof.
All operations below are the recorded condensed operations. In particular scalar
change is derived extension of coefficients, compact-support comparisons have their
proper/open normalization, and the purity map is selected by its counit universal
property. There is no arbitrary transport, orientation, Frobenius map or hcoh.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open WeilConjectures.PurityWeil WeilConjectures.PurityWeil.Condensed
open WeilConjectures.Purity.Condensed
open scoped CategoryTheory.Obj

namespace WeilConjectures.PurityWeil.Compatibilities

variable (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
  (hEll : ell ≠ D.p)

/-- Coefficient and model-pullback equations for the u-forms themselves. The scalar
case allows different finite coefficient fields, so O_E -> O_F, E -> F and E -> Qbar
are included, as well as every positive uniformizer reduction. The transported phi
is the canonical scalar or commuting-square comparison followed by phi, not new data.
Source: item proof, last paragraph and coefficient-change parenthesis
(blueprint: prop-pur-weil-equivariance-compatibilities). -/
def UCompatibility (C : ScalarSixPullbackData.{u}) : Prop :=
  (∀ (E E' : PadicAlgCl.FiniteIntermediateField ell)
    (Λ Λ' : ScalarSixRing.{u})
    (_hΛ : IsPurityFrobeniusCoefficient ell E Λ)
    (_hΛ' : IsPurityFrobeniusCoefficient ell E' Λ')
    (a : Λ ⟶ Λ') (_ha : ListedScalarChange ell a)
    (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
    (K : frobeniusD D Λ T₀) (phi : (frobeniusG D Λ T₀).obj K ≅ K),
    (scalarSixChange a (D.purityFrobeniusFiber T₀).left).map
        ((condensedFrobeniusComparison D Λ T₀).hom.app K ≫ phi.hom) =
      (C.theta a (D.puritySchemeFrobenius T₀)).hom.app K ≫
        (condensedFrobeniusComparison D Λ' T₀).hom.app
          ((scalarSixChange a (D.purityFrobeniusFiber T₀).left).obj K) ≫
        (C.theta a (D.purityGaloisMap T₀)).inv.app K ≫
        (scalarSixChange a (D.purityFrobeniusFiber T₀).left).map phi.hom) ∧
  (∀ (E : PadicAlgCl.FiniteIntermediateField ell) (Λ : ScalarSixRing.{u})
    (_hΛ : IsPurityFrobeniusCoefficient ell E Λ)
    (S₀ T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType S₀.hom] [QuasiCompact S₀.hom] [IsSeparated S₀.hom]
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
    (h₀ : S₀ ⟶ T₀) (K : frobeniusD D Λ T₀)
    (phi : (frobeniusG D Λ T₀).obj K ≅ K),
    (frobeniusU D Λ h₀).map
        ((condensedFrobeniusComparison D Λ T₀).hom.app K ≫ phi.hom) =
      (condensedSchemeFrobeniusSquare D Λ h₀).hom.app K ≫
        (condensedFrobeniusComparison D Λ S₀).hom.app ((frobeniusU D Λ h₀).obj K) ≫
        (condensedGaloisFrobeniusSquare D Λ h₀).inv.app K ≫
        (frobeniusU D Λ h₀).map phi.hom)

/-- The coefficient equations, including the nonflat O_E -> O_E/pi_E^n case.
The exceptional comparison delta is the actual transpose of the inverse of the
canonical compact-support scalar map followed by scalar extension of the counit.
Only membership and invertibility proofs are existential; no map is chosen.
The three equations are respectively purity, exceptional counit, and trace.
Source: coefficient-change parenthesis in the item proof and
lem-pur-condensed-purity-coefficient-change, all three displayed equations
(blueprint: prop-pur-weil-equivariance-compatibilities). -/
def CoefficientEquations : Prop :=
  ∀ (E E' : PadicAlgCl.FiniteIntermediateField ell) (c c' : Coefficient ell)
    (_hc : IsPurityFrobeniusCoefficient ell E (c.bundled.{u} ell))
    (_hc' : IsPurityFrobeniusCoefficient ell E' (c'.bundled.{u} ell))
    (a : c.bundled.{u} ell ⟶ c'.bundled.{u} ell)
    (_ha : ListedScalarChange ell a),
  ∃ ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell,
  ∀ (s : SmoothDatum D),
  ∃ p : ScalarLineCoordinates ell a ha s.X.left,
  ∀ (R : ScalarExceptionalAdjoint (c.bundled.{u} ell) s.compactification)
    (R' : ScalarExceptionalAdjoint (c'.bundled.{u} ell) s.compactification)
    (K : c.ctf ell s.Y.left),
  ∃ hK : property ell c' s.Y.left ((scalarSixChange a s.Y.left).obj K.obj),
  ∃ hG : property ell c' s.X.left
    ((scalarSixChange a s.X.left).obj (R.upper.obj K).obj),
  ∃ hB : IsIso ((scalarSupportMap a s.compactification).app (R.upper.obj K).obj),
  letI := hB
  let K' : c'.ctf ell s.Y.left := ⟨_, hK⟩
  let M : c'.ctf ell s.X.left := ⟨_, hG⟩
  let delta := (R'.restrictedAdjunction.homEquiv M K')
    (ObjectProperty.homMk
      (inv ((scalarSupportMap a s.compactification).app (R.upper.obj K).obj) ≫
        (scalarSixChange a s.Y.left).map (R.counit K)))
  let gammaK := ((canonicalPurity ell D hEll c s R).hom.app K).hom
  let gammaK' := ((canonicalPurity ell D hEll c' s R').hom.app K').hom
  (scalarSixChange a s.X.left).map gammaK ≫ delta.hom =
      sourceScalar ell a s.map s.dim ha p K.obj ≫ gammaK' ∧
    (scalarSupportMap a s.compactification).app (R.upper.obj K).obj ≫
        (rightDerivedLowerShriekOfCompactification (c'.obj ell) s.compactification).map
          delta.hom ≫ R'.counit K' =
      (scalarSixChange a s.Y.left).map (R.counit K) ∧
    (scalarSixChange a s.Y.left).map
        ((rightDerivedLowerShriekOfCompactification (c.obj ell) s.compactification).map
          gammaK ≫ R.counit K) =
      (scalarSupportMap a s.compactification).app
          ((c.smoothSource ell s.map s.dim).obj K.obj) ≫
        (rightDerivedLowerShriekOfCompactification (c'.obj ell) s.compactification).map
          (sourceScalar ell a s.map s.dim ha p K.obj) ≫
        (rightDerivedLowerShriekOfCompactification (c'.obj ell) s.compactification).map
          gammaK' ≫ R'.counit K'

set_option maxHeartbeats 1200000 in
-- Elaborating the three equations expands several derived adjunction Hom equivalences.
/-- Composition equations for canonical purity, exceptional counit, and normalized trace.
The right-adjoint compositor is the transpose of the independently normalized support
compositor, and the source compositor is the recorded root/tensor/shift composite.
The intermediate f-trace is evaluated on the still-twisted g-source.
Source: composition paragraph of the item proof and sk-thm-purity-transport
(blueprint: prop-pur-weil-equivariance-compatibilities). -/
def CompositionEquations (E : PadicAlgCl.FiniteIntermediateField ell) : Prop :=
  ∀ (c : Coefficient ell)
    (hc : IsPurityFrobeniusCoefficient ell E (c.bundled.{u} ell))
    (s : SmoothDatum D) (Z : Over (Spec (.of D.k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (g : s.Y.left ⟶ Z.left) [g.IsOver (Spec (.of D.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (e : ℕ) [SmoothOfRelativeDimension e g] (cg : Compactification g)
    (cr : Compactification.BoundaryCompactification (s.compactification.g ≫ cg.i)),
  letI : ∀ x : s.X.left, Invertible (ell : s.X.left.residueField x) :=
    fun x ↦ (by
      simpa using (primeUnit D ell hEll).map
        ((s.X.left ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
          IsUnit (ell : s.X.left.residueField x)).invertible
  let t : SmoothDatum D :=
    { X := s.Y, Y := Z, map := g, dim := e, compactification := cg }
  let st := s.comp Z g e cg cr
  ∃ p : LinePullCoordinates ell c s.map,
  ∀ (Rf : ScalarExceptionalAdjoint (c.bundled.{u} ell) s.compactification)
    (Rg : ScalarExceptionalAdjoint (c.bundled.{u} ell) cg)
    (Rgf : ScalarExceptionalAdjoint (c.bundled.{u} ell) st.compactification)
    (K : c.ctf ell Z.left),
  let h := coefficientCoherent ell D hEll E c hc
  let alpha := supportComposition D h
    (SepFinType.homMk (X := s.X) (Y := s.Y)
      (Over.homMk s.map (comp_over s.map (Spec (.of D.k)))))
    (SepFinType.homMk (X := s.Y) (Y := Z)
      (Over.homMk g (comp_over g (Spec (.of D.k)))))
    s.compactification cg st.compactification
  let delta := ((Rf.restrictedAdjunction.comp Rg.restrictedAdjunction).homEquiv
    (Rgf.upper.obj K) K)
    (ObjectProperty.homMk
      (alpha.hom.app ((inclusion ell c s.X.left).obj (Rgf.upper.obj K)) ≫ Rgf.counit K))
  let gammaF := canonicalPurity ell D hEll c s Rf
  let gammaG := canonicalPurity ell D hEll c t Rg
  let gammaGF := canonicalPurity ell D hEll c st Rgf
  let HgK := (source ell c g e (normalizedFamily ell D hEll c t).source_closed).obj K
  let Ff := rightDerivedLowerShriekOfCompactification (c.obj ell) s.compactification
  let Fg := rightDerivedLowerShriekOfCompactification (c.obj ell) cg
  let Fgf := rightDerivedLowerShriekOfCompactification (c.obj ell) st.compactification
  let HgfK := (source ell c st.map st.dim
    (normalizedFamily ell D hEll c st).source_closed).obj K
  (gammaGF.hom.app K).hom ≫ delta.hom =
      (sourceComp ell c s.map g s.dim e p K.obj).hom ≫
        (c.smoothSource ell s.map s.dim).map (gammaG.hom.app K).hom ≫
        (gammaF.hom.app (Rg.upper.obj K)).hom ∧
    alpha.hom.app ((inclusion ell c s.X.left).obj (Rgf.upper.obj K)) ≫ Rgf.counit K =
      Fg.map (Ff.map delta.hom) ≫ Fg.map (Rf.counit (Rg.upper.obj K)) ≫ Rg.counit K ∧
    alpha.hom.app ((inclusion ell c s.X.left).obj HgfK) ≫
        Fgf.map (gammaGF.hom.app K).hom ≫ Rgf.counit K =
      Fg.map (Ff.map (sourceComp ell c s.map g s.dim e p K.obj).hom) ≫
        Fg.map (Ff.map (gammaF.hom.app HgK).hom ≫ Rf.counit HgK) ≫
        Fg.map (gammaG.hom.app K).hom ≫ Rg.counit K

/-- Canonical compact-support base exchange on the literal pulled-back compactification.
Source: sk-thm-sf-comp-composition, normalized proper/open exchange
(blueprint: prop-pur-weil-equivariance-compatibilities). -/
def baseExchange (E : PadicAlgCl.FiniteIntermediateField ell)
    (c : Coefficient ell) (hc : IsPurityFrobeniusCoefficient ell E (c.bundled.{u} ell))
    (s : SmoothDatum D) (Y' : Over (Spec (.of D.k)))
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    (v : Y'.left ⟶ s.Y.left) [v.IsOver (Spec (.of D.k))]
    (M : c.ctf ell s.X.left) :=
  let s' := s.baseChange Y' v
  (supportExchange D (coefficientCoherent ell D hEll E c hc)
    (f := SepFinType.homMk (X := s.X) (Y := s.Y)
      (Over.homMk s.map (comp_over s.map (Spec (.of D.k)))))
    (f' := SepFinType.homMk (X := s'.X) (Y := s'.Y)
      (Over.homMk s'.map (comp_over s'.map (Spec (.of D.k)))))
    (IsPullback.of_hasPullback s.map v) s.compactification s'.compactification).app
      ((inclusion ell c s.X.left).obj M)

set_option maxHeartbeats 1200000 in
-- The literal pullback and adjunction transpose require the same larger elaboration budget.
/-- Cartesian base-change equations for purity, exceptional counit, and trace.
The exceptional exchange is the adjunction transpose of inverse B followed by
pullback of the counit, while the source exchange is the canonical Tate comparison.
Existential fields certify membership only; no arbitrary exchange map is supplied.
Source: base-change paragraph of the item proof, and operation-comparison counit equation
(blueprint: prop-pur-weil-equivariance-compatibilities). -/
def BaseChangeEquations (E : PadicAlgCl.FiniteIntermediateField ell) : Prop :=
  ∀ (c : Coefficient ell)
    (hc : IsPurityFrobeniusCoefficient ell E (c.bundled.{u} ell))
    (s : SmoothDatum D) (Y' : Over (Spec (.of D.k)))
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    (v : Y'.left ⟶ s.Y.left) [v.IsOver (Spec (.of D.k))],
  let s' := s.baseChange Y' v
  ∃ p : LinePullCoordinates ell c (pullback.fst s.map v),
  ∀ (R : ScalarExceptionalAdjoint (c.bundled.{u} ell) s.compactification)
    (R' : ScalarExceptionalAdjoint (c.bundled.{u} ell) s'.compactification)
    (K : c.ctf ell s.Y.left),
  ∃ hK : property ell c Y'.left ((actualPull (c.obj ell) v).obj K.obj),
  ∃ hG : property ell c s'.X.left
    ((actualPull (c.obj ell) (pullback.fst s.map v)).obj (R.upper.obj K).obj),
  let K' : c.ctf ell Y'.left := ⟨_, hK⟩
  let M : c.ctf ell s'.X.left := ⟨_, hG⟩
  let B := baseExchange ell D hEll E c hc s Y' v (R.upper.obj K)
  let delta := (R'.restrictedAdjunction.homEquiv M K')
    (ObjectProperty.homMk (B.inv ≫ (actualPull (c.obj ell) v).map (R.counit K)))
  let gammaK := ((canonicalPurity ell D hEll c s R).hom.app K).hom
  let gammaK' := ((canonicalPurity ell D hEll c s' R').hom.app K').hom
  let HK := (source ell c s.map s.dim
    (normalizedFamily ell D hEll c s).source_closed).obj K
  let F := rightDerivedLowerShriekOfCompactification (c.obj ell) s.compactification
  let F' := rightDerivedLowerShriekOfCompactification (c.obj ell) s'.compactification
  (actualPull (c.obj ell) (pullback.fst s.map v)).map gammaK ≫ delta.hom =
      (sourceBaseChange ell c s.map v s.dim p K.obj).hom ≫ gammaK' ∧
    B.hom ≫ F'.map delta.hom ≫ R'.counit K' =
      (actualPull (c.obj ell) v).map (R.counit K) ∧
    (actualPull (c.obj ell) v).map (F.map gammaK ≫ R.counit K) =
      (baseExchange ell D hEll E c hc s Y' v HK).hom ≫
        F'.map (sourceBaseChange ell c s.map v s.dim p K.obj).hom ≫
        F'.map gammaK' ≫ R'.counit K'

/-- The four-stage coefficient predicate agrees with the published operation predicate.
Source: coefficient conventions of lem-pur-condensed-operation-comparisons
(blueprint: prop-pur-weil-equivariance-compatibilities).
Proof: split the four cases. At a positive finite level use the canonical ULift
coefficient isomorphism; the three continuous coefficient cases are identical. -/
theorem coefficientIsCoefficient (E : PadicAlgCl.FiniteIntermediateField ell)
    (c : Coefficient ell)
    (_hc : IsPurityFrobeniusCoefficient ell E (c.bundled.{u} ell)) :
    OperationComparisons.IsCoefficient ell (c.bundled.{u} ell) := by
  rcases _hc with ⟨n, hn, h | h | h | h⟩
  · left
    refine ⟨E, n, hn, ?_⟩
    let A := Padic.coefficientExtensionRing ell E.1 n
    let : Finite A := Padic.finite_coefficientExtensionRing ell E.1 n hn
    let : TopologicalSpace A := ⊥
    let : DiscreteTopology A := discreteTopology_bot A
    let J := coherentTopology Profinite.{u}
    let f := Profinite.constantToContinuousRing.{u} A
    have hf₁ : Presheaf.IsLocallyInjective J f :=
      ⟨fun x y hxy ↦ Presheaf.equalizerSieve_mem J
        (Functor.whiskerRight f (forget₂ RingCat Ab)) x y hxy⟩
    have hf₂ : Presheaf.IsLocallySurjective J f :=
      ⟨fun s ↦ Presheaf.imageSieve_mem J
        (Functor.whiskerRight f (forget₂ RingCat Ab)) s⟩
    have hf : IsIso ((presheafToSheaf J RingCat.{u + 1}).map f) :=
      (J.W_iff f).mp (J.W_of_isLocallyBijective f)
    have hg : IsIso (IntegralModelsEmbedded.constantToContinuous.{u} A) := by
      unfold IntegralModelsEmbedded.constantToContinuous
      have : IsIso (((sheafificationAdjunction J RingCat.{u + 1}).homEquiv _
          (Profinite.continuousMapRingSheaf.{u} A)).symm f) := by
        change IsIso ((presheafToSheaf J RingCat.{u + 1}).map f ≫
          (sheafificationAdjunction J RingCat.{u + 1}).counit.app
            (Profinite.continuousMapRingSheaf.{u} A))
        infer_instance
      change IsIso
        (((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
            (CommRingCat.of (ULift.{u + 1} A))).hom ≫
          ((sheafificationAdjunction J RingCat.{u + 1}).homEquiv _
            (Profinite.continuousMapRingSheaf.{u} A)).symm f)
      infer_instance
    let e := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso
      (asIso (IntegralModelsEmbedded.constantToContinuous.{u} A))
    have : IsMonHom e.hom := by
      change IsMonHom ((sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (IntegralModelsEmbedded.constantToContinuous.{u} A))
      infer_instance
    let em : Mon.mk (IntegralModelsEmbedded.discreteObj.{u} A) ≅
        Mon.mk (Profinite.continuousMapRingObj.{u} A) :=
      Mon.mkIso e (IsMonHom.one_hom e.hom) (IsMonHom.mul_hom e.hom)
    let : TopologicalSpace (ULift.{u} A) := ⊥
    let : DiscreteTopology (ULift.{u} A) := discreteTopology_bot _
    let up : A →+* ULift.{u} A := ULift.ringEquiv.symm.toRingHom
    let down : ULift.{u} A →+* A := ULift.ringEquiv.toRingHom
    let er : Profinite.continuousMapRingSheaf.{u} A ≅
        Profinite.continuousCoefficientRingSheaf (ULift.{u} A) :=
      { hom := ⟨
          { app := fun S ↦
              RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
                ((up.compLeftContinuous S.unop continuous_of_discreteTopology).comp
                  ULift.ringEquiv.toRingHom))
            naturality := fun _ _ _ ↦ rfl }⟩
        inv := ⟨
          { app := fun S ↦
              RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
                ((down.compLeftContinuous S.unop continuous_of_discreteTopology).comp
                  ULift.ringEquiv.toRingHom))
            naturality := fun _ _ _ ↦ rfl }⟩
        hom_inv_id := by ext S x; rfl
        inv_hom_id := by ext S x; rfl }
    let eu := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso er
    have : IsMonHom eu.hom := by
      change IsMonHom ((sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).map er.hom)
      infer_instance
    let eum : Mon.mk (Profinite.continuousMapRingObj.{u} A) ≅
        Mon.mk (cartesianFinitePointRing (ULift.{u} A)) :=
      Mon.mkIso eu (IsMonHom.one_hom eu.hom) (IsMonHom.mul_hom eu.hom)
    exact ⟨h.some ≪≫ em ≪≫ eum⟩
  · exact Or.inr (Or.inl ⟨E, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨E, h⟩))
  · exact Or.inr (Or.inr (Or.inr h))

/-- The recorded scalar/exchange rectangle, identity, successive base change,
scalar/composition equation and pasted scalar rectangles on the very same normalized
support systems used above. The right-adjoint presentation in S is quantified by
existence, and no definition chooses its data.
Source: operation-comparison paragraphs in the item proof
(blueprint: prop-pur-weil-equivariance-compatibilities). -/
def OperationCompatibilities : Prop :=
  ∃ S : OperationComparisons.Data D ell,
    OperationComparisons.Laws S ∧
    ∀ (E : PadicAlgCl.FiniteIntermediateField ell) (c : Coefficient ell)
      (hc : IsPurityFrobeniusCoefficient ell E (c.bundled.{u} ell)),
      S.coherent (c.bundled.{u} ell) (coefficientIsCoefficient ell E c hc) =
        coefficientCoherent ell D hEll E c hc

/-- The published root/scalar/Frobenius equations, scalar associators, identities and
successive coefficient changes, on the same canonical smooth adjunction family.
In particular the closure coefficient's identity is retained.
Source: coefficient-change parenthesis of the item proof
(blueprint: prop-pur-weil-equivariance-compatibilities). -/
def TateCoefficientCompatibilities : Prop :=
  ∃ P : PurityCoefficientChange.Coordinates.{u} ell,
    PurityCoefficientChange.Equations ell D hEll (normalizedFamily ell D hEll) P ∧
    PurityCoefficientChange.FrobeniusCompatible ell D P ∧
    PurityCoefficientChange.CompositionCoherent ell D hEll P ∧
    PurityCoefficientChange.IdentityCoherent ell D hEll P

variable (E : PadicAlgCl.FiniteIntermediateField ell)
  (c : Coefficient ell) (hc : IsPurityFrobeniusCoefficient ell E (c.bundled.{u} ell))
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
  (f₀ : X₀ ⟶ Y₀)
  [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
  (d : ℕ) [SmoothOfRelativeDimension d (D.purityFrobeniusMap f₀)]
  (cf : Compactification (D.purityFrobeniusMap f₀))

/-- All three scheme-Frobenius forms, using the actual arrows of the repaired
condensed parent and the recorded kappa. The two compact-support vertical maps
are exactly B followed by F of the corresponding induced datum.
Source: scheme-Frobenius identification in the item proof, order 3548
(blueprint: prop-pur-weil-equivariance-compatibilities). -/
def SchemeThreeSquares (R : ScalarExceptionalAdjoint (c.bundled.{u} ell) cf) : Prop :=
  ∀ (K : c.ctf ell (D.purityFrobeniusFiber Y₀).left)
    (phi : (actualPull (c.obj ell) (D.purityGaloisMap Y₀)).obj K.obj ≅ K.obj),
  let a := normalizedFamily ell D hEll c (smoothIndex D f₀ d cf)
  let H := source ell c (D.purityFrobeniusMap f₀) d a.source_closed
  let P := pullCtf ell D hEll E c hc (D.purityFrobeniusFiber Y₀)
    (D.purityFrobeniusFiber Y₀) (D.purityGaloisMap Y₀)
  let phi' : P.obj K ≅ K := ObjectProperty.isoMk _ phi
  let F := rightDerivedLowerShriekOfCompactification (c.obj ell) cf
  let Q := actualPull (c.obj ell) (D.purityGaloisMap X₀)
  let gammaK := (property ell c _).ι.mapIso
    ((gamma (ell := ell) (D := D) (hEll := hEll) (c := c) f₀ d cf R).app K)
  let gammaPK := (property ell c _).ι.mapIso
    ((gamma (ell := ell) (D := D) (hEll := hEll) (c := c) f₀ d cf R).app (P.obj K))
  let b := sourceComparison ell D hEll c f₀ d K.obj
  let apur := (b ≪≫ (property ell c _).ι.mapIso (H.mapIso phi')).hom
  let aexc := ((Q.mapIso gammaK).symm ≪≫ b ≪≫ gammaPK ≪≫
    (property ell c _).ι.mapIso (R.upper.mapIso phi')).hom
  let eps := R.counit K
  let tr := F.map gammaK.hom ≫ eps
  let zG := compactComparison ell D hEll E c hc f₀ cf (R.upper.obj K) ≫ F.map aexc
  let zH := compactComparison ell D hEll E c hc f₀ cf (H.obj K) ≫ F.map apur
  (actualPull (c.obj ell) (D.puritySchemeFrobenius X₀)).map gammaK.hom ≫
        uDatum D (c.bundled.{u} ell) X₀ (R.upper.obj K).obj aexc =
      uDatum D (c.bundled.{u} ell) X₀ (H.obj K).obj apur ≫ gammaK.hom ∧
    (actualPull (c.obj ell) (D.puritySchemeFrobenius Y₀)).map eps ≫
        uDatum D (c.bundled.{u} ell) Y₀ K.obj phi.hom =
      uDatum D (c.bundled.{u} ell) Y₀ (F.obj (R.upper.obj K).obj) zG ≫ eps ∧
    (actualPull (c.obj ell) (D.puritySchemeFrobenius Y₀)).map tr ≫
        uDatum D (c.bundled.{u} ell) Y₀ K.obj phi.hom =
      uDatum D (c.bundled.{u} ell) Y₀ (F.obj (H.obj K).obj) zH ≫ tr

/-- The scheme-Frobenius squares, the coefficient equations, the composition
equations and the Cartesian base-change equations, left after the parent
equivariance square.
Source: the scheme-Frobenius, coefficient, composition, and base-change
paragraphs of the proof of prop-pur-weil-equivariance-compatibilities.
Proof: (1) scheme squares: each `uDatum` is `kappa` followed by the geometric
datum, so naturality of the natural isomorphism `kappa` at the horizontal arrow
(purity `gammaK`, counit `eps`, trace `tr`) turns each scheme square into
`kappa` followed by the corresponding square of
`weilEquivarianceOfPurityAndTrace`. (2) coefficients: expand the canonical scalar
exceptional adjunction; the coefficient-change equations of
lem-pur-condensed-purity-coefficient-change and the scalar/exchange rectangles of
lem-pur-condensed-operation-comparisons identify purity, the transposed counit
`delta` and trace. (3) composition: purity transport identifies composite purity
with iterated purity, the normalized compositor cancels, and the f-trace is
applied at the still-twisted g-source before the g-trace. (4) base change: the
purity base-change compatibility and the B,e counit and pasting equations give
both paths of each square for the base-changed map
(blueprint: prop-pur-weil-equivariance-scheme-coefficient-composition-base-change). -/
theorem schemeCoefficientCompositionBaseChangeCompatibilities
    (R : ScalarExceptionalAdjoint (c.bundled.{u} ell) cf) :
    SchemeThreeSquares ell D hEll E c hc f₀ d cf R ∧
    CoefficientEquations ell D hEll ∧
    CompositionEquations ell D hEll E ∧
    BaseChangeEquations ell D hEll E := by
  sorry

/-- The scheme-Frobenius compatibility for all listed coefficient changes and
pullbacks, for coefficient rings of possibly different finite coefficient fields.
Source: the scheme-Frobenius paragraph of the proof of
prop-pur-weil-equivariance-compatibilities.
Proof: write each `u` as the specified comparison followed by `phi` and apply
functoriality of scalar change, resp. model pullback. For pullback, the `pullback`
law of `condensedFrobeniusComparison_coherence` (at the field `E` of `Λ`), solved
for the pulled-back comparison, gives the second conjunct directly. For scalar
change the `scalar` law gives `change(kappa) = theta_P ≫ kappa' ≫ theta_G⁻¹`;
that law is recorded for one fixed field, but its proof (scalar balancing of the
absolute Frobenius trivialization, with the canonical `theta` fixed by
`thetaNormalization`) uses no property of the field, so it holds for `Λ` and `Λ'`
attached to different fields `E` and `E'`
(blueprint: prop-pur-weil-equivariance-u-compatibility). -/
theorem uCompatibilityAssembly (C : ScalarSixPullbackData.{u}) :
    UCompatibility ell D C := by
  sorry

/-- The complete condensed statement of the item. The coefficient equations are
explicit above. CompositionCompatible retains the f-trace at g* K(e)[2e] before
the g-trace; BaseChangeCompatible retains the actual proper/open exchange and
source comparison. Both concern the same normalized family as the parent gamma.
Coherent retains the compositor/exchange pasting equation and all normalizations.
The last record gives coefficient and pullback preservation of the specified kappa,
including identities, towers, mixed changes and model composition.
Source: current blueprint prop-pur-weil-equivariance-compatibilities.md, order 3548,
and its proof, coefficient/composition/base-change and scheme-identification clauses
(blueprint: prop-pur-weil-equivariance-compatibilities).
Proof: use the repaired condensed parent for the three geometric squares. For a listed
coefficient map, transpose the inverse canonical compact-support comparison followed by
the scalar counit. Normalized scalar trace compatibility and uniqueness of the purity
comparison give the purity equation; the adjunction Hom equivalence gives the counit
equation, and naturality of compact-support scalar comparison gives the trace equation.
The normalized family's CompositionCompatible equation applies the f-trace at the
still-twisted g-source and then the g-trace. Uniqueness of counit-compatible purity and
conjugacy of the compact-support compositor identify the other two pasted squares.
For Cartesian base change the same argument uses sourceBaseChange and the canonical
proper/open exchange; the counit is its transpose. The Coherent compositor/exchange
law identifies horizontal and vertical pasting, independently of compactifications.
Use lem-pur-condensed-operation-comparisons for scalar_exchange, scalar_composition,
and successive base-change rectangles, identifying its coherent data by uniqueness.
Use lem-pur-condensed-purity-coefficient-change for normalized Tate coordinates,
Frobenius preservation, scalar associators and all endpoint identities; uniqueness
of the normalized adjunction family identifies its family with normalizedFamily.
Finally expand every u as kappa followed by its geometric datum. Naturality of kappa
and the corresponding geometric square give each of the three scheme squares.
Its scalar and pullback coherence equations commute with all preceding transports,
including nonflat reduction. No Cartesian exchange for scheme Frobenius is invoked. -/
theorem weilEquivarianceCompatibilities
    (R : ScalarExceptionalAdjoint (c.bundled.{u} ell) cf)
    (C : ScalarSixPullbackData.{u}) :
    ThreeCondensedSquares ell D hEll E c hc f₀ d cf R ∧
    SchemeThreeSquares ell D hEll E c hc f₀ d cf R ∧
    CoefficientEquations ell D hEll ∧
    OperationCompatibilities ell D hEll ∧
    TateCoefficientCompatibilities ell D hEll ∧
    CompositionEquations ell D hEll E ∧
    BaseChangeEquations ell D hEll E ∧
    ScalarCompatible ell D (normalizedFamily ell D hEll) ∧
    CompositionCompatible ell D hEll (normalizedFamily ell D hEll) ∧
    BaseChangeCompatible ell D (normalizedFamily ell D hEll) ∧
    CompactSupportComposition.Coherent (c.obj ell) D.k ∧
    UCompatibility ell D C ∧
    CondensedFrobeniusComparisonCoherence D ell E C := by
  let hnorm := (existsUniqueNormalizedFamily ell D hEll).choose_spec
  let hcomp :=
    AlgebraicGeometry.ProEtale.PurityCoefficientChange.condensed_purity_coefficient_change
      ell D hEll
  rcases hcomp with ⟨A, hBrown, hScalar, hBase, hCompA, hAffine, P, hP, hF, hComp, hId⟩
  have hAeq : A = normalizedFamily ell D hEll :=
    (existsUniqueNormalizedFamily ell D hEll).choose_spec.2 A
      ⟨hBrown, hScalar, hBase, hCompA, hAffine⟩
  let hop :=
    AlgebraicGeometry.ProEtale.CondensedRing.OperationComparisons.condensedOperationComparisons
      D ell hEll
  letI : Fact D.p.Prime := ⟨D.prime⟩
  let hcsc :=
    AlgebraicGeometry.ProEtale.CondensedRing.CompactSupportComposition.coherent_exists
      ell D.p (Ne.symm hEll) D.k (c.obj ell)
      (by exact PurityCoefficientChange.coefficientAdmissible ell c)
  have hcore :=
    schemeCoefficientCompositionBaseChangeCompatibilities ell D hEll E c hc f₀ d cf R
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact weilEquivarianceOfPurityAndTrace ell D hEll E c hc f₀ d cf R
  · exact hcore.1
  · exact hcore.2.1
  · rcases hop with ⟨S, hS⟩
    refine ⟨S, hS, ?_⟩
    intro E c hc
    exact (coefficientCoherent_existsUnique ell D hEll E c hc).choose_spec.2
      (S.coherent (c.bundled.{u} ell) (coefficientIsCoefficient ell E c hc)) trivial
  · simpa [TateCoefficientCompatibilities, hAeq] using
      (show ∃ P, PurityCoefficientChange.Equations ell D hEll
          (normalizedFamily ell D hEll) P ∧
        PurityCoefficientChange.FrobeniusCompatible ell D P ∧
        PurityCoefficientChange.CompositionCoherent ell D hEll P ∧
        PurityCoefficientChange.IdentityCoherent ell D hEll P from
        ⟨P, by simpa [hAeq] using hP, hF, hComp, hId⟩)
  · exact hcore.2.2.1
  · exact hcore.2.2.2
  · exact hnorm.1.2.1
  · exact hnorm.1.2.2.2.1
  · exact hnorm.1.2.2.1
  · exact hcsc
  · exact uCompatibilityAssembly ell D C
  · exact condensedFrobeniusComparison_coherence D ell hEll E C


end WeilConjectures.PurityWeil.Compatibilities
