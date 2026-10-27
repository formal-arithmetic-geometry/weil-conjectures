module

public import Sheaf.Paper.ClosedTestChainMateData

public import Sheaf.Paper.ClosedTestKInjectiveSectionModels
public import Sheaf.Paper.ClosedTestDerivedExchangeModel
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

import Sheaf.Paper.ClosedTestChainExchangeNormalization
import Sheaf.Paper.ClosedTestChainUnitNormalization

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # The closed-test chain mate is normalized derived restriction

Source: Stacks Project, proetale.tex, Tag 09BL; derived.tex, Tag 09T5;
sites-cohomology.tex, Tags 08FI, 0D6E and 0D6F; the unit--counit calculation
(blueprint: lem-sfb-closed-test-chain-mate-restriction).

The existing derived exchange, restriction and section-composition maps are reused.
The new maps below are their ordinary chain representatives on the specified tests.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ClosedTestChainMateRestriction

open ClosedTestKInjectiveSectionModels

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem ordinary_pasting {X U T Z : Scheme.{u}} {f : X ⟶ U} {s : Z ⟶ U}
    {h : T ⟶ X} {fZ : T ⟶ Z} (w : CommSq h fZ f s) :
    directSquare Λ w = conjugateIsoEquiv
      ((CondensedRing.upperStarLowerStarAdjunction Λ f).comp
        (CondensedRing.upperStarLowerStarAdjunction Λ h))
      ((CondensedRing.upperStarLowerStarAdjunction Λ s).comp
        (CondensedRing.upperStarLowerStarAdjunction Λ fZ)) (ordinarySquare Λ w) := by
  unfold ordinarySquare directSquare
  rw [conjugateIsoEquiv_trans _ (CondensedRing.upperStarLowerStarAdjunction Λ
      (fZ ≫ s)) _,
    conjugateIsoEquiv_trans _ (CondensedRing.upperStarLowerStarAdjunction Λ (h ≫ f)) _]
  rw [CondensedRing.conjugateIsoEquiv_upperStarComp,
    conjugateIsoEquiv_iso_symm, CondensedRing.conjugateIsoEquiv_upperStarComp]
  have he (p q : T ⟶ U) (hpq : p = q) : conjugateIsoEquiv
      (CondensedRing.upperStarLowerStarAdjunction Λ p)
      (CondensedRing.upperStarLowerStarAdjunction Λ q)
      (eqToIso (congrArg (CondensedRing.upperStar Λ) hpq.symm)) =
      eqToIso (congrArg (CondensedRing.lowerStar Λ) hpq) := by
    cases hpq
    apply Iso.ext
    simp
  rw [he _ _ w.w, Iso.trans_assoc]

private theorem derived_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.rightDerivedFunctorCompIso' (CondensedRing.lowerStar Λ f)
      (CondensedRing.lowerStar Λ g) (CondensedRing.lowerStarComp Λ f g) =
    conjugateIsoEquiv ((ClosedTestDerivedExchangeModel.adj Λ g).comp
      (ClosedTestDerivedExchangeModel.adj Λ f)) (ClosedTestDerivedExchangeModel.adj Λ
        (f ≫ g)) (ClosedTestDerivedExchangeModel.pullComp Λ f g) := by
  apply Iso.ext
  apply Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (CondensedRing.upperStarLowerStarAdjunction Λ f)
    (CondensedRing.upperStarLowerStarAdjunction Λ g)
    (CondensedRing.upperStarLowerStarAdjunction Λ (f ≫ g))
  exact congrArg Iso.hom (CondensedRing.conjugateIsoEquiv_upperStarComp Λ f g).symm

private theorem derived_iso_trans {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C]
    {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    (e : F ≅ G) (d : G ≅ H) :
    Functor.rightDerivedFunctorNatIso (e ≪≫ d) =
      Functor.rightDerivedFunctorNatIso e ≪≫ Functor.rightDerivedFunctorNatIso d := by
  apply Iso.ext
  simp [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans,
    ← Functor.whiskerRight_comp, ← NatTrans.mapHomotopyCategory_comp]

private theorem derived_pasting {X U T Z : Scheme.{u}} {f : X ⟶ U} {s : Z ⟶ U}
    {h : T ⟶ X} {fZ : T ⟶ Z} (w : CommSq h fZ f s) :
    derivedDirectSquare Λ w = conjugateIsoEquiv
      ((ClosedTestDerivedExchangeModel.adj Λ f).comp
        (ClosedTestDerivedExchangeModel.adj Λ h))
      ((ClosedTestDerivedExchangeModel.adj Λ s).comp
        (ClosedTestDerivedExchangeModel.adj Λ fZ))
      (ClosedTestDerivedExchangeModel.square Λ w) := by
  have hcongr (p q : T ⟶ U) (hpq : p = q) :
      conjugateIsoEquiv (ClosedTestDerivedExchangeModel.adj Λ p)
        (ClosedTestDerivedExchangeModel.adj Λ q)
        (eqToIso (congrArg (fun b : T ⟶ U ↦
          ClosedTestDerivedExchangeModel.pull Λ b) hpq.symm)) =
      Functor.rightDerivedFunctorNatIso
        (eqToIso (congrArg (CondensedRing.lowerStar Λ) hpq)) := by
    cases hpq
    ext : 1
    simp [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans]
    rfl
  unfold ClosedTestDerivedExchangeModel.square
  rw [conjugateIsoEquiv_trans _ (ClosedTestDerivedExchangeModel.adj Λ (fZ ≫ s)) _,
    conjugateIsoEquiv_trans _ (ClosedTestDerivedExchangeModel.adj Λ (h ≫ f)) _,
    ← derived_comp, conjugateIsoEquiv_iso_symm, ← derived_comp, hcongr _ _ w.w]
  unfold derivedDirectSquare directSquare
  rw [derived_iso_trans, derived_iso_trans]
  simp only [Functor.rightDerivedFunctorCompIso', Iso.trans_symm,
    Iso.symm_symm_eq, Iso.trans_assoc]
  rfl

private theorem derived_square {X U T Z : Scheme.{u}} {f : X ⟶ U} {s : Z ⟶ U}
    {h : T ⟶ X} {fZ : T ⟶ Z} (w : CommSq h fZ f s) :
    ClosedTestDerivedExchangeModel.square Λ w =
      Functor.mapDerivedCategorySquareIso (ordinarySquare Λ w) := by
  have hcongr (p q : T ⟶ U) (hpq : p = q) :
      (Functor.mapDerivedCategoryNatIso
        (eqToIso (congrArg (CondensedRing.upperStar Λ) hpq))).hom =
      (eqToIso (congrArg (fun b : T ⟶ U ↦
        ClosedTestDerivedExchangeModel.pull Λ b) hpq)).hom := by
    cases hpq
    exact Functor.mapDerivedCategoryNatIso_refl
  apply Iso.ext
  simp only [ClosedTestDerivedExchangeModel.square, ClosedTestDerivedExchangeModel.pullComp,
    Functor.mapDerivedCategorySquareIso, ordinarySquare, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
  rw [hcongr _ _ w.w.symm]

/-- The unit--counit calculation on all sections.
Source: Stacks 09BL (blueprint: lem-sfb-closed-test-chain-mate-restriction).
Proof, steps 1--2 of the node:
1. Use lem-sfb-closed-test-unit-evaluation to transport to section-ring modules,
   preserving the specified adjunctions. Its actual closed-unit map is invertible;
   the literal direct-image formulas identify the source and target with F(T) and
   (h*F)(T0). Thus calculate Ex-zero after the actual unit, without inverting exchange.
2. Expand Adjunction.squareExchange. Unit insertion carries x to fZ-inverse-image of
   s-inverse-image of x; ordinarySquare identifies this with h-inverse-image of
   f-inverse-image of x. The counit sends an inverse-image generator (W, phi, y) to
   restriction of y along phi: this is the adjunct of the identity of f_*F.
   At W=B, phi=identity and y=x it returns x. Restricting after h-inverse-image is
   therefore exactly the inverse-image unit along testArrow. Coefficients from the
   point use the same module adjunctions, so the equality is linear and natural in F. -/
theorem closed_test_mate_sections
    (A : Type u) [CommRing A] (a : Ideal A)
    {X XZ : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of A))
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ a)))
    (w : IsPullback h fZ f (closedMap A a))
    (V : (Spec (.of (A ⧸ a))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ((liftedTest A a V).left, ⊤)] :
    Functor.whiskerLeft (CondensedRing.lowerStar Λ f) (closedUnit Λ A a V) ≫
        (Functor.associator (CondensedRing.lowerStar Λ f)
          (CondensedRing.upperStar Λ (closedMap A a))
          (evaluation Λ (closedTest A a V))).inv ≫
        Functor.whiskerRight (ordinaryExchange Λ w.toCommSq)
          (evaluation Λ (closedTest A a V)) ≫
        (Functor.associator (CondensedRing.upperStar Λ h)
          (CondensedRing.lowerStar Λ fZ) (evaluation Λ (closedTest A a V))).hom ≫
        Functor.whiskerLeft (CondensedRing.upperStar Λ h)
          (pushEvaluation Λ fZ (closedTest A a V)).hom =
      (pushEvaluation Λ f (liftedTest A a V)).hom ≫ testSectionUnit Λ A a w V := by
  sorry


private theorem evaluatedChainMate_eq_sectionChain
    (A : Type u) [CommRing A] (a : Ideal A)
    {X XZ : Scheme.{u}} [IsAffine X] {f : X ⟶ Spec (.of A)}
    {h : XZ ⟶ X} {fZ : XZ ⟶ Spec (.of (A ⧸ a))}
    (w : IsPullback h fZ f (closedMap A a))
    (V : (Spec (.of (A ⧸ a))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ((liftedTest A a V).left, ⊤)]
    (L : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ)
    (J : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology XZ) Ab.{u + 1})
      (condensedRingObj Λ XZ)) ℤ)
    (j : (complexes (CondensedRing.upperStar Λ h)).obj L ⟶ J) :
    evaluatedChainMate Λ A a w V L J j = sectionChain Λ A a w V L J j := by
  have he : evaluatedExchange Λ A a f h fZ w V = testSectionUnit Λ A a w V := by
    unfold evaluatedExchange
    apply (Iso.inv_comp_eq (pushEvaluation Λ f (liftedTest A a V))).2
    simpa only [Category.assoc] using closed_test_mate_sections Λ A a f h fZ w V
  unfold evaluatedChainMate sectionChain
  rw [he]

/-- The chain mate represents the actual derived exchange and evaluates to the normalized
restriction chain map. Under the specified section-localization maps it is the derived
unit followed by global-section composition, with the canonical coefficient identification.
Source: Stacks 09BL, 09T5, 08FI, 0D6E, 0D6F
(blueprint: lem-sfb-closed-test-chain-mate-restriction).

Proof, steps 3--6 of the node:
3. lem-sfb-closed-test-kinjective-section-models gives pushModel for L and J.
   Apply lem-sfb-resolving-derived-adjunction-normalization to f and fZ. Exactness makes
   their left comparisons the localization identifications. The ordinary adjunct of
   chainMate is j composed with h* of the ordinary counit and theta. On K-injectives
   the normalized derived Hom bijection sends its localized class to h* epsilon theta,
   after cancelling Q(j). Uniqueness of adjuncts gives the first displayed equation.
4. Apply closed_test_mate_sections in every degree of L; naturality makes it commute
   with differentials. Composing with j gives the second equation of chain maps, hence
   the same equality after Q, before taking any cohomology.
5. lem-pur-kinjective-restrict-localized-universes makes the restricted L and J
   K-injective. def-pur-localized-ringed-site identifies their sections degreewise.
   The normalized pullback composition identifies the restriction of j with a resolution
   of a* of the restricted L. The normalized derived Hom bijection identifies the class
   of a_*j followed by the actual unit with the specified derived unit for a.
6. lem-weil-pbc-right-adjoint-preserves-kinjective makes a_* of the restricted J
   K-injective. Apply lem-weil-pbc-ringed-topoi-derived-pushforward-composition to a
   and sections, allowing the identity resolution. Its comparison is the degreewise
   equality Gamma(T,a_*J0)=Gamma(T0,J0). Therefore the third displayed equation is
   precisely the unit followed by this normalized comparison in D(Ab). -/
theorem closed_test_chain_mate_restriction
    (A : Type u) [CommRing A] (a : Ideal A)
    {X XZ : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of A))
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ a)))
    (w : IsPullback h fZ f (closedMap A a))
    (V : (Spec (.of (A ⧸ a))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ((liftedTest A a V).left, ⊤)]
    (K : DerivedCategory.Plus
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (L : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ)
    [L.IsKInjective] (e : DerivedCategory.Q.obj L ≅ K.obj)
    (J : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology XZ) Ab.{u + 1}) (condensedRingObj Λ XZ)) ℤ)
    [J.IsKInjective] (j : (complexes (CondensedRing.upperStar Λ h)).obj L ⟶ J)
    [QuasiIso j] :
    HEq (DerivedCategory.Q.map (chainMate Λ w.toCommSq L J j) ≫
        pushModel Λ fZ ((CondensedRing.upperStar Λ h).mapDerivedCategory.obj K.obj)
          J (pullRepresentative Λ h K.obj L e J j))
      ((CondensedRing.upperStar Λ (closedMap A a)).mapDerivedCategoryFactors.inv.app
          ((complexes (CondensedRing.lowerStar Λ f)).obj L) ≫
        (CondensedRing.upperStar Λ (closedMap A a)).mapDerivedCategory.map
          (pushModel Λ f K.obj L e) ≫
        (ClosedTestDerivedExchangeModel.exchange Λ w.toCommSq).app K.obj) ∧
    evaluatedChainMate Λ A a w V L J j = sectionChain Λ A a w V L J j ∧
    HEq (DerivedCategory.Q.map (sectionChain Λ A a w V L J j) ≫
        globalLocalizationModel Λ (testFibre fZ (closedTest A a V))
          ((CondensedRing.upperStar Λ h).mapDerivedCategory.obj K.obj)
          J (pullRepresentative Λ h K.obj L e J j))
      (globalLocalizationModel Λ (testFibre f (liftedTest A a V)) K.obj L e ≫
        (ClosedTestDerivedExchangeModel.restriction Λ (testArrow A a w V)).app
          ((CondensedRing.upperStar Λ
            (testFibre f (liftedTest A a V)).hom).mapDerivedCategory.obj K.obj) ≫
        (condensedModuleSections Λ
          (testFibre fZ (closedTest A a V)).left).rightDerivedFunctor.map
            ((derivedTestPullbackComposition Λ A a w V).inv.app K.obj)) := by
  refine ⟨?_, evaluatedChainMate_eq_sectionChain Λ A a w V L J j, ?_⟩
  · exact closed_test_chain_exchange_normalization Λ A a f h fZ w V K L e J j
  · exact closed_test_chain_unit_normalization Λ A a f h fZ w V K L e J j


/-- Both ordinary and derived localized pasting comparisons are the conjugates under
the specified adjunctions. Conjugacy is exactly preservation of their units and counits.
Source: Stacks 09T5, 0D6E; normalization of the localized section identities
(blueprint: lem-sfb-closed-test-chain-mate-restriction).

Proof, step 7 of the node: conjugation reverses composition and preserves inverses.
The ordinary pushforward compositors are conjugate to the specified pullback compositors;
transport along the commutativity equality is conjugate by equality induction. This
identifies directSquare with the ordinary conjugate for every commutative square.
For the derived compositors, use the existing representative-normalized theorem
rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv. Right derivation preserves composition
of natural isomorphisms, and equality induction treats the middle transport. Finally,
mapDerivedCategorySquareIso identifies the exact localization of ordinarySquare with
square. Apply these identities to the test square and the three displayed pasting squares. -/
theorem closed_test_localized_adjunctions
    (A : Type u) [CommRing A] (a : Ideal A)
    {X XZ : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of A))
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ a)))
    (w : IsPullback h fZ f (closedMap A a))
    (V : (Spec (.of (A ⧸ a))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ((liftedTest A a V).left, ⊤)] :
    HEq (directSquare Λ (h := testArrow A a w V)
      (fZ := (testFibre fZ (closedTest A a V)).hom)
      (f := (testFibre f (liftedTest A a V)).hom) (s := h)
      (CommSq.mk (pullback.lift_snd _ _ _)))
      (conjugateIsoEquiv
        ((CondensedRing.upperStarLowerStarAdjunction Λ
          (testFibre f (liftedTest A a V)).hom).comp
            (CondensedRing.upperStarLowerStarAdjunction Λ (testArrow A a w V)))
        ((CondensedRing.upperStarLowerStarAdjunction Λ h).comp
          (CondensedRing.upperStarLowerStarAdjunction Λ
            (testFibre fZ (closedTest A a V)).hom))
        (testPullbackComposition Λ A a w V)) ∧
    HEq (derivedDirectSquare Λ (h := testArrow A a w V)
      (fZ := (testFibre fZ (closedTest A a V)).hom)
      (f := (testFibre f (liftedTest A a V)).hom) (s := h)
      (CommSq.mk (pullback.lift_snd _ _ _)))
      (conjugateIsoEquiv
        ((ClosedTestDerivedExchangeModel.adj Λ (testFibre f (liftedTest A a V)).hom).comp
          (ClosedTestDerivedExchangeModel.adj Λ (testArrow A a w V)))
        ((ClosedTestDerivedExchangeModel.adj Λ h).comp
          (ClosedTestDerivedExchangeModel.adj Λ (testFibre fZ (closedTest A a V)).hom))
        (derivedTestPullbackComposition Λ A a w V)) ∧
    pastingAdjunctionCompatible Λ
      (h := (testFibre f (liftedTest A a V)).hom)
      (fZ := pullback.fst (liftedTest A a V).hom f)
      (f := f) (s := (liftedTest A a V).hom) (CommSq.mk pullback.condition.symm) ∧
    pastingAdjunctionCompatible Λ
      (h := (testFibre fZ (closedTest A a V)).hom)
      (fZ := pullback.fst (closedTest A a V).hom fZ)
      (f := fZ) (s := (closedTest A a V).hom) (CommSq.mk pullback.condition.symm) ∧
    pastingAdjunctionCompatible Λ
      (h := Scheme.AffineProEt.closedSiteLiftInclusion A a V)
      (fZ := V.hom) (f := (liftedTest A a V).hom) (s := closedMap A a)
      (((Scheme.AffineProEt.affine_closed_site_functor_properties A a).2.2.2.2.2.2.2
        V).2.1.toCommSq) := by
  have ordinary {X U T Z : Scheme.{u}} {f : X ⟶ U} {s : Z ⟶ U}
      {h : T ⟶ X} {fZ : T ⟶ Z} (q : CommSq h fZ f s) :
      pastingAdjunctionCompatible Λ q :=
    ⟨heq_of_eq (ordinary_pasting Λ q), heq_of_eq (derived_pasting Λ q)⟩
  refine ⟨?_, ?_, ordinary _, ordinary _, ordinary _⟩
  · exact heq_of_eq (ordinary_pasting Λ
      (CommSq.mk (pullback.lift_snd _ _ _)))
  · have hp := derived_pasting Λ (h := testArrow A a w V)
      (fZ := (testFibre fZ (closedTest A a V)).hom)
      (f := (testFibre f (liftedTest A a V)).hom) (s := h)
      (CommSq.mk (pullback.lift_snd _ _ _))
    rw [derived_square] at hp
    exact heq_of_eq hp

end AlgebraicGeometry.ProEtale.ClosedTestChainMateRestriction
