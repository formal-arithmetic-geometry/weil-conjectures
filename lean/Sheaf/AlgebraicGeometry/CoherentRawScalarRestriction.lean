/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentHigherImageClasses
import Sheaf.AlgebraicGeometry.SheafHDerivedNaturality
import Sheaf.AlgebraicGeometry.RawRestrictedResolutionNaturality
import Sheaf.AlgebraicGeometry.RawRestrictedResolutionRestriction
import Sheaf.AlgebraicGeometry.RawScalarRestrictionAux
import Sheaf.AlgebraicGeometry.RawEvaluationFormulaAux

/-! # Local scalars and restriction before higher-image sheafification

Source: Stacks Project, Tags 03Q8 and 03DR.
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
attribute [local irreducible] affineRealizationRawEquiv coherentEtaleMap
  tensorPullback tensorPullbackObj coherentEtaleRestrictionIso
  Etale.sheafHDerivedEquiv Etale.sheafHToDerived CategoryTheory.derivedExtEvaluation
  Etale.rawRestrictedCohomologyComparison
  Etale.rawAffineComplexPullback Etale.normalizationCohomologyRestriction
  Etale.upperStarComp Etale.upperStar Etale.cohomology Etale.rightDerivedGlobalSections
  Etale.normalizationRestrictedIso Etale.normalizationPresheafComplex
attribute [local instance] Etale.RawRestrictedComparison.etaleComposition
  Etale.RawRestrictedComparison.etaleIdentities Etale.RawRestrictedComparison.etalePullbacks
  Etale.RawRestrictedComparison.etaleBaseChange Etale.RawRestrictedComparison.sheafifyInstance
  Etale.RawRestrictedComparison.weakSheafifyInstance

attribute [local irreducible] restrictionScalar


private theorem cancel_comparison_square {C : Type*} [Category* C]
    {A A' B B' D D' : C} (r : A ⟶ A') (c : A ⟶ B) (c' : A' ⟶ B')
    (p : B ⟶ B') (i : B ⟶ D) (i' : B' ⟶ D') [Mono i'] (t : D ⟶ D')
    (hn : r ≫ c' ≫ i' = c ≫ i ≫ t) (hp : p ≫ i' = i ≫ t) :
    r ≫ c' = c ≫ p := by
  apply (cancel_mono i').mp
  simpa only [Category.assoc, hp] using hn

private theorem raw_restriction_formula {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {V V' : S.Etale} (h : V' ⟶ V)
    (z : (Etale.abelianHigherDirectImageRawPresheaf f q F).obj (op V)) :
    Etale.rawRestrictedCohomologyComparison f q F V'
        ((Etale.abelianHigherDirectImageRawPresheaf f q F).map h.op z) =
      Etale.normalizationCohomologyRestriction f q F h
        (Etale.rawRestrictedCohomologyComparison f q F V z) := by
  let I := injectiveResolution F
  have hp := Etale.rawRestrictedResolution_restriction f q F h
  have he := cancel_comparison_square
    ((Etale.abelianHigherDirectImageRawPresheaf f q F).map h.op)
    (Etale.rawRestrictedCohomologyComparison f q F V)
    (Etale.rawRestrictedCohomologyComparison f q F V')
    (Etale.normalizationCohomologyRestriction f q F h)
    (Etale.normalizationRestrictedIso f q F I V).hom
    (Etale.normalizationRestrictedIso f q F I V').hom
    (((Etale.normalizationPresheafComplex f F I).homology (q : ℤ)).map h.op)
    (Etale.rawRestrictedResolution_naturality f q F h.op)
    hp
  exact ConcreteCategory.congr_hom he z



private theorem evaluation_conjugation {C : Type*} [Category* C]
    (D : C ⥤ AddCommGrpCat.{v}) {F F' : C} (K : F ≅ F')
    {A : AddCommGrpCat.{v}} {B : Type*} [AddCommGroup B]
    (c : A ⟶ D.obj F) (e : A ≃+ B) (t : B → D.obj F')
    (he : ∀ z, t (e z) = D.map K.hom (c z))
    (m : F' ⟶ F') (μ : B → B) (ht : ∀ x, t (μ x) = D.map m (t x)) (z : A) :
    c (e.symm (μ (e z))) = D.map (K.hom ≫ m ≫ K.inv) (c z) := by
  have h := he (e.symm (μ (e z)))
  rw [e.apply_symm_apply, ht, he] at h
  apply (D.mapIso K).addCommGroupIsoToAddEquiv.injective
  change D.map K.hom _ = D.map K.hom (D.map (K.hom ≫ m ≫ K.inv) _)
  have hm : (K.hom ≫ m ≫ K.inv) ≫ K.hom = K.hom ≫ m := by simp
  have hs : D.map (K.hom ≫ m ≫ K.inv) ≫ D.map K.hom =
      D.map K.hom ≫ D.map m := by rw [← D.map_comp, hm, D.map_comp]
  exact h.symm.trans (ConcreteCategory.congr_hom hs _).symm

private theorem raw_scalar_formula {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) [G.IsQuasicoherent] (q : ℕ) (V : S.Etale)
    (r : Γ(Limits.pullback V.hom f, ⊤))
    (z : (Etale.abelianHigherDirectImageRawPresheaf f q
      (liftedCoherentEtaleSheaf G)).obj (op V)) :
    Etale.rawRestrictedCohomologyComparison f q (liftedCoherentEtaleSheaf G) V
        ((affineRealizationRawEquiv f G q V).symm
          (Sheaf.H.map (coherentEtaleMap _ _
            ((affineRealizationCoefficient f G V).smulHom r)) q
              (affineRealizationRawEquiv f G q V z))) =
      (Etale.cohomology AddCommGrpCat.{u + 1} (Limits.pullback V.hom f) (q : ℤ)).map
        (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
          (restrictionScalar (pullback.snd V.hom f) G r)))
            (Etale.rawRestrictedCohomologyComparison f q (liftedCoherentEtaleSheaf G) V z) := by
  let K := coherentEtaleRestrictionIso (pullback.snd V.hom f) G
  let c := Etale.rawRestrictedCohomologyComparison f q (liftedCoherentEtaleSheaf G) V
  let T := CochainComplex.singleFunctor
    (Sheaf (Limits.pullback V.hom f).smallEtaleTopology AddCommGrpCat.{u + 1}) 0
  let H := Etale.cohomology AddCommGrpCat.{u + 1} (Limits.pullback V.hom f) (q : ℤ)
  let D : Sheaf (Limits.pullback V.hom f).smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      AddCommGrpCat.{u + 1} :=
    { T ⋙ DerivedCategory.Q ⋙ H with
      obj A := H.obj (DerivedCategory.Q.obj (T.obj A))
      map φ := H.map (DerivedCategory.Q.map (T.map φ)) }
  let m := coherentEtaleMap _ _ ((affineRealizationCoefficient f G V).smulHom r)
  unfold restrictionScalar
  exact evaluation_conjugation D K c (affineRealizationRawEquiv f G q V)
    (Etale.sheafHToDerived _ q) (raw_evaluation_formula_aux f G q V)
    m (Sheaf.H.map m q) (Etale.sheafHToDerived_map m q) z



private theorem square_transport {A A' B B' : Type*}
    (r : A → A') (c : A → B) (c' : A' → B') (p : B → B')
    (m : A → A) (m' : A' → A') (n : B → B) (n' : B' → B')
    (hi : Function.Injective c') (hr : ∀ z, c' (r z) = p (c z))
    (hm : ∀ z, c (m z) = n (c z)) (hm' : ∀ z, c' (m' z) = n' (c' z))
    (hs : ∀ y, p (n y) = n' (p y)) (z : A) : r (m z) = m' (r z) := by
  apply hi
  exact (hr (m z)).trans ((congrArg p (hm z)).trans
    ((hs (c z)).trans ((congrArg n' (hr z).symm).trans (hm' (r z)).symm)))

/-- Raw restriction intertwines multiplication by a function on the source chart
with multiplication by its pullback on the target chart.
Source: Stacks Project, Tag 03Q8, lemma-higher-direct-images; Descent, Tag 03DR.
(blueprint: lem-weil-pbc-coherent-raw-scalar-restriction).

Proof: Write B(V) for V times_S X and b:B(V') to B(V) for the map induced by h.
The raw evaluation comparison identifies raw restriction with cohomological
pullback along b, followed by inverse-image composition on coefficients. Use
the fixed-resolution naturality and restriction comparisons for the restriction
square. The defining evaluation formula and coefficient naturality of
sheafHToDerived transport multiplication through the fixed evaluation equivalences.
The normalized coherent restriction isomorphism sends sections by the inverse
tensor-composition isomorphism. On each etale object over B(V'), this isomorphism
intertwines multiplication by a function c on B(V) with multiplication by
b.appTop c: tensor pullback carries scalar multiplication to multiplication by
the pulled-back scalar, and its composition isomorphisms are module-linear.
Apply coefficient naturality of cohomology pullback to this square. The identity
b followed by the first projection equals the first projection followed by h
identifies b.appTop of the pullback of a with the pullback of h.appTop a.
Conjugate this cohomology identity by the two fixed raw evaluation equivalences.
Their inverse pairs cancel and give exactly the displayed formula. This argument
is on cohomology before sheafification: it constructs no higher-image action and
uses no surjectivity of the map from cohomology classes to higher-image sections.
For q=0 this is restriction of scalar multiples of sections. For zero coefficients
and empty charts both sides are zero; identity arrows follow by cancellation. -/
theorem coherentRawScalarRestriction {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) [G.IsQuasicoherent] (q : ℕ) {V V' : S.Etale} (h : V' ⟶ V)
    (a : Γ(V.left, ⊤))
    (z : (Etale.abelianHigherDirectImageRawPresheaf f q
      (liftedCoherentEtaleSheaf G)).obj (op V)) :
    (Etale.abelianHigherDirectImageRawPresheaf f q
        (liftedCoherentEtaleSheaf G)).map h.op
      ((affineRealizationRawEquiv f G q V).symm
        (Sheaf.H.map (coherentEtaleMap _ _
          ((affineRealizationCoefficient f G V).smulHom
            ((Limits.pullback.fst V.hom f).appTop a))) q
              (affineRealizationRawEquiv f G q V z))) =
      (affineRealizationRawEquiv f G q V').symm
        (Sheaf.H.map (coherentEtaleMap _ _
          ((affineRealizationCoefficient f G V').smulHom
            ((Limits.pullback.fst V'.hom f).appTop (h.left.appTop a)))) q
              (affineRealizationRawEquiv f G q V'
                ((Etale.abelianHigherDirectImageRawPresheaf f q
                  (liftedCoherentEtaleSheaf G)).map h.op z)))  := by
  let F := liftedCoherentEtaleSheaf G
  let j := pullback.snd V.hom f
  let k := pullback.snd V'.hom f
  let b := Etale.normalizationChartMap f h
  have hk : k = b ≫ j :=
    (MorphismProperty.Over.w ((MorphismProperty.Over.pullback @Etale ⊤ f).map h)).symm
  have : AlgebraicGeometry.Etale b := by
    have : AlgebraicGeometry.Etale (b ≫ j) := by rw [← hk]; infer_instance
    exact AlgebraicGeometry.Etale.of_comp b j
  let r := (pullback.fst V.hom f).appTop a
  have hr : b.appTop r = (pullback.fst V'.hom f).appTop (h.left.appTop a) := by
    change b.appTop ((pullback.fst V.hom f).appTop a) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
    have hp : b ≫ pullback.fst V.hom f = pullback.fst V'.hom f ≫ h.left := by
      dsimp only [b, Etale.normalizationChartMap]
      rw [MorphismProperty.Over.pullback_map_left, pullback.lift_fst]
    rw [hp, Scheme.Hom.comp_appTop]
    rfl
  let r' := b.appTop r
  have : IsIso (Etale.rawRestrictedCohomologyComparison f q F V') :=
    Etale.isIso_rawRestrictedCohomologyComparison f q F V'
  let c := Etale.rawRestrictedCohomologyComparison f q F V
  let c' := Etale.rawRestrictedCohomologyComparison f q F V'
  let s := normalizationCohomologySquare f q F h
    (restrictionScalar j G r) (restrictionScalar k G r')
    (restrictionScalar_comp_aux j b k hk G r)
  let p := s.pullbackMap
  let n : Etale.rawAffineRestrictedCohomology f q F V ⟶
      Etale.rawAffineRestrictedCohomology f q F V := s.sourceAction
  let n' : Etale.rawAffineRestrictedCohomology f q F V' ⟶
      Etale.rawAffineRestrictedCohomology f q F V' := s.targetAction
  have hp : Etale.normalizationCohomologyRestriction f q F h = p := by
    exact s.pullback_formula.symm
  have hres (y : (Etale.abelianHigherDirectImageRawPresheaf f q F).obj (op V)) :=
    (raw_restriction_formula f q F h y).trans
      (ConcreteCategory.congr_hom hp (c y))
  have hs (y : Etale.rawAffineRestrictedCohomology f q F V) :
      p (n y) = n' (p y) :=
    ConcreteCategory.congr_hom s.commutes y
  have hm (y : (Etale.abelianHigherDirectImageRawPresheaf f q F).obj (op V)) :=
    (raw_scalar_formula f G q V r y).trans
      (ConcreteCategory.congr_hom
        (s.source_formula.trans (normalizationCohomologyAction_formula f q F V _))
        (c y)).symm
  have hm' (y : (Etale.abelianHigherDirectImageRawPresheaf f q F).obj (op V')) :=
    (raw_scalar_formula f G q V' r' y).trans
      (ConcreteCategory.congr_hom
        (s.target_formula.trans (normalizationCohomologyAction_formula f q F V' _))
        (c' y)).symm
  have he := square_transport
    ((Etale.abelianHigherDirectImageRawPresheaf f q F).map h.op) c c' p _ _
    n n'
    (ConcreteCategory.bijective_of_isIso c').1
    hres hm hm' hs z
  exact he.trans (congrArg (fun s ↦
    (affineRealizationRawEquiv f G q V').symm
      (Sheaf.H.map (coherentEtaleMap _ _
        ((affineRealizationCoefficient f G V').smulHom s)) q
          (affineRealizationRawEquiv f G q V'
            ((Etale.abelianHigherDirectImageRawPresheaf f q F).map h.op z)))) hr)

end AlgebraicGeometry.Scheme.Modules
