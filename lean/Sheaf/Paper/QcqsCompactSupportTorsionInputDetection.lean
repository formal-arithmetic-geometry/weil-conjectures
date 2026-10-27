/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups B9, E2
-/
module

public import Sheaf.Paper.CompactSupportFiniteAction
public import Sheaf.Paper.IntegralCompactSupportCoefficientData
import Sheaf.Paper.QcqsCompactSupportNormalizedIsoExistence
import Sheaf.Paper.QcqsCompactSupportFiniteComparison
import Sheaf.Paper.QcqsCompactSupportTorsionCoefficientAction
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import all Sheaf.Paper.IntegralPrincipalConeQuotientAugmentation
import Sheaf.Paper.AdicReductionTriangle
import Sheaf.Paper.IntegralReductionShiftedHomFiniteAlgClosed
import Sheaf.Paper.DerivedCompleteFiniteReductionDetection

/-! # Finite-coefficient inputs detect compact-support comparisons

Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7; Stacks 0941, 0F7J
(blueprint: lem-qcqs-compact-support-torsion-input-detection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport CategoryTheory.Pretriangulated

private theorem reduction_naturality
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    {F G : C ⥤ D} {V : D ⥤ B} {L : C ⥤ A} {H : A ⥤ B}
    (e : G ⋙ V ≅ L ⋙ H) (τ τ' : F ⟶ G) {K Q : C} (q : K ⟶ Q)
    (r : L.obj Q ⟶ L.obj K) (hqr : L.map q ≫ r = 𝟙 _)
    (h : τ.app Q = τ'.app Q) : V.map (τ.app K) = V.map (τ'.app K) := by
  have hn : τ.app K ≫ G.map q = τ'.app K ≫ G.map q := by
    rw [← τ.naturality, ← τ'.naturality, h]
  let v := e.hom.app Q ≫ H.map r ≫ e.inv.app K
  have hr : V.map (G.map q) ≫ v = 𝟙 _ := by
    change V.map (G.map q) ≫ e.hom.app Q ≫ H.map r ≫ e.inv.app K = _
    have he : V.map (G.map q) ≫ e.hom.app Q =
        e.hom.app K ≫ H.map (L.map q) := e.hom.naturality q
    rw [← Category.assoc (V.map (G.map q)), he]
    change (e.hom.app K ≫ H.map (L.map q)) ≫ H.map r ≫ e.inv.app K = _
    rw [Category.assoc, ← Category.assoc (H.map (L.map q)), ← H.map_comp, hqr,
      H.map_id, Category.id_comp, Iso.hom_inv_id_app]
    rfl
  have hm : Mono (V.map (G.map q)) := mono_of_mono_fac hr
  apply (cancel_mono (V.map (G.map q))).mp
  simpa only [← V.map_comp] using congrArg V.map hn

private theorem quotient_constructible
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Scheme.{u}) (K : sfIntegralConstructibleCategory l E W) (n : ℕ) :
    sfIntegralConstructible l E W
      ((scalarReductionDerivedRestriction.{u, u} l E W n).obj
        ((scalarReductionDerivedExtension.{u, u} l E W n).obj K.obj)) := by
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} W
  let : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} W
  let R := completedIntegralCommRingSheafUnrestricted.{u, u} l E W
  let S := integralCoefficientCommRingSheaf.{u, u} l E W n
  let φ : R ⟶ S := completedIntegralCommRingProjectionUnrestricted.{u, u} l E W n
  let f : SheafOfModules.unit ((adicLisseForget W).obj R) ⟶
      SheafOfModules.unit ((adicLisseForget W).obj R) :=
    (SheafOfModules.RegularQuotientCone.scalar R (uniformizerPower.{u, u} l E W n)).app _
  let p : SheafOfModules.unit ((adicLisseForget W).obj R) ⟶
      (pbcRestrict φ).obj (SheafOfModules.unit ((adicLisseForget W).obj S)) :=
    SheafOfModules.RegularQuotientCone.ringMap φ
  have he := regularExact.{u, u} l E W n
  change ∃ hz : f ≫ p = 0, (ShortComplex.mk f p hz).ShortExact at he
  obtain ⟨hz, hs⟩ := he
  have hp (U : W.ProEtᵒᵖ) : p.val.app U (1 : R.obj.obj U) = (1 : S.obj.obj U) := by
    change (φ.hom.app U).hom 1 * 1 = 1
    rw [map_one, one_mul]
  obtain ⟨a, δ, hT, _⟩ := pbc_adic_reduction_triangle.{u} W φ f p hp hz hs K.obj
  let := sfIntegralConstructible_isTriangulated l E W
  have hQ : sfIntegralConstructible l E W
      ((pbcDerivedRestrict.{u} φ).obj ((pbcDerivedExtend.{u} φ).obj K.obj)) :=
    (sfIntegralConstructible l E W).ext_of_isTriangulatedClosed₃
      (Triangle.mk a ((pbcDerivedScalarAdjunction.{u} φ).unit.app K.obj) δ)
      hT K.property K.property
  let e : pbcDerivedExtend.{u} φ ≅ scalarReductionDerivedExtension.{u, u} l E W n :=
    (pbcDerivedScalarAdjunction.{u} φ).leftAdjointUniq
    (derivedScalarExtensionRestrictionAdjunction.{u, u} l E W n).choose
  exact (sfIntegralConstructible l E W).prop_of_iso
    ((scalarReductionDerivedRestriction.{u, u} l E W n).mapIso (e.app K.obj)) hQ

private theorem reduction_map_ext_on_restriction
    {A B : Type*} [Category A] [Category B] {L : A ⥤ B} {R : B ⥤ A}
    (a : L ⊣ R) {P Q : A} (hQ : R.essImage Q) {f g : P ⟶ Q}
    (h : L.map f = L.map g) : f = g := by
  obtain ⟨N, ⟨e⟩⟩ := hQ
  apply (cancel_mono e.inv).mp
  apply (a.homEquiv P N).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, h]

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- Agreement on finite-coefficient inputs gives equality after every finite reduction.
This is the finite-evaluation part of the torsion-input detection argument, without
asserting that finite evaluations detect arbitrary derived morphisms.

Source: the quotient-input/naturality step of
`lem-qcqs-compact-support-torsion-input-detection`; Bhatt--Scholze, Section 3.5;
Mathlib's scalar-adjunction triangle identity.
Proof: for a constructible integral input K, let Q be the restriction of its nth
finite derived reduction. The completed coefficient principal short exact sequence
and the derived reduction triangle express Q as a cone between two copies of K.
The integral constructible property is triangulated, so Q is a permissible test
input. Let q : K -> Q be the scalar-adjunction unit. Its nth scalar extension has
the adjunction counit as a retraction. The actual compact-support reduction mate
is invertible on constructible inputs. Composing these mates with the independent
normalized realization isomorphism gives a natural finite-reduction isomorphism
for the recorded integral functor. Under this isomorphism, the image of q also
has a retraction. Naturality of the two transformations at q and their equality
at Q now give equality of their reduced components at K by cancellation.
Index zero means exponent one; the construction includes zero inputs and empty
schemes, without any finite-field or separatedness hypothesis on the base schemes. -/
private theorem torsion_input_reduction_eq
    (τ τ' : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ⟶
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι)
    (h : ∀ (n : ℕ) (K : sfIntegralConstructibleCategory l E X),
      (scalarReductionDerivedRestriction.{u, u} l E X n).essImage K.obj →
        τ.app K = τ'.app K)
    (K : sfIntegralConstructibleCategory l E X) (n : ℕ) :
    (scalarReductionDerivedExtension.{u, u} l E Y n).map (τ.app K) =
      (scalarReductionDerivedExtension.{u, u} l E Y n).map (τ'.app K) := by
  classical
  let I := (sfIntegralConstructible l E X).ι
  let F := I ⋙ image (completed l E) c
  let G := sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
    (sfIntegralConstructible l E Y).ι
  let LX := scalarReductionDerivedExtension.{u, u} l E X n
  let RX := scalarReductionDerivedRestriction.{u, u} l E X n
  let LY := scalarReductionDerivedExtension.{u, u} l E Y n
  let H := sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c
  let a := (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose
  let Q : sfIntegralConstructibleCategory l E X :=
    ⟨RX.obj (LX.obj K.obj), quotient_constructible l E X K n⟩
  let q : K ⟶ Q := ObjectProperty.homMk (a.unit.app K.obj)
  let r := a.counit.app (LX.obj K.obj)
  have hqr : (I ⋙ LX).map q ≫ r = 𝟙 _ := a.left_triangle_components K.obj
  obtain ⟨σ, _⟩ := sfQcqsCompactSupport_normalizedIso_exists l E K₀ hl c
  let m := Functor.whiskerLeft I
    (comparison (reduction l E (n + 1) (Nat.le_add_left 1 n)) c)
  have hm (P : sfIntegralConstructibleCategory l E X) : IsIso (m.app P) :=
    (sfQcqsCompactSupport_finiteComparison l E K₀ hl c P).2 n
  let : ∀ P, IsIso (m.app P) := hm
  let : IsIso m := NatIso.isIso_of_isIso_app m
  let eF : F ⋙ LY ≅ (I ⋙ LX) ⋙ H :=
    Functor.isoWhiskerLeft F (finiteReductionIso l E Y n).symm ≪≫
    asIso m ≪≫
    Functor.isoWhiskerLeft I
      (Functor.isoWhiskerLeft
        (pbcDerivedExtend (projection l E (n + 1) (Nat.le_add_left 1 n) X))
        (finiteImageIso l E n c) ≪≫
      Functor.isoWhiskerRight (finiteReductionIso l E X n) H)
  let eG : G ⋙ LY ≅ (I ⋙ LX) ⋙ H := Functor.isoWhiskerRight σ.symm LY ≪≫ eF
  exact reduction_naturality eG τ τ' q r hqr
    (h n Q ⟨LX.obj K.obj, ⟨Iso.refl _⟩⟩)

/-- The torsion-input and finite-evaluation hypotheses are equivalent for these
natural compact-support comparisons. This does not identify the transformations.

Source: the quotient-input/naturality step of the torsion-input detection plan and
its parent's scalar-adjunction argument; Bhatt--Scholze, Section 3.5.
(blueprint: lem-qcqs-compact-support-torsion-input-finite-evaluation).

Proof: the forward implication is `torsion_input_reduction_eq`: restrict the finite
reduction of K, prove this test input constructible by the principal tensor triangle,
and use naturality at the scalar-adjunction unit. Its finite image has an explicit
counit retraction, which the natural compact-support finite comparison transports
into a retraction on the output. Cancel that split monomorphism.
For the converse, on a restricted finite input the output of the recorded integral
compact-support functor is again a restriction from the same quotient, by the proved
torsion coefficient action. In any adjunction L adjoint to R, maps into R(N) are
determined by their images under L: compose that image with the counit at N and use
injectivity of the inverse Hom transpose. Transport through the essential-image
isomorphism. Apply this to the equality of reductions at that input and that level.
Both arguments include zero objects, exponent one and empty schemes. -/
theorem sfQcqsCompactSupport_torsion_input_iff_reduction_eq
    (τ τ' : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ⟶
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι) :
    (∀ (n : ℕ) (K : sfIntegralConstructibleCategory l E X),
      (scalarReductionDerivedRestriction.{u, u} l E X n).essImage K.obj →
        τ.app K = τ'.app K) ↔
    (∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
      (scalarReductionDerivedExtension.{u, u} l E Y n).map (τ.app K) =
        (scalarReductionDerivedExtension.{u, u} l E Y n).map (τ'.app K)) := by
  constructor
  · intro h K n
    exact torsion_input_reduction_eq l E K₀ hl c τ τ' h K n
  · intro h n K hK
    exact reduction_map_ext_on_restriction
      (derivedScalarExtensionRestrictionAdjunction.{u, u} l E Y n).choose
      (sfQcqsCompactSupport_torsion_coefficient_action l E K₀ hl c n K hK) (h K n)


/-- Torsion-input agreement detects the comparisons when the shifted Hom groups
in the output reduction towers are finite.

Source: the Milnor mapping-limit argument in
`lem-sf-integral-reductions-jointly-faithful`, together with the proved
quotient-input/naturality part of the torsion-input detection plan.
(blueprint: lem-qcqs-compact-support-torsion-input-finite-hom).

Proof: quotient-input naturality gives equality of every scalar reduction. The
recorded target is constructible, so its canonical reduction cone is a homotopy
limit by its defining Roos triangle. Finiteness of the displayed shifted Hom
sets makes the Milnor map injective. Naturality of the scalar-adjunction units
identifies the two images under that map, hence the two original components.
Componentwise equality identifies the natural transformations. This argument
includes exponent one, zero inputs and empty schemes. -/
theorem sfQcqsCompactSupport_torsion_input_ext_of_finite_shifted_hom
    (hfin : ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ), Finite
      (((image (completed l E) c).obj K.obj)⟦(1 : ℤ)⟧ ⟶
        (sfDerivedReductionRestricted l E Y n).obj
          ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).obj))
    (τ τ' : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ⟶
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι)
    (h : ∀ (n : ℕ) (K : sfIntegralConstructibleCategory l E X),
      (scalarReductionDerivedRestriction l E X n).essImage K.obj →
        τ.app K = τ'.app K) : τ = τ' := by
  ext K
  exact derivedComplete_finiteReduction_ext l E Y
    ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).property.1
    (hfin K) (τ.app K) (τ'.app K)
    (torsion_input_reduction_eq l E K₀ hl c τ τ' h K)

/-- Torsion inputs detect compact-support comparisons over an algebraically
closed base field, with no separatedness assumption on the structure morphisms.

Source: finite-coefficient Hom finiteness over algebraically closed fields and
its Milnor mapping-limit consequence for the torsion-input detection plan.
(blueprint: lem-qcqs-compact-support-torsion-input-alg-closed).

Proof: the independent normalized compact-support isomorphism identifies the
actual output with the recorded constructible output. Shift this isomorphism and
transport the algebraically closed qcqs finite shifted-Hom theorem along it.
Finite-Hom detection applies to the original natural transformations. The proof
uses the stated algebraic closedness of the original base field, and adds no
separatedness hypothesis. Zero inputs and empty schemes are included. -/
theorem sfQcqsCompactSupport_torsion_input_ext_of_isAlgClosed
    [IsAlgClosed K₀]
    (τ τ' : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ⟶
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι)
    (h : ∀ (n : ℕ) (K : sfIntegralConstructibleCategory l E X),
      (scalarReductionDerivedRestriction l E X n).essImage K.obj →
        τ.app K = τ'.app K) : τ = τ' := by
  classical
  obtain ⟨σ, _⟩ := sfQcqsCompactSupport_normalizedIso_exists l E K₀ hl c
  apply sfQcqsCompactSupport_torsion_input_ext_of_finite_shifted_hom l E K₀ hl c
    ?_ τ τ' h
  intro K n
  let M := (sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K
  let e := (shiftFunctor _ (1 : ℤ)).mapIso (σ.app K)
  have hfin : Finite
      (M.obj⟦(1 : ℤ)⟧ ⟶ (sfDerivedReductionRestricted l E Y n).obj M.obj) :=
    integralReduction_shiftedHom_finite_algClosed l E K₀ hl Y M M n
  exact @Finite.of_equiv _ _ hfin (e.homCongr (Iso.refl _)).symm

/-- Agreement on inputs carrying a finite quotient coefficient action detects natural
compact-support comparisons. The test is on the original components at restricted
finite-coefficient inputs, rather than on finite evaluations of a derived tower.

Source: the strict-resolution/naturality step of
lem-qcqs-compact-support-reduction-rigidity; Bhatt--Scholze 6.7.6--6.7.7 and
Stacks Tags 0941, 0F7J.
(blueprint: lem-qcqs-compact-support-torsion-input-detection).

The finite-evaluation part of this plan is proved below the same hypotheses by
`sfQcqsCompactSupport_torsion_input_iff_reduction_eq`: the restricted quotient input
is constructible by the principal reduction triangle, and naturality at its unit
can be cancelled after reduction using the adjunction triangle identity. This
still does not identify maps in the derived category from their finite evaluations.
The reverse implication also holds: torsion-input agreement and finite-evaluation
agreement are equivalent hypotheses, so the stronger conclusion requires the same
rigidity argument in either formulation.

Uncompleted proof plan: use strict flat-term K-flat resolutions and the augmented quotient-tensor
systems of complete integral inputs. Each finite quotient complex, regarded as an
integral complex by restriction, is a constructible integral test input. Resolve
all these inputs and their proper/open diagrams simultaneously, retaining the
augmentation, quotient transition and comparison maps. Agreement on the restricted
finite inputs identifies the two induced comparisons on this resolving diagram.
Naturality with respect to the augmentations and resolution comparison maps then
identifies the universal counit comparisons on the resolving category. Transpose
under the reduction/total-limit adjunction, before evaluating any derived system.
Uniqueness of the universal transpose identifies the comparisons there. Descend
through the resolving localization and conjugate by the projection-normalized gamma
of exists_compactSupportRepresentativeComparison. This identifies the original
natural transformations. This is the adic density step for natural comparisons;
it does not assert joint monicity of the individual derived limit projections.
Zero complexes and empty schemes are included by the same augmentations. -/
-- STATEMENT-DISPUTED: The asserted passage from agreement on torsion inputs to equality
-- on strict resolving diagrams requires a coherent lift of arbitrary ordinary natural
-- transformations. None is part of the hypotheses or supplied by the cited declarations.
-- The reduction/limit adjunction detects a whole system map; it does not identify such
-- maps from their finite evaluations. Over an arbitrary base field, the available
-- finite-field Milnor injectivity theorem does not apply. No counterexample is claimed.
theorem sfQcqsCompactSupport_torsion_input_ext
    (τ τ' : (sfIntegralConstructible l E X).ι ⋙ image (completed l E) c ⟶
      sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι)
    (h : ∀ (n : ℕ) (K : sfIntegralConstructibleCategory l E X),
      (scalarReductionDerivedRestriction l E X n).essImage K.obj →
        τ.app K = τ'.app K) : τ = τ' := by sorry

end WeilConjectures
