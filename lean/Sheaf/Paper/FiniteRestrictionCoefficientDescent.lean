/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.FiniteRestrictionCoefficientDescentData
import Sheaf.Paper.FiniteRestrictionIntegralAssembly
import Sheaf.Paper.FiniteRestrictionRationalAssembly
/-!
# Finite restriction coefficient descent

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15; the finite-stalk
step of the blueprint finite pushforward proof (blueprint:
lem-zl-finite-restriction-coefficient-descent).

## Main statements

- `WeilConjectures.FiniteRestrictionCoefficient.finiteRestrictionCoefficientDescent`: finite
restriction coefficient descent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  AlgebraicGeometry AlgebraicGeometry.Scheme TensorProduct
namespace WeilConjectures.FiniteRestrictionCoefficient
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (Stage integralTransition transition stageSystem)
variable (l : ℕ) [Fact l.Prime] {s X Y : Scheme.{u}} (f : X ⟶ Y) (y : s ⟶ Y)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
attribute [local irreducible] IntegralDiagram.functor source middle target ambient
  HasDerivedCategory.standard sfIntegralScalarUnit sfRationalScalarComp sfRationalScalarUnit
  GeneralAlgebraicallyClosedCoefficients.associator
  GeneralAlgebraicallyClosedCoefficients.unitor
private theorem finiteData (W : Scheme.{u}) : FiniteData l Ω W := by
  classical
  intro n m t e K a b f T hT A M N r s eqs
  let S := stageSystem l Ω W
  choose k hkK hkL hk using fun j ↦ StageSystem.PairCategory.exists_mkHom_eq (f j)
  have htri : ∀ j, ∃ (B : Index l Ω) (U : Triangle (Stage l Ω W B)),
      U ∈ distTriang _ ∧
        Nonempty (T j ≅ (S.ι B).mapTriangle.obj U) := by
    intro j
    exact (GeneralAlgebraicallyClosedCoefficients.distinguished_iff (T j)).mp (hT j)
  choose C U hU eU using htri
  have heq : ∀ j, ∃ (B : Index l Ω) (h : A j ≤ B),
      (S.T h).map (r j) = (S.T h).map (s j) := by
    intro j
    exact (StageSystem.ι_map_eq_ι_map_iff (r j) (s j)).mp (eqs j)
  choose E hE eqE using heq
  obtain ⟨B, hB⟩ := Finite.exists_le (fun j : (Fin n ⊕ Fin m) ⊕ (Fin t ⊕ Fin e) ↦
    Sum.elim (Sum.elim (fun j ↦ (K j).stage) k) (Sum.elim C E) j)
  let hK : ∀ j, (K j).stage ≤ B := fun j ↦ hB (.inl (.inl j))
  let KB : Fin n → Stage l Ω W B := fun j ↦ (K j).toStage (hK j)
  let iK : ∀ j, (S.ι B).obj (KB j) ≅ K j :=
    fun j ↦ (S.isoToStage (K j) (hK j)).symm
  have hf : ∀ j, ∃ g : KB (a j) ⟶ KB (b j),
      StageSystem.PairCategory.mkHom B (hK (a j)) (hK (b j)) g = f j := by
    intro j
    obtain ⟨g, hg⟩ := hk j B (hB (.inl (.inr j)))
    exact ⟨g, hg.symm⟩
  choose fB hfB using hf
  let ht : ∀ j, C j ≤ B := fun j ↦ hB (.inr (.inl j))
  let TB : Fin t → Triangle (Stage l Ω W B) :=
    fun j ↦ (S.T (ht j)).mapTriangle.obj (U j)
  refine ⟨B, fun j ↦ (hE j).trans (hB (.inr (.inr j))), KB, iK, fB, TB, ?_, ?_, ?_⟩
  · intro j
    change (S.ι B).map (fB j) ≫ (S.isoToStage (K (b j)) (hK (b j))).inv =
      (S.isoToStage (K (a j)) (hK (a j))).inv ≫ f j
    rw [← hfB j, StageSystem.mkHom_eq_isoToStage]
    dsimp only [S]
    simp only [Iso.inv_hom_id_assoc]
  · intro j
    refine ⟨(S.T (ht j)).map_distinguished _ (hU j), ?_⟩
    obtain ⟨ej⟩ := eU j
    exact ⟨((Functor.mapTriangleCompIso (S.T (ht j)) (S.ι B)).app (U j)).symm ≪≫
      (Functor.mapTriangleIso (S.transIso (ht j))).app (U j) ≪≫ ej.symm⟩
  · intro j
    have H := congrArg (fun g ↦ (S.T (hB (.inr (.inr j)))).map g) (eqE j)
    have H' := (S.assoc (hE j) (hB (.inr (.inr j)))).hom.naturality (r j)
    have H'' := (S.assoc (hE j) (hB (.inr (.inr j)))).hom.naturality (s j)
    dsimp only [Functor.comp_map] at H' H''
    apply (cancel_epi ((S.assoc (hE j) (hB (.inr (.inr j)))).hom.app (M j))).mp
    exact H'.symm.trans ((congrArg (fun g ↦ g ≫
      (S.assoc (hE j) (hB (.inr (.inr j)))).hom.app (N j)) H).trans H'')

private theorem tExactDescent_of_representatives {Z : Scheme.{u}}
    (F : (stageSystem l Ω X).Morphism (stageSystem l Ω Z)) :
    TExactDescent l Ω X F := by
  intro hF b n K hK
  obtain ⟨A, M, hM, ⟨e⟩⟩ := hK
  exact ⟨A, (F.Φ A).obj M, hF A b n M hM,
    ⟨F.functor.mapIso e ≪≫ (F.ιCompFunctorIso A).app M⟩⟩

private theorem inverseSquare {C : Type*} [Category C] {A B X Y : C}
    (e : A ≅ B) (f : X ≅ Y) (u : A ⟶ X) (v : B ⟶ Y)
    (h : v ≫ f.inv = e.inv ≫ u) : u ≫ f.hom = e.hom ≫ v := by
  calc
    u ≫ f.hom = (e.hom ≫ (e.inv ≫ u)) ≫ f.hom := by simp
    _ = (e.hom ≫ (v ≫ f.inv)) ≫ f.hom := by rw [h]
    _ = e.hom ≫ v := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsAlgClosure (Padic l) Ω] in
private theorem sectionsCompatible (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    SectionsCompatible l Ω D hl := by
  constructor
  · intro A B h M N g
    let E := Coefficient.{u} l Ω A
    let L := Coefficient.{u} l Ω B
    let ι := coefficientInclusion l Ω A B h
    let eM := pointSectionsScalarExtensionIso l E L ι D hl M.obj
      ((pointIntegralConstructible_iff l E D hl M.obj).mpr M.property)
    let eN := pointSectionsScalarExtensionIso l E L ι D hl N.obj
      ((pointIntegralConstructible_iff l E D hl N.obj).mpr N.property)
    apply inverseSquare eM eN
    let ψ := (pointDerivedSectionsTensor D.k l E L ι).hom ≫
      Functor.whiskerRight (completedScalarComparison l E L ι (Spec (.of D.k)))
        (pointCompletedDerivedSections D.k l L)
    have hn := ψ.naturality g.hom
    dsimp only [ψ, Functor.comp_map, NatTrans.comp_app,
      Functor.whiskerRight_app] at hn
    dsimp only [eM, eN, pointSectionsScalarExtensionIso, pointConstructibleCompletionIso,
      Iso.symm_inv, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, asIso_hom]
    exact hn
  · intro A B h M N g
    exact (pointRationalFibreScalarIso D l hl (Coefficient.{u} l Ω A)
      (Coefficient.{u} l Ω B) (coefficientInclusion l Ω A B h)).hom.naturality g

/-- Finite coefficient descent for the actual exchange and counit restriction.

Source: Bhatt--Scholze Proposition 6.8.14(1),(2), Remark 6.8.15; the finite-stalk
step of the blueprint's finite pushforward proof
(blueprint: lem-zl-finite-restriction-coefficient-descent).

Proof:
1. Finite completed-image comparison and integral constructible pullback preservation
supply all domains. The completed coefficient presentation transport identifies these
with the PBC conventions, without changing rings or reductions.
2. Restrict the normalized scalar/direct-image and completed tensor/pullback comparisons.
Conjugate ordinary direct image by its projection-normalized tower comparison. The
finite-free completed scalar comparison identifies the actual completed ring extension,
also for ramified inclusions; no common quotient exponent is used.
3. Apply ordinary-adjunction scalar compatibility to the inverse adjunct of identity.
This is the counit equation before taking reductions. Its mate is the exchange square.
Pull the equation along each fibre lift and use the unit/composition comparisons.
The geometric adjunctions are fixed by ordinary cochain adjuncts, completion units and
the retained reconstruction. Ordinary composition and identity are fixed by section
pasting and their universal K-flat cochain comparisons. Their completed mates and
point counits are therefore the actual geometric arrows. Comparing the strict derived
arrows with those mates gives Endpoints.ArrowsNormalized; no sign is chosen by scalar
compatibility. The comparison follows on the same K-flat flat-term models and descends
by the resolving localization universal property.
4. The resulting components are the strict-system counit restrictions, so their tuple
is precisely restriction above. On tensor generators this is a tensor m mapped to a
tensor the restriction of m to the lift. Finite product projections detect equality;
the empty product is zero. Identities and tensor associativity give all tower equations.
5. Raw rational transport tensors all integral morphisms with scalars, preserving the
actual components and equations. The normalized exact point-sections comparisons are
natural on both arrows; their rationalizations are the prescribed point-fibre ones.
6. Coherent pair-functor descent gives the representative formula beta-source,
functor of the representative, inverse beta-target. Its Hom construction descends the
two compatible transformations and preserves identities, compositions and equations.
7. Choose finitely many object, arrow and distinguished-triangle representatives and
equality witnesses. Their compositum, enlarged for the finitely many equality witnesses,
is one common finite stage. The empty collection is represented over the base field.
8. Represent each standard-half object at one stage. Stagewise t-exactness keeps its
image in that half. A short exact heart sequence is a distinguished triangle; its image
is distinguished and remains in the heart, hence is short exact. This uses common-stage
truncations, t-exact pair descent, and the heart short-exact-triangle criterion. -/
theorem finiteRestrictionCoefficientDescent
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsFinite f]
    (y : Spec (.of D.k) ⟶ Y) :
    Finite (FiniteCounitTowers.Points f y) ∧
    ∃ (G : Geometry l Ω f y) (I : IntegralComparisons l f y Ω)
      (N : Endpoints l Ω f y G I) (R : RationalComparisons l f y Ω I)
      (J : GeometricArrows l Ω f y G),
      G.Normalized ∧ I.Laws ∧ I.Coherent ∧ N.ScalarNormalized ∧
      J.Normalized l Ω f y ∧ N.ArrowsNormalized l Ω f y J ∧
      TowerAgreement l Ω f ∧ TowerAgreement l Ω (pullback.snd f y) ∧
      TensorRestrictionFormula l Ω f y ∧
      DirectImageDescent l f y Ω G ∧ SectionsCompatible l Ω D hl ∧
      (∀ W : Scheme.{u}, FiniteData l Ω W) ∧
      (∀ q : Vertex, TExactDescent l Ω X (R.diagram q)) ∧
      (∀ q : Vertex, HeartExactDescent l Ω X (R.diagram q)) := by
  have hpoints := FiniteCounitTowers.finitePoints D.k f y
  obtain ⟨G, I, N, J, hG, hI, hcI, hN, hJ, ha, ht, hf, hTensor⟩ :=
    finiteRestrictionIntegralAssembly l Ω f D hl y
  obtain ⟨R, hdirect, hheart⟩ :=
    finiteRestrictionRationalAssembly l Ω f D hl y G I N hG hI hcI hN
  exact ⟨hpoints, G, I, N, R, J, hG, hI, hcI, hN, hJ, ha, ht, hf,
    hTensor, hdirect, sectionsCompatible l Ω D hl, finiteData l Ω,
    fun q ↦ tExactDescent_of_representatives l Ω (R.diagram q), hheart⟩

end WeilConjectures.FiniteRestrictionCoefficient
