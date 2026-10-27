/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.Paper.SystemTensorMateArrows
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.SixFunctors.ProperOpenProjectionMate
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains

public import Sheaf.Paper.SystemTensorPresentationData
import Sheaf.Paper.SystemTensorPresentationCoreExistence
import Sheaf.Paper.SystemTensorSemilinearRealization

/-! # Identification of strict quotient-system tensor presentations

Source: Stacks 0B56 and 0E8I. The normalized comparisons identify the counit-defined
projection and the open-unit transpose before evaluation.
(blueprint: lem-pur-system-tensor-presentation-identification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.leftAdjoint
  WeilConjectures.pullbackTensorCalculus HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategoryFactors
attribute [local irreducible] WeilConjectures.CoefficientClosedStructure.tensor
  WeilConjectures.SystemTensorMate.Operations.derivedAdj
  WeilConjectures.SystemTensorMate.Operations.derivedOpenAdj
  WeilConjectures.SystemTensorMate.TensorOperations.projection
  WeilConjectures.SystemTensorMate.TensorOperations.deltaInv
  WeilConjectures.SystemTensorMate.Operations.pComp

universe u v u' v' w z
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.SemilinearSections

namespace PresentationMateAlgebra

section
open CategoryTheory
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
variable (F G : C ⥤ D) (R : D ⥤ C) (a : F ⊣ R) (b : G ⊣ R)
  (TC TC' : C × C ⥤ C) (TD TD' : D × D ⥤ D)
  (p : F ≅ G) (tC : TC ≅ TC') (tD : TD ≅ TD')
  (m : TC ⋙ F ≅ F.prod F ⋙ TD) (n : TC' ⋙ G ≅ G.prod G ⋙ TD')
  (unit_eq : ∀ M, a.unit.app M ≫ R.map (p.hom.app M) = b.unit.app M)
  (counit_eq : ∀ H, p.hom.app (R.obj H) ≫ b.counit.app H = a.counit.app H)
  (mu_eq : ∀ M N, F.map (tC.hom.app (M, N)) ≫ p.hom.app (TC'.obj (M, N)) ≫
    n.hom.app (M, N) = m.hom.app (M, N) ≫ tD.hom.app (F.obj M, F.obj N) ≫
      TD'.map (Prod.mkHom (p.hom.app M) (p.hom.app N)))

include unit_eq counit_eq mu_eq in
private theorem projection (H : D) (Q : C) :
    tC.hom.app (R.obj H, Q) ≫
      b.homEquiv _ _ (n.hom.app (R.obj H, Q) ≫
        TD'.map (Prod.mkHom (b.counit.app H) (𝟙 _))) =
    a.homEquiv _ _ (m.hom.app (R.obj H, Q) ≫
      TD.map (Prod.mkHom (a.counit.app H) (𝟙 _))) ≫
        R.map (tD.hom.app (H, F.obj Q) ≫
          TD'.map (Prod.mkHom (𝟙 H) (p.hom.app Q))) := by
  let A := (R.obj H, Q)
  let K := tD.hom.app (H, F.obj Q) ≫
    TD'.map (Prod.mkHom (𝟙 H) (p.hom.app Q))
  have hu := unit_eq (TC.obj A)
  have hn := b.unit.naturality (tC.hom.app A)
  simp only [Functor.id_map, Functor.comp_map] at hn
  have hp := p.hom.naturality (tC.hom.app A)
  have hm := mu_eq (R.obj H) Q
  have hc := counit_eq H
  have ht := tD.hom.naturality
    (Prod.mkHom (a.counit.app H) (𝟙 (F.obj Q)))
  have he : Prod.mkHom (p.hom.app (R.obj H)) (p.hom.app Q) ≫
      Prod.mkHom (b.counit.app H) (𝟙 (G.obj Q)) =
      Prod.mkHom (a.counit.app H) (𝟙 (F.obj Q)) ≫
        Prod.mkHom (𝟙 H) (p.hom.app Q) := by
    apply Prod.ext
    · change p.hom.app (R.obj H) ≫ b.counit.app H = a.counit.app H ≫ 𝟙 H
      exact hc.trans (Category.comp_id (a.counit.app H)).symm
    · change p.hom.app Q ≫ 𝟙 _ = 𝟙 _ ≫ p.hom.app Q
      exact (Category.comp_id (p.hom.app Q)).trans (Category.id_comp _).symm
  have hw : p.hom.app (TC.obj A) ≫
      G.map (tC.hom.app A) ≫ n.hom.app A ≫
        TD'.map (Prod.mkHom (b.counit.app H) (𝟙 _)) =
      m.hom.app A ≫
        TD.map (Prod.mkHom (a.counit.app H) (𝟙 _)) ≫ K := by
    rw [← reassoc_of% hp, reassoc_of% hm]
    rw [← TD'.map_comp, he, TD'.map_comp]
    rw [← reassoc_of% ht]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [R.map_comp, Category.assoc] at *
  rw [reassoc_of% hn, ← hu]
  simp only [Category.assoc, ← R.map_comp]
  exact congrArg (fun t ↦ a.unit.app (TC.obj A) ≫ R.map t) hw

end

section
open CategoryTheory
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
variable (F G : C ⥤ D) (J J' : D ⥤ C) (a : J ⊣ F) (b : J' ⊣ G)
  (TC TC' : C × C ⥤ C) (TD TD' : D × D ⥤ D)
  (p : F ≅ G) (e : J ≅ J') (tC : TC ≅ TC') (tD : TD ≅ TD')
  (m : TC ⋙ F ≅ F.prod F ⋙ TD) (n : TC' ⋙ G ≅ G.prod G ⋙ TD')
  (unit_eq : ∀ M, a.unit.app M ≫ F.map (e.hom.app M) ≫
    p.hom.app (J'.obj M) = b.unit.app M)
  (mu_eq : ∀ M N, F.map (tC.hom.app (M, N)) ≫ p.hom.app (TC'.obj (M, N)) ≫
    n.hom.app (M, N) = m.hom.app (M, N) ≫ tD.hom.app (F.obj M, F.obj N) ≫
      TD'.map (Prod.mkHom (p.hom.app M) (p.hom.app N)))

include unit_eq mu_eq in
private theorem open_inverse (H : D) (Q : C) :
    e.hom.app (TD.obj (H, F.obj Q)) ≫
      J'.map (tD.hom.app (H, F.obj Q) ≫ TD'.map (Prod.mkHom (𝟙 H) (p.hom.app Q))) ≫
      (b.homEquiv _ _).symm (TD'.map (Prod.mkHom (b.unit.app H) (𝟙 _)) ≫
        n.inv.app (J'.obj H, Q)) =
    (a.homEquiv _ _).symm (TD.map (Prod.mkHom (a.unit.app H) (𝟙 _)) ≫
      m.inv.app (J.obj H, Q)) ≫ tC.hom.app (J.obj H, Q) ≫
        TC'.map (Prod.mkHom (e.hom.app H) (𝟙 Q)) := by
  let K := tD.hom.app (H, F.obj Q) ≫
    TD'.map (Prod.mkHom (𝟙 H) (p.hom.app Q))
  let B := tC.hom.app (J.obj H, Q) ≫
    TC'.map (Prod.mkHom (e.hom.app H) (𝟙 Q))
  have unit_transport (M : D) :
      a.unit.app M ≫ p.hom.app (J.obj M) ≫
        G.map (e.hom.app M) =
      b.unit.app M := by
    have hn := p.hom.naturality (e.hom.app M)
    rw [← hn]
    exact unit_eq M
  have transpose_transport {M : D} {N : C}
      (z : J'.obj M ⟶ N) :
      a.homEquiv M N (e.hom.app M ≫ z) ≫
        p.hom.app N = b.homEquiv M N z := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    rw [F.map_comp]
    simp only [Category.assoc]
    have hn := p.hom.naturality z
    rw [hn, reassoc_of% (unit_eq M)]
  have inverse_mu :
      m.inv.app (J.obj H, Q) ≫
        F.map (tC.hom.app (J.obj H, Q)) ≫
        p.hom.app (TC'.obj (J.obj H, Q)) =
      tD.hom.app (F.obj (J.obj H), F.obj Q) ≫
        TD'.map (Prod.mkHom
          (p.hom.app (J.obj H)) (p.hom.app Q)) ≫
        n.inv.app (J.obj H, Q) := by
    apply (cancel_epi (m.hom.app (J.obj H, Q))).1
    apply (cancel_mono (n.hom.app (J.obj H, Q))).1
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app,
      ]
    exact (mu_eq (J.obj H) Q).trans
      (congrArg (fun z ↦ m.hom.app (J.obj H, Q) ≫
        tD.hom.app (F.obj (J.obj H), F.obj Q) ≫ z)
        (Category.comp_id (TD'.map
          (Prod.mkHom (p.hom.app (J.obj H)) (p.hom.app Q))))).symm
  have mu_natural := n.inv.naturality
    (Prod.mkHom (e.hom.app H) (𝟙 Q))
  simp only [Functor.comp_map, Functor.prod_map] at mu_natural
  have tensor_natural := tD.hom.naturality
    (Prod.mkHom (a.unit.app H) (𝟙 (F.obj Q)))
  have pairs :
      Prod.mkHom (a.unit.app H) (𝟙 (F.obj Q)) ≫
        Prod.mkHom (p.hom.app (J.obj H)) (p.hom.app Q) ≫
        Prod.mkHom (G.map (e.hom.app H))
          (G.map (𝟙 Q)) =
      Prod.mkHom (𝟙 H) (p.hom.app Q) ≫
        Prod.mkHom (b.unit.app H) (𝟙 (G.obj Q)) := by
    apply Prod.ext
    · change a.unit.app H ≫ p.hom.app (J.obj H) ≫ G.map (e.hom.app H) =
        (𝟙 H) ≫ b.unit.app H
      rw [Category.id_comp]
      exact unit_transport H
    · change (𝟙 (F.obj Q)) ≫ p.hom.app Q ≫ G.map (𝟙 Q) =
        p.hom.app Q ≫ (𝟙 (G.obj Q))
      rw [G.map_id Q, Category.id_comp]
  apply (a.homEquiv _ _).injective
  apply (cancel_mono (p.hom.app _)).1
  rw [transpose_transport]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [Equiv.apply_symm_apply, Functor.id_obj, Functor.comp_obj]
  rw [F.map_comp]
  simp only [Category.assoc]
  have hp := p.hom.naturality
    (TC'.map (Prod.mkHom (e.hom.app H) (𝟙 Q)))
  rw [hp, reassoc_of% inverse_mu]
  rw [← mu_natural, reassoc_of% tensor_natural]
  simp only [← TD'.map_comp_assoc]
  rw [pairs]

end

section
variable {C : Type w} [Category.{z} C] {W X Y Z : C}

private theorem inverse_square (i : W ≅ X) (j : Y ≅ Z)
    (A : X ⟶ Z) (B : W ⟶ Y) (h : A ≫ j.inv = i.inv ≫ B) :
    B ≫ j.hom = i.hom ≫ A := by
  apply (cancel_mono j.inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h, Iso.hom_inv_id_assoc]

end

end PresentationMateAlgebra

namespace WeilConjectures.SystemTensorMate

variable {l : ℕ} [Fact l.Prime] {E : Type (u + 1)} [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem projection_comparison (o d : TensorOperations l E)
    (c : TensorPresentationCore o d) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : D l E X) (Q : D l E Y) :
    (c.tensor Y).hom.app ((pushDerived l E f).obj H, Q) ≫ d.projection f H Q =
      o.projection f H Q ≫ (pushDerived l E f).map
        ((c.tensor X).hom.app (H, (o.P f).obj Q) ≫
          (d.T X).map (Prod.mkHom (𝟙 H) ((c.pull f).hom.app Q))) := by
  unfold TensorOperations.projection
  exact PresentationMateAlgebra.projection
    (o.P f) (d.P f) (pushDerived l E f) (o.derivedAdj f) (d.derivedAdj f)
    (o.T Y) (d.T Y) (o.T X) (d.T X) (c.pull f) (c.tensor Y) (c.tensor X)
    (o.mu f) (d.mu f) (c.unit f) (c.counit f) (c.mu f) H Q

private theorem delta_inverse_comparison (o d : TensorOperations l E)
    (c : TensorPresentationCore o d) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (H : D l E U) (Q : D l E X) :
    (c.extension j).hom.app ((o.T U).obj (H, (o.P j).obj Q)) ≫
      (d.J j).map ((c.tensor U).hom.app (H, (o.P j).obj Q) ≫
        (d.T U).map (Prod.mkHom (𝟙 H) ((c.pull j).hom.app Q))) ≫ d.deltaInv j H Q =
    o.deltaInv j H Q ≫ (c.tensor X).hom.app ((o.J j).obj H, Q) ≫
      (d.T X).map (Prod.mkHom ((c.extension j).hom.app H) (𝟙 Q)) := by
  unfold TensorOperations.deltaInv
  exact PresentationMateAlgebra.open_inverse
    (o.P j) (d.P j) (o.J j) (d.J j) (o.derivedOpenAdj j) (d.derivedOpenAdj j)
    (o.T X) (d.T X) (o.T U) (d.T U) (c.pull j) (c.extension j)
    (c.tensor X) (c.tensor U) (o.mu j) (d.mu j) (c.open_unit j) (c.mu j) H Q

private theorem delta_comparison (o d : TensorOperations l E)
    (c : TensorPresentationCore o d) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (H : D l E U) (Q : D l E X) :
    (c.tensor X).hom.app ((o.J j).obj H, Q) ≫
      (d.T X).map (Prod.mkHom ((c.extension j).hom.app H) (𝟙 Q)) ≫
        (d.delta j H Q).hom =
    (o.delta j H Q).hom ≫
      (c.extension j).hom.app ((o.T U).obj (H, (o.P j).obj Q)) ≫
        (d.J j).map ((c.tensor U).hom.app (H, (o.P j).obj Q) ≫
          (d.T U).map (Prod.mkHom (𝟙 H) ((c.pull j).hom.app Q))) := by
  let A := (c.extension j).hom.app ((o.T U).obj (H, (o.P j).obj Q)) ≫
    (d.J j).map ((c.tensor U).hom.app (H, (o.P j).obj Q) ≫
      (d.T U).map (Prod.mkHom (𝟙 H) ((c.pull j).hom.app Q)))
  let B := (c.tensor X).hom.app ((o.J j).obj H, Q) ≫
    (d.T X).map (Prod.mkHom ((c.extension j).hom.app H) (𝟙 Q))
  have h := delta_inverse_comparison o d c j H Q
  have hi : A ≫ (d.delta j H Q).inv = (o.delta j H Q).inv ≫ B := by
    simpa only [A, B, TensorOperations.delta, Iso.symm_inv, asIso_hom,
      Category.assoc] using h
  simpa only [A, B, Category.assoc] using
    PresentationMateAlgebra.inverse_square (o.delta j H Q) (d.delta j H Q) A B hi

private def completeComparison (o d : TensorOperations l E)
    (c : TensorPresentationCore o d) : TensorPresentationComparison o d where
  toTensorPresentationCore := c
  projection := projection_comparison o d c
  delta := delta_comparison o d c
  delta_inverse := delta_inverse_comparison o d c

/-- Reindexing identifies all specified tensor and operation factors before
system evaluation. The source operations are supplied by the recorded semilinear datum, transported
from inverse-image coefficients by the canonical constant-coefficient identification.
Source: Stacks 0B56, 0E8I and 0GL1; explicit presentation comparison
(blueprint: lem-pur-system-tensor-presentation-identification).

Proof: (1) identify systems with modules on the vertical sequence site by
`M_(a+1)(U)`; horizontal restrictions are the given quotient-semilinear maps.
The inverse is restriction to slices. Both functors are exact and descend by
localization to the unbounded derived categories. In the published shared model
this is presentationReindexing. (2) Ordinary tensor is sheafification of the
same balanced pure tensors. Identity on these tensors preserves the unit,
associators and symmetry. (3) Apply exact monoidal equivalence total K-flat
descent; the tensor comparison is identity on every signed total summand.
Cochain tensor-model rigidity gives its unique natural derived extension.
(4) Sectionwise direct image is unchanged, including constant scalars. Uniqueness
of left adjoints identifies ordinary pullback and open extension, with units and
counits. (5) Exact equivalences preserve K-injectives; compute right derived
image on a system K-injective resolution. Derived localization identifies the
canonical derived adjunctions, without evaluating that resolution at a level.
(6) Direct-image pasting has the same section formula; conjugating by the
identified adjunctions identifies pullback compositors. (7) The ordinary
inverse-image tensor comparison is the transpose of the same pure-tensor lax
map. Its signed total-summand normalization and cochain rigidity identify mu
for all unbounded inputs. (8) Substitute tensor, mu, unit and counit comparisons
in the projection mate word of def-exchange-projection. (9) Substitute the
open unit and mu inverse in the open-adjunction transpose. Injectivity of the
Hom bijection identifies delta inverse; open tensor normalization gives delta.
For the source operations, apply this construction to a.geometric and a.localization;
transport the inverse-image coefficients by the constant-section identification.
The source and target K-flat normalizations identify the actual geometric mu and
its projection mate. The localization unit fixes the open comparison uniquely.
No cartesianness, flat coefficient transitions,
or boundedness is used, and no equality is inferred from evaluated equalities. -/
theorem tensorPresentationIdentification
    (a : ∀ W : Scheme.{u}, PresentationSections (l := l) (E := E) W)
    (d : TensorOperations l E) :
    ∃ o : TensorOperations l E,
      Nonempty (SemilinearPresentationComparison a o) ∧
        Nonempty (TensorPresentationComparison o d) := by
  obtain ⟨o, ho⟩ := semilinearPresentation_realization a
  obtain ⟨c⟩ := tensorPresentationCore_nonempty o d
  exact ⟨o, ho, ⟨completeComparison o d c⟩⟩

end WeilConjectures.SystemTensorMate

-- Keep valuation choices abstract while elaborating the explicit universe transport.
attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionAbsoluteValue

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] WeilConjectures.IntegralSystemRealization.Direct.adj
  WeilConjectures.IntegralSystemRealization.properProjection
  WeilConjectures.IntegralSystemRealization.Compositors.square
  WeilConjectures.pullbackTensorSystemComparison
  WeilConjectures.SystemTensorMate.Operations.square

namespace WeilConjectures.SystemTensorMate.Realization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The explicit coefficient universe lift used to compare the realization interface
with the diagram interface. It keeps the schemes and both site universes unchanged.
Source: the size convention; Stacks 0941
(blueprint: lem-pur-system-tensor-presentation-identification). -/
abbrev liftedField := ULift.{u + 1} E

variable {l E}

/-- The square compatibility equation, as a named proposition to keep the large
realization record's field types compact. Source: presentation comparison Step 6;
Stacks 07A7 (blueprint: lem-pur-system-tensor-presentation-identification). -/
def squareCompatibility (a : IntegralSystemRealization.Operations l E)
    (c : IntegralSystemRealization.Compositors l E a)
    (d : TensorOperations l (liftedField E))
    (rings : ∀ W : Scheme.{u},
      coefficientSequenceCommRingSheaf l E W ≅ R l (liftedField E) W)
    (pull : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      IntegralSystemRealization.pull l E f ⋙ resD (rings X).inv ≅
        resD (rings Y).inv ⋙ d.P f) : Prop :=
  ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C) (p : B ⟶ D) (i : C ⟶ D)
    (h : k ≫ p = r ≫ i) (Q : IntegralSystemRealization.System l E D),
    (resD (rings A).inv).map ((c.square l E k r p i h).hom.app Q) ≫
      (pull k).hom.app ((IntegralSystemRealization.pull l E p).obj Q) ≫
      (d.P k).map ((pull p).hom.app Q) =
    (pull r).hom.app ((IntegralSystemRealization.pull l E i).obj Q) ≫
      (d.P r).map ((pull i).hom.app Q) ≫
      (d.square k r p i h).inv.app ((resD (rings D).inv).obj Q)

/-- Universe transport and identification of the exact factors in the system clause
of properOpenProjectionMateSystems. The ring map is fixed on quotient representatives
and constant sections; the ordinary functor is actual scalar restriction, and its tensor
comparison retains the full K-flat model. No arbitrary categorical equivalence is used.
Source: Stacks 0B56, 0E8I; presentation comparison Steps 1--9 and size convention
(blueprint: lem-pur-system-tensor-presentation-identification). -/
structure Comparison (a : IntegralSystemRealization.Operations l E)
    (c : IntegralSystemRealization.Compositors l E a)
    (z : IntegralSystemRealization.OpenComparisons l E a c)
    (d : TensorOperations l (liftedField E)) where
  /-- Identity on the field identifies both valuation rings. -/
  integers : ∀ x : Padic.coefficientExtensionIntegers l E,
    ∃ y : Padic.coefficientExtensionIntegers l (liftedField E), y.val = ULift.up x.val
  /-- The actual quotient-ring identification across the coefficient universe lift. -/
  quotients : ∀ n : ℕ, Padic.coefficientExtensionRing l E (n + 1) ≃+*
    Padic.coefficientExtensionRing l (liftedField E) (n + 1)
  /-- It sends each quotient representative to the identical lifted field element. -/
  representatives : ∀ (n : ℕ) (x : Padic.coefficientExtensionIntegers l E)
    (y : Padic.coefficientExtensionIntegers l (liftedField E)), y.val = ULift.up x.val →
    quotients n (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x) =
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l (liftedField E) (n + 1)) y
  /-- The same constant-section transport on the vertical sequence site. -/
  rings : ∀ W : Scheme.{u}, coefficientSequenceCommRingSheaf l E W ≅ R l (liftedField E) W
  /-- Constant sections fix the assembled ring isomorphism uniquely. -/
  constants : ∀ (W : Scheme.{u}) (n : ℕ) (V : W.ProEt)
    (x : ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))),
    (rings W).hom.hom.app (op (n, V))
      (((toSheafify (Scheme.ProEt.topology W)
        ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app (op V)) x) =
      scalar l (liftedField E) W n V (ULift.up (quotients n x.down))
  /-- This is an equivalence on the unbounded derived categories. -/
  equivalence : ∀ W : Scheme.{u}, (resD (rings W).inv).IsEquivalence
  /-- Actual pullback comparison after the explicit coefficient transport. -/
  pull : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    IntegralSystemRealization.pull l E f ⋙ resD (rings X).inv ≅
      resD (rings Y).inv ⋙ d.P f
  /-- Actual total right-derived direct-image comparison. -/
  push : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    IntegralSystemRealization.Operations.push l E a f ⋙ resD (rings Y).inv ≅
      resD (rings X).inv ⋙ pushDerived l (liftedField E) f
  /-- Exact open-extension comparison. -/
  extension : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j],
    IntegralSystemRealization.Operations.shriek l E a j ⋙ resD (rings X).inv ≅
      resD (rings U).inv ⋙ d.J j
  /-- The exact systemClosed.tensor factor of the realization theorem. -/
  tensor : ∀ W : Scheme.{u},
    (IntegralSystemRealization.calculus l E W).systemClosed.tensor ⋙ resD (rings W).inv ≅
      ((resD (rings W).inv).prod (resD (rings W).inv)) ⋙ d.T W
  /-- Coefficient transport preserves the actual K-flat representative class. -/
  kflat : ∀ (W : Scheme.{u}) (P : CochainComplex (coefficientSequenceModules l E W) ℤ),
    CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) P →
    CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := R l (liftedField E) W)
      (((res (rings W).inv).mapHomologicalComplex (.up ℤ)).obj P)
  /-- The comparison of the two actual signed total complexes. -/
  chain : ∀ (W : Scheme.{u}) (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ),
    (totalTensor.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology W)) (R l (liftedField E) W)).obj
      (((res (rings W).inv).mapHomologicalComplex (.up ℤ)).obj P,
        ((res (rings W).inv).mapHomologicalComplex (.up ℤ)).obj Q) ⟶
    ((res (rings W).inv).mapHomologicalComplex (.up ℤ)).obj
      ((coefficientTotalTensor.{u, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)).obj (P, Q))
  /-- Every total summand keeps its pure tensor and its signed differential. -/
  generators : ∀ (W : Scheme.{u}) (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (p q k : ℤ) (h : p + q = k) (V : (ℕ × W.ProEt)ᵒᵖ)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
    ((chain W P Q).f k).val.app V
      (coefficientTensorGenerator.{u + 1, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W)) (R l (liftedField E) W)
        (((res (rings W).inv).mapHomologicalComplex (.up ℤ)).obj P)
        (((res (rings W).inv).mapHomologicalComplex (.up ℤ)).obj Q) p q k h V x y) =
      coefficientTensorGenerator.{u, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W) P Q p q k h V x y
  /-- Localization identifies the two published K-flat models, with their own universes. -/
  tensor_model : ∀ (W : Scheme.{u}) (P Q : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) Q),
    (tensorModelIso.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology W)) (R l (liftedField E) W)
      (d.systems W).closed (d.systems W).tensorModels
      (((res (rings W).inv).mapHomologicalComplex (.up ℤ)).obj P)
      (((res (rings W).inv).mapHomologicalComplex (.up ℤ)).obj Q)
      (kflat W P hP) (kflat W Q hQ)).hom ≫
      (d.T W).map (Prod.mkHom
        ((Functor.mapDerivedCategoryFactors (res (rings W).inv)).inv.app P)
        ((Functor.mapDerivedCategoryFactors (res (rings W).inv)).inv.app Q)) ≫
      (tensor W).inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (resD (rings W).inv).map
        ((pullbackTensorSystemModel l E W P Q hP hQ).inv) ≫
      (Functor.mapDerivedCategoryFactors (res (rings W).inv)).hom.app
        ((coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)).obj (P, Q)) =
      DerivedCategory.Q.map (chain W P Q)
  /-- The specified proper adjunction unit is preserved. -/
  unit : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : IntegralSystemRealization.System l E Y),
    (resD (rings Y).inv).map ((a.direct f).adj.unit.app M) ≫
      (push f).hom.app ((IntegralSystemRealization.pull l E f).obj M) ≫
      (pushDerived l (liftedField E) f).map ((pull f).hom.app M) =
        (d.derivedAdj f).unit.app ((resD (rings Y).inv).obj M)
  /-- The specified open adjunction unit is preserved. -/
  open_unit : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : IntegralSystemRealization.System l E U),
    (resD (rings U).inv).map ((a.extension j).adj.unit.app M) ≫
      (pull j).hom.app ((IntegralSystemRealization.Operations.shriek l E a j).obj M) ≫
      (d.P j).map ((extension j).hom.app M) =
        (d.derivedOpenAdj j).unit.app ((resD (rings U).inv).obj M)
  /-- Identification of the published tensor-pullback comparison mu. -/
  mu : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : IntegralSystemRealization.System l E Y),
    (resD (rings X).inv).map ((pullbackTensorSystemComparison l E f).hom.app (M, N)) ≫
      (tensor X).hom.app ((IntegralSystemRealization.pull l E f).obj M,
        (IntegralSystemRealization.pull l E f).obj N) ≫
      (d.T X).map (Prod.mkHom ((pull f).hom.app M) ((pull f).hom.app N)) =
    (pull f).hom.app ((IntegralSystemRealization.calculus l E Y).systemClosed.tensor.obj
      (M, N)) ≫ (d.P f).map ((tensor Y).hom.app (M, N)) ≫
      (d.mu f).hom.app ((resD (rings Y).inv).obj M, (resD (rings Y).inv).obj N)
  /-- The exact properProjection factor, for arbitrary unbounded H and Q. -/
  projection : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : IntegralSystemRealization.System l E X) (Q : IntegralSystemRealization.System l E Y),
    (resD (rings Y).inv).map
        (((IntegralSystemRealization.properProjection l E a f).app H).app Q) ≫
      (push f).hom.app ((IntegralSystemRealization.calculus l E X).systemClosed.tensor.obj
        (H, (IntegralSystemRealization.pull l E f).obj Q)) ≫
      (pushDerived l (liftedField E) f).map
        ((tensor X).hom.app (H, (IntegralSystemRealization.pull l E f).obj Q) ≫
          (d.T X).map (Prod.mkHom (𝟙 _) ((pull f).hom.app Q))) =
    (tensor Y).hom.app ((IntegralSystemRealization.Operations.push l E a f).obj H, Q) ≫
      (d.T Y).map (Prod.mkHom ((push f).hom.app H) (𝟙 _)) ≫
      d.projection f ((resD (rings X).inv).obj H) ((resD (rings Y).inv).obj Q)
  /-- The exact z.openComparisons.projection factor equals delta under transport. -/
  delta : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (H : IntegralSystemRealization.System l E U) (Q : IntegralSystemRealization.System l E X),
    (resD (rings X).inv).map ((z.projection j).hom.app (H, Q)) ≫
      (extension j).hom.app ((IntegralSystemRealization.calculus l E U).systemClosed.tensor.obj
        (H, (IntegralSystemRealization.pull l E j).obj Q)) ≫
      (d.J j).map ((tensor U).hom.app (H, (IntegralSystemRealization.pull l E j).obj Q) ≫
        (d.T U).map (Prod.mkHom (𝟙 _) ((pull j).hom.app Q))) =
    (tensor X).hom.app ((IntegralSystemRealization.Operations.shriek l E a j).obj H, Q) ≫
      (d.T X).map (Prod.mkHom ((extension j).hom.app H) (𝟙 _)) ≫
      (d.delta j ((resD (rings U).inv).obj H) ((resD (rings X).inv).obj Q)).hom
  /-- The exact canonical pullback compositor, in its inverse orientation. -/
  composition : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (Q : IntegralSystemRealization.System l E Z),
    (resD (rings X).inv).map ((c.pullComp f g).hom.app Q) ≫
      (pull f).hom.app ((IntegralSystemRealization.pull l E g).obj Q) ≫
      (d.P f).map ((pull g).hom.app Q) =
    (pull (f ≫ g)).hom.app Q ≫
      (d.pComp f g).inv.app ((resD (rings Z).inv).obj Q)
  /-- The exact z.compositors.square factor, in terms of the two pComp paths. -/
  square : squareCompatibility a c d rings pull

/-- The 'in particular' clause for the precise factors used in the system
proper/open projection-mate theorem. The explicit ULift transport identifies its
systemClosed.tensor, properProjection, open projection and square factors with
the diagram tensor, pi, delta and canonical pComp paths.
Source: Stacks 0B56, 0E8I; presentation comparison Steps 1--9
(blueprint: lem-pur-system-tensor-presentation-identification).
Proof: lift E by identity on its field elements. Uniqueness of the extended
absolute value identifies the valuation rings and their uniformizer ideals;
the quotient maps give the unique representative-preserving ring isomorphisms.
Sheafify their constant maps and assemble over the sequence index. Restriction
along their inverses gives an exact equivalence, hence an equivalence of ordinary
unbounded localizations. On K-flat representatives tensor transport is the
same pure tensor with the same signed differential. The unit-normalized ordinary
adjoint comparisons descend to the specified derived adjunctions. Tensor-model
rigidity identifies pullbackTensorSystemComparison with mu. Substitute these
tensor, unit and counit equations in properProjection to obtain pi. The open Hom
bijection and z.projection_transpose identify its inverse with deltaInv, hence
its forward arrow with delta. The section-normalized direct-image compositors
and their adjunction conjugates give composition and square, with the displayed
inverse orientations. This identifies each named factor before evaluation. -/
theorem properOpenFactors (a : IntegralSystemRealization.Operations l E)
    (c : IntegralSystemRealization.Compositors l E a)
    (z : IntegralSystemRealization.OpenComparisons l E a c)
    (d : TensorOperations l (liftedField E)) : Nonempty (Comparison a c z d) := by
  sorry

end WeilConjectures.SystemTensorMate.Realization
