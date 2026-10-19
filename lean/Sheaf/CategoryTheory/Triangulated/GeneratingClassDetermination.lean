/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.Algebra.DualNumber
public import Mathlib.Data.ZMod.Basic
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingClassicalGenerator
import Sheaf.CategoryTheory.DerivedCategory.PerfectDerivationTransformation
import Sheaf.CategoryTheory.DerivedCategory.TwoTermSelfExtensionHom

/-! # Invertibility on a thick generating class, and failure of determination

Source: blueprint sec-smooth-purity, sk-lem-sf-determination, statement and counterexample
(blueprint: lem-sf-generating-class-determination).

The invertibility assertions reuse the imported
`NatTrans.isIso_app_of_triangEnvelope` and
`NatTrans.isIso_of_isClassicalTriangulatedGenerator`. To include the empty generating
class, apply the former to the class with the zero object adjoined.

The counterexample is expressed through the fully faithful inclusion of perfect complexes
in the derived category. Thus its natural transformations and automorphisms are recorded
as transformations of functors with values in the ambient derived category.
-/

@[expose] public section

set_option autoImplicit false

universe w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

namespace GeneratingClassCounterexample

/-- The dual numbers over the field with two elements, realizing F₂[ε]/(ε²).
Source: blueprint sk-lem-sf-determination, counterexample
(blueprint: lem-sf-generating-class-determination). -/
abbrev Ring := DualNumber (ZMod 2)

/-- The actual coefficient derivation ∂(a+bε)=b, embedded as a constant dual number.
Source: blueprint sk-lem-sf-determination, counterexample
(blueprint: lem-sf-generating-class-determination). -/
def delta (r : Ring) : Ring := TrivSqZeroExt.inl r.snd

variable [HasDerivedCategory.{w} (ModuleCat.{0} Ring)]

/-- The full-subcategory predicate, using the recorded perfect-ring-complex definition.
Source: blueprint sk-lem-sf-determination, Perf(R)
(blueprint: lem-sf-generating-class-determination). -/
abbrev perfect : ObjectProperty (DerivedCategory (ModuleCat.{0} Ring)) :=
  DerivedCategory.IsPerfectRingComplex

/-- The inclusion Perf(R) → D(R), with every derived morphism between its objects.
Source: blueprint sk-lem-sf-determination, counterexample
(blueprint: lem-sf-generating-class-determination). -/
noncomputable abbrev inclusion := perfect.ι

/-- The identity on perfect objects, followed by the ambient shift by one.
Source: blueprint sk-lem-sf-determination, counterexample
(blueprint: lem-sf-generating-class-determination). -/
noncomputable abbrev shiftedInclusion :=
  inclusion ⋙ shiftFunctor (DerivedCategory (ModuleCat.{0} Ring)) (1 : ℤ)

/-- The object R placed in degree zero in D(R).
Source: blueprint sk-lem-sf-determination, counterexample
(blueprint: lem-sf-generating-class-determination). -/
noncomputable abbrev generator :=
  (DerivedCategory.singleFunctor (ModuleCat.{0} Ring) 0).obj (ModuleCat.of Ring Ring)

/-- The commutator characterization of the transformation induced by ∂. For every bounded
finite projective model and every additive ∂-connection, a chain representative has components
∇d-d∇. The localization functor's specified shift isomorphism identifies its target with
Q(A)[1]. This pins down the construction, rather than choosing an arbitrary transformation
with the two displayed values.

Source: blueprint sk-lem-sf-determination, commutator construction, proof steps 6–10
(blueprint: lem-sf-generating-class-determination). -/
def InducedByPartial (η : inclusion ⟶ shiftedInclusion) : Prop :=
  ∀ (A : CochainComplex (ModuleCat.{0} Ring) ℤ) (a b : ℤ),
    A.IsStrictlyGE a → A.IsStrictlyLE b →
    (∀ i : ℤ, Module.Projective Ring (A.X i) ∧ Module.Finite Ring (A.X i)) →
    ∀ (nabla : ∀ i : ℤ, A.X i →+ A.X i),
      (∀ (i : ℤ) (r : Ring) (m : A.X i),
        nabla i (r • m) = delta r • m + r • nabla i m) →
      ∃ (hA : perfect (DerivedCategory.Q.obj A)) (f : A ⟶ A⟦(1 : ℤ)⟧),
        (∀ (i : ℤ) (m : A.X i),
          ((f.f i) ≫ (A.shiftFunctorObjXIso (1 : ℤ) i (i + 1) rfl).hom).hom m =
            nabla (i + 1) ((A.d i (i + 1)).hom m) -
              (A.d i (i + 1)).hom (nabla i m)) ∧
        η.app ⟨DerivedCategory.Q.obj A, hA⟩ =
          DerivedCategory.Q.map f ≫ (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app A

private def modelX (i : ℤ) : ModuleCat.{0} Ring :=
  if i = 0 ∨ i = 1 then ModuleCat.of Ring Ring else ModuleCat.of Ring PUnit

private noncomputable def modelD (i : ℤ) : modelX i ⟶ modelX (i + 1) :=
  if hi : i = 0 then
    eqToHom (by simp [modelX, hi]) ≫
      ModuleCat.ofHom (LinearMap.mulLeft Ring (DualNumber.eps : Ring)) ≫
        eqToHom (by simp [modelX, hi])
  else 0

omit [HasDerivedCategory.{w} (ModuleCat.{0} Ring)] in
private theorem modelD_sq (i : ℤ) : modelD i ≫ modelD (i + 1) = 0 := by
  by_cases hi : i = 0
  · subst i
    simp [modelD]
  · simp [modelD, hi]

private noncomputable def model : CochainComplex (ModuleCat.{0} Ring) ℤ :=
  CochainComplex.of modelX modelD modelD_sq

private noncomputable def modelIso₀ : model.X 0 ≅ ModuleCat.of Ring Ring :=
  eqToIso (by simp [model, modelX])

private noncomputable def modelIso₁ : model.X 1 ≅ ModuleCat.of Ring Ring :=
  eqToIso (by simp [model, modelX])

omit [HasDerivedCategory.{w} (ModuleCat.{0} Ring)] in
private theorem model_ge : model.IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  change IsZero (modelX i)
  simp only [modelX, if_neg (show ¬ (i = 0 ∨ i = 1) by omega)]
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

omit [HasDerivedCategory.{w} (ModuleCat.{0} Ring)] in
private theorem model_le : model.IsStrictlyLE 1 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  change IsZero (modelX i)
  simp only [modelX, if_neg (show ¬ (i = 0 ∨ i = 1) by omega)]
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

omit [HasDerivedCategory.{w} (ModuleCat.{0} Ring)] in
private theorem model_terms (i : ℤ) :
    Module.Projective Ring (model.X i) ∧ Module.Finite Ring (model.X i) := by
  by_cases hi : i = 0 ∨ i = 1
  · let e : model.X i ≅ ModuleCat.of Ring Ring := eqToIso (by simp [model, modelX, hi])
    exact ⟨Module.Projective.of_equiv e.toLinearEquiv.symm,
      Module.Finite.equiv e.toLinearEquiv.symm⟩
  · let e : model.X i ≅ ModuleCat.of Ring PUnit.{1} :=
      eqToIso (by simp [model, modelX, hi])
    exact ⟨Module.Projective.of_equiv e.toLinearEquiv.symm,
      Module.Finite.equiv e.toLinearEquiv.symm⟩

omit [HasDerivedCategory.{w} (ModuleCat.{0} Ring)] in
private theorem model_diff (r : Ring) :
    (modelIso₀.inv ≫ model.d 0 1 ≫ modelIso₁.hom).hom r = DualNumber.eps * r := by
  simp only [modelIso₀, modelIso₁, model]
  rfl

private def deltaAdd : Ring →+ Ring where
  toFun := delta
  map_zero' := by simp [delta]
  map_add' := by intros; simp [delta]

omit [HasDerivedCategory.{w} (ModuleCat.{0} Ring)] in
private theorem delta_leibniz (r s : Ring) :
    deltaAdd (r * s) = deltaAdd r * s + r * deltaAdd s := by
  ext
  · simp [deltaAdd, delta, add_comm]
  · simp [deltaAdd, delta, CharTwo.add_self_eq_zero]

private noncomputable def modelConnection (i : ℤ) : model.X i →+ model.X i := by
  by_cases hi : i = 0 ∨ i = 1
  · let e : model.X i ≅ ModuleCat.of Ring Ring := eqToIso (by simp [model, modelX, hi])
    exact e.inv.hom.toAddMonoidHom.comp (deltaAdd.comp e.hom.hom.toAddMonoidHom)
  · exact 0

omit [HasDerivedCategory.{w} (ModuleCat.{0} Ring)] in
private theorem modelConnection_leibniz (i : ℤ) (r : Ring) (m : model.X i) :
    modelConnection i (r • m) = delta r • m + r • modelConnection i m := by
  by_cases hi : i = 0 ∨ i = 1
  · let e : model.X i ≅ ModuleCat.of Ring Ring := eqToIso (by simp [model, modelX, hi])
    simp only [modelConnection, dif_pos hi]
    change e.inv.hom (deltaAdd (e.hom.hom (r • m))) =
      delta r • m + r • e.inv.hom (deltaAdd (e.hom.hom m))
    rw [map_smul, smul_eq_mul, delta_leibniz, map_add]
    change e.inv.hom (delta r • e.hom.hom m) + e.inv.hom (r • _) = _
    rw [map_smul, map_smul]
    simp
  · have : Subsingleton (model.X i) := by
      change Subsingleton (modelX i)
      simp only [modelX, if_neg hi]
      infer_instance
    exact Subsingleton.elim _ _

omit [HasDerivedCategory.{w} (ModuleCat.{0} Ring)] in
private theorem quotient_one_ne_zero :
    (1 : Ring ⧸ Ideal.span {(DualNumber.eps : Ring)}) ≠ 0 := by
  intro h
  have hmem : (1 : Ring) ∈ Ideal.span {(DualNumber.eps : Ring)} := by
    exact (Ideal.Quotient.eq_zero_iff_mem).1 (by simpa using h)
  have hle : Ideal.span {(DualNumber.eps : Ring)} ≤
      RingHom.ker (TrivSqZeroExt.fstHom (ZMod 2) (ZMod 2) (ZMod 2)).toRingHom := by
    rw [Ideal.span_le]
    intro x hx
    have hx' : x = DualNumber.eps := Set.mem_singleton_iff.mp hx
    subst x
    simp
  have hbad := hle hmem
  simp at hbad

private theorem generator_perfect : perfect generator := by
  change DerivedCategory.IsPerfectRingComplex generator
  rw [DerivedCategory.isPerfectRingComplex_eq_triangEnvelope_singleton Ring]
  exact (ObjectProperty.singleton generator).le_triangEnvelope _ (by simp)

private theorem transformation_generator_zero (η : inclusion ⟶ shiftedInclusion)
    (hR : perfect generator) : η.app ⟨generator, hR⟩ = 0 := by
  have : Subsingleton (generator ⟶ generator⟦(1 : ℤ)⟧) := by
    apply (DerivedCategory.subsingleton_singleFunctor_hom_shift_iff_of_projective
      (ModuleCat.of Ring Ring) generator 1).2
    exact ⟨fun f g ↦ (generator.isZero_of_isLE 0 1 (by omega)).eq_of_tgt f g⟩
  change (η.app ⟨generator, hR⟩ : generator ⟶ generator⟦(1 : ℤ)⟧) = 0
  exact this.elim _ _

private noncomputable def shear (η : inclusion ⟶ shiftedInclusion) :
    (inclusion ⊞ shiftedInclusion) ≅ (inclusion ⊞ shiftedInclusion) where
  hom := 𝟙 _ + biprod.fst ≫ η ≫ biprod.inr
  inv := 𝟙 _ - biprod.fst ≫ η ≫ biprod.inr
  hom_inv_id := by
    simp [Preadditive.add_comp, Preadditive.comp_sub, Category.assoc]
  inv_hom_id := by
    simp [Preadditive.sub_comp, Preadditive.comp_add, Category.assoc]

private theorem shear_app_eq_id_iff (η : inclusion ⟶ shiftedInclusion)
    (X : perfect.FullSubcategory) :
    (shear η).hom.app X = 𝟙 ((inclusion ⊞ shiftedInclusion).obj X) ↔ η.app X = 0 := by
  change (𝟙 _ + biprod.fst ≫ η ≫ biprod.inr).app X = _ ↔ _
  simp only [NatTrans.app_add, NatTrans.id_app, NatTrans.comp_app]
  constructor
  · intro h
    have h' := congrArg
      (fun f ↦ (biprod.inl : inclusion ⟶ inclusion ⊞ shiftedInclusion).app X ≫ f ≫
        (biprod.snd : inclusion ⊞ shiftedInclusion ⟶ shiftedInclusion).app X) h
    simpa [Preadditive.comp_add, Preadditive.add_comp, ← NatTrans.comp_app,
      Category.assoc] using h'
  · intro h
    simp [h]

/-- The explicit dual-number counterexample: ∂ induces η:Id→[1], zero on R and equal
to the class 1 in Hom(P,P[1])=R/(ε) on P=[R --ε→ R] in degrees 0 and 1. The displayed
Hom identification is normalized by evaluation of the degree-zero component at 1.
The two automorphisms of Id⊕[1] are the identity and 1+inr η fst, written using the
fully faithful inclusion into D(R).

Source: blueprint sk-lem-sf-determination, counterexample paragraph
(blueprint: lem-sf-generating-class-determination).

Proof: On a projective module choose a splitting into a free module and use the coordinate
operator ∂ to obtain an additive ∂-connection. The Leibniz identity holds in characteristic
two. On a bounded projective complex form a=∇d-d∇: its components are R-linear, and
d a+a d=0. Changing connections changes a by a homotopy. For a chain map g the difference
a_B g-g[1] a_A is the homotopy boundary of ∇_B g-g ∇_A. Bounded above projectives are
K-projective, so the derived-map representation lemma transports these homotopy classes
through all perfect models and proves naturality and independence of the model.
For the bimodule E=R⊕R with (x,y)r=(xr+y∂r,yr), the connection splits E⊗M by
m↦(0,1)⊗m-(1,0)⊗∇m. The differential in these splittings has off-diagonal entry -a,
so its connecting map is a in characteristic two. This identifies the transformation
with the specified bimodule-extension construction.
On R in degree zero the commutator vanishes. On P with differential ε, it is
multiplication by ∂ε=1. Chain maps P→P[1] are scalars r; homotopies change r by a
multiple of ε, giving the normalized additive isomorphism with R/(ε). In particular
1 is nonzero. A finite projective module is a retract of a finite free module. Finite
stupid-tail cone triangles build every bounded finite projective complex from its terms,
so the thick closure of R is precisely Perf(R). Finally 1+inr η fst is natural and has
inverse 1-inr η fst, since fst inr=0. Its component at R is the identity, while its
lower-left block at P is η_P≠0. -/
theorem exists_dualNumber_counterexample :
    ∃ (hR : perfect generator)
      (P : CochainComplex (ModuleCat.{0} Ring) ℤ)
      (e₀ : P.X 0 ≅ ModuleCat.of Ring Ring) (e₁ : P.X 1 ≅ ModuleCat.of Ring Ring)
      (hP : perfect (DerivedCategory.Q.obj P)),
      P.IsStrictlyGE 0 ∧ P.IsStrictlyLE 1 ∧
      (∀ r : Ring, (e₀.inv ≫ P.d 0 1 ≫ e₁.hom).hom r = DualNumber.eps * r) ∧
      (ObjectProperty.singleton generator).triangEnvelope = perfect ∧
      ∃ η : inclusion ⟶ shiftedInclusion,
        InducedByPartial η ∧ η.app ⟨generator, hR⟩ = 0 ∧
        (∃ e : (DerivedCategory.Q.obj P ⟶ (DerivedCategory.Q.obj P)⟦(1 : ℤ)⟧) ≃+
            Ring ⧸ Ideal.span {DualNumber.eps},
          (∀ f : P ⟶ P⟦(1 : ℤ)⟧,
            e (DerivedCategory.Q.map f ≫
                (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app P) =
              Ideal.Quotient.mk (Ideal.span {DualNumber.eps})
                ((e₀.inv ≫ f.f 0 ≫
                  (P.shiftFunctorObjXIso (1 : ℤ) 0 1 rfl).hom ≫ e₁.hom).hom 1)) ∧
          e (η.app ⟨DerivedCategory.Q.obj P, hP⟩) = 1) ∧
        η.app ⟨DerivedCategory.Q.obj P, hP⟩ ≠ 0 ∧
        ∃ T : (inclusion ⊞ shiftedInclusion) ≅ (inclusion ⊞ shiftedInclusion),
          T.hom = 𝟙 _ + biprod.fst ≫ η ≫ biprod.inr ∧
          T.hom.app ⟨generator, hR⟩ = 𝟙 ((inclusion ⊞ shiftedInclusion).obj ⟨generator, hR⟩) ∧
          T.hom.app ⟨DerivedCategory.Q.obj P, hP⟩ ≠
            𝟙 ((inclusion ⊞ shiftedInclusion).obj ⟨DerivedCategory.Q.obj P, hP⟩) := by
  classical
  let hR := generator_perfect
  let hP : perfect (DerivedCategory.Q.obj model) :=
    ⟨model, 0, 1, model_ge, model_le, model_terms, ⟨Iso.refl _⟩⟩
  obtain ⟨η, hη⟩ := DerivedCategory.exists_perfect_derivation_transformation Ring
    deltaAdd delta_leibniz
  have hind : InducedByPartial η := hη
  obtain ⟨e, he⟩ := DerivedCategory.exists_twoTerm_selfExtension_hom_equiv Ring
    model modelIso₀ modelIso₁ DualNumber.eps model_ge model_le model_diff
  obtain ⟨hP', f, hf, hηf⟩ := hind model 0 1 model_ge model_le model_terms
    modelConnection modelConnection_leibniz
  have hvalue : e (η.app ⟨DerivedCategory.Q.obj model, hP⟩) = 1 := by
    rw [hηf, he]
    have hf0 := hf 0 (modelIso₀.inv.hom 1)
    have hv : (modelIso₀.inv ≫ f.f 0 ≫
        (model.shiftFunctorObjXIso (1 : ℤ) 0 1 rfl).hom ≫ modelIso₁.hom).hom 1 = 1 := by
      simpa [modelConnection, modelIso₀, modelIso₁, model, modelX, modelD,
        CochainComplex.of.d, deltaAdd, delta] using hf0
    rw [hv]
    rfl
  have hnonzero : η.app ⟨DerivedCategory.Q.obj model, hP⟩ ≠ 0 := by
    intro h
    have hbad : (1 : Ring ⧸ Ideal.span {(DualNumber.eps : Ring)}) = 0 := by
      rw [← hvalue, h, map_zero]
    exact quotient_one_ne_zero hbad
  refine ⟨hR, model, modelIso₀, modelIso₁, hP, model_ge, model_le, model_diff,
    (DerivedCategory.isPerfectRingComplex_eq_triangEnvelope_singleton Ring).symm,
    η, hind, transformation_generator_zero η hR, ⟨e, he, hvalue⟩, hnonzero,
    shear η, rfl, ?_, ?_⟩
  · exact (shear_app_eq_id_iff η ⟨generator, hR⟩).2 (transformation_generator_zero η hR)
  · exact fun h ↦ hnonzero ((shear_app_eq_id_iff η _).1 h)

end GeneratingClassCounterexample

end CategoryTheory
