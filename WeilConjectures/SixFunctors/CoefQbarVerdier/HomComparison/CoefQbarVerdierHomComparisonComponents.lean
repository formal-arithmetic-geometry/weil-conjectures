/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierData
/-! # Explicit finite-stage dual-to-Hom comparison components

Source: the coefficient-transport paragraph of blueprint
sec-six-functors-basics/sk-prop-sf-biduality-general, retained
thm-coef-qbar-verdier step 5.

The object components are constructed from the published operations. Naturality
within each finite stage is proved here; compatibility with changing the field
of definition is a separate scalar square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] WeilConjectures.rationalDerivedInternalHom
  WeilConjectures.commonStageHomComparison CategoryTheory.StageSystem.PairCategory.mkHom
set_option allowUnsafeReducibility true in
attribute [local reducible] WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageCategory
universe u v
open CategoryTheory Opposite AlgebraicGeometry
namespace WeilConjectures.CoefQbarVerdier.HomComparison
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion stageSystem)

private theorem comp_eqToHom_of_heq {C : Type*} [Category C]
    {A B A' B' : C} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B') (hfg : HEq f g) :
    f ≫ eqToHom hB = eqToHom hA ≫ g := by
  subst hA
  subst hB
  cases hfg
  simp

private theorem conjugate_naturality {C : Type*} [Category C]
    {A B A' B' A'' B'' : C} (hA : A = A') (hB : B = B')
    (eA : A' ≅ A'') (eB : B' ≅ B'')
    (f : A ⟶ B) (g : A'' ⟶ B'')
    (hfg : HEq f (eA.hom ≫ g ≫ eB.inv)) :
    f ≫ (eqToIso hB ≪≫ eB).hom = (eqToIso hA ≪≫ eA).hom ≫ g := by
  dsimp only [Iso.trans_hom, eqToIso.hom]
  rw [← Category.assoc, comp_eqToHom_of_heq hA hB f _ hfg]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem mkHom_conjugate
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)] (S : StageSystem C)
    {A B : S.PairCategory} {L : I} (hA : A.stage ≤ L) (hB : B.stage ≤ L)
    {M N : C L} (eA : A.toStage hA ≅ M) (eB : B.toStage hB ≅ N) (f : M ⟶ N) :
    StageSystem.PairCategory.mkHom L hA hB (eA.hom ≫ f ≫ eB.inv) =
      (S.isoToStage A hA ≪≫ (S.ι L).mapIso eA).hom ≫ (S.ι L).map f ≫
        (S.isoToStage B hB ≪≫ (S.ι L).mapIso eB).inv := by
  rw [StageSystem.mkHom_eq_isoToStage]
  simp only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u})

/-- The specified common-stage Hom compared with its value at a larger finite stage.
Source: the finite-coefficient transport in blueprint thm-coef-qbar-verdier, step 5.
(blueprint: def-coef-qbar-verdier-hom-comparison-components).

Construction/proof: Compose its literal object equality, the pair-category stage isomorphism,
and the recorded Hom comparison. -/
def homToStage (P : (commonStageHomPairs l Ω X).FullSubcategory)
    (L : Index l Ω) (h : (commonStageHomObject l Ω X P).stage ≤ L) :
    (commonStageDerivedInternalHom l Ω X).obj P ≅
      (inclusion L).obj ((rationalDerivedInternalHom l (Coefficient.{u} l Ω L) X).obj
        (commonStageHomPairAtStage l Ω X P L h)) :=
  eqToIso ((commonStageDerivedInternalHom_existsUnique l Ω X).exists.choose_spec.1 P) ≪≫
    (stageSystem l Ω X).isoToStage (commonStageHomObject l Ω X P) h ≪≫
    (inclusion L).mapIso (commonStageHomComparison l Ω X P L h)

/-- The Hom comparison carries a representative to its finite internal-Hom map.
Source: the finite-coefficient transport in blueprint thm-coef-qbar-verdier, step 5.
(blueprint: def-coef-qbar-verdier-hom-comparison-components).

Construction/proof: Use the representative formula of
commonStageDerivedInternalHom_existsUnique. Factor the output representative through isoToStage,
map its two comparison isomorphisms, and cancel the target inverse. -/
theorem homToStage_naturality
    (P Q : (commonStageHomPairs l Ω X).FullSubcategory)
    (L : Index l Ω)
    (h : (commonStageHomObject l Ω X P).stage ≤ L)
    (h' : (commonStageHomObject l Ω X Q).stage ≤ L)
    (a : (commonStageHomPairAtStage l Ω X Q L h').obj.1.unop ⟶
      (commonStageHomPairAtStage l Ω X P L h).obj.1.unop)
    (b : (commonStageHomPairAtStage l Ω X P L h).obj.2 ⟶
      (commonStageHomPairAtStage l Ω X Q L h').obj.2) :
    let f : P ⟶ Q := ObjectProperty.homMk (Prod.mkHom
      (StageSystem.PairCategory.mkHom L
        (((Padic.finiteCoefficientFields_properties l Ω).1
          Q.obj.1.unop.stage Q.obj.2.stage).1.trans h')
        (((Padic.finiteCoefficientFields_properties l Ω).1
          P.obj.1.unop.stage P.obj.2.stage).1.trans h) a).op
      (StageSystem.PairCategory.mkHom L
        (((Padic.finiteCoefficientFields_properties l Ω).1
          P.obj.1.unop.stage P.obj.2.stage).2.trans h)
        (((Padic.finiteCoefficientFields_properties l Ω).1
          Q.obj.1.unop.stage Q.obj.2.stage).2.trans h') b))
    (commonStageDerivedInternalHom l Ω X).map f ≫ (homToStage l Ω X Q L h').hom =
      (homToStage l Ω X P L h).hom ≫
        (inclusion L).map ((rationalDerivedInternalHom l (Coefficient.{u} l Ω L) X).map
          (ObjectProperty.homMk (Prod.mkHom a.op b))) := by
  dsimp only
  have hm := (commonStageDerivedInternalHom_existsUnique l Ω X).exists.choose_spec.2
    P Q L h h' a b
  have he := mkHom_conjugate (stageSystem l Ω X) h h'
    (commonStageHomComparison l Ω X P L h)
    (commonStageHomComparison l Ω X Q L h')
    ((rationalDerivedInternalHom l (Coefficient.{u} l Ω L) X).map
      (ObjectProperty.homMk (Prod.mkHom a.op b)))
  have hf := conjugate_naturality
    ((commonStageDerivedInternalHom_existsUnique l Ω X).exists.choose_spec.1 P)
    ((commonStageDerivedInternalHom_existsUnique l Ω X).exists.choose_spec.1 Q)
    ((stageSystem l Ω X).isoToStage (commonStageHomObject l Ω X P) h ≪≫
      (inclusion L).mapIso (commonStageHomComparison l Ω X P L h))
    ((stageSystem l Ω X).isoToStage (commonStageHomObject l Ω X Q) h' ≪≫
      (inclusion L).mapIso (commonStageHomComparison l Ω X Q L h'))
    _ _ (hm.trans (heq_of_eq he))
  simpa only [homToStage, Iso.trans_hom, Category.assoc,
    commonStageDerivedInternalHom, GeneralAlgebraicallyClosedCoefficients.inclusion] using hf

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Every common-stage pair is permitted by finite rational Hom closure.
Source: the finite-coefficient transport in blueprint thm-coef-qbar-verdier, step 5.
(blueprint: def-coef-qbar-verdier-hom-comparison-components).

Construction/proof: Apply the recorded HomIdentification at the literal compositum of the input
stages. -/
theorem allPairs (F : Finite D l hl Ω X)
    (K M : generalAlgebraicallyClosedConstructibleCategory l Ω X) :
    commonStageHomPairs l Ω X (op K, M) :=
  (F.hom (Padic.finiteCoefficientCompositum l Ω K.stage M.stage)).permitted _ _

/-- Include a pair of finite-stage objects into the permitted common-stage pairs.
Source: the finite-coefficient transport in blueprint thm-coef-qbar-verdier, step 5.
(blueprint: def-coef-qbar-verdier-hom-comparison-components).

Construction/proof: Lift the product of the opposite stage inclusion and the stage inclusion
using finite Hom closure. -/
def stagePairs (F : Finite D l hl Ω X) (E : Index l Ω) :
    (Stage l Ω X E)ᵒᵖ × Stage l Ω X E ⥤ (commonStageHomPairs l Ω X).FullSubcategory :=
  (commonStageHomPairs l Ω X).lift ((inclusion E).op.prod (inclusion E))
    (fun P ↦ allPairs l Ω X D hl F ((inclusion E).obj P.1.unop) ((inclusion E).obj P.2))

/-- The finite internal-Hom functor on all pairs allowed by the recorded closure proof.
Source: the finite-coefficient transport in blueprint thm-coef-qbar-verdier, step 5.
(blueprint: def-coef-qbar-verdier-hom-comparison-components).

Construction/proof: Compose the full-subcategory lift with the published rational internal Hom. -/
def stageHom (F : Finite D l hl Ω X) (E : Index l Ω) :
    (Stage l Ω X E)ᵒᵖ × Stage l Ω X E ⥤ Stage l Ω X E :=
  RationalOperations.homPair l (Coefficient.{u} l Ω E) X (F.hom E).permitted ⋙
    rationalDerivedInternalHom l (Coefficient.{u} l Ω E) X

omit [IsAlgClosure (Padic l) Ω] in
/-- The compositum of a finite coefficient field with itself lies in that field.
Source: the finite-coefficient transport in blueprint thm-coef-qbar-verdier, step 5.
(blueprint: def-coef-qbar-verdier-hom-comparison-components).

Construction/proof: The underlying field is its supremum with itself; apply sup_le to the two
reflexive inequalities. -/
theorem selfCompositum_le (E : Index l Ω) :
    Padic.finiteCoefficientCompositum l Ω E E ≤ E := by
  change E.val ⊔ E.val ≤ E.val
  exact sup_le le_rfl le_rfl

/-- The product of the two repeated-stage transition functors.
Source: the finite-coefficient transport in blueprint thm-coef-qbar-verdier, step 5.
(blueprint: def-coef-qbar-verdier-hom-comparison-components).

Construction/proof: Use the opposite transition in the first variable and the transition in the
second variable. -/
def stageSelf (E : Index l Ω) :
    (Stage l Ω X E)ᵒᵖ × Stage l Ω X E ⥤ (Stage l Ω X E)ᵒᵖ × Stage l Ω X E :=
  ((stageSystem l Ω X).T (le_refl E)).op.prod ((stageSystem l Ω X).T (le_refl E))

/-- Common-stage Hom of a finite pair compared with Hom of its self-extended pair.
Source: the finite-coefficient transport in blueprint thm-coef-qbar-verdier, step 5.
(blueprint: def-coef-qbar-verdier-hom-comparison-components).

Construction/proof: Apply homToStage at the original field. Its naturality follows from
homToStage_naturality because inclusion maps are the identity-stage representatives. -/
def stageToSelf (F : Finite D l hl Ω X) (E : Index l Ω) :
    stagePairs l Ω X D hl F E ⋙ commonStageDerivedInternalHom l Ω X ≅
      stageSelf l Ω X E ⋙ stageHom l Ω X D hl F E ⋙ inclusion E :=
  NatIso.ofComponents
    (fun P ↦ homToStage l Ω X ((stagePairs l Ω X D hl F E).obj P) E
      (selfCompositum_le l Ω E)) (fun {P Q} f ↦ by
        exact homToStage_naturality l Ω X
          ((stagePairs l Ω X D hl F E).obj P)
          ((stagePairs l Ω X D hl F E).obj Q) E
          (selfCompositum_le l Ω E) (selfCompositum_le l Ω E)
          (((stageSystem l Ω X).T (le_refl E)).map f.1.unop)
          (((stageSystem l Ω X).T (le_refl E)).map f.2))

/-- The unit isomorphism for the actual stage-system self transition.
Source: the finite-coefficient transport in blueprint thm-coef-qbar-verdier, step 5.
(blueprint: def-coef-qbar-verdier-hom-comparison-components).

Construction/proof: Compose the equality from the normalized stage system with the published
scalar unitor. -/
def stageUnit (E : Index l Ω) :
    (stageSystem l Ω X).T (le_refl E) ≅ 𝟭 (Stage l Ω X E) :=
  operationStageTransitionIso l Ω X E E le_rfl ≪≫
    GeneralAlgebraicallyClosedCoefficients.unitor l Ω X E

/-- Remove the two self transitions from a finite pair.
Source: the finite-coefficient transport in blueprint thm-coef-qbar-verdier, step 5.
(blueprint: def-coef-qbar-verdier-hom-comparison-components).

Construction/proof: Take the product of the opposite inverse scalar unitor and the scalar
unitor. -/
def stageSelfIso (E : Index l Ω) : stageSelf l Ω X E ≅ 𝟭 _ :=
  NatIso.prod (NatIso.op (stageUnit l Ω X E)).symm (stageUnit l Ω X E)

/-- The finite internal-Hom functor commutes with stage inclusion.
Source: the finite-coefficient transport in blueprint thm-coef-qbar-verdier, step 5.
(blueprint: def-coef-qbar-verdier-hom-comparison-components).

Construction/proof: Compare common-stage Hom with Hom of the self-extended pair, remove the two
self transitions by stageSelfIso, and invert. -/
def stageHomInclusion (F : Finite D l hl Ω X) (E : Index l Ω) :
    stageHom l Ω X D hl F E ⋙ inclusion E ≅
      stagePairs l Ω X D hl F E ⋙ commonStageDerivedInternalHom l Ω X :=
  ((stageToSelf l Ω X D hl F E) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (stageSelfIso l Ω X E) (stageHom l Ω X D hl F E))
      (inclusion E)).symm

/-- The dual-to-Hom comparison is natural on every fixed finite stage.
Source: the finite-coefficient transport in blueprint thm-coef-qbar-verdier, step 5.
(blueprint: def-coef-qbar-verdier-hom-comparison-components).

Construction/proof: Invert the recorded duality inclusion comparison, include the finite
HomIdentification, apply stageHomInclusion, and map the recorded omegaComparison in the second
Hom variable. Functoriality of internal Hom proves naturality of the last factor. -/
@[irreducible] def localComparison (B : Duality D l hl Ω X) (E : Index l Ω) :
    (inclusion E).op ⋙ B.duality.dual ≅
      (inclusion E).op ⋙ homDual l Ω X B.omega
        (fun K ↦ allPairs l Ω X D hl B.finite K B.omega) := by
  let w := (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
    (B.finite.omega E).omega
  let C : (Stage l Ω X E)ᵒᵖ ⥤ (Stage l Ω X E)ᵒᵖ × Stage l Ω X E :=
    (𝟭 _).prod' ((Functor.const _).obj w)
  let e : C ⋙ stagePairs l Ω X D hl B.finite E ⋙
        commonStageDerivedInternalHom l Ω X ≅
      (inclusion E).op ⋙ homDual l Ω X B.omega
        (fun K ↦ allPairs l Ω X D hl B.finite K B.omega) :=
    NatIso.ofComponents (fun K ↦
      (commonStageDerivedInternalHom l Ω X).mapIso
        (ObjectProperty.isoMk _ (Iso.prod (Iso.refl _) (B.omegaComparison E)))) (by
      intro K M f
      dsimp [homDual, stagePairs, C]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      apply ObjectProperty.hom_ext
      ext <;> simp)
  exact (B.comparison E).symm ≪≫
    Functor.isoWhiskerRight (B.finite.hom E).duality (inclusion E) ≪≫
    Functor.isoWhiskerLeft C (stageHomInclusion l Ω X D hl B.finite E) ≪≫ e

/-- The specified dual-to-Hom isomorphism at each literal pair object.
Source: the finite-coefficient transport in blueprint thm-coef-qbar-verdier, step 5.
(blueprint: def-coef-qbar-verdier-hom-comparison-components).

Construction/proof: Evaluate localComparison at the actual stage and actual object of the pair.
All data are explicit composites of the recorded comparisons. -/
@[irreducible] def component (B : Duality D l hl Ω X)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) :
    B.duality.dual.obj (op K) ≅
      (homDual l Ω X B.omega (fun K ↦ allPairs l Ω X D hl B.finite K B.omega)).obj
        (op K) :=
  (localComparison l Ω X D hl B K.stage).app (op K.obj)

/-- The specified components are natural for maps included from one finite stage.
Source: the finite-coefficient transport in blueprint thm-coef-qbar-verdier, step 5.
(blueprint: def-coef-qbar-verdier-hom-comparison-components).

Construction/proof: Apply naturality of localComparison and unfold only the component and
inclusion presentations. -/
theorem component_naturality_stage (B : Duality D l hl Ω X)
    (E : Index l Ω) {K M : Stage l Ω X E} (f : K ⟶ M) :
    B.duality.dual.map ((inclusion E).map f).op ≫
        (component l Ω X D hl B ((inclusion E).obj K)).hom =
      (component l Ω X D hl B ((inclusion E).obj M)).hom ≫
        (homDual l Ω X B.omega (fun K ↦ allPairs l Ω X D hl B.finite K B.omega)).map
          ((inclusion E).map f).op := by
  simpa only [component, GeneralAlgebraicallyClosedCoefficients.inclusion,
    StageSystem.ι_obj, Functor.comp_map, Functor.op_map, Iso.app_hom,
    Functor.comp_obj, Functor.op_obj, Quiver.Hom.unop_op] using
    (localComparison l Ω X D hl B E).hom.naturality f.op

end WeilConjectures.CoefQbarVerdier.HomComparison
