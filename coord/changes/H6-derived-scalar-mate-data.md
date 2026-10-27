# AlgebraicGeometry.Scheme.DerivedScalarMate shared comparison data

## Reason

The two geometric proof dependencies must use the existing normalized comparison definitions,
while the item must import those dependencies. Move the existing auxiliary declarations together
to `Sheaf.Paper.DerivedScalarMateData` and publicly reexport that module from the item to avoid
an import cycle. Every existing public name, signature, definition body, and old public import
remains available to consumers. This is a module relocation, not a change of any operation.
The pre-existing `derivedTensorIso_existsUnique` hole is moved unchanged and separately attached;
only the principal theorem receives a new proof assembled from smaller statements.

## Old

The item itself held the following unchanged declarations, including the ordinary proof and
the pre-existing derived-tensor normalization hole. This is the original text verbatim:

```lean
module

public import Sheaf.Paper.FourCorners
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import Sheaf.Paper.ProEtaleProjectionFormulaArrows
public import Sheaf.Paper.ProjectionFormulaBaseChangeNaturality
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Sheaf.Paper.KFlatScalarComparisonNormalization
public import Sheaf.Paper.RingedProjectionFirstShift
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
import Sheaf.Algebra.Homology.ExtensionTensorComparisonIndependent
import Sheaf.SecSmoothPurity.ModuleTensorGenerators

/-! # The derived scalar mate and its thick isomorphism locus

Source: blueprint main-20261015, sk-thm-sf-ctf-stability-direct-images.proof.md,
paragraph (3), agent-extracted ring-sheaf subargument; Stacks Tags 03EL, 06YY,
07A4, 07A6, 0G7E, 0FPT and 014A
(blueprint: lem-sfb-derived-scalar-mate-thick-locus).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme.DerivedScalarMate

/-- The actual scalar restriction, with unchanged underlying abelian sheaf.
Source: Stacks 03EK (blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
noncomputable abbrev restriction {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) :=
  Scheme.proEtaleRingRestrictScalars φ

/-- The coefficient B_W with its A_W action, without deriving or resolving B.
Source: Stacks 0B56 (blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
noncomputable abbrev coefficient {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) :=
  (restriction φ).obj (SheafOfModules.unit
    ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B))

/-- The degree-zero coefficient complex B_W, as an A_W-module complex.
Source: Stacks 0B56 (blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
noncomputable abbrev coefficientComplex {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) :=
  (CochainComplex.singleFunctor (Scheme.proEtaleRingModules W
    A) (0 : ℤ)).obj (coefficient φ)

/-- The existing ordinary tensor with B as its last factor.
Source: Stacks 03EK (blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
noncomputable abbrev ordinaryTensor {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) :=
  (Scheme.proEtaleOrdinaryTensor W A).flip.obj
    (coefficient φ)

/-- The original sheafification image of b tensor m in scalar extension.
Source: Stacks 03EK (blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
noncomputable def pureSection {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B)
    (M : Scheme.proEtaleRingModules W A)
    (U : W.ProEtᵒᵖ) (b : B.obj.obj U)
    (m : M.val.obj U) :
    (SheafOfModules.changeOfRings φ M).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (R := (sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)
    (𝟙 _)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
            φ M)).app U)
    (b ⊗ₜ[_, (φ.hom.app U).hom] m)

/-- The normalization on all sectionwise pure tensors, including nonconstant local scalars.
Source: Stacks 03EK (blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
def IsOrdinaryTensor {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B)
    (e : Scheme.proEtaleRingExtension φ ⋙
      restriction φ ≅ ordinaryTensor φ) : Prop :=
  ∀ (M : Scheme.proEtaleRingModules W A)
    (U : W.ProEtᵒᵖ) (b : B.obj.obj U)
    (m : M.val.obj U),
    ((restriction φ).map
      (eqToHom (Scheme.proEtaleRingExtension_obj
        φ M).symm) ≫
      e.hom.app M).val.app U (pureSection φ M U b m) =
        Scheme.proEtaleTensorPair W A M
          (coefficient φ) U m b

private theorem tensorPair_hom_ext {W : Scheme.{u}}
    (A : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1})
    {M N H : Scheme.proEtaleRingModules W A}
    {v w : ((Scheme.proEtaleOrdinaryTensor W A).obj M).obj N ⟶ H}
    (h : ∀ U m n, v.val.app U (Scheme.proEtaleTensorPair W A M N U m n) =
      w.val.app U (Scheme.proEtaleTensorPair W A M N U m n)) : v = w := by
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A).obj)).homEquiv
        (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  exact h U

private theorem pureSection_toSheafify {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) (M : Scheme.proEtaleRingModules W A)
    (U : W.ProEtᵒᵖ) (b : B.obj.obj U) (m : M.val.obj U) :
    pureSection φ M U b m =
      (toSheafify (Scheme.ProEt.topology W)
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
          (b ⊗ₜ[_, (φ.hom.app U).hom] m) := by
  have h :=
    PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app.{u + 1, u, u + 1, u + 1}
    (J := Scheme.ProEt.topology W)
    (𝟙 ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B).obj)
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M)
  exact congrArg (fun q ↦ q.app U (b ⊗ₜ[_, (φ.hom.app U).hom] m)) h

private theorem pureSection_map {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) {M N : Scheme.proEtaleRingModules W A} (v : M ⟶ N)
    (U : W.ProEtᵒᵖ) (b : B.obj.obj U) (m : M.val.obj U) :
    (SheafOfModules.changeOfRingsHom φ M v).val.app U (pureSection φ M U b m) =
      pureSection φ N U b (v.val.app U m) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B).obj)
  let q : SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M ⟶
      SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ N :=
    { app := fun V ↦ (ModuleCat.extendScalars (φ.hom.app V).hom).map (v.val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality φ M v }
  exact (congrArg (fun k ↦ k.app U (b ⊗ₜ[_, (φ.hom.app U).hom] m))
    (adj.unit.naturality q)).symm

private theorem extension_map_eq {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) {M N : Scheme.proEtaleRingModules W A} (v : M ⟶ N) :
    (Scheme.proEtaleRingExtension φ).map v =
      eqToHom (Scheme.proEtaleRingExtension_obj φ M) ≫
        SheafOfModules.changeOfRingsHom φ M v ≫
          eqToHom (Scheme.proEtaleRingExtension_obj φ N).symm := by
  exact (Scheme.reductionChangeExistence W φ).choose_spec.choose_spec.choose v

private noncomputable def ordinaryComponent {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) (M : Scheme.proEtaleRingModules W A) :
    (ordinaryTensor φ).obj M ≅
      (restriction φ).obj ((Scheme.proEtaleRingExtension φ).obj M) := by
  let := SheafOfModules.monoidalCategory A
  let := SheafOfModules.symmetricCategory A
  exact (BraidedCategory.braiding M (coefficient φ)) ≪≫
    (SheafOfModules.IndependentExtensionTensor.exists_extensionTensorComparison φ M).choose ≪≫
      (restriction φ).mapIso (eqToIso (Scheme.proEtaleRingExtension_obj φ M).symm)

private theorem ordinaryComponent_pure {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) (M : Scheme.proEtaleRingModules W A)
    (U : W.ProEtᵒᵖ) (m : M.val.obj U) (b : B.obj.obj U) :
    (ordinaryComponent φ M).hom.val.app U
        (Scheme.proEtaleTensorPair W A M (coefficient φ) U m b) =
      ((restriction φ).map (eqToHom (Scheme.proEtaleRingExtension_obj φ M).symm)).val.app U
        (pureSection φ M U b m) := by
  let := SheafOfModules.monoidalCategory A
  let := SheafOfModules.symmetricCategory A
  have he :=
    (SheafOfModules.IndependentExtensionTensor.exists_extensionTensorComparison φ M).choose_spec
      U b m
  have hb := CategoryTheory.CochainPullback.moduleTmul_braiding M (coefficient φ) U m b
  change ((eqToHom (Scheme.proEtaleRingExtension_obj φ M).symm).val.app U)
    (((SheafOfModules.IndependentExtensionTensor.exists_extensionTensorComparison φ M).choose
      ).hom.val.app U
        ((BraidedCategory.braiding M (coefficient φ)).hom.val.app U
          (Scheme.proEtaleTensorPair W A M (coefficient φ) U m b))) = _
  rw [show (BraidedCategory.braiding M (coefficient φ)).hom.val.app U
      (Scheme.proEtaleTensorPair W A M (coefficient φ) U m b) =
        Scheme.proEtaleTensorPair W A (coefficient φ) M U b m from hb]
  rw [show ((SheafOfModules.IndependentExtensionTensor.exists_extensionTensorComparison
      φ M).choose).hom.val.app U
        (Scheme.proEtaleTensorPair W A (coefficient φ) M U b m) = _ from he]
  rw [pureSection_toSheafify]
  rfl

private theorem ordinaryComponent_naturality {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) {M N : Scheme.proEtaleRingModules W A} (v : M ⟶ N) :
    (ordinaryTensor φ).map v ≫ (ordinaryComponent φ N).hom =
      (ordinaryComponent φ M).hom ≫
        (restriction φ).map ((Scheme.proEtaleRingExtension φ).map v) := by
  let := SheafOfModules.monoidalCategory A
  apply tensorPair_hom_ext A
  intro U m b
  have ht := CategoryTheory.CochainPullback.moduleTmul_map v (𝟙 (coefficient φ)) U m b
  simp only [MonoidalCategory.tensorHom_id, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply] at ht
  change (ordinaryComponent φ N).hom.val.app U
      (((ordinaryTensor φ).map v).val.app U
        (Scheme.proEtaleTensorPair W A M (coefficient φ) U m b)) =
    ((restriction φ).map ((Scheme.proEtaleRingExtension φ).map v)).val.app U
      ((ordinaryComponent φ M).hom.val.app U
        (Scheme.proEtaleTensorPair W A M (coefficient φ) U m b))
  rw [show (((ordinaryTensor φ).map v).val.app U)
      (Scheme.proEtaleTensorPair W A M (coefficient φ) U m b) =
        Scheme.proEtaleTensorPair W A N (coefficient φ) U (v.val.app U m) b from ht]
  rw [ordinaryComponent_pure, ordinaryComponent_pure]
  have hcomp :
      (restriction φ).map (eqToHom (Scheme.proEtaleRingExtension_obj φ M).symm) ≫
        (restriction φ).map ((Scheme.proEtaleRingExtension φ).map v) =
      (restriction φ).map (SheafOfModules.changeOfRingsHom φ M v) ≫
        (restriction φ).map (eqToHom (Scheme.proEtaleRingExtension_obj φ N).symm) := by
    rw [← Functor.map_comp, extension_map_eq]
    simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp,
      Functor.map_comp]
  change _ = (((restriction φ).map
    (eqToHom (Scheme.proEtaleRingExtension_obj φ M).symm) ≫
      (restriction φ).map ((Scheme.proEtaleRingExtension φ).map v)).val.app U)
        (pureSection φ M U b m)
  rw [hcomp]
  change _ = (eqToHom (Scheme.proEtaleRingExtension_obj φ N).symm).val.app U
    ((SheafOfModules.changeOfRingsHom φ M v).val.app U (pureSection φ M U b m))
  rw [pureSection_map]
  rfl

/-- The canonical ordinary identification, uniquely fixed by balanced pure tensors.
Source: Stacks 03EK, 06YY (blueprint: lem-sfb-derived-scalar-mate-thick-locus).
Proof: the restricted scalar extension and tensor have the same balanced tensor
abelian presheaf, with factors reversed. Sheafify this identification. The inverse
reverses the factors back; both composites fix pure tensors. The balancing relation
proves linearity, and id tensor a proves naturality. Sheafification uniqueness proves
that the displayed formula determines the natural isomorphism uniquely. This is
step 1 of the node, retaining its specified normalization. -/
theorem ordinaryTensorIso_existsUnique
    {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) :
    ∃! e : Scheme.proEtaleRingExtension φ ⋙
        restriction φ ≅ ordinaryTensor φ,
      IsOrdinaryTensor φ e := by
  let c : ordinaryTensor φ ≅ Scheme.proEtaleRingExtension φ ⋙ restriction φ :=
    NatIso.ofComponents (ordinaryComponent φ) (fun v ↦ ordinaryComponent_naturality φ v)
  have hc : ∀ (M : Scheme.proEtaleRingModules W A) (U : W.ProEtᵒᵖ)
      (b : B.obj.obj U) (m : M.val.obj U),
      (c.hom.app M).val.app U
        (Scheme.proEtaleTensorPair W A M (coefficient φ) U m b) =
      ((restriction φ).map (eqToHom (Scheme.proEtaleRingExtension_obj φ M).symm)).val.app U
        (pureSection φ M U b m) := fun M U b m ↦ ordinaryComponent_pure φ M U m b
  have hn : IsOrdinaryTensor φ c.symm := by
    intro M U b m
    change (c.inv.app M).val.app U
      (((restriction φ).map (eqToHom (Scheme.proEtaleRingExtension_obj φ M).symm)).val.app U
        (pureSection φ M U b m)) = _
    rw [← hc]
    exact congrArg (fun v ↦ v.val.app U
      (Scheme.proEtaleTensorPair W A M (coefficient φ) U m b)) (c.hom_inv_id_app M)
  refine ⟨c.symm, hn, ?_⟩
  intro e he
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (cancel_epi (c.hom.app M)).mp
  change c.hom.app M ≫ e.hom.app M = c.hom.app M ≫ c.inv.app M
  apply tensorPair_hom_ext A
  intro U m b
  change (e.hom.app M).val.app U
      ((c.hom.app M).val.app U (Scheme.proEtaleTensorPair W A M (coefficient φ) U m b)) =
    (c.inv.app M).val.app U
      ((c.hom.app M).val.app U (Scheme.proEtaleTensorPair W A M (coefficient φ) U m b))
  rw [hc]
  exact (he M U b m).trans (hn M U b m).symm

/-- The uniquely normalized ordinary identification; its data are determined by the formula.
Source: Stacks 03EK (blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
noncomputable def ordinaryTensorIso
    {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) :=
  Classical.choose (ordinaryTensorIso_existsUnique φ).exists


/-- On complexes, reverse the balanced tensors degreewise and use the degree-zero
single-factor identification. This is an actual chain isomorphism.
Source: Stacks 06YY (blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
noncomputable def ordinaryComplexIso
    {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B)
    (P : CochainComplex (Scheme.proEtaleRingModules W A) ℤ) :=
  (Functor.mapHomologicalComplexCompIso (ordinaryTensorIso φ)
    (ComplexShape.up ℤ)).app P ≪≫
      (CochainComplex.mapBifunctorSingle₂Iso
        (Scheme.proEtaleOrdinaryTensor W A)
        (coefficient φ) P).symm

/-- The full normalization of h on two flat K-flat representatives, resolving B too.
The equation uses Q → B[0] only after tensoring with the K-flat first factor.
Source: Stacks 06YY, 07A4 (blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
def IsDerivedTensor {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B)
    (a : Scheme.ProEtaleTensorModel W A)
    (h : Scheme.proEtaleRingDerivedExtension φ ⋙ (restriction φ).mapDerivedCategory ≅
      (Functor.curryObj a.tensor).flip.obj
        (DerivedCategory.Q.obj (coefficientComplex φ))) : Prop :=
  ∀ (P Q : CochainComplex (Scheme.proEtaleRingModules W
      A) ℤ)
    (hp : Scheme.proEtaleFlatRepresentatives W A P)
    (hq : Scheme.proEtaleFlatRepresentatives W A Q)
    (q : Q ⟶ coefficientComplex φ), QuasiIso q →
    a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) ≫
      a.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map q)) ≫
      h.inv.app (DerivedCategory.Q.obj P) ≫
      (restriction φ).mapDerivedCategory.map
        ((Scheme.proEtaleRingDerivedExtensionCounit
          φ).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≫
      (restriction φ).mapDerivedCategoryFactorsh.hom.app
        (((Scheme.proEtaleRingExtension
          φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) =
    DerivedCategory.Q.map
      (HomologicalComplex.mapBifunctorMap (𝟙 P) q
        (Scheme.proEtaleOrdinaryTensor W A)
        (ComplexShape.up ℤ) ≫ (ordinaryComplexIso φ P).inv)

/-- The restricted extension is the derived tensor with B, with its full normalization.
Source: Stacks 06YY, 07A4 (blueprint: lem-sfb-derived-scalar-mate-thick-locus).
Proof: use step 1 of the node. Resolve the first input P and B[0] by flat K-flat
complexes. The ordinary complex identification is identity on the balanced tensor,
with the symmetry putting B last. Tensoring P with the resolution of B is a
quasi-isomorphism because P is K-flat, even when B is nonflat. The scalar derived
counit is invertible on P. These maps construct h and give the displayed equation.
Naturality descends from the ordinary comparison through the resolving-class
localization. Every derived object has such a representative, so the equation
uniquely determines h, including compatibility with changes of resolutions. -/
theorem derivedTensorIso_existsUnique
    {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B)
    (a : Scheme.ProEtaleTensorModel W A) :
    ∃! h : Scheme.proEtaleRingDerivedExtension φ ⋙ (restriction φ).mapDerivedCategory ≅
        (Functor.curryObj a.tensor).flip.obj
          (DerivedCategory.Q.obj (coefficientComplex φ)),
      IsDerivedTensor φ a h := by
  sorry

/-- The comparison h selected by its unique representative normalization.
Source: Stacks 06YY (blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
noncomputable def derivedTensorIso
    {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B)
    (a : Scheme.ProEtaleTensorModel W A) :=
  Classical.choose (derivedTensorIso_existsUnique φ a).exists



/-- Literal inverse-image coefficient ring, on the original small site.
Source: Stacks 03EL (blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
abbrev inverseRing {Z T : Scheme.{u}} (f : Z ⟶ T)
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj A

/-- Literal inverse-image coefficient map.
Source: Stacks 03EL (blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
abbrev inverseMap {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B) :=
  (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map a

/-- The canonical exact derived inverse image with identified coefficients.
Source: Stacks 07A6 (blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
abbrev pull {Z T : Scheme.{u}} (f : Z ⟶ T)
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  proEtaleRingDerivedPullback f A (inverseRing f A) (Iso.refl _)

/-- The ordinary unbounded derived direct image with identified coefficients.
Source: Stacks 07A6 (blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
abbrev push {Z T : Scheme.{u}} (f : Z ⟶ T)
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  proEtaleRingDerivedDirectImage f A (inverseRing f A) (Iso.refl _)

/-- The existing canonical, tensor-unit normalized derived module adjunction.
Source: Stacks 07A6 (blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
abbrev adjunction {Z T : Scheme.{u}} (f : Z ⟶ T)
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  proEtaleRingDerivedAdjunction f A (inverseRing f A) (Iso.refl _)

/-- The existing balanced scalar/pullback comparison, in the direction lambda.
It is the inverse mate of the exact restriction square with normalized scalar adjunctions.
Source: Stacks 03EL, 06YY (blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
def scalarPullback {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B) :=
  proEtaleReductionPullbackIso f A B (inverseRing f A) (inverseRing f B)
    a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)

/-- The prescribed beta, the geometric adjunction mate of lambda followed by T(epsilon).
Source: Stacks 07A6 (blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
def beta {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B) :
    push f A ⋙ proEtaleRingDerivedExtension a ⟶
      proEtaleRingDerivedExtension (inverseMap f a) ⋙ push f B :=
  (mateEquiv (adjunction f A) (adjunction f B) (scalarPullback f a).hom).natTrans

/-- The canonical restriction/direct-image comparison d, with its adjunction normalization.
Source: Stacks 0D6E (blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
def restrictionPush {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B) :=
  proEtaleRingRestrictionDerivedDirectImage f A B (inverseRing f A) (inverseRing f B)
    a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)

/-- The ordinary identification f_A^*(r_T B_T) = r_Z B_Z, from the restriction square
and the uniquely unit-normalized pullback of the B-ring module.
Source: Stacks 03EL (blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
def coefficientPullback {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B) :=
  (@asIso _ _ _ _
    (proEtaleRingRestrictionPullbackInv f A B (inverseRing f A) (inverseRing f B)
      a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp))
    (proEtaleRingRestrictionPullbackInv_isIso f A B (inverseRing f A) (inverseRing f B)
      a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp))).app
        (SheafOfModules.unit ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)) ≪≫
    (restriction (inverseMap f a)).mapIso
      (Classical.choose (proEtaleProjectionUnit_existsUnique f B (inverseRing f B)
        (Iso.refl _)).exists)

/-- The same coefficient identification in the derived category, in degree zero.
Source: Stacks 07A4 (blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
def derivedCoefficientPullback {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B) :=
  (proEtaleRingDerivedPullbackFactors f A (inverseRing f A) (Iso.refl _)).app
      (coefficientComplex a) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _))
        (ComplexShape.up ℤ) 0).app (coefficient a)) ≪≫
    DerivedCategory.Q.mapIso
      ((CochainComplex.singleFunctor (proEtaleRingModules Z (inverseRing f A))
        (0 : ℤ)).mapIso (coefficientPullback f a))

/-- The full isomorphism locus of the prescribed scalar mate.
Source: blueprint, direct-image proof (3)
(blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
def locus {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B) :
    ObjectProperty (DerivedCategory (proEtaleRingModules Z (inverseRing f A))) :=
  fun K ↦ IsIso ((beta f a).app K)

/-- Canonical signed-total shifts on the tensor model, using the existing general
representative-normalization predicate, including the unsigned first-factor shift.
Source: Stacks 06YU (blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
def CanonicalTensorShifts {W : Scheme.{u}}
    {A : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : ProEtaleTensorModel W A) [(Functor.curryObj a.tensor).CommShift₂Int] : Prop :=
  SheafOfModules.MateCanonicalShiftData (proEtaleOrdinaryTensor W A) DerivedCategory.Q
    a.tensor (proEtaleFlatRepresentatives W A)
    (fun P Q hp hq ↦ a.representative.app (⟨P, hp⟩, ⟨Q, hq⟩))

/-- The source identification e_T after direct image, with the functor associator explicit.
Source: Stacks 06YY (blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
def sourceIso {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B)
    (t : ProEtaleTensorModel T A) :=
  (Functor.associator (push f A) (proEtaleRingDerivedExtension a)
      (restriction a).mapDerivedCategory) ≪≫
    Functor.isoWhiskerLeft (push f A) (derivedTensorIso a t)

/-- The target identification d followed by e_Z and the canonical pulled-back coefficient
identification, oriented to the exact projection functor.
Source: Stacks 0D6E, 06YY (blueprint: lem-sfb-derived-scalar-mate-thick-locus). -/
def targetIso {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B)
    (z : ProEtaleTensorModel Z (inverseRing f A)) :=
  (Functor.associator (proEtaleRingDerivedExtension (inverseMap f a))
    (push f B) (restriction a).mapDerivedCategory) ≪≫
  Functor.isoWhiskerLeft (proEtaleRingDerivedExtension (inverseMap f a))
    (restrictionPush f a) ≪≫
  (Functor.associator (proEtaleRingDerivedExtension (inverseMap f a))
    (restriction (inverseMap f a)).mapDerivedCategory (push f A)).symm ≪≫
  Functor.isoWhiskerRight (derivedTensorIso (inverseMap f a) z) (push f A) ≪≫
  Functor.isoWhiskerRight
    ((Functor.curryObj z.tensor).flip.mapIso (derivedCoefficientPullback f a).symm)
    (push f A)

```

## New

The text above is in `lean/Sheaf/Paper/DerivedScalarMateData.lean`, with the module title and
blueprint ownership tags changed to the new extracted node. No public signature or definition
body changes. The original module starts with the following public reexport and proof imports:

```lean
module

public import Sheaf.Paper.DerivedScalarMateData
import Sheaf.Paper.DerivedScalarMateProjectionNormalization
import Sheaf.Paper.DerivedScalarMateExactStructures
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
```

It retains the original `derivedScalarMateThickLocus` signature, proves its mate-counit,
triangle-morphism, thick-closure, finite-sum and explicit-retract conclusions, and uses the
separate geometric lemmas for projection normalization and canonical exact structures.
Both new statements have complete source proofs in their docstrings and matching DAG nodes.
No target statement or definition has a mathematical change, so no target interpretation
review is reopened by this relocation.

## Users

The textual downstream scanner over-approximates uses of short names such as `pull`, `push`,
`coefficient` and `locus`. All its hits are listed below to make that check reproducible.
The effect for every row is the same: identical declarations publicly reexported; no source
adaptation. The four direct importers are compiled against the delivered files separately.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Algebra.Homology.NativeStandardHomRepresentatives` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Algebra.Homology.RingedForgetTensorTransposition` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.ClosedDirectImageStrictReduction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.ClosedSourceSiteTensorComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicProperConstructibleCohomology` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.FieldActionCoefficientTransportData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.FieldActionGeometricTransportData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.FieldActionScalarTransportData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.FieldActionTransportData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.FieldRingedScalarAdjunctionTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.FieldScalarProjectionMateCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTransposeData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteTypeDirectImageSingleConstructible` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteTypeIntegralHeartBound` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.GeoP1Cohomology` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.IntegralConstantSectionProjection` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.IntegralModelsCompletionTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.IntegralModelsResidueTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.IntegralModelsStacks` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.IntegralResidueCoefficientTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.IntegralResidueModelComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.NodalDeformationSmoothingParameters` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.OrdinaryAffineLineTensorCounit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.OrdinaryAffineTensorActions` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.OrdinaryAffineTowerTensorCounit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1TensorAction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.PointBlowupFibreDefects` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleP1DiagonalComponents` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedBottomGluing` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.BarCyclicEvaluationRoof` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.CondensedActionInjectiveRestriction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.CondensedBarScalarResolutionComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.CondensedDerivedInflationArrows` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.CondensedInflationActionSiteData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.CondensedInflationNativeSiteData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.CondensedNormalSubgroupComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.CondensedProductActionInflation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.CondensedProductBarComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.CondensedSplitCosetInduction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.CyclicRowDerivedComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.DerivedInflationMonoidalNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.InternalBarCharacterLiftNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.InternalBarCharacterRoofCup` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.InternalBarRoofAdjunction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.InternalInflationGradedCup` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.NormalInflationResolutionNaturality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.PrimeToEllCondensedAcyclicity` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.ProfiniteActionCoherentPresentation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.ProfiniteActionModuleLift` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.ProfiniteInvariantsSheafifiedCohomology` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.RelativeCoefficientComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.RelativeCyclicTotal` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.RelativeDerivedInvariants` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.RelativeInvariantForgetting` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.RelativeRestrictionMateForgetting` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.CategoryTheory.Sites.FiniteCoproductToposCoherent` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.DeligneLaumon.ContinuousCoefficientGeometricCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.DeligneLaumon.ContinuousConstructibleLatticeData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.DeligneLaumon.ContinuousConstructibleStratifiedLattices` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.DeligneLaumon.FiniteStageFibreVanishing` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.DeligneLaumon.RawHeartAdicLisseData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.DeligneLaumon.RawHeartAdicLisseStratification` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.A1LisseSectionEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.A1QbarOpenClosedCohomology` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicFibreComparisonCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicFibreComparisonData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicFiniteRealizationData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicNormalizedFibreCommonStageData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicNormalizedFibreData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicNormalizedFibrePullback` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicNormalizedFibreScalar` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicOperationDomainsSourceComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicPerfectModelsCohomologicalBounds` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicProjectionShiftCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicProjectionShiftData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicProperAdjunctionRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicPurityScalarNaturalityData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicResidueLocalHomologyComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicScalarFlatReductionModel` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicSmoothBaseChange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicStratifiedPullbackInterface` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicTraceTransposeCoefficientCalculus` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicTraceTransposeData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceConstruction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceReductionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceScalarData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceTransposeReductions` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdmissibleHomSubstitution` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AffineCoefficientCounitMaps` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AffineCoefficientCounitNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AffineLineAdjunctionAssembly` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AffineLineCompositeTranspose` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AffineLinePurityComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AffineLinePuritySource` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AffineOrderedIntegrationData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AffineSpacePurityComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AffineSpaceRationalInduction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AffineSpaceTraceContractionProduct` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AffineSpaceTraceSuccessorContraction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AffineTowerIntegrationSiteTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AnchoredPureCurveCriterion` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AugmentedReductionNaturality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.AutomorphismConstructibleStageEquivalence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.BalancedFiniteTowerGeneratorComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.BalancedFiniteTowerKoszulAugmentation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.BalancedFiniteTowerQuotientComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.BalancedFiniteTowerScalarComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.BarrettIndRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.BaseChangedLineTraceEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.BasicOperationsCoefficientReduction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.BoundaryComparisonCompositionTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.BoundaryFiniteSiteData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.BoundaryFiniteTorDomains` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.BoundedSiteExchangeTransposes` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.BrownTowerBoundedTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.BrownTowerFiniteEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.BrownTowerFiniteSiteComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.BrownTowerGeometricTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.BrownTowerSite` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CanonicalOpenRestrictionModel` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CanonicalTateComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CanonicalTateCompletedComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CanonicalTateOrdinaryNaturality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CanonicalTateScalarNaturality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CartesianCoefficientTwists` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CartesianSectionAdjointMates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CbcRationalExchangeCoefficientSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CbcRationalExchangeStage` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CentredDiagonalSourcePasting` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ChartDiagonalSourceMate` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ChartDncVectorFactorData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ChartDncVectorFactors` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ChartExceptionalMateCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ChartIntegrationAdjoints` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ChartNormalIntegrationSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClassicalFiniteWeilDiagramData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClassicalLisseWeilFrontierData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClassicalLisseWeilRestrictionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClassicalLisseWeilRestrictionMaps` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClassicalNormalizedTwoFibreData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseCommonRestrictionComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseCommonRestrictionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseOperations` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClassicalRawLissePointFibres` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClassicalSystemRawLisseRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClassicalTwoFibreScalarData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClopenCompletedOperationTowers` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClopenCounitAdjointComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClopenExceptionalScalarDescent` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClopenStrictSystemComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClopenStrictSystemSupport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClopenSystemFiniteRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClosedCoefficientTransposeCocycles` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClosedLiftedTestIsomorphismCriterion` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClosedSupportExceptionalMate` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClosedTestChainMateRestriction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClosedTestChainUnitNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClosedTestDerivedExchangeModel` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClosedTestLocalizedModelCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClosedTestLocalizedModelData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClosedTestScalarComparisonMaps` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClosedTestScalarSectionCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ClosedTestScalarSectionSquares` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoefFiniteHomSiteDescent` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoefTowerCoaugmentation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoefficientDualModelTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoefficientEvaluationNaturality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoefficientExtensionReductionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoefficientExtensionStrictTensorNormalized` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoefficientGammaRepresentatives` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoefficientScalarSectionRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoefficientScalarTensorData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoefficientTensorNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoefficientTowerShriekInterfaces` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoefficientUnitTowerNormalized` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoherentPrimitiveReductionPresentation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoherentQuotientModelComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoherentQuotientOrdinaryLift` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoherentQuotientReductionComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CommonAdicOpenSectionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CommonProjectionCompactificationOnStage` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CommonProjectionComparisonEquations` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CommonProjectionCompositionOnStage` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CommonProjectionOpenFactor` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CommonProjectionOpenPullbackTensor` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CommonProjectionProperFactor` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CommonProjectionProperOnStage` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CommonProjectionPullbackTensorCompatibility` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CommonStageOpenHeartAdjunction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CommonStageTensorLineCoherenceNaturality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CommonStageTensorRightUnitorNaturality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactExchangeOperationCoordinates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportCoefficientExchangeInvertible` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportCoefficientModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportCondensedRealization` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportCondensedRealizationSetup` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportFiniteAction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportLimitEquationData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportNormalizedTowerLimit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportProjectionCoefficientChange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportProjectionCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportProjectionFieldStages` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportProjectionFiniteStages` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportProjectionFormula` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportProjectionIntegralStages` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportProjectionRealizationLift` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportRealizationCoordinates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportRealizationFactorNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportRealizationFactorization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportRealizationIdentity` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportRepresentativeIndependence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportScalarCoordinates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportScalarProjectionIdentification` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportScalarProofs` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportScalarShiftStructures` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportStageActionAdjunction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportStrictScalarComposition` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportStrictScalarMate` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportStrictScalarRefinement` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportSystemRealizationNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactSupportSystemTransposeNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactificationBOrdinaryProjectionSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactificationBProjectionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactificationBProjectionReduction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactificationCompletedRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactificationCompletedRealizationData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactificationStrictRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompactifiedTowerComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ComparedSmoothExchangeComposition` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompleteCompactSupportProetale` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompleteCompactificationLimitSupport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompleteProetaleStrictTowerRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompleteProjectionDescentMaps` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompleteProjectionMateDescent` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompleteProjectionReductionSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedBaseChangeMap` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedCoefficientAdjunctionTransportModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedCoefficientDirectImageDiagrams` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedCoefficientFamilyTransportModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedCoefficientMonoidalAdjunctionTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedCoefficientStrictImage` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedCoefficientSystemRestrictionAcyclic` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedCoefficientSystemTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedCoefficientTensorTransportModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedCoefficientTransportExpressions` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedCompactSupportExchange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedComparisonQuotientRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedComparisonQuotientRealizationDefs` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedConstructiblePreservation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedConstructibleReductionControl` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedDirectImageLimits` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedExchangeCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedExchangeUnit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedHomScalarTranspose` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedLineTensorCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedMapReduction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedModelSectionsTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedOpenEndpointLimitTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedOpenExchangeTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedOpenStrictMateIdentification` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedOpenTensorRepresentatives` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedOpenTensorSystemRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedOperationTowerSubstitution` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedOrdinaryComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedOrdinaryExchangeCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedPrimitiveCounitComparison` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedProjectionCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedProperIndependentOrigins` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedPullbackReflection` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedPullbackTensorPullbackCounit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedPullbackTensorTensorCounit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedPullbackTowerRealizations` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedPullbackUnitTower` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedPullbackUniverseTransportData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedReductionPullbackSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedReductionSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedScalarMateCoefficientTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedScalarProjectionTensorComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedSourceAugmentationNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedStalkReparametrizationCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedSupportIntermediateTower` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedSupportIntermediateTowerCore` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedTargetAugmentationNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedTensorHomTranspose` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedTensorProjectionCoefficientTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedTowerCorners` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedUnitPullbackData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedUnitPullbackTower` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompletedUnitReduction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompositeProjectionCoefficients` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CompositionComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConcreteIntegralProjectionCone` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConcreteProjectionCoefficientCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConcreteProjectionFactorizationData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConcreteProjectionFieldDescent` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConcreteProjectionReductionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConcreteProjectionReductionSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CondensedClosedExchangeAffineDescent` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CondensedCompositorRealization` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CondensedERealizationDefinitions` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalReconstruction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalReconstructionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalRefinementCounits` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CondensedExchangeOpenRestriction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CondensedOpenCoefficientModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CondensedOpenCounitComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CondensedOpenCounitRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CondensedOpenCounitRealizationSupport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CondensedOpenCounitUnits` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CondensedTateIntegralData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CondensedTateIntegralTower` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CondensedTateIntegralTowerData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConstantExtensionSheetHeartData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConstantPerfectQuotientProjection` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConstantPurityFrobeniusSquare` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConstantQuotientTensorComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConstantScalarTowerAdjunction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConstructibleCompleteBaseChange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConstructibleDegreeZeroProperSupport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientConstructionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalCompositor` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalCompositorData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalRefinementMate` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConstructibleInternalHomContinuity` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConstructibleMateCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConstructibleProjectionMates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConstructibleTensorCompletionAssembly` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ConstructibleTensorCompletionConstructible` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ContinuousModuleSectionModel` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ContinuousRationalDerivedRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ContinuousRationalRealizationData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoordinateAdjunctionComposition` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoordinateBoundaryGeometricPullback` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoordinateLineAdjunction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoordinateLineAdjunctionMaps` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoordinateLineAugmentationRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoordinateLineCounitTensor` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.CoordinateSectionTensorTrace` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DerivedPoincarePairing` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DerivedPullbackTensorConstraints` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DerivedScalarRestrictionPullbackMate` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DerivedWeilOperations` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalAffineCounitRestriction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientFiniteDiagonal` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientFiniteRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalCoefficientReference` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalCompleteScalarRestriction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalCompletedDiagramRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalCompletedFrame` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalCounitComparisonData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalDncAffineModel` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalDncChartNormalization` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalDncEtaleBeta` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalDncEtaleDualizing` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalDncEtaleFactors` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalDncEtaleNaturality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalDncEtaleNaturalityLocalInverse` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalDncEtaleNaturalityTwist` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalEtaleInverseDeformation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalEtaleNormalTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalEtaleSourceDualizing` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalEtaleSourceTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalFiniteArrowEquations` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalOrdinaryChartLift` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalOrdinaryOrientationGluing` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalOrdinaryOrientationNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalOrdinaryRealizeRestriction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalOrientationCompatibility` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalOrientationRefinement` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalOrientationRefinementData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalTowerSystemInterface` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalTowerTraceCoefficients` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalTowerTraceModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalTowerTracePresentations` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalTraceComparisonPartial` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalTraceFiniteChernCohomology` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalTraceFiniteChernComparison` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalTraceFiniteSplitting` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalTraceGeometricModelExistence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalTraceIntegrationSystems` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalTraceLimitWitnessExistence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalTraceModelTraceComponents` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalTraceOrdinaryScalars` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalTraceResultExistence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalTraceScalarComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalTraceTwistedSplittingComponents` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalTraceUnitArrowComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalTraceUnitComparisonIso` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DiagonalUniformizerFiniteModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DifferenceCoordinateSectionIdentifications` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DifferenceFirstInputRestriction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DifferenceSecondInputRestriction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DirectImageCoefficientExchangeInvertible` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DirectImageLimitComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DirectImageReductionHomSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DirectImageScalarRealizationSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DlConstantFieldCharts` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DlLocallyConstructibleAdicHeart` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DoubleDiagonalSectionIdentifications` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DualBaseChange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DualizingCocycleSourceEtale` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DualizingPrimitiveOpenRestriction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.DualizingSigmaCocycleLocality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EffectiveComparisonRealizationModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EffectiveCompletionPresentationModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EffectiveQuotientModelDescent` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EmbeddedFiniteCoefficientRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EmbeddedFiniteHeartConstructibility` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EmbeddedIntegralCompletenessTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EmbeddedIntegralResidueTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EmbeddedIntegralScalarKernelSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EquivariantAdicFibreData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EquivariantAdicFibreNaturalityData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EquivariantAdicFibreRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EquivariantAdicFibreRealizationData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EtaleAffineProjectionCoefficientMate` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EtaleBrownEvaluationMate` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EtaleBrownGeometricComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EtaleBrownLevelComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EtaleBrownProjectionRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EtaleBrownProperSingletonEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EtaleCartesianTowerTensorComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EtaleCoefficientSystemAdjoint` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EtaleCompositeEComposition` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EtaleFiniteCoefficientHomArrow` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EtaleMiddleTensorAssembly` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EtaleOrientationLocality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EtaleSystemBrownConstruction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EtaleSystemCoefficientProjection` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EtaleSystemCofinalData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EtaleSystemCofinalMate` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EtaleSystemImageTensor` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EtaleSystemProjectionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EtaleSystemScalarMateCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EtaleSystemTensorEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EtaleTensorSourceTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.EtaleTowerBrownAdjunction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExactProperOpenProjectionMate` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExceptionalAdjointAdmissibility` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExceptionalBaseChangeIntegralMaps` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExceptionalFieldDescent` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExceptionalFieldStageCompletion` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExceptionalFiniteScalarMates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExceptionalIntegralScalarMates` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExceptionalOriginAdjunctionEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionContext` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionPresentations` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExceptionalRefinementMates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExceptionalRefinementMatesData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExceptionalRefinementRightSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExceptionalRefinementSystemData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExceptionalSiteOriginComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExceptionalSystemInterfaces` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExceptionalSystemTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExchangeFunctoriality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExplicitScalarConeWordCoordinates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExpressionCounitSubstitutionCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ExtensionZeroPerfectModelTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FdCompletedCompositorNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FdCompletionInverseScalarCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FdPullbackAugmentationCounitMatching` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FdPullbackSignedShiftWordTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FdPullbackWeilReturnSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FdScalarPullbackRealizationIdentification` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FdScalarRoosComparisonIntertwining` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldActionToposCoefficients` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldCohomologyPerfectDescent` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldExtensionIntegralComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldExtensionIntegralCoordinates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldExtensionIntegralModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldExtensionRationalComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldExtensionRationalModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldExtensionReductionLimits` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldOrientationSystemHeart` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldProjectionOpenSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldProjectionOriginWitnesses` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldProjectionProperSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldProjectionRefinementSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldProjectionSystemData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldProjectionSystemSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldPurityTransposeArrows` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldPurityTransposeLevelWords` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldScalarReductionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldScalarSystemData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldShriekCompositionNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldShriekLowerBound` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldShriekSupportEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldShriekSystemCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldShriekSystemEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldShriekSystemModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FieldWeilShriekShiftData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FilteredCondensedCounitFiniteFormula` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FilteredCondensedRepresentingPair` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FilteredCondensedRepresentingPairData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteAdicCompactificationSectionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteAdicImageNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteAdicOpenSectionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteAdicOrdinarySectionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteAdicProperSectionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteAdicSectionRealizationCore` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteAdjointCompositorTransposes` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteClopenDerivedDecomposition` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteClopenExceptionalRestriction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientAdjointData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientDerivedExchangeIdentification` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientHomChange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientProperFormulaTools` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientSiteScalarArrow` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteCounitRestrictionTowers` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteEtaleAdicCohomology` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteExceptionalCompositorCoefficients` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteExceptionalSiteNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteExpressionReductionComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteExtensionCompactSupportBaseChange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteExtensionProperBaseChange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteFreeCoefficientExtensionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactComposition` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteFreeProjectionExchange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteFreeProperScalarComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteFreeScalarCalculusData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteFreeScalarDerivedComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteFreeTensorCtf` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteGammaEvaluationIsIso` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteHomDomainCalculus` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteImageOpenKernelInflation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteLevelProjectionFactors` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteLocalizingSmoothLocalFormula` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteMateDomain` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteModelOrdinaryScalar` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteOpenGammaRestriction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteOpenProductOperations` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteOpenProductRestriction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteOpenProductSwap` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteOpenProductSwapRestriction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteOrientationReduction` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FinitePointCounitUnitNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FinitePointReconstructedEvaluationSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteProductEvaluationSwap` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteProductNormalForm` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteProjectionExchangeData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteProjectionExchangeTransposes` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteProjectionInputNaturality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteProjectionOpenAssembly` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteProjectionOperationPresentation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteProjectionRefinementLeft` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteProjectionTensorSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteProjectiveModelPullback` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteProperBaseChange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteProperLocalizing` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteProperProductMaps` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteProperProductTranspose` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteProperTransportTranspose` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FinitePullbackStrictTowerComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FinitePullbackStrictTowerData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FinitePullbackTensorChainComposition` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FinitePullbackTensorCompositionRepresentatives` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FinitePullbackTensorCompositorFactors` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FinitePullbackTensorRepresentativeData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FinitePullbackTensorRepresentativeSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FinitePullbackTensorUnitRepresentatives` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FinitePurityCounitSystem` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteRationalHeartComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteReductionExchangeRectangle` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteRefinementProjectionRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteRestrictionCoefficientCore` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteRestrictionCoefficientDescentData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteRestrictionCoefficientGeometry` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteRestrictionCoefficientNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteRestrictionDiagramModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteRestrictionDiagramNaturality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteRestrictionGeometricArrows` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteRingSectionDeformation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteSiteCounitProjectionTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteSmoothAdjunctionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteSmoothCoefficientArrows` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteSmoothLevelOfOrientation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteSmoothPurityMaps` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteSmoothQuotientCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteSmoothSiteRealizations` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteSpanModuleComparisonData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteSpanScalarTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteStageSupportedGeneration` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteStrataCompletionDetection` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteTargetChangeCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteTensorPullCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteTensorReductionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteTraceDiagonalDatum` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FiniteTwistRootTrivialization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FirstRootLinePullback` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FixProjectionCompactificationComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FlatCoefficientSquareNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FormalClosedSupport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FourArrows` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FourierArtinSchreierProperties` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FramedProRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FrameworkPbcComparisonSystem` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FrameworkPbcPullbackScalarBridge` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FrameworkPbcRawComparisonLaws` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FreeParameterDegreeZeroData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FreeParameterEvaluationCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FreeParameterScalarMaps` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FrobeniusCompactSupportExchange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FrobeniusEvaluationProjectionCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FrobeniusExchangeDegreeZero` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FrobeniusFiniteRootTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FrobeniusIntegralRootTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.FrobeniusSystemExchangeInverse` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.GaloisKInjectiveSectionModel` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.GeneralHomComparisonCocycles` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.GeneralLfpAdicInputWitness` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.GeneralNearbySliceTest` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.GenericRetractSupportGluing` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.GeometricComparisonData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.GeometricCondensedFiniteScalarModel` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.GeometricFiberFiniteExtension` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.GeometricFrobeniusInternalHomComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.GeometricOperations` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.GeometricSectionsAdjunction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.GeometricSmoothReconstructionSetup` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.GlobalInternalHomDetection` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.GlobalVerdierDuality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.GlobalVerdierDualityData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.HomChainPairingNaturality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IdentificationFibreAdjunction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IdentityOpenUnderivedSquareNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ImmersionWeilLocalBehavior` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralAdjunctionBijection` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralAmbientCoefficientPresentation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralAmbientTowerComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralAugmentedQuotientTowers` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralChartPullbackComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralClosedSupportNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralCoefficientModelComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralCoefficientSquareNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralCoherenceData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralCoherenceTower` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralCompactSupportUniformRestriction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralComparisonCanonicalShifts` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralComparisonRealizationModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralComparisonSequenceSystems` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralComparisonSystemData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralCompletedEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralCompletedLocalPerfectCriterion` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralCompletedTowerPullbackUniverses` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralCompositionCounitImages` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralCompositorLimitRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralDerivedHomBilinear` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralDirectImageTower` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralDirectImageTowerData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralEquivarianceMate` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralExceptionalInverseImage` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralExpressionSystemComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralFibreSectionSpecialization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralFiniteScalarModelDefinitions` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralFiniteScalarPerfectModel` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralGeneralLfpHomInversion` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralGeometricComparisonData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralGeometricComparisonRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralGeometricSupportRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralGeometricTransposeIdentity` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralInverseImageComparisonComposition` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralLissePullbackNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralLocalizingProperBaseChange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralModelsEmbedded` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralModelsEmbeddedCompletion` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralModelsEmbeddedResidueComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralModelsEmbeddedStacksCriterion` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralOrdinaryTensorPullbackNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralOrientationReductionInjectivity` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralPerfectChartComplete` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralPointTransportComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralPointTransportTowerPowers` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralPositiveReductionConstructible` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralProjectionCoordinateData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralProjectionEvaluationFactors` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralProjectionFactorData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralProjectionFiniteEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralProjectionFiniteEvaluationData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralProjectionLocalFactors` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralProjectionMiddleMap` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralProjectionOpenFactorReduction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralProjectionOpenTensorCoordinates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralProjectionPullEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralProjectionReductionCoordinates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralProjectionReductionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralProjectionRefinementSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralProjectionSupportFactorCoordinates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralProjectionSystemCoordinates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralProperOperationProjection` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralProperProjectionCoefficientData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralProperProjectionSystemNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralProperReductionModel` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralProperSupportReductionIdentity` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralProperTensorPullbackReduction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralPullbackAugmentationAmbient` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralPullbackCompletedComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralPullbackCounitProjection` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralPullbackReductionCounit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralPullbackResolutionMatching` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralPullbackStrictRoosData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralPullbackSystemComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralPurityCounitReduction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralQuotientDirectImageComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralQuotientPullbackFaceModel` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralQuotientSectionMateRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralReconstructionComparisonData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralReconstructionComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralResidueExchange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralScalarIsomorphismExchange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralScalarPullbackCompletionNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralScalarPullbackCounitCompatibility` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralScalarResidueLayerConstructible` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralScalarResidueLayerTensorComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralScalarResidueLayerVanishing` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralSectionHomContinuity` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralSmoothAdjunctionPresentation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralStageProjectionStructuralIdentities` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralStratumChartRestrictionsData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralSupportAdjunctFiniteCoordinates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralSupportFunctorNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralSupportNormalizationData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralSupportReductionNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralSystemReductionFullyFaithful` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralTensorPullback` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralTowerLimitComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntegralTowerPullTensorConstructible` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.InternalAdjunctionPairingChange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IntrinsicSitePerfectHomWindow` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.InverseContravariantBidual` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IsomorphismComparisonNatural` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IsomorphismComparisonScalarExtension` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IsomorphismDerivedPullback` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IsomorphismFiniteExchangeCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IsomorphismPullbackRawStage` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IsomorphismScalarComparisonAgreement` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IteratedPurityScalarPasting` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.IteratedReturnTransportScalarCalculus` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.KummerPartialNerveChart` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.KummerPartialNerveMorphism` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.KummerPartialNerveScalarMorphism` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.KummerRefinement` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.KummerScalarInvariantSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.KummerStratumChart` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.KummerStratumScalarMaps` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.LevelwiseNormalizedAdjointDescent` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.LevelwiseNormalizedStrictSystems` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.LineZeroClassExchange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.LisseFieldNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.LisseLatticeHeartLiftData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.LissePointSectionsRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.LissePullbackNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.LisseRationalRealizationData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.LisseTensorPullbackRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.LisseTensorPullbackRealizationData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.LocalizedOrdinaryPullbackData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.LocallyClosedHomGenerator` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.LocallyClosedOrdinaryComparisonIso` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.LocallyClosedScalarPasting` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.LocallyFiniteAdicCompactSupportData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.LocallyFiniteAdicConstructibleRealization` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.LocallyFiniteCompactSupportStageAction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.MiddleExchangeProjectionBaseChange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.MixedCupNormalizedScalars` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.MixedCupRingedNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NativeAdicFiniteNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NativeCompactSupportFiniteComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NativeConstantSupportModel` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NativeGeometricHomComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NativeOpenDerivedTensor` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NativeOrdinaryClosedTensorModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NativeOrdinaryTensorIdentification` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NativeProperCoefficientOperations` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NativeProperTensorComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NativeWeilDualizingHomTransposition` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NativeWeilFreeCoproduct` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NativeWeilHomClosedStructure` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NativeWeilHomRightAdjoint` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NativeWeilRingedTensorModel` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NativeWeilScalarCounitCategories` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NativeWeilScalarCounitData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NativeWeilScalarFrobeniusCounit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NativeWeilTensorAdjoints` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NativeWeilTensorConstraintLifts` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NativeWeilTensorLift` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NativeWeilTensorTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NearbyFiniteBaseDescent` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NearbyGeometricSlice` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NearbyProperHyperdescent` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NearbySpecializationSlice` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NearbySpreadOut` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NoetherianEtaleSectionSpecialization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NonaffineClosedTestExchangeIdentification` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NormAlgclCohomologyTopologyComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NormalizedClassicalWeilRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NormalizedCoefficientFamilies` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NormalizedCommonCoefficientLaws` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NormalizedCompletedOperationModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NormalizedCompletionRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NormalizedEtaleComparisonComposition` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NormalizedFieldPurityTrace` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NormalizedIntegralPurityTrace` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NormalizedInternalSupportScalars` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NormalizedOrientationPerfectDuality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NormalizedPullbackCompositionTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NormalizedPullbackObjects` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NormalizedRationalEvaluationNaturality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NormalizedTateTensorTower` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.NormalizedTensorConstraintTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OpenCompletedRestrictionIdentification` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OpenExceptionalScalarLocality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OpenProEtaleCounitScalar` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OpenProjectionFactorCoefficientChange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OpenProjectionFactorCompositorTransport` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OpenProjectionIsoCoefficientChange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OpenRestrictionAugmentedDescent` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OpenRestrictionCompleteness` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OpenRestrictionCounitOnGoodComplexes` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OpenRestrictionGoodComplex` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OperationCoefficientActionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrderedAffineTransposeData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrderedAffineTransposeProjection` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrderedExchangeCoefficientComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrderedExchangeCoefficientData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrderedExchangeRawCoefficientEquation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrderedExchangeReconstructionEquations` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrderedExchangeStrictCoefficientEquations` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrderedTowerOrientation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrdinaryCompactSupportCoefficientTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrdinaryDerivedProductLegTransposes` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrdinaryIntegralLocalModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrdinaryOpenRestrictionQuotient` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrdinaryOpenScalarComposition` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrgogozoGoodModification` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrgogozoInductionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrientationGeometricComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrientationIntegralCoefficientTwists` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrientationScalarTowerTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrientedClosedBaseExtension` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrientedClosedBaseRestriction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrientedDoubleHomCancellation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrientedHypercoverDescentDatum` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrientedNearbyCycles` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrientedNearbyStrictLocalDescription` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrientedPerfectDuality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrientedProductPointsConservative` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrientedProperFibreExchange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.OrientedProperImageConstructibility` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.P1CounitScalar` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PartialKummerBoundaryUnitModel` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PbcActualCompletedExchangeTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PbcActualStrictPullback` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PbcCompletedPullbackActual` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PbcIntrinsicTowerComplete` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PerAdicNormalizedFibreComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PerfectDualPairAndTateStability` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PfReductionProperOpenIdentities` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PodCompletionReindexCoefficientTransition` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PodCompletionReindexModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PodCompletionReindexShifts` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PodCompletionScalarFormulas` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PodCompletionUnitScalarIntertwining` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PodCounitScalarWordCoordinates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PodCtfAdjunctions` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PodCtfPairingMaps` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PodHomChainCounitFormula` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PodHomChainCtfDomains` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PodHomChainUncurriedTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PodReconstructionRawRationalNaturality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PodReindexingCompletedEvaluationReflection` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PodReindexingCompletionNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PodReindexingCompletionUnitTensor` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PodReindexingDerivedComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PodReindexingEvaluationShiftComposition` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PodReindexingHomCoefficientDescent` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointAutomorphismDerivedTransportInverse` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointAutomorphismTransportScalarExtension` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointCompletedEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointDerivedTensorTowerCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointEvaluationCompletionNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointFrobeniusNormalizationDefinitions` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointFrobeniusTransportNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointIdentityAdmissibility` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointIntegralTensorChain` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointPerfectOrdinaryEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointProjectiveDualTensorModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointRestrictionSystemChainMap` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointRestrictionWholeRoosSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointScalarCompatibleTransportTransfer` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointSectionsBalancingCompletion` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointSectionsCompletionCone` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointSectionsScalarExtension` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointSystemEvaluationComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointSystemFiniteTensorComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointSystemInsertionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointSystemNormalizedComparisonData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointSystemPowerRoosCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointSystemPowerRoosData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointSystemRoosTransportData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointSystemTensorTransition` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PointSystemTransportDescent` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PositiveRootGeneratorExt` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PrimeToEllDerivedInvariantsReduction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProEtaleConstantReductionModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProEtaleConstantReductionTower` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProEtaleCtfPullbackDomains` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProEtaleLocalScalarDerivedIso` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProEtaleLocalScalarHomologyIso` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProEtaleScalarMateIdentifications` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProductExchangeCoordinateDefinitions` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProductExchangeCounitCoordinates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProductHorizontalExchangeFactorization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProductOpenCounitNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProductOpenSupportNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProductOpenTensorProjection` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProductOpenTensorProjectionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProjectionCompactificationData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProjectionFactorCoordinates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProjectionFiniteBaseChangeCoordinates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProjectionFiniteReduction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProjectionFormulaCoherence` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProjectionIdentityAssembly` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProjectionIdentityProperCounit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProjectionIdentityPullbackUnits` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProjectionMateFactors` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProjectionReductionPresentation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProjectionScalarSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProjectionWeilTensorDomainBridge` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProperBiproductCoordinate` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProperCoefficientDescentData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProperConstructibleClosedExchangeHeart` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProperConstructibleLiftedTestRestriction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProperExceptionalRestriction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProperIntegralTowerComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProperOpenBoundaryZero` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProperProductCounitTranspose` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProperSectionsSemilinearGerms` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ProperSupportFiniteAdjunction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PullbackIdentitiesScalarExtension` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PulledKoszulTowerChainComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PulledKoszulTowerNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PulledReductionComparisonData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PulledReductionNormalizationComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurCompletedReductionReindexing` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurCompletedReductionReindexingLifted` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurCompletedReindexingData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurFrameworkPbcCoefficientCategoryComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurIntegralRepresentingPair` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurIntegralRepresentingPairData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurIntegralSupportComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurIntegralSupportComparisonData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurIntegralTwistLineInverseImage` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurReindexingLimitNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurRepresentingPairFiniteScalar` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurStrictIntegralExchangeData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurStrictIntegralExchangeNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurSupportPresentationAlpha` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurityAffineChartExceptionalIdentification` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurityCompactSupportTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurityConjugatesTowerReduction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurityDiagonalSectionPastingData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurityFiniteReductionTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurityPullbackLevelBounds` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurityRankOneLocalCalculation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurityRankOneLocalData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurityRankZeroFamilyReadings` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurityRelativeKummer` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PuritySectionBaseComparisonLaws` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PuritySectionEtaleRestriction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PuritySectionFibreSquares` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PuritySectionNormalizedSpecialization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PuritySectionRestrictionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PuritySectionRestrictionEtaleFunctorial` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.PurityTwistCancellation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.QbarCoefficientSmoothBaseChange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.QbarCohomologyFiniteLevelComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.QbarCompactSupportBaseChange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.QbarCompactSupportExchangeModel` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.QcqsCompactSupportFiniteMates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.QcqsCompactSupportNormalizedLift` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.QcqsCompactSupportProperComplete` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.QcqsCompactSupportTorsionCoefficientAction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.QcqsCompletionOrdinaryModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.QcqsIntegralFiniteModelCompleteness` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.QlbarBoundedTensorColimit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.QlbarInternalHomCoefficientData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.QuotientCompletedCompositorUnit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.QuotientCornerFrobeniusStructures` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.QuotientExpressionKFlatOperations` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.QuotientExpressionStrictKFlatTowers` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RamifiedReductionComparisonSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RamifiedScalarSystemTranspose` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RankOneFiniteKummerCohomology` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalAffineAdjunctionCalculus` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalAffineTensorCalculus` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalAmbientPullComposition` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalAmbientPullModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalBalancedFreePullback` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalCoefficientCategoryComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalDirectImageRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalEvaluationData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalModuleRealizationFunctor` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalP1CompletedLimitBridge` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalP1FirstAmbientContraction` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalP1KernelContractions` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalP1LocalizingProjection` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalP1SecondAmbientContraction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalP1SecondDiagonalInsertionFactor` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalP1SecondPretrace` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalP1SecondPullComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalP1SecondScalarTrace` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalP1SecondTraceReordering` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalP1Triangle` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalP1UnitCounit` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalProjectionComparisonEquations` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalProjectionTensorCompatibility` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalPurityCoefficientModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalPurityCompactLattices` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalPurityScalarModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalRealizationScalarCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalRealizationTensorComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalScalarComparisonData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalScalarCompletionUnitSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalScalarMixedUnitCancellation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalSliceCompletedEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalStratumPullbackData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalStratumPullbackModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalTatePullback` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalThickEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalTwistedPullbackCompositor` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RealWeilSheaves` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RealizationAdjointComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RealizationCompletedMate` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RealizationLocalizedPush` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RealizationRestrictionNormalizations` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RealizedPullbackComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ReconstructedPairRefinementCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ReconstructedPairRefinementData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ReducedFrontierMixedGluing` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ReductionOpenEtaleOrigin` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RegularCoefficientCoherentReduction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RegularImmersionPurityComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ReindexingSystemHomReductionSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RelativeKunneth` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RelativeKunnethConstructions` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RelativeKunnethCubeFactorTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RelativeProductBaseChangeFactorSquares` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RelativeProductFactors` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RelativeProductInputDomains` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RelativeSupportBottomDescent` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ResidueCompatiblePullbackFrobenius` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RestrictedAffineDiagonalDncTrace` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RestrictedAffineDiagonalTraceBaseChange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RootTowerCoordinateFace` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.RootTowerPuncturedFaceDiagram` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SbcCompletedOperations` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SbcDatumExchangeComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ScalarFibreComponentData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ScalarPullCoefficientComplexNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ScalarPullCoefficientModuleTensor` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ScalarPullCoefficientTotalTensor` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ScalarPullTensorCoefficientCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ScalarPullbackIsoExistence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ScalarPullbackIsoUniqueness` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ScalarReductionTowerBalancing` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ScalarRestrictionComplexNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ScalarSourceCounitUniversal` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ScalarTargetCounitUniversal` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SectionSupportedProExchangeIso` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SemilinearCommonOrdinaryCubes` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SemilinearCommonSupportCubes` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SemilinearCompactSupportCoefficientTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SemilinearExchangeCubeCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SemilinearExchangeCubeData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SemilinearExchangeDescentData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SemilinearExchangeReindexing` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SemilinearFieldOperationLifts` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SemilinearRationalOrdinaryCubes` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SemilinearRationalSupportCubes` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfAdicCommonStageDescentEquivalence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfBcCompletedMateDomain` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfCbcCompactSupportCompositionLimit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfCbcDirectImageReductionUnit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfCoefficientComparisonConclusions` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfCompleteDirectImageReduction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfCompletedExchangeTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfExchanges` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfFrameworkThetaShiftCompatibility` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfImmersionCompletedPullbackComparison` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfIntegralLocalizationConstruction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfIntegralOrdinaryRecollementRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfIntegralPullbackLinearAdjunction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfOpenReductionAdjunctionTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfPackageBaseChangeDomainRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfPackageExceptionalCoherenceRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfPackageIntegralRecollementNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfPackageIntegralRecollementSource` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfPackageLocalizationBoundaryData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfPackageLocalizationProjectionRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfPackageLocalizationRationalTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfProEtaleProjectionFormula` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfRationalLocalizationOrthogonality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SfRecollementReductionBoundary` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ShriekNormalizedTransitionComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SixFunctorDatum` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SixFunctorOperationDatumStages` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SixFunctorOrientationHigherPair` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityBaseChangeData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityBaseChangeFactors` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityCofinalIntegralBounds` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityCompletedTowerRoos` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityCompositionFactors` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateCategories` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateComposition` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateRightComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateTensorComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityFieldExtension` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityNormalizedEquivalence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityStrictCompactificationComparisonData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityStrictPlusComparisonsRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityStrictPlusEvaluationRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerBinaryCounitPredicates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerBinaryCtfFibre` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerBound` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerBoundsOperations` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerChartAdmissibility` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerChartData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerCompatibleCounitLift` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerFibreProjections` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerGamma` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerGammaData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerGluingData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerLocalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerOpenHomComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerOrdinaryLocalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerOrdinaryUnitEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerP1Adjunction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerP1Data` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerShriekData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerShriekLevels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SourceSectionStalkConeComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SourceSectionStalkConeData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SpEllCoefficientTower` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.StrictDirectImageMixedUnit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.StrictDirectImageMixedUnitData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.StrictLineHeartAssembly` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.StrictMixedScalarSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.StrictPullbackAdjointConstructor` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.StrictPullbackEvaluationConstructor` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.StrictQuotientExpressions` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.StrictReductionCompactSupportNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.StrictScalarFiniteEvaluationTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.StrictScalarOpenUnit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.StrictScalarPullbackComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.StrictTensorAdjointConstructor` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.StrictTowerExchangeMateNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.StrictTowerRealizationComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SupportProperUnitNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SupportReductionAugmentationPull` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SupportedCartierDerivedPullback` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SupportedCoefficientHomNaturality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SupportedCommonFieldScalarData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SupportedHomPullback` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SupportedRootScalarSiteComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SupportedTensorCartesianUnit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SupportedTensorIdentityUnitor` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SupportedTensorIsomorphismTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SupportedTensorSignedUnit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SystemClopenMateIdentification` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SystemCompactSupportData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SystemCompactSupportEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SystemCompactSupportRestrictionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SystemEnrichedProjectionAdjunction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SystemInternalHomRepresentability` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SystemOperationExchangeRealization` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SystemProjectionChangeCompatibility` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SystemProjectionFormulaCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SystemProjectionFormulaMaps` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SystemProjectionTriangleCompatibility` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SystemProperIdentityOpenProjection` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SystemPullbackCompositorEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SystemRefinementConstructibleDomain` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SystemScalarProjectionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SystemScalarProjectionIdentification` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SystemScalarRefinementRestriction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SystemScalarTensorConstituents` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SystemTensorPresentationData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.SystemTensorPresentationIdentification` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TameRootTowerExtension` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TensorHomExchange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TensorTransposeFiniteEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TorsionCdTopologicalSerreTransfer` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerAdjointCompositorRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerChernPullback` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerChernRealizationPullback` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerChernScalarUnit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerClassChern` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerClassCoefficients` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerClassDiagonal` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerClassFinite` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerClassFiniteDiagonal` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerClassPositiveUnitSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerClassProjective` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerClassPullback` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerClassReduction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerClassSectionAdjoint` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerClassSectionAdjointFaithful` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerClassSectionAdjointNaturality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerClassSystems` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerClassTensorPullback` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerClassTwisting` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerCompactSupportProjectionFormula` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerFactorOrientation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerFactorTensor` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerGeometricPurityAssembly` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerGeometricPurityData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerGeometryAdjunctionEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerOperationsGroundFieldRetagging` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerOrientationEvaluation` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1CoefficientCoordinates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1CtfData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1DiagonalTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1EtaleDelta` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1EtaleEpsilon` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1EtaleFiniteData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1EtaleOperations` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1EtaleOriginComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1EtaleWords` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1FirstTraceReordering` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1FormulaLevelComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1GeometricCoordinates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1KernelScalarData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1KernelScalarNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1KernelSplittingBaseChange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1LevelWords` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1ProjectionLevelComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1ProjectiveCoordinates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1ProperCtf` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1SecondTraceReordering` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1SingleLevelData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1SingleLevelTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1SingleLevelTriangles` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1TensorChainCoordinates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1TensorOrdinaryCoordinates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1TriangleFactorization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1TriangleWords` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1UniformCtfDomains` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerP1UniformPresentation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerProjectionDomainEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerPurityRealizedData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerPurityRealizedTranspose` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerSemilinearPurityFactors` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerTensorTransposeEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerTensorTransposeWords` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerTraceNormalizedPresentations` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerTracePurityComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TowerTracePurityComparisonData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TraceCorrespondences` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TraceStalkCompositorTowerData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TraceStalkCompositorTowerRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TraceStalkTowerDescent` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TransportIntegralCounitData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TransportIntegralCounitRealization` | claimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TransportedReductionPullbackNormalized` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionOrdinary` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TwistedPullbackAdicAgreement` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcTwist` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TwistedPullbackReductionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TwistedPullbackReductionTower` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TwistedPullbackScalarShifts` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareCoordinates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TwistedPullbackTowerDomainDefinitions` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.TwoOpenTensorChainNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.VaryingDimensionDualizingInverse` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.VaryingRingGraphSummand` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.VectorBundleFrameOrientationRestriction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.VectorIntegrationSiteComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.VerdierCompositionMateNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.VerdierHomChainComposition` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.VerdierHomChainCompositionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.VerdierIdentityProjection` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.VerdierOrdinaryTensorTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.VerdierPairingThreeTransposes` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.VerdierProjectionExceptionalPaste` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.WeilBaseChangeSemilinearPasting` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.WeilChosenDualityExchangeData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.WeilEquivarianceOfPurityAndTrace` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.WeilIndProperHigherRepresentability` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.WeilInternalHom` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.WeilPurityEquivarianceData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.WfTateTwist` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.WfTensorUnitSquareData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ZlFiniteIntegralFibreReconstruction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ZlFrameworkOpenExchange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ZlFrameworkPbcOpenComparisonData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ZlFrameworkQuotientAugmentation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ZlImmersionWeilLocalData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ZlOpenCompactSupportRestriction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ZlOpenDiagramComparisonTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ZlOpenExtensionTExact` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ZlOpenWeilUnitEmptyFibre` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Paper.ZlSfPbcNormalizedHeartModel` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.RepresentationTheory.ProfiniteAlgclDerivedInvariantsComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SecSmoothPurity.ClosedUnitAllStages` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SecSmoothPurity.NestedAffineChartFormulas` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SecSmoothPurity.NestedAffineFormulaData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SecSmoothPurity.ProEtaleCoefficientTowerNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SecSmoothPurity.ProEtaleProjectionMateIdentification` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SecSmoothPurity.RationalPurityCommonComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SecSmoothPurity.ReductionExceptionalObjects` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SecSmoothPurity.ScalarExtensionFunctor` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SecSmoothPurity.SupportedScalarTorInterval` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SecSmoothPurity.TransportFamily` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SecSmoothPurity.TransportGeometry` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.AmbientClopenRestrictionUniqueness` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.AmbientExactClopenComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.AmbientExactClopenData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.AmbientOrdinaryClopenLocalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.AmbientSystemBetaLocalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.AmbientSystemClopenLocalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.AmbientUnderivedClopenPasting` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.AugmentedStrictIntegralCompletion` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.BasicRealizationShiftSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.BoundaryDualityDischarge` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CanonicalReductionPullComposition` | claimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CanonicalReductionPullTensor` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CoefDualizingSiteMates` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CoefFinitePairingEvaluationData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionCocycles` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtensionReductionPairing` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CoefPairingCompactificationModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CoefPairingFiniteNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CoefPairingFrameNaturality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CoefPairingSystemDinaturality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdierCore` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdierData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdierInternalHom` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CoefSystemProjectionEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairingData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CoefVerdierWeilData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CoefWeilExceptionalCompatibility` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CoefficientProjectionPointData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CompactSupportProperImageTower` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CompactifiedProperTowerExchange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CompletedProjectionExchangeData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CompletedProjectionExchangeSystem` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CompletedShriekCompositionLaws` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CompositionProjectionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.CompositionProjectionMate` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.DiagramPullbackShiftData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.DualizingOpenMate` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.EtaleHomComparisonModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ExceptionalIntegralReconstructionEquivalence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ExceptionalIntegralReconstructionInterfaces` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ExceptionalIntegralSystemExistence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.FiniteCoefficientVerdierData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.FiniteDualitySiteComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.FiniteExceptional` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.FiniteExceptionalData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.FiniteExceptionalDomain` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.FiniteIntrinsicBidualComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.FiniteOpenCartesianCalculus` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.FiniteOpenDirectImageCtf` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.FiniteScalarMateData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.FiniteScalarMateRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyComparisonFactors` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyRealizationTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusPointTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.GeneratorReductionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.GraphFrobeniusOpenExchange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IndependentExpressionReductionShift` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IndependentExpressionShiftNaturality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralAffinePurityInduction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralBasicGeneratorSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralBasicRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralBasicRealizationData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralBoundaryExchange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralBoundaryRefinementNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralCanonicalAmbientModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralCanonicalRealizationSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralCanonicalSystemCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralCartesianCompactSupport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactSupportDefs` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactSupportPullback` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeWords` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationComparisonData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationRealizationData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralComparisonRecursionLaws` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompatibleComposition` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompletedDirectImageComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralDualExceptionalSystem` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineChart` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineFactorization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalDescendedCounit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalMappingSystem` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralExpressionCanonicalSupport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralExpressionCoefficientSquares` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralExpressionOccurrences` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralExpressionRecursion` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralExpressionRecursionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralExpressionTransposeIsIso` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralKernelContractions` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralKernelUnitCounit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralNormalizedComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralNormalizedRefinementPasting` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralOpenMateNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralOpenRealizationNaturality` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralOpenReductionComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralOpenReductionDefinitions` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralOpenReductionNormalizedLimit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralOperationShiftData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralOrdinaryCompactificationSquares` | claimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralOrdinaryExchangeProjectionSquares` | claimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralOrdinaryExpressionNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralOrdinaryExpressionReduction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralOrdinaryLimitModel` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralOrdinaryProperOpenSquare` | claimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralProjectiveLineAdjunction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralProperTowerTransition` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationAssemblyData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralReductionPullbackModel` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionBoundedDescent` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionChartCover` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionFunctors` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionGlue` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralRingedModelExistence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralRingedPullCompletion` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralSupportCounitProjection` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralSupportProjectionTransport` | claimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralSupportRealizationComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralSupportStrictTowerComparison` | claimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralSupportTowerNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemCanonicalBridge` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemCompositorAssociativity` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemDualityCompatibility` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemExpressionDomain` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemOperationModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemOperations` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemTensorComposition` | claimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdier` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdierModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdierReductionPairing` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.IntegralVerdierSignedCalculus` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.KappaCoefficientCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.KappaGeometricComparisons` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.KunnethFirstOpenSubstitution` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.KunnethSecondOpenSubstitution` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenBaseChangeReductionSquare` | claimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenBaseChangeSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenBaseChangeSquareData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateIntegral` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenDvrRingedIdentification` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenExchangeRoosRestriction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenExternalTensorNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorCoherenceData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorExchangeRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorProjectionRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenFactorPullModel` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenInterchangeReductionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenInterchangeReductionSquares` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenNormalizedProductCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenProjectionCompletedSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenProjectionOrdinaryRoos` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenProjectionRestrictionNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenProjectionRoosCompletion` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenProjectionRoosCompletionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenQuotientCompletionUnitComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenReconstructionEffectivity` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenReductionMateLocalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenRoosRestrictionDescent` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenRoosUnitAdjunction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenScalarTensorNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenSemilinearTensorModel` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenSemilinearTensorModelData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenStarShriekScalarMateSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenSupportStepBounds` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OpenTensorReductionSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OrdinaryFiniteQuotientOpenSupport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OrdinaryOpenFiniteEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OrdinaryOpenReductionMate` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.OrdinaryReductionAugmentedComputation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.PrimitiveCompletionEffectivity` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.PrimitiveQuotientAugmentations` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.InternalCompletionSectionTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.InternalCompletionStacksComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.InternalFirstResidueReductionComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.InternalResidueStacksComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ProductCompactificationIdentity` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ProductNormalizationRealizationTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ProductSystemUniformRealizationDomain` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ProjectionRefinementDescent` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ProjectionRefinementInputs` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ProjectionSystemCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ProjectiveChartOrdinaryTensorModel` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenInterchangeReductionSquare` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenLambdaReductionSquare` | claimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ProperSupportStepBounds` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.PublishedSystemAmbientCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.PublishedSystemAmbientPresentation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.PublishedSystemCompositorIdentification` | claimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.PublishedSystemTensorComposition` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.PullQuotientAugmentationOnGood` | claimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.RamifiedScalarExceptionalLimit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.RamifiedScalarPreparation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.RationalExceptionalIdentifications` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.RationalOperationsData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.RationalVerdierModels` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.RealizationAdjunctionInsertionShift` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.RealizationTreeShiftData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.RealizationTreeShiftTransport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.RefinementProjectionCounit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.RefinementProjectionLocalTensor` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.RefinementProjectionProperComposition` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.RefinementProjectionWords` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ScalarDirectImageMateCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ScalarSixDirectImage` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ScalarSixGeometry` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.SemilinearOpenExternalCoherence` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ShortWordCompletionIsomorphism` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.ShortWordIntegralDomain` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.StrictCompactificationProjectionShift` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.SystemAdjunctionOpenMapShift` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.SystemProperOpenLambdaExchange` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.SystemProperOpenProjectionShift` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.SystemProperOpenSupport` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.SystemPullbackCompositorIdentification` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.SystemPushCompositionLaws` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.SystemPushIdentityPullUnit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.SystemTotalEnrichedTranspose` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.TensorAdjunctionReductionSquares` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.TensorExchangePresentation` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.TensorHomTranspositionData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.TensorQuotientAugmentationOnGood` | claimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.TriangleProjectionCompositorContraction` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.TriangleProjectionSystemNormalForm` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.VerdierExchangeData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.SixFunctors.WeilChosenDualityHom` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Targets.AffineSpaceRationalLine` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.Targets.PoincareTateBoundedConstructible` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.TraceFormula.CounitRealizationSubstitution` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.TraceFormula.FiniteCoverTubeComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.TraceFormula.OrientedDerivedCohomologyContinuity` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.TraceFormula.OrientedPointCohomology` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.TraceFormula.PsiProperSurjectiveConstructibility` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.TraceFormula.ScalarModelAssociativity` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.TraceFormula.ScalarModelUnit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.TraceFormula.StrictQuotientCompletionUnit` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.WeilSheaf.DualRealizationComparison` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.WeilSheaf.NativeBidualEvaluationRealization` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.WeilSheaf.NativeDualRealizationComparisonData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.WeilSheaf.NativeExceptionalForgetful` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.WeilSheaf.NativeExceptionalForgetfulData` | unclaimed | Identical reexport; no adaptation. |
| `Sheaf.WeilSheaf.NativeExceptionalLeftModels` | unclaimed | Identical reexport; no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | Identical reexport; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.Adic.EtaleBaseChange` | unclaimed | Identical reexport; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension` | unclaimed | Identical reexport; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ScalarExtension` | unclaimed | Identical reexport; no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat` | unclaimed | Identical reexport; no adaptation. |

## Status

All four direct importers compiled without errors against the sandbox overlay.
A profiled check of the initially slow devissage consumer completed in 6.1 s
against the packet and 5.6 s against the published item, with no slow declaration.
No consumer source is changed by this delivery.


open
