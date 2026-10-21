/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Localization.Predicate

/-! # The unbounded scalar model of an ind-finite-free algebra sheaf

Source: Stacks Project, sites-modules.tex, Tags 03EU (2), 03EP (2), and Section 03EK;
sites-cohomology.tex, Tags 06YT and 06YY; derived.tex, Tag 015F.
(blueprint: lem-sfb-ind-finite-free-scalar-model).
The auxiliary functors spell out the coefficient diagram and its termwise tensor colimit.
All derived scalar extensions are the existing universal cochain models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r wR wS wT
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings

namespace SheafOfModules.IndFiniteFree

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]

/-- The existing module category at the coefficient universe.
Source: Stacks 03D2 (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)

/-- Ordinary scalar restriction, with the same sections and restricted action.
Source: Stacks 03D2 (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
abbrev restriction {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S) :
    Modules S ⥤ Modules R :=
  restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)

/-- Forget the algebra structure of an algebra sheaf, retaining its R-module structure.
On morphisms this is the original section map, linear by the triangle over R.
Source: Stacks 03EK (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
def algebraModules (R : Sheaf J CommRingCat.{r}) : Under R ⥤ Modules R where
  obj A := (restriction A.hom).obj
    (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A.right))
  map {A B} f :=
    { val := PresheafOfModules.homMk
        (Functor.whiskerRight f.right.hom
          (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) (by
          intro V x a
          change A.right.obj.obj V at a
          change R.obj.obj V at x
          change (f.right.hom.app V).hom ((A.hom.hom.app V).hom x * a) =
            (B.hom.hom.app V).hom x * (f.right.hom.app V).hom a
          rw [map_mul]
          congr 1
          exact congrArg (fun t ↦ t.hom.app V x) (Under.w f)) }

/-- Tensor a complex termwise with a coefficient module; coefficient maps act by tensor.
Source: Stacks 03EK (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
def tensorComplex (R : Sheaf J CommRingCat.{r}) :
    Modules R ⥤ (CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ) where
  obj M := (tensorLeft M).mapHomologicalComplex (.up ℤ)
  map f := ((curriedTensor (Modules R)).map f).mapHomologicalComplex (.up ℤ)
  map_id M := by simp
  map_comp f g := by simp

/-- The diagram i ↦ S_i tensor A, with all differentials and transitions termwise.
Source: Stacks 03EP (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
def tensorDiagram {R : Sheaf J CommRingCat.{r}} {I : Type r} [SmallCategory I]
    (D : I ⥤ Under R) (A : CochainComplex (Modules R) ℤ) :
    I ⥤ CochainComplex (Modules R) ℤ :=
  (D ⋙ algebraModules R ⋙ tensorComplex R).flip.obj A

/-- The actual colimit functor on these complexes. Colimits of complexes are termwise.
Source: Stacks 03EP (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
def tensorColimit {R : Sheaf J CommRingCat.{r}} {I : Type r} [SmallCategory I]
    (D : I ⥤ Under R) :
    CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ :=
  (D ⋙ algebraModules R ⋙ tensorComplex R).flip ⋙ colim

/-- A pure tensor in the sheaf tensor, using its presheaf-to-sheaf unit.
The supplied factor is the actual underlying module, not a choice of basis.
Source: Stacks 03EK, 03CY (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
def pureTensor {R : Sheaf J CommRingCat.{r}} (M N : Modules R)
    (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) : (M ⊗ N).val.obj V :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J R).obj)).unit.app
      (M.val ⊗ N.val)).app V (x ⊗ₜ[R.obj.obj V] y) |>
    (tensorObjIsoSheafification M N).inv.val.app V

variable {R S : Sheaf J CommRingCat.{r}} {φ : R ⟶ S}
  [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wS} (Modules S)]

/-- The pure tensor in the ordinary functor of the existing derived scalar model.
Source: Stacks 03EK, 06YY (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
def extensionPure (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    (M : Modules R) (V : Cᵒᵖ) (s : S.obj.obj V) (a : M.val.obj V) :
    (m.E.obj M).val.obj V :=
  (eqToHom (m.obj_eq M).symm).val.app V
    ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app V
      (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] a))

/-- Normalization of the chain comparison on the sheafification-unit images of local
pure tensors. The coprojections are those of the supplied algebra colimit.
Source: Stacks 03EP, 03CY (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
def Normalized {I : Type r} [SmallCategory I] (D : I ⥤ Under R) (c : Cocone D)
    [HasDerivedCategory.{wS} (Modules c.pt.right)]
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} c.pt.hom)
    (κ : tensorColimit D ≅ m.E.mapHomologicalComplex (.up ℤ) ⋙
      (restriction c.pt.hom).mapHomologicalComplex (.up ℤ)) : Prop :=
  ∀ (A : CochainComplex (Modules R) ℤ) (i : I) (n : ℤ) (V : Cᵒᵖ)
    (s : (D.obj i).right.obj.obj V) (a : (A.X n).val.obj V),
    (((colimit.ι (tensorDiagram D A) i) ≫ κ.hom.app A).f n).val.app V
        (pureTensor ((algebraModules R).obj (D.obj i)) (A.X n) V s a) =
      extensionPure m (A.X n) V ((c.ι.app i).right.hom.app V s) a

/-- Compatibility of the chain comparison and the derived counit with coefficient
maps, also allowing a functor between the indexing categories. Both ordinary maps are
specified by their local tensors or their colimit legs. The derived map is specified by
its square with the counits after exact restriction along S → S'; its naturality includes
inverted quasi-isomorphisms. The underlying R-linear map has the same section maps.
Source: Stacks 03EP, 06YY, and localization 04VK
(blueprint: lem-sfb-ind-finite-free-scalar-model). -/
def CoefficientCompatible {I : Type r} [SmallCategory I]
    (D : I ⥤ Under R) (c : Cocone D)
    [HasDerivedCategory.{wS} (Modules c.pt.right)]
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} c.pt.hom)
    [PreservesFiniteLimits (restriction c.pt.hom)]
    [PreservesFiniteColimits (restriction c.pt.hom)]
    (κ : tensorColimit D ≅ m.E.mapHomologicalComplex (.up ℤ) ⋙
      (restriction c.pt.hom).mapHomologicalComplex (.up ℤ)) : Prop :=
  ∀ (I' : Type r) [SmallCategory I'] [IsFiltered I']
    [HasExactColimitsOfShape I' (Modules R)]
    (D' : I' ⥤ Under R) (c' : Cocone D'),
    IsColimit c' → IsColimit ((algebraModules R).mapCocone c') →
    (∀ i : I', ∃ d : ℕ, Nonempty ((algebraModules R).obj (D'.obj i) ≅
      ∏ᶜ fun _ : Fin d ↦ unit (derivedChangeRingIndependentCoefficients J R))) →
    ∀ [HasDerivedCategory.{wT} (Modules c'.pt.right)]
      (m' : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wT} c'.pt.hom)
      (κ' : tensorColimit D' ≅ m'.E.mapHomologicalComplex (.up ℤ) ⋙
        (restriction c'.pt.hom).mapHomologicalComplex (.up ℤ)),
      Normalized D' c' m' κ' →
      ∀ (F : I ⥤ I') (τ : D ⟶ F ⋙ D') (h : c.pt ⟶ c'.pt),
        (∀ i : I, c.ι.app i ≫ h = τ.app i ≫ c'.ι.app (F.obj i)) →
        ∃ (_ : PreservesFiniteLimits (restriction c'.pt.hom))
          (_ : PreservesFiniteColimits (restriction c'.pt.hom))
          (_ : PreservesFiniteLimits (restriction h.right))
          (_ : PreservesFiniteColimits (restriction h.right))
          (βS : m.E ⟶ m'.E ⋙ restriction h.right)
          (β : m.E ⋙ restriction c.pt.hom ⟶ m'.E ⋙ restriction c'.pt.hom)
          (L : tensorColimit D ⟶ tensorColimit D')
          (βD : m.T ⟶ m'.T ⋙ (restriction h.right).mapDerivedCategory),
          (∀ (M : Modules R) (V : Cᵒᵖ) (z : (m.E.obj M).val.obj V),
            (β.app M).val.app V z = (βS.app M).val.app V z) ∧
          (∀ (M : Modules R) (V : Cᵒᵖ) (s : c.pt.right.obj.obj V) (a : M.val.obj V),
            (βS.app M).val.app V (extensionPure m M V s a) =
              extensionPure m' M V (h.right.hom.app V s) a) ∧
          (∀ (A : CochainComplex (Modules R) ℤ) (i : I),
            colimit.ι (tensorDiagram D A) i ≫ L.app A =
              (((tensorComplex R).map ((algebraModules R).map (τ.app i))).app A) ≫
                colimit.ι (tensorDiagram D' A) (F.obj i)) ∧
          (∀ A : CochainComplex (Modules R) ℤ,
            L.app A ≫ κ'.hom.app A =
              κ.hom.app A ≫ (β.mapHomologicalComplex (.up ℤ)).app A) ∧
          (∀ A : CochainComplex (Modules R) ℤ,
            m.ε.app A ≫ DerivedCategory.Q.map ((βS.mapHomologicalComplex (.up ℤ)).app A) =
              βD.app (DerivedCategory.Q.obj A) ≫
                (restriction h.right).mapDerivedCategory.map (m'.ε.app A) ≫
                (restriction h.right).mapDerivedCategoryFactors.hom.app
                  ((m'.E.mapHomologicalComplex (.up ℤ)).obj A))

/-- An ind-finite-free coefficient algebra has an exact ordinary scalar-extension model
on all unbounded complexes, with the canonical counit and normalized colimit comparison.
Source: Stacks Project, sites-modules.tex, Tags 03EU (2), 03EP (2), Section 03EK;
sites-cohomology.tex, Tags 06YT, 06YY; derived.tex, Tag 015F.
(blueprint: lem-sfb-ind-finite-free-scalar-model).

Proof, following the eight DAG steps:
1. Tensoring with each S_i is a finite sum of the identity by finite freeness, the
   tensor unit, and additivity (lem-pc-sheaf-modules-tensor-closed). Finite sums preserve
   short exact sequences, also for rank zero; compatible bases are unnecessary.
2. The underlying-module colimit and tensor preservation of coefficient-small colimits
   (lem-weil-pbc-independent-sheaf-tensor-colimits), symmetry, and the normalized
   extension/tensor comparison (lem-weil-pbc-extension-tensor-comparison) give the
   canonical module comparison with restricted E, with leg q_i tensor 1.
3. Apply exact I-colimits to the stagewise short exact sequences. Restriction is exact
   by lem-pur-sheaf-ring-coefficient-ordinary-adjunction and reflects exactness because
   kernels and sheafified cokernels have unchanged underlying abelian sheaves. Thus E
   is exact (def-weil-sheaf-of-modules-category, def-pc-sheaf-restrict-scalars).
4. Apply the module comparison degreewise. Naturality with each differential gives
   the chain comparison; before sheafification its legs send s tensor a to q_i(s)
   tensor a. Pure tensors generate and sheafification is universal (03CY).
5. The chain and coefficient naturality squares agree on these pure tensors. For a
   functor between index categories use the target coprojections. Tensor generation,
   sheafification and colimit uniqueness prove both squares, independently of bases.
6. Exact-functor cohomology identifies H^n(EA) with E(H^n A), so termwise E preserves
   every quasi-isomorphism; exact-functor-derived-factorization gives D(E) on ordinary
   unbounded derived categories with its comparison.
7. The exact-functor-derived-functor lemma and lem-pur-derived-change-of-rings identify
   the two universal left-derived pairs uniquely respecting counits. Thus the existing
   counit is invertible at every A. A K-flat resolution exists by lem-pc-kflat-resolution;
   for any such p, counit naturality identifies its component with Q(Ep) under the
   canonical comparison inv(T(Qp)) followed by the counit at P.
8. Exact restriction also preserves quasi-isomorphisms. Localization's fully faithful
   precomposition (lem-weil-pbc-localization-universal-property) descends the chain
   comparison and all its squares, including inverted quasi-isomorphisms. For a
   coefficient map use a common K-flat resolution and localize E'p composed with the
   coefficient map = the coefficient map composed with Ep. Step 7 identifies this
   with the displayed derived-counit square. No step requires a bounded complex. -/
theorem ind_finite_free_scalar_model
    {I : Type r} [SmallCategory I] [IsFiltered I]
    [HasExactColimitsOfShape I (Modules R)]
    (D : I ⥤ Under R) (c : Cocone D)
    (hc : IsColimit c) (hcModules : IsColimit ((algebraModules R).mapCocone c))
    (hfree : ∀ i : I, ∃ d : ℕ, Nonempty ((algebraModules R).obj (D.obj i) ≅
      ∏ᶜ fun _ : Fin d ↦ unit (derivedChangeRingIndependentCoefficients J R)))
    [HasDerivedCategory.{wS} (Modules c.pt.right)]
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} c.pt.hom) :
    ∃ (_ : PreservesFiniteLimits m.E) (_ : PreservesFiniteColimits m.E)
      (_ : PreservesFiniteLimits (restriction c.pt.hom))
      (_ : PreservesFiniteColimits (restriction c.pt.hom)),
      (∀ (A B : CochainComplex (Modules R) ℤ) (f : A ⟶ B),
        QuasiIso f → QuasiIso ((m.E.mapHomologicalComplex (.up ℤ)).map f)) ∧
      IsIso m.ε ∧
      (∀ (P A : CochainComplex (Modules R) ℤ) (p : P ⟶ A) [QuasiIso p],
        CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
        ∃ e : m.T.obj (DerivedCategory.Q.obj A) ≅
            DerivedCategory.Q.obj ((m.E.mapHomologicalComplex (.up ℤ)).obj P),
          e.hom = m.T.map (inv (DerivedCategory.Q.map p)) ≫ m.ε.app P ∧
          e.hom ≫ DerivedCategory.Q.map ((m.E.mapHomologicalComplex (.up ℤ)).map p) =
            m.ε.app A) ∧
      ∃ κ : tensorColimit D ≅ m.E.mapHomologicalComplex (.up ℤ) ⋙
          (restriction c.pt.hom).mapHomologicalComplex (.up ℤ),
        Normalized D c m κ ∧
        (∀ (A B : CochainComplex (Modules R) ℤ) (f : A ⟶ B),
          QuasiIso f → QuasiIso ((tensorColimit D).map f)) ∧
        (∃ (KD : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules R))
          (θ : DerivedCategory.Q ⋙ KD ≅ tensorColimit D ⋙ DerivedCategory.Q)
          (κD : KD ≅ m.T ⋙ (restriction c.pt.hom).mapDerivedCategory),
          ∀ A : CochainComplex (Modules R) ℤ,
            θ.hom.app A ≫ DerivedCategory.Q.map (κ.hom.app A) =
              κD.hom.app (DerivedCategory.Q.obj A) ≫
                (restriction c.pt.hom).mapDerivedCategory.map (m.ε.app A) ≫
                (restriction c.pt.hom).mapDerivedCategoryFactors.hom.app
                  ((m.E.mapHomologicalComplex (.up ℤ)).obj A)) ∧
        CoefficientCompatible.{u, v, r, wR, wS, wT} D c m κ := by
  sorry

end SheafOfModules.IndFiniteFree
