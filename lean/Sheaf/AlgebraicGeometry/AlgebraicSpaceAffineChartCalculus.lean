/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceCommAlgebraSheaf
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Sheaf.CategoryTheory.RingedSheafSliceAdjunction
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra
import WeilConjectures.RingTheory.SymmetricAlgebraBaseChange
import WeilConjectures.RingTheory.FilteredColimitAlgebrasUnderlyingModule

/-! # Quasi-coherent affine etale chart calculus

Source: Stacks Project, Properties of Spaces, Tags 03LZ, 03M0, 03M1 and local module
properties; Limits of Spaces, Tags 082A and 086Z
(blueprint: lem-sfb-space-qcoh-affine-chart-calculus).

Algebra sections are objects of the under category of their actual commutative section
ring. Isomorphisms of quotients are characterized by their quotient projections.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The ordinary associated module sheaf on an affine chart: tilde, transported along
its canonical isomorphism with Spec of its section ring. No module is chosen.
Source: Stacks, Schemes, Tags 01HV and 01IA; Properties of Spaces, Tag 03LZ
(blueprint: lem-sfb-space-qcoh-affine-chart-calculus). -/
def affineChartAssociated {S : Scheme.{u}} (X : AlgebraicSpace S) (U : X.EtaleSite)
    [IsAffine (X.etaleForget.obj U)] :
    ModuleCat.{u} (X.commStructureSheaf.obj.obj (op U)) ⥤ (X.etaleForget.obj U).Modules :=
  tilde.functor _ ⋙ Scheme.Modules.pullback (X.etaleForget.obj U).isoSpec.hom

/-- Affine etale charts compute quasi-coherent modules and their algebra operations.
Source: Stacks, Properties of Spaces, Tags 03LZ, 03M0, 03M1 and section-properties-modules;
Limits of Spaces, Tags 082A and 086Z
(blueprint: lem-sfb-space-qcoh-affine-chart-calculus).

Proof:
1. Restrict to the chart using lem-sfb-space-qcoh-cartesian-chart-family. The equivalence
   lem-trf-scheme-zariski-etale-quasi-coherent-equivalence and tilde/Gamma unit and counit
   (lem-weil-pbc-affine-tilde-gamma-adjunction) identify this restriction with the associated
   sheaf of its sections, naturally. The module pullback adjunction gives the same Hom
   formula for an arbitrary target, not just a quasi-coherent one.
2. Slice restriction is exact and preserves colimits by the ringed-sheaf-slice and module
   adjunctions and lem-weil-pbc-left-adjoint-preserves-colimits. Apply
   lem-sfb-space-qcoh-kernels-colimits and the affine tilde equivalence to kernels,
   cokernels, images and filtered module colimits; this also gives the canonical maps.
3. Use lem-weil-pbc-ringed-topoi-module-pullback-tensor and the affine tensor-sections
   theorem to compute tensor products. For an affine arrow W to U, the formula is
   F(W) = O(W) tensor F(U), with restriction m mapped to 1 tensor m.
4. The scheme etale exact-finiteness comparison and the affine finite-type criterion
   identify local finite generation and presentation with their section-module versions.
   A surjective etale chart covers every etale object after base change; refine by local
   presentations and compose covers. A finite presentation is already a local presentation
   and hence implies quasi-coherence, even without an initial quasi-coherence assumption.
5. Form symmetric algebras on scheme charts using the scheme symmetric-algebra theorem.
   Symmetric-algebra base change identifies restrictions; agreement on degree-one
   generators proves the cocycle. Glue the modules and multiplication by the cartesian
   chart-family theorem. On affines this gives Sym_R(F(U)), with its degree-one map.
6. For any algebra target H, extend F(U) to Sym_R(F(U)) by the ordinary universal
   property. Step 1 extends the resulting linear map to the chart. Multiplication and
   unit equations follow by Step 1 applied to the quasi-coherent tensor square and unit.
   Uniqueness makes the extensions agree under affine restriction; affine open covers
   of arbitrary etale objects glue them, including for non-quasi-coherent H.
7. The module kernel and image of an algebra map are quasi-coherent by Step 2. Its kernel
   is an ideal and image is a unital algebra, checked locally on sections. The quotient
   operations on D/ker are induced by those of D. Ordinary affine first-isomorphism maps
   commute with restriction and glue, identifying that quotient with the image algebra.
8. The generated ideal is the image of D tensor E to D, d tensor x mapped to d e(x).
   Steps 2 and 3 give quasi-coherence and the ordinary affine generated ideal. It contains
   e(E), and every ideal sheaf containing e(E) contains the products, sums and local
   gluings. Its cokernel gives the quotient, computed on affines; affine quotient lifts
   of every algebra map killing e glue uniquely, giving its full universal property.
9. For a small filtered algebra diagram take the ambient colimit of underlying modules
   (lem-sfb-space-qcoh-kernels-colimits). Step 2 and the filtered-algebra underlying-module
   theorem identify each affine value with the ordinary ring colimit. Restrictions
   preserve its operations by uniqueness of module-colimit maps. Glue these operations
   over affine open covers of every etale object to equip the module colimit with an
   algebra structure and algebra cocone legs.
10. For any algebra target, the ambient module-colimit lift preserves multiplication
    and unit on every affine chart, hence globally. Thus the cocone is colimiting in all
    algebra sheaves. Any cocone with quasi-coherent vertex and colimiting affine values
    has an isomorphic comparison from this colimit: the affine inverse maps commute with
    restrictions and glue. This proves the final chart test. -/
theorem quasiCoherent_affine_chart_calculus {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (∀ (U : X.EtaleSite) [IsAffine (X.etaleForget.obj U)],
      Nonempty ((ObjectProperty.ι (SheafOfModules.isQuasicoherent X.structureSheaf) ⋙
        schemeRestriction X U) ≅
        (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.structureSheaf) ⋙
          SheafOfModules.evaluation X.structureSheaf (op U) ⋙ affineChartAssociated X U))) ∧
    (∀ (F G : X.Modules) (f : F ⟶ G), F.IsQuasicoherent → G.IsQuasicoherent →
      (kernel f).IsQuasicoherent ∧ (cokernel f).IsQuasicoherent ∧
      (image f).IsQuasicoherent ∧
      ∀ (U : X.EtaleSite), IsAffine (X.etaleForget.obj U) →
        IsIso (kernelComparison f (SheafOfModules.evaluation X.structureSheaf (op U))) ∧
        IsIso (cokernelComparison f (SheafOfModules.evaluation X.structureSheaf (op U))) ∧
        Set.range ((image.ι f).val.app (op U)) = Set.range (f.val.app (op U))) ∧
    (∀ (F G : X.Modules), F.IsQuasicoherent → G.IsQuasicoherent →
      ((SheafOfModules.siteSheafTensorRight (A := X.commStructureSheaf) G).obj F).IsQuasicoherent ∧
      ∀ (U : X.EtaleSite), IsAffine (X.etaleForget.obj U) →
        ∃ e : TensorProduct (X.commStructureSheaf.obj.obj (op U))
            (F.val.obj (op U)) (G.val.obj (op U)) ≃ₗ[X.commStructureSheaf.obj.obj (op U)]
              ((SheafOfModules.siteSheafTensorRight (A := X.commStructureSheaf) G).obj F).val.obj
                (op U),
          ∀ (x : F.val.obj (op U)) (y : G.val.obj (op U)),
            e (x ⊗ₜ[X.commStructureSheaf.obj.obj (op U)] y) =
              SheafOfModules.siteSheafTensorTmul (A := X.commStructureSheaf) F G (op U) x y) ∧
    (∀ (J : Type u) [SmallCategory J] [IsFiltered J] (D : J ⥤ X.Modules),
      (∀ j : J, (D.obj j).IsQuasicoherent) →
      ∃ c : Cocone D, Nonempty (IsColimit c) ∧ c.pt.IsQuasicoherent ∧
        ∀ (U : X.EtaleSite), IsAffine (X.etaleForget.obj U) →
          Nonempty (IsColimit ((SheafOfModules.evaluation X.structureSheaf (op U)).mapCocone c))) ∧
    (∀ F : X.Modules, F.IsQuasicoherent →
      (F.IsFiniteType ↔ ∀ (U : X.EtaleSite), IsAffine (X.etaleForget.obj U) →
        Module.Finite (X.commStructureSheaf.obj.obj (op U)) (F.val.obj (op U))) ∧
      (F.IsFinitePresentation ↔ ∀ (U : X.EtaleSite), IsAffine (X.etaleForget.obj U) →
        Module.FinitePresentation (X.commStructureSheaf.obj.obj (op U)) (F.val.obj (op U))) ∧
      (∀ (U : X.EtaleSite), IsSurjective U.obj.hom →
        (F.IsFiniteType ↔ ((schemeRestriction X U).obj F).IsFiniteType) ∧
        (F.IsFinitePresentation ↔ ((schemeRestriction X U).obj F).IsFinitePresentation))) ∧
    (∀ F : X.Modules, F.IsFinitePresentation → F.IsQuasicoherent) ∧
    (∀ F : X.Modules, F.IsQuasicoherent →
      ∃ (A : X.CommAlgebraSheaf) (j : F ⟶ A.toModule),
        A.toModule.IsQuasicoherent ∧
        (∀ (B : X.CommAlgebraSheaf) (f : F ⟶ B.toModule),
          ∃! t : A ⟶ B, j ≫ (algebraModuleFunctor X).map t = f) ∧
        ∀ (U : X.EtaleSite), IsAffine (X.etaleForget.obj U) →
          ∃ e : SymmetricAlgebra (X.commStructureSheaf.obj.obj (op U))
              (F.val.obj (op U)) ≃+* A.right.obj.obj (op U),
            (∀ r : X.commStructureSheaf.obj.obj (op U),
              e (algebraMap (X.commStructureSheaf.obj.obj (op U))
                (SymmetricAlgebra (X.commStructureSheaf.obj.obj (op U))
                  (F.val.obj (op U))) r) = A.hom.hom.app (op U) r) ∧
            (∀ x : F.val.obj (op U),
              e (SymmetricAlgebra.ι (X.commStructureSheaf.obj.obj (op U))
                (F.val.obj (op U)) x) = j.val.app (op U) x)) ∧
    (∀ (D A : X.CommAlgebraSheaf) (ψ : D ⟶ A),
      D.toModule.IsQuasicoherent → A.toModule.IsQuasicoherent →
      IsAlgebraIdeal (kernel.ι ((algebraModuleFunctor X).map ψ)) ∧
      ∃ (Q B : X.CommAlgebraSheaf) (q : D ⟶ Q) (b : B ⟶ A) (e : Q ≅ B),
        Q.toModule.IsQuasicoherent ∧ B.toModule.IsQuasicoherent ∧
        q ≫ e.hom ≫ b = ψ ∧
        (∃ eb : B.toModule ≅ image ((algebraModuleFunctor X).map ψ),
          eb.hom ≫ image.ι ((algebraModuleFunctor X).map ψ) =
            (algebraModuleFunctor X).map b) ∧
        (kernel.ι ((algebraModuleFunctor X).map ψ) ≫
          (algebraModuleFunctor X).map q = 0) ∧
        (∀ (C : X.CommAlgebraSheaf) (g : D ⟶ C),
          kernel.ι ((algebraModuleFunctor X).map ψ) ≫
            (algebraModuleFunctor X).map g = 0 →
          ∃! t : Q ⟶ C, q ≫ t = g) ∧
        ∀ (U : X.EtaleSite), IsAffine (X.etaleForget.obj U) →
          Set.range (b.right.hom.app (op U)) = Set.range (ψ.right.hom.app (op U)) ∧
          ∃ eq : (D.right.obj.obj (op U) ⧸ RingHom.ker (ψ.right.hom.app (op U)).hom)
              ≃+* Q.right.obj.obj (op U),
            ∀ a : D.right.obj.obj (op U), eq (Ideal.Quotient.mk _ a) =
              q.right.hom.app (op U) a) ∧
    (∀ (E : X.Modules) (D : X.CommAlgebraSheaf) (e : E ⟶ D.toModule),
      E.IsQuasicoherent → D.toModule.IsQuasicoherent →
      ∃ (I : X.Modules) (i : I ⟶ D.toModule) (Q : X.CommAlgebraSheaf) (q : D ⟶ Q),
        I.IsQuasicoherent ∧ Q.toModule.IsQuasicoherent ∧ IsAlgebraIdeal i ∧
        (∃ t : E ⟶ I, t ≫ i = e) ∧
        (∀ (K : X.Modules) (k : K ⟶ D.toModule), IsAlgebraIdeal k →
          (∃ t : E ⟶ K, t ≫ k = e) → ∃ t : I ⟶ K, t ≫ k = i) ∧
        i ≫ (algebraModuleFunctor X).map q = 0 ∧
        (∀ (B : X.CommAlgebraSheaf) (f : D ⟶ B),
          e ≫ (algebraModuleFunctor X).map f = 0 → ∃! t : Q ⟶ B, q ≫ t = f) ∧
        ∀ (U : X.EtaleSite), IsAffine (X.etaleForget.obj U) →
          Set.range (i.val.app (op U)) =
            (↑(Ideal.span (Set.range (fun x : E.val.obj (op U) ↦
              @id (D.right.obj.obj (op U)) (e.val.app (op U) x)))) :
                Set (D.right.obj.obj (op U))) ∧
          ∃ eq : (D.right.obj.obj (op U) ⧸ Ideal.span (Set.range (fun x : E.val.obj (op U) ↦
            @id (D.right.obj.obj (op U)) (e.val.app (op U) x))))
              ≃+* Q.right.obj.obj (op U),
            ∀ a : D.right.obj.obj (op U), eq (Ideal.Quotient.mk _ a) =
              q.right.hom.app (op U) a) ∧
    (∀ (J : Type u) [SmallCategory J] [IsFiltered J] (D : J ⥤ X.CommAlgebraSheaf),
      (∀ j : J, ((D.obj j).toModule).IsQuasicoherent) →
      (∃ c : Cocone D, Nonempty (IsColimit c) ∧ (CommAlgebraSheaf.toModule c.pt).IsQuasicoherent ∧
        ∀ (U : X.EtaleSite), IsAffine (X.etaleForget.obj U) →
          Nonempty (IsColimit ((algebraEvaluation X U).mapCocone c))) ∧
      (∀ c : Cocone D, (CommAlgebraSheaf.toModule c.pt).IsQuasicoherent →
        (∀ (U : X.EtaleSite), IsAffine (X.etaleForget.obj U) →
          Nonempty (IsColimit ((algebraEvaluation X U).mapCocone c))) →
        Nonempty (IsColimit c))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
