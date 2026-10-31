/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.Algebra.Homology.DerivedInternalHomMixedUniverses
public import WeilConjectures.Algebra.Homology.RingedInternalHomExactUniverses
public import WeilConjectures.Algebra.Homology.DerivedTensorShiftDescent
public import Mathlib.CategoryTheory.Triangulated.Functor

/-! # The canonical coefficient tensor-Hom action and its exactness predicates

Source: Stacks 0BYU, 06YU and 0FNH.
(blueprint: def-sf-tensor-hom-action-predicates).
The definitions retain their original names and bodies; the entry module reexports them.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe a b c v u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite WeilConjectures

namespace CategoryTheory

section ClosedAction
variable {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
  (S : CoefficientClosedStructure H)

/-- Tensoring on the left by a fixed object, in the recorded closed structure.
Source: Stacks 0BYU (blueprint: lem-sf-tensor-hom-action-exact). -/
abbrev tensorHomActionSource (V : D) : D ⥤ D := Prod.sectR V D ⋙ S.tensor

/-- The target coefficient functor A ↦ H(K,L tensor A).
Source: Stacks 0BYU (blueprint: lem-sf-tensor-hom-action-exact). -/
abbrev tensorHomActionTarget (K L : D) : D ⥤ D :=
  tensorHomActionSource S L ⋙ (Functor.curry.obj H).obj (op K)

/-- The action is the transpose of reassociation, exchange, and evaluation tensor identity.
Source: Stacks 0BYU (blueprint: lem-sf-tensor-hom-action-exact). -/
def tensorHomAction
    (β : @SymmetricCategory D _ S.monoidal) (K L A : D) :
    S.tensor.obj (H.obj (op K, L), A) ⟶ H.obj (op K, S.tensor.obj (L, A)) :=
  S.transpose _ K _
    ((S.monoidal.associator (H.obj (op K, L)) A K).hom ≫
      S.tensor.map
        (X := (H.obj (op K, L), S.tensor.obj (A, K)))
        (Y := (H.obj (op K, L), S.tensor.obj (K, A)))
        (𝟙 _, (β.toBraidedCategory.braiding A K).hom) ≫
      (S.monoidal.associator (H.obj (op K, L)) K A).inv ≫
      S.tensor.map (X := (S.tensor.obj (H.obj (op K, L), K), A))
        (Y := (L, A)) (S.evaluation K L, 𝟙 A))
end ClosedAction

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})
  [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]

/-- The coefficient shifts are the signed total-tensor shifts transported by the actual
K-flat comparison and the localization shift. This fixes the comparisons without
making a new choice of resolutions or stability witnesses. The fixed factor `V` is
arbitrary and `eV` is any identification of it with a K-flat representative, so the
shift of `V ⊗ -` is pinned for every derived object `V`, not only for objects that are
literally localizations of K-flat complexes.
Source: Stacks 06YU and More on Algebra, Tag 0FNH, item-shift-tensor
(blueprint: lem-sf-tensor-hom-action-exact). -/
def tensorHomActionShiftNormalization
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (T : CoefficientTensorModels.{u, c, v, w} J R S)
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (hc : RingedDerivedTensorCoherence.{c, v, u, w} J R S T β)
    (s : ∀ V : DerivedCategory (RingedTensorModules.{c, v, u} J R),
      (tensorHomActionSource S V).CommShift ℤ) : Prop :=
  ∀ (V : DerivedCategory (RingedTensorModules.{c, v, u} J R))
    (P Q : CochainComplex (RingedTensorModules.{c, v, u} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q)
    (eV : DerivedCategory.Q.obj P ≅ V) (n : ℤ),
    letI := s V
    (hc.tensorIso P (Q⟦n⟧) (Or.inl hP)).hom ≫
        S.tensor.map
          (X := (DerivedCategory.Q.obj P, DerivedCategory.Q.obj (Q⟦n⟧)))
          (Y := (V, (DerivedCategory.Q.obj Q)⟦n⟧))
          (eV.hom, (DerivedCategory.Q.commShiftIso n).hom.app Q) ≫
        ((tensorHomActionSource S V).commShiftIso n).hom.app
          (DerivedCategory.Q.obj Q) =
      DerivedCategory.Q.map
          (CochainComplex.mapBifunctorShift₂Iso P Q (MonoidalCategory.curriedTensor _) n).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app
          ((coefficientTotalTensor.{u, c, v} J R).obj (P, Q)) ≫
        ((hc.tensorIso P Q (Or.inr hQ)).hom ≫
          S.tensor.map
            (X := (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
            (Y := (V, DerivedCategory.Q.obj Q)) (eV.hom, 𝟙 _))⟦n⟧'

/-- The complete coefficient action assertion. The Hom shift is the recorded uniquely
normalized unsigned target shift; the target functor uses the composite shift. A triangle
morphism with the prescribed components includes the connecting-arrow square by definition.
Source: Stacks 0BYU, with the DAG's exact coefficient enhancement
(blueprint: lem-sf-tensor-hom-action-exact). -/
def tensorHomActionExactSpec
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (s : ∀ V : DerivedCategory (RingedTensorModules.{c, v, u} J R),
      (tensorHomActionSource S V).CommShift ℤ) : Prop :=
  letI (V : DerivedCategory (RingedTensorModules.{c, v, u} J R)) := s V
  (∀ V : DerivedCategory (RingedTensorModules.{c, v, u} J R),
    (tensorHomActionSource S V).IsTriangulated) ∧
  (∀ K L : DerivedCategory (RingedTensorModules.{c, v, u} J R),
    (tensorHomActionTarget S K L).IsTriangulated) ∧
  (∀ (K K' L L' A A' : DerivedCategory (RingedTensorModules.{c, v, u} J R))
    (k : K' ⟶ K) (l : L ⟶ L') (f : A ⟶ A'),
    S.tensor.map ((derivedInternalHomOfUniverses.{c, v, u, w} J R).map (k.op, l), f) ≫
        tensorHomAction S β K' L' A' =
      tensorHomAction S β K L A ≫
        (derivedInternalHomOfUniverses.{c, v, u, w} J R).map (k.op, S.tensor.map (l, f))) ∧
  (∀ (K L A : DerivedCategory (RingedTensorModules.{c, v, u} J R)) (n : ℤ),
    tensorHomAction S β K L (A⟦n⟧) ≫
        ((tensorHomActionTarget S K L).commShiftIso n).hom.app A =
      ((tensorHomActionSource S
        ((derivedInternalHomOfUniverses.{c, v, u, w} J R).obj (op K, L))).commShiftIso n).hom.app
          A ≫ (tensorHomAction S β K L A)⟦n⟧') ∧
  (∀ (K L : DerivedCategory (RingedTensorModules.{c, v, u} J R))
    (Δ : Triangle (DerivedCategory (RingedTensorModules.{c, v, u} J R))),
    Δ ∈ distTriang _ →
      ((tensorHomActionSource S
        ((derivedInternalHomOfUniverses.{c, v, u, w} J R).obj (op K, L))).mapTriangle.obj Δ ∈
          distTriang _) ∧
      ((tensorHomActionTarget S K L).mapTriangle.obj Δ ∈ distTriang _) ∧
      ∃ φ : (tensorHomActionSource S
          ((derivedInternalHomOfUniverses.{c, v, u, w} J R).obj (op K, L))).mapTriangle.obj Δ ⟶
            (tensorHomActionTarget S K L).mapTriangle.obj Δ,
        φ.hom₁ = tensorHomAction S β K L Δ.obj₁ ∧
        φ.hom₂ = tensorHomAction S β K L Δ.obj₂ ∧
        φ.hom₃ = tensorHomAction S β K L Δ.obj₃) ∧
  (∀ K L : DerivedCategory (RingedTensorModules.{c, v, u} J R),
    tensorHomAction S β K L S.monoidal.tensorUnit ≫
        (derivedInternalHomOfUniverses.{c, v, u, w} J R).map
          (X := (op K, S.tensor.obj (L, S.monoidal.tensorUnit)))
          (Y := (op K, L)) (𝟙 (op K), (S.monoidal.rightUnitor L).hom) =
      (S.monoidal.rightUnitor
        ((derivedInternalHomOfUniverses.{c, v, u, w} J R).obj (op K, L))).hom)

/-- Exact functors and shift compatibility of the action.
Naturality and the unit law are proved generically; these laws then
formally imply the triangle-morphism assertion.
Source: Stacks 0BYU (blueprint: lem-sf-tensor-hom-action-normalized-laws). -/
def tensorHomActionExactCore
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J R))
    (β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, u} J R))
      _ S.monoidal)
    (s : ∀ V : DerivedCategory (RingedTensorModules.{c, v, u} J R),
      (tensorHomActionSource S V).CommShift ℤ) : Prop :=
  letI (V : DerivedCategory (RingedTensorModules.{c, v, u} J R)) := s V
  (∀ V : DerivedCategory (RingedTensorModules.{c, v, u} J R),
    (tensorHomActionSource S V).IsTriangulated) ∧
  (∀ K L : DerivedCategory (RingedTensorModules.{c, v, u} J R),
    (tensorHomActionTarget S K L).IsTriangulated) ∧
  (∀ (K L A : DerivedCategory (RingedTensorModules.{c, v, u} J R)) (n : ℤ),
    tensorHomAction S β K L (A⟦n⟧) ≫
        ((tensorHomActionTarget S K L).commShiftIso n).hom.app A =
      ((tensorHomActionSource S
        ((derivedInternalHomOfUniverses.{c, v, u, w} J R).obj (op K, L))).commShiftIso n).hom.app
          A ≫ (tensorHomAction S β K L A)⟦n⟧')

end CategoryTheory
