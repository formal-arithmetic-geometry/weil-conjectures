/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Paper.IndHeartCanonicalPresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.CategoryTheory.SheafTensor
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.Paper.CoefficientHeart
import Sheaf.Paper.IndHeartFullFaithfulness
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!
# Kernels and cokernels of ind-constructible sheaves

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ind-heart/
sk-prop-ind-heart-kernels-cokernels.md and its proof
(blueprint: det-ind-heart-kernels-cokernels).

The square category is `CostructuredArrow ι.mapArrow (Arrow.mk f)`, where ι is the
constructible inclusion. Its tautological arrow cocone is Mathlib's pointwise left
extension cocone. Applying `ker` and `coker` gives exactly the canonical cocones at
ker(f) and coker(f); asserting their colimit properties fixes the comparisons themselves.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w t

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Source projection of the category of squares from arrows of C to f onto J(B).
This is the standard comma-category map induced by the source functors.
Source: blueprint sk-prop-ind-heart-kernels-cokernels.md, definition of P_f and its projections
(blueprint: det-ind-heart-kernels-cokernels). -/
def indHeartSquareSource {C : Type u} [Category.{v} C] {M : Type w} [Category.{t} M]
    (ι : C ⥤ M) {B B' : M} (f : B ⟶ B') :
    CostructuredArrow ι.mapArrow (Arrow.mk f) ⥤ CostructuredArrow ι B :=
  CostructuredArrow.map₂ (F := Arrow.leftFunc) (G := Arrow.leftFunc) (𝟙 _) (𝟙 _)

/-- Target projection of the category of squares from arrows of C to f onto J(B').
This is the standard comma-category map induced by the target functors.
Source: blueprint sk-prop-ind-heart-kernels-cokernels.md, definition of P_f and its projections
(blueprint: det-ind-heart-kernels-cokernels). -/
def indHeartSquareTarget {C : Type u} [Category.{v} C] {M : Type w} [Category.{t} M]
    (ι : C ⥤ M) {B B' : M} (f : B ⟶ B') :
    CostructuredArrow ι.mapArrow (Arrow.mk f) ⥤ CostructuredArrow ι B' :=
  CostructuredArrow.map₂ (F := Arrow.rightFunc) (G := Arrow.rightFunc) (𝟙 _) (𝟙 _)

/-- The canonical cocone of constructible squares at f, with legs the squares themselves.
Source: blueprint sk-prop-ind-heart-kernels-cokernels.md, f = colim v
(blueprint: det-ind-heart-kernels-cokernels). -/
def indHeartSquareCocone {C : Type u} [Category.{v} C] {M : Type w} [Category.{t} M]
    (ι : C ⥤ M) {B B' : M} (f : B ⟶ B') :
    Cocone (CostructuredArrow.proj ι.mapArrow (Arrow.mk f) ⋙ ι.mapArrow) :=
  (Functor.LeftExtension.mk (𝟭 (Arrow M)) ι.mapArrow.rightUnitor.inv).coconeAt
    (Arrow.mk f)

/-- All clauses for a fixed coefficient ring: P_f is essentially small and filtered,
its two projections are final, its canonical arrow cocone has colimit f, and applying
ker and coker gives colimit cocones at the ambient kernel and cokernel of f. Both
objects belong to the same replete filtered-colimit closure of constructible modules.
Smallness is relative to u+1, as in the canonical-presentation dependency; universal
properties on the full category are equivalent to those on any small skeleton.
Source: blueprint sk-prop-ind-heart-kernels-cokernels.md, entire statement
(blueprint: det-ind-heart-kernels-cokernels). -/
def IndHeartKernelsCokernelsAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) : Prop :=
  ∀ (B B' : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (f : B ⟶ B'),
    ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) B →
    ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) B' →
    EssentiallySmall.{u + 1} (CostructuredArrow
      (ObjectProperty.ι (IsConstantModelConstructible Λ X)).mapArrow (Arrow.mk f)) ∧
    IsFiltered (CostructuredArrow
      (ObjectProperty.ι (IsConstantModelConstructible Λ X)).mapArrow (Arrow.mk f)) ∧
    (indHeartSquareSource (ObjectProperty.ι (IsConstantModelConstructible Λ X)) f).Final ∧
    (indHeartSquareTarget (ObjectProperty.ι (IsConstantModelConstructible Λ X)) f).Final ∧
    Nonempty (IsColimit
      (indHeartSquareCocone (ObjectProperty.ι (IsConstantModelConstructible Λ X)) f)) ∧
    Nonempty (IsColimit (Functor.mapCocone (ker (C := _))
      (indHeartSquareCocone (ObjectProperty.ι (IsConstantModelConstructible Λ X)) f))) ∧
    Nonempty (IsColimit (Functor.mapCocone (coker (C := _))
      (indHeartSquareCocone (ObjectProperty.ι (IsConstantModelConstructible Λ X)) f))) ∧
    ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) (kernel f) ∧
    ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) (cokernel f)

/-- Kernels and cokernels in the ind-constructible heart, with the canonical filtered
presentation by constructible squares, for both canonical coefficient rings.
Source: blueprint sk-prop-ind-heart-kernels-cokernels.md and its proof, with the
standing setting in sk-def-sfb-dc-setting
(blueprint: det-ind-heart-kernels-cokernels).

Proof (the node's six steps):
1. By sk-def-sfb-pulled-back-coefficients the coefficient is a commutative ring object.
Use sk-def-sfb-module-objects and sk-def-sfb-sheaf-tensor, then
def-weil-pbc-internal-abelian-sheaf-module-equivalence and
lem-weil-pbc-ring-sheaves-grothendieck to obtain ambient abelianness, all small colimits
and exact filtered colimits. Transport across the equivalence by universal properties.
2. By sk-lem-coefficient-heart constructibles are essentially small and closed under
kernels and cokernels. Squares form an essentially small category: choose representatives
of their constructible vertices and use the sets of maps between them and to B and B'.
The zero square gives nonemptiness; direct sums give common successors. For parallel
pairs (a,b), (a',b'), take the constructible cokernels of a-a' and b-b'. Commutativity
makes v and both structure maps descend, providing an equalizing successor. These are
the filteredness conditions of def-weil-pbc-category-colimit.
3. For j=(C,c) in J(B), the square (C,C,id,c,fc) is initial in (j down source).
A comma object represented by u:C -> C_p receives the unique pair (u,v_p u).
Thus the source projection is final, directly from nonempty connected comma categories.
4. For j'=(D,d) in J(B'), the square (0,D,0,0,d) is initial in (j' down target).
The unique map to a comma object represented by u:D -> D_p is (0,u), proving finality.
5. By det-ind-heart-canonical-presentation the canonical J(B) and J(B') cocones are
colimits. Reindex along the two final projections. Explicitly restrict source cocones
to (C,C,id,c,fc) and target cocones to (0,D,0,0,d); the maps (id,v_p) and (0,id) show
these operations invert pullback of cocones. Hence the component cocones have vertices
B and B'. The square equations identify the resulting arrow with f on every source leg;
the component universal properties give the universal property in the arrow category.
6. Take the diagrams 0 -> ker(v) -> C -> im(v) -> 0 and
0 -> im(v) -> D -> coker(v) -> 0. Exact filtered colimits identify the kernel and
cokernel of f with the colimits of ker(v) and coker(v), respectively. The induced legs
are the canonical kernel and cokernel maps of each square, by their universal properties.
By sk-lem-coefficient-heart the individual kernels and cokernels are constructible;
by det-ind-heart-full-faithfulness(2) their small filtered colimits are ind-constructible. -/
theorem indHeart_kernelsCokernels
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (hp : 0 < p) (hne : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      IndHeartKernelsCokernelsAssertions (Profinite.continuousMapRingObj.{u} E) X) ∧
    IndHeartKernelsCokernelsAssertions (Profinite.padicAlgClRingObj.{u} ℓ) X := by
  sorry

end AlgebraicGeometry.ProEtale
