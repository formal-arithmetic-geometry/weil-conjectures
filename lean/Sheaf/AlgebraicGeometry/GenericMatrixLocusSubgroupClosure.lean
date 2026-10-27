/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Sheaf.AlgebraicGeometry.LinearGroupSchemes
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Generic matrix-group laws extend to the scheme-theoretic closure

Source: Milne, Algebraic Groups (2017), Section 1c, Lemma 1.40 and Theorem 1.45,
printed pp. 18–19; the agent generalization and coordinate-kernel proof in the DAG.
(blueprint: lem-sfb-generic-matrix-locus-subgroup-closure)

The auxiliary definitions give the actual kernel quotient and its canonical map to G.
GL(E) is expressed in coordinates on a basis of E, with index Fin(finrank F E) lifted
to the field universe. This index is empty for E = 0, covering GL(0) = 1.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj
open scoped TensorProduct

namespace AlgebraicGeometry
namespace GenericMatrixLocus

variable {F : Type u} [Field F] {A : Type u} [CommRing A] [Algebra F A]
  {G : Over (Spec (.of F))}

/-- The coordinate map B → A, with Γ(Spec A) identified canonically with A.
Source: Milne, Section 1c, Lemma 1.40 and Theorem 1.45, coordinate-kernel generalization.
(blueprint: lem-sfb-generic-matrix-locus-subgroup-closure) -/
noncomputable def coordinates (j : (Spec (.of A)).asOver (Spec (.of F)) ⟶ G) :
    Γ(G.left, ⊤) ⟶ CommRingCat.of A :=
  j.left.appTop ≫ (Scheme.ΓSpecIso (.of A)).hom

/-- The closed subscheme Spec(B/ker(j*)) in the coordinate presentation of G.
Source: Milne, Section 1c, Lemma 1.40 and Theorem 1.45, coordinate-kernel generalization.
(blueprint: lem-sfb-generic-matrix-locus-subgroup-closure) -/
noncomputable def closure (j : (Spec (.of A)).asOver (Spec (.of F)) ⟶ G) : Scheme.{u} :=
  Spec (.of (Γ(G.left, ⊤) ⧸ RingHom.ker (coordinates j).hom))

/-- The quotient map on coordinates followed by the canonical affine identification of G.
Source: Milne, Section 1c, Lemma 1.40 and Theorem 1.45, coordinate-kernel generalization.
(blueprint: lem-sfb-generic-matrix-locus-subgroup-closure) -/
noncomputable def inclusion [IsAffine G.left]
    (j : (Spec (.of A)).asOver (Spec (.of F)) ⟶ G) : closure j ⟶ G.left :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker (coordinates j).hom))) ≫
    G.left.isoSpec.inv

/-- Spec(B/ker(j*)) as an F-scheme through its specified inclusion into G.
Source: Milne, Section 1c, Lemma 1.40 and Theorem 1.45, coordinate-kernel generalization.
(blueprint: lem-sfb-generic-matrix-locus-subgroup-closure) -/
noncomputable def closureOver [IsAffine G.left]
    (j : (Spec (.of A)).asOver (Spec (.of F)) ⟶ G) : Over (Spec (.of F)) :=
  Over.mk (inclusion j ≫ G.hom)

/-- Generic multiplication and inverse make the kernel quotient a closed subgroup scheme.
Source: Milne, Algebraic Groups (2017), Section 1c, Lemma 1.40 and Theorem 1.45,
printed pp. 18–19; agent generalization to generic laws on an affine locus.
(blueprint: lem-sfb-generic-matrix-locus-subgroup-closure)

Proof plan:
1. Set B = Γ(G), I = ker(j*), D = B/I. The quotient universal property
   (def-weil-pbc-algebra-hom-quotient) gives an injection p : D → A. The given group
   operations induce the Hopf maps on B (lem-sfb-affine-group-coordinate-hopf).
   Identify C × C with Spec(A ⊗ A) (lem-weil-pbc-fibre-product-affine-spectra).
2. The hypothesis at L = F makes A a nonzero domain. Tensor A → Frac(A) with A;
   vector spaces are flat (lem-weil-pbc-module-over-field-flat), so tensoring preserves
   injections (lem-trf-flat-tensor-preserves-injection). The target A ⊗ Frac(A) is a
   domain by the hypothesis at L = Frac(A); therefore A ⊗ A is a domain. Hence C and
   C × C are integral (def-pc-integral-scheme).
3. Tensor the injection p twice to see that p ⊗ p is injective, using the same flatness
   inputs. For b in I, the pullback of its comultiplication vanishes on V by hm.
   Choose a point of V and use injectivity of germs on an integral scheme
   (lem-sc-integral-scheme-stalks-in-function-field) to obtain global vanishing.
   Injectivity of p ⊗ p shows that (q ⊗ q)Δ kills I.
4. On W, hi similarly shows that the antipode preserves I, by germ injectivity.
   The point c₀ and hc₀ show that the counit kills I.
5. Descend the three coordinate maps through the quotient using
   def-weil-pbc-algebra-hom-quotient. By def-weil-affine-spectrum and the affine product
   identification they define operations on closure j. The quotient inclusion is a
   closed immersion (def-weil-closed-immersion).
6. On every test algebra, precomposition with B → D is injective and its image is
   closed under all three operations of G. All group identities are inherited from G,
   so these operations give GrpObj and IsClosedSubgroupScheme, as in def-sc-group-scheme
   and def-sc-group-scheme-subgroup; nonreduced test algebras are included.
7. The coordinate map factors through D. For every closed subscheme Spec(B/J) of G,
   j factors through it exactly when J ≤ I, giving a unique comparison from Spec D.
   Thus this is precisely the scheme-theoretic image (def-nagata-scheme-theoretic-image,
   lemma-nagata-scheme-theoretic-closure-minimal; Stacks Tags 01R7 and 01R8).
-/
theorem isClosedSubgroupScheme_closure
    (E : Type u) [AddCommGroup E] [Module F E] [FiniteDimensional F E]
    (G : Over (Spec (.of F))) [GrpObj G] [IsAffine G.left]
    [LocallyOfFiniteType G.hom]
    (embedding : G ⟶
      GeneralLinearGroup (LinearGroupSchemes.Index.{u} (Module.finrank F E)) F)
    [IsClosedSubgroupScheme embedding]
    [Algebra.FiniteType F A]
    (hgeom : ∀ (L : Type u) [Field L] [Algebra F L], IsDomain (A ⊗[F] L))
    (j : (Spec (.of A)).asOver (Spec (.of F)) ⟶ G)
    [IsImmersion j.left] [QuasiCompact j.left]
    (c₀ : 𝟙_ (Over (Spec (.of F))) ⟶ (Spec (.of A)).asOver (Spec (.of F)))
    (hc₀ : c₀ ≫ j = η[G])
    (V : (((Spec (.of A)).asOver (Spec (.of F))) ⊗
      ((Spec (.of A)).asOver (Spec (.of F)))).left.Opens)
    (W : (Spec (.of A)).Opens) (hV : Nonempty V) (hW : Nonempty W)
    (m₀ : V.toScheme ⟶ Spec (.of A)) (i₀ : W.toScheme ⟶ Spec (.of A))
    (hm : m₀ ≫ j.left = V.ι ≫ (j ⊗ₘ j).left ≫ μ[G].left)
    (hi : i₀ ≫ j.left = W.ι ≫ j.left ≫ ι[G].left) :
    (∃ _ : GrpObj (closureOver j),
      IsClosedSubgroupScheme (Over.homMk (inclusion j) : closureOver j ⟶ G)) ∧
    ∃ e : closure j ≅ j.left.image, e.hom ≫ j.left.imageι = inclusion j := by
  sorry

end GenericMatrixLocus
end AlgebraicGeometry
