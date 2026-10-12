/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.AlgebraicGeometry.CompletionInternalHomQuotient
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import Sheaf.AlgebraicGeometry.CoherentSheafHom
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.Algebra.Module.FinitePresentation

/-! # Unique section lifts of compatible quotient morphisms

Source: Stacks Project, Cohomology of Schemes, Lemma 0882, proof.
(blueprint: lem-weil-pbc-completion-internal-hom-sections-lift).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Every compatible family of maps between the completed quotient terms has a
unique lift to compatible sections of the quotients of internal Hom. The maps e
are required to be the quotient factorizations of postcomposition.

Source: Stacks Project, Cohomology of Schemes, Lemma 0882, affine-local proof;
Lemma 087W, and Algebra, Lemmas 00MA and 00MB; More on Algebra, Lemma 087R.
(blueprint: lem-weil-pbc-completion-internal-hom-sections-lift).

Proof:
1. On an affine open U, put A = O_X(U), M = F(U), N = G(U), and J = I(U).
   A is Noetherian. Coherence and the affine tilde-sections adjunction identify
   F, G, and Hom(G,F) on U with the finite modules M, N, and H = Hom_A(N,M).
   Ideal products and quotient projections on affine sections are J^n-products
   and the corresponding module quotient projections. The equation he therefore
   identifies e_n(U) with h mod J^n H ↦ (x mod J^n N ↦ h(x) mod J^n M).
   Surjectivity of the source quotient and the unique factorization through
   G/J^n G determine this map; there is no choice of a different e_n.
2. The affine formal-module equivalence identifies compatible quotient morphisms
   with Hom over the completed ring A^ of N^ and M^. Compatible H/J^n H
   sections identify with H^. Their evaluation map is the completed-ring-linear
   map beta evaluating compatible representatives componentwise.
3. Completion of each finite module P = N, M, H is A^ tensor_A P. The completed
   ring is flat over A, and the finite A-module N is finitely presented, so flat
   base change identifies A^ tensor_A H with Hom_{A^}(A^ tensor_A N, A^ tensor_A M).
   Conjugating by the completion-tensor isomorphisms gives a bijection to
   Hom_{A^}(N^, M^). It equals beta: both maps are A^-linear and on each generator
   1 tensor h their values are the completed map h^, by tensor-completion
   naturality. Thus each compatible local morphism family has a unique section lift.
4. For a global family t, restrict it to every affine open and use step 3 to
   obtain local lifts. Evaluation commutes with restriction because e_n are
   sheaf morphisms. On affine subopens of intersections, uniqueness makes these
   lifts agree. Such subopens cover the intersections; the sheaf condition
   therefore glues each level to a global section s_n. Transition compatibility
   holds on the affine cover, hence globally, so s is a compatible section family.
   Evaluation agrees with t locally, hence globally. Finally, any two global
   lifts agree on every affine open by step 3 and thus agree at every level.
This proves existence and uniqueness, without claiming any e_n is an isomorphism. -/
theorem completion_internal_hom_sections_lift {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F G : CoherentModules X)
    (e : ∀ n : ℕᵒᵖ,
      formalModuleQuotient I (n.unop + 1) (SheafOfModules.homObj
        (R := X.toRingedSpace.sheaf) G.obj F.obj) ⟶
        SheafOfModules.homObj
          (R := X.toRingedSpace.sheaf) (formalModuleQuotient I (n.unop + 1) G.obj)
          (formalModuleQuotient I (n.unop + 1) F.obj))
    (he : ∀ n : ℕᵒᵖ,
        formalModuleQuotientπ I (n.unop + 1) (SheafOfModules.homObj
          (R := X.toRingedSpace.sheaf) G.obj F.obj) ≫
          e n ≫ SheafOfModules.homObjMap
            (R := X.toRingedSpace.sheaf) (formalModuleQuotientπ I (n.unop + 1) G.obj)
            (𝟙 (formalModuleQuotient I (n.unop + 1) F.obj)) =
        SheafOfModules.homObjMap
          (R := X.toRingedSpace.sheaf) (𝟙 G.obj) (formalModuleQuotientπ I (n.unop + 1) F.obj))
    (t : ∀ n : ℕᵒᵖ, formalModuleQuotient I (n.unop + 1) G.obj ⟶
      formalModuleQuotient I (n.unop + 1) F.obj)
    (ht : ∀ (a b : ℕᵒᵖ) (f : a ⟶ b),
      t a ≫ (formalCompletionSystem I F.obj).map f =
        (formalCompletionSystem I G.obj).map f ≫ t b) :
    ∃! s : {s : ∀ n : ℕᵒᵖ,
          (formalModuleQuotient I (n.unop + 1) (SheafOfModules.homObj
            (R := X.toRingedSpace.sheaf) G.obj F.obj)).sections //
          ∀ (a b : ℕᵒᵖ) (f : a ⟶ b),
            SheafOfModules.sectionsMap
              ((formalCompletionSystem I (SheafOfModules.homObj
                (R := X.toRingedSpace.sheaf) G.obj F.obj)).map f)
              (s a) = s b}, ∀ n : ℕᵒᵖ,
      SheafOfModules.homObjSectionsEquiv (R := X.toRingedSpace.sheaf)
        (formalModuleQuotient I (n.unop + 1) G.obj)
        (formalModuleQuotient I (n.unop + 1) F.obj)
        (SheafOfModules.sectionsMap (e n) (s.val n)) = t n := by
  sorry

end AlgebraicGeometry
