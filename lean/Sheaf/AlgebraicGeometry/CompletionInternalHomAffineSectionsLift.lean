/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
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

/-! # Affine comparison for completed internal Hom

Source: Stacks Project, Cohomology of Schemes, Lemma 0882, affine-local argument.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A compatible quotient morphism family has a unique compatible lift on each affine open.

Source: Stacks Project, Cohomology of Schemes, Lemma 0882, affine-local proof;
Lemma 087W; Algebra, Lemmas 00MA and 00MB; More on Algebra, Lemma 087R.
(blueprint: lem-weil-pbc-completion-internal-hom-affine-sections-lift).

Proof:
1. For the affine open U put A = O_X(U), J = I(U), N = G(U), M = F(U),
   H = Hom_A(N,M). The ring A is Noetherian and N, M, H are finite. The affine
   tilde-sections adjunction, coherence of internal Hom, and the affine ideal-product
   and quotient comparison identify the source at level n with H/J^(n+1)H.
   The quotient projections on affine sections are surjective. The factorization
   equation he therefore identifies e_n(U) with canonical evaluation of quotient
   linear maps, using unique factorization through the quotient of G.
2. The affine formal-module equivalence identifies compatible quotient morphisms
   with Hom over the completed ring A^ from N^ to M^. Compatible sections of the
   source identify with H^. Their evaluation is the A^-linear componentwise map
   beta : H^ -> Hom_{A^}(N^,M^).
3. Completion of each finite module P is A^ tensor_A P. Flatness of A^ over A and
   finite presentation of N identify A^ tensor_A H with
   Hom_{A^}(A^ tensor_A N, A^ tensor_A M). Conjugate by the natural completion-tensor
   equivalences. The resulting bijection agrees with beta: both are A^-linear and
   on 1 tensor h both are the completed map h^, by completion-tensor naturality.
   Apply this bijection to the family t restricted to U. Its inverse gives the
   local section family, including transition compatibility. Injectivity gives
   uniqueness of the entire compatible family; no finite-level e_n is asserted
   to be an isomorphism. -/
theorem completion_internal_hom_affine_sections_lift {X : Scheme.{u}} [IsNoetherian X]
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
        (formalCompletionSystem I G.obj).map f ≫ t b)
    (U : X.affineOpens) :
    ∃! s : {s : ∀ n : ℕᵒᵖ,
          (formalModuleQuotient I (n.unop + 1) (SheafOfModules.homObj
            (R := X.toRingedSpace.sheaf) G.obj F.obj)).val.obj (op U.val) //
          ∀ (a b : ℕᵒᵖ) (f : a ⟶ b),
            ((formalCompletionSystem I (SheafOfModules.homObj
              (R := X.toRingedSpace.sheaf) G.obj F.obj)).map f).val.app (op U.val)
              (s a) = s b}, ∀ n : ℕᵒᵖ,
      (e n).val.app (op U.val) (s.val n) =
        ((SheafOfModules.homObjSectionsEquiv (R := X.toRingedSpace.sheaf)
          (formalModuleQuotient I (n.unop + 1) G.obj)
          (formalModuleQuotient I (n.unop + 1) F.obj)).symm (t n)).val (op U.val) := by
  sorry

end AlgebraicGeometry
