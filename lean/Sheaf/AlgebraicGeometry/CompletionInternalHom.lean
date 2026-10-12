/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import Sheaf.AlgebraicGeometry.CoherentSheafHom
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

/-! # Internal Hom and coherent formal completion

Source: Stacks Project, Cohomology of Schemes, Lemma 30.23.5, Tag 0882
(blueprint: lem-weil-pbc-completion-internal-hom).

The inverse limit is written as compatible families of global sections. The existential
maps are specified by quotient factorization and by their components, so the bijection
is the canonical map in the node, rather than an unspecified equivalence of sets.
As in `formalCompletionSystem`, `op n` denotes the positive level `n + 1`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical map from completed global internal Hom to morphisms of completions is
bijective. The first two clauses express annihilation and unique local factorization.
The maps `e` factor postcomposition with the quotient projection through both quotients;
the next clause expresses compatibility with every transition. Finally `Φ` has components
obtained by taking sections of `e` and the global internal-Hom identification.

Source: Stacks Project, Cohomology of Schemes, Lemma 30.23.5, Tag 0882
(blueprint: lem-weil-pbc-completion-internal-hom).

Proof (the node's five steps):
1. Ideal products are locally sums of products of ideal sections with module sections
   (def-weil-pbc-coherent-formal-module, def-pur-sheaf-tensor-product). Since I^n kills
   F/I^n F, every local map G → F/I^n F kills I^n G. Postcomposition with the quotient
   kills I^n Hom(G,F), giving e_n by the two cokernel properties. Restriction and reduction
   commute with these factorizations by uniqueness; this defines Φ on compatible families.
2. On an affine open U = Spec A, A is Noetherian (pqf-lem-affine-open-locnoeth).
   Coherent F and G correspond to finite modules M and N, and Hom(G,F) to Hom_A(N,M),
   by lem-weil-pbc-affine-tilde-gamma-adjunction, pqf-lem-coherent-ft-locnoeth,
   lem-weil-pbc-quasi-coherent-finite-type-affine and
   lem-weil-pbc-coherent-sheaf-hom-coherent. Quotients and their maps on affine sections
   are module quotients (lem-weil-pbc-ideal-times-quasi-coherent-affine-sections).
3. The equivalence lem-weil-pbc-coherent-formal-modules-affine identifies Φ_U with the
   map Hom_A(N,M)^ → Hom_{A^}(N^,M^) evaluating compatible reductions componentwise.
4. Completion of finite modules equals tensoring with A^ (three applications of
   lem-weil-pbc-completion-finite-module-tensor). A^ is flat over A
   (lem-weil-pbc-noetherian-completion-flat), so flat base change commutes with Hom from N
   (lem-weil-pbc-flat-base-change-hom-finitely-presented). These identifications agree
   with the specified map on generators 1 ⊗ h by naturality, hence Φ_U is bijective.
5. The affine opens form a basis. Injectivity holds by restriction to this basis.
   Local inverse images of any compatible morphism agree on affine subopens of overlaps
   by local injectivity, so glue at every level to global sections. Their compatibility
   and the required equality of morphisms hold locally and hence globally by the sheaf
   condition (def-weil-sheaf-of-modules-category, def-pur-sheaf-hom). -/
theorem completion_internal_hom_bijective {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F G : CoherentModules X) :
    (∀ n : ℕ,
      Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι (n + 1)).2
          (SheafOfModules.homObj (R := X.toRingedSpace.sheaf) G.obj F.obj) ≫
        SheafOfModules.homObjMap
          (R := X.toRingedSpace.sheaf) (𝟙 G.obj) (formalModuleQuotientπ I (n + 1) F.obj) = 0) ∧
    (∀ n : ℕ, IsIso (SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf)
      (formalModuleQuotientπ I (n + 1) G.obj)
      (𝟙 (formalModuleQuotient I (n + 1) F.obj)))) ∧
    ∃ e : ∀ n : ℕᵒᵖ,
      formalModuleQuotient I (n.unop + 1) (SheafOfModules.homObj
        (R := X.toRingedSpace.sheaf) G.obj F.obj) ⟶
        SheafOfModules.homObj
          (R := X.toRingedSpace.sheaf) (formalModuleQuotient I (n.unop + 1) G.obj)
          (formalModuleQuotient I (n.unop + 1) F.obj),
      (∀ n : ℕᵒᵖ,
        formalModuleQuotientπ I (n.unop + 1) (SheafOfModules.homObj
          (R := X.toRingedSpace.sheaf) G.obj F.obj) ≫
          e n ≫ SheafOfModules.homObjMap
            (R := X.toRingedSpace.sheaf) (formalModuleQuotientπ I (n.unop + 1) G.obj)
            (𝟙 (formalModuleQuotient I (n.unop + 1) F.obj)) =
        SheafOfModules.homObjMap
          (R := X.toRingedSpace.sheaf) (𝟙 G.obj) (formalModuleQuotientπ I (n.unop + 1) F.obj)) ∧
      (∀ (a b : ℕᵒᵖ) (f : a ⟶ b),
        e a ≫ SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf)
          (𝟙 (formalModuleQuotient I (a.unop + 1) G.obj))
          ((formalCompletionSystem I F.obj).map f) =
        (formalCompletionSystem I (SheafOfModules.homObj
          (R := X.toRingedSpace.sheaf) G.obj F.obj)).map f ≫
          e b ≫ SheafOfModules.homObjMap
            (R := X.toRingedSpace.sheaf) ((formalCompletionSystem I G.obj).map f)
            (𝟙 (formalModuleQuotient I (b.unop + 1) F.obj))) ∧
      ∃ Φ : {s : ∀ n : ℕᵒᵖ,
          (formalModuleQuotient I (n.unop + 1) (SheafOfModules.homObj
            (R := X.toRingedSpace.sheaf) G.obj F.obj)).sections //
          ∀ (a b : ℕᵒᵖ) (f : a ⟶ b),
            SheafOfModules.sectionsMap
              ((formalCompletionSystem I (SheafOfModules.homObj
                (R := X.toRingedSpace.sheaf) G.obj F.obj)).map f)
              (s a) = s b} → ((completion X I).obj G ⟶ (completion X I).obj F),
        (∀ s n, (Φ s).hom.app n =
          SheafOfModules.homObjSectionsEquiv (R := X.toRingedSpace.sheaf)
            (formalModuleQuotient I (n.unop + 1) G.obj)
            (formalModuleQuotient I (n.unop + 1) F.obj)
            (SheafOfModules.sectionsMap (e n) (s.val n))) ∧
        Function.Bijective Φ := by
  sorry

end AlgebraicGeometry
