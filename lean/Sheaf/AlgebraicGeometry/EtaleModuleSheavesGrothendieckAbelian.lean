/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Grothendieck abelianness of constant-coefficient etale module sheaves

Source: Stacks Project, Modules on Sites, Tags 03DA, 03DB, 03DI and 03EW;
Topologies, Tags 021A, 021B and 04HR
(blueprint: lem-weil-pbc-module-sheaves-grothendieck-abelian).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The module sheaves over the constant ring sheaf on the small etale site are
Grothendieck abelian. A small family of affine etale objects covers every object,
and the coproduct of the sheafified free Yoneda modules for this family is a generator.
The free module on `uliftYoneda U` has sections the direct sum of copies of `R(V)`
indexed by `V ⟶ U`; `ULift` only adjusts universes. Its sheafification is `j_{U!} R_U`.
The constant ring sheaf `Λ_T` is the `constantSheaf` of `ULift Λ`, written out in place.
The last conjunct states the abelian-sheaf case, with integer coefficients.

Source: Stacks Project, Tags 03DA, 03DB, 03DI, 03EW, 021B and 04HR
(blueprint: lem-weil-pbc-module-sheaves-grothendieck-abelian).

Proof:
1. Kernels are sectionwise and cokernels are sheafified sectionwise cokernels (03DA),
   using `def-weil-sheaf-of-modules-category`. The forgetful functor to abelian sheaves
   is faithful and exact by `lem-weil-pbc-module-sheaves-colimits-forgetful` (1).
2. Sheafify sectionwise colimits, using that lemma's (2) and (3), to obtain all small
   colimits and their preservation by the forgetful functor (03DB).
3. For a filtered diagram of short exact sequences, colimits preserve cokernels.
   The forgotten colimit of the first maps is mono by
   `lem-weil-pbc-abelian-etale-sheaves-grothendieck`; faithfulness reflects monos.
   Thus filtered colimits are exact.
4. Choose affine etale representatives forming a covering family for every object by
   `lem-weil-pbc-affine-etale-essentially-small-cover`. Sheafify the free Yoneda
   module (03DI); sheafification adjunction and
   `lem-weil-pbc-free-yoneda-presheaf-module` identify maps from it to F with F(U).
   This identification is natural and additive, so zero sections give zero maps.
5. A nonzero difference of sheaf morphisms is nonzero on a section over some V.
   Sheaf separatedness on an affine cover detects a nonzero restriction over U.
   The corresponding map from the free sheaf at U detects the difference. Extend it
   by zero on the other summands to a map from the coproduct. The coproduct therefore
   separates morphisms and is a generator (03EW).
6. These properties give `def-sp-grothendieck-abelian`. For integer coefficients,
   abelian sheaves have their unique integer-module structure; alternatively apply
   `lem-weil-pbc-abelian-etale-sheaves-grothendieck` directly. -/
theorem etaleModuleSheaves_grothendieckAbelian (T : Scheme.{u})
    (Λ : Type u) [CommRing Λ] :
    IsGrothendieckAbelian.{u + 1} (SheafOfModules.{u + 1}
      ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1, u} Λ)))) ∧
      (∃ (I : Type (u + 1)) (U : I → T.Etale),
        (∀ i : I, IsAffine (U i).left) ∧
        (∀ V : T.Etale, ∃ (K : Type (u + 1)) (i : K → I)
          (f : ∀ k : K, U (i k) ⟶ V),
          Sieve.ofArrows (fun k : K ↦ U (i k)) f ∈ T.smallEtaleTopology V) ∧
        ∃ c : Cofan (fun i : I ↦
          (PresheafOfModules.sheafification.{u + 1}
            (𝟙 ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
              (RingCat.of (ULift.{u + 1, u} Λ))).obj)).obj
            ((PresheafOfModules.free ((constantSheaf T.smallEtaleTopology RingCat.{u + 1}).obj
              (RingCat.of (ULift.{u + 1, u} Λ))).obj).obj (uliftYoneda.{u + 1}.obj (U i)))),
          Nonempty (IsColimit c) ∧ IsSeparator c.pt) ∧
      IsGrothendieckAbelian.{u + 1} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  sorry

end AlgebraicGeometry.Scheme
