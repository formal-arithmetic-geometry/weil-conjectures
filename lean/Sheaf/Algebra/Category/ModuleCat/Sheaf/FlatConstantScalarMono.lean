/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O4
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Regular constant scalars on flat module sheaves

Source: Stacks Project, Modules on Sites, Tags 03EI, 03ER(3), 03EK and 03DA
(blueprint: lem-sfb-flat-constant-module-scalar-mono).
-/

@[expose] public section

set_option autoImplicit false

universe uC vC r m

open CategoryTheory Opposite

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A regular scalar of a commutative ring acts injectively on sections of its constant
ring sheaf and of every flat module sheaf over that ring sheaf. Sectionwise injectivity
is the monomorphism condition, since kernels of module sheaves are computed sectionwise.
Source: Stacks Project, Tags 03EI, 03ER(3), 03EK and 03DA
(blueprint: lem-sfb-flat-constant-module-scalar-mono).

Proof:
1. Let O be the constant ring presheaf A and P its regular module presheaf. Multiplication
by a has zero kernel on P. Exact abelian sheafification preserves this zero kernel
[lem-weil-pbc-sheafification-exact]. The module sheafification interface
[lem-pc-sites-module-sheafification-interface] gives P# its unique O#-action. Identify P#
with R = O#: the extension of O → R and the map r ↦ r · η(1) are inverse, since one
composite is the identity by evaluation on 1 and the other by uniqueness of extension.
The sheafified endomorphism agrees with multiplication by the constant section η(a),
by that same uniqueness. It is therefore monic on R.
2. Construct R ⊗_R M ≅ M on presheaf tensors by r ⊗ m ↦ r · m, with inverse
m ↦ 1 ⊗ m. Balancing gives 1 ⊗ (r · m) = r ⊗ m. These maps commute with restrictions,
so sheafification gives the tensor-unit isomorphism [def-pur-sheaf-tensor-product].
3. Flatness [def-pc-flat-sheaf-modules] says the right tensor functor with M is exact.
Apply monomorphism preservation [lem-sp-exact-functor-preserves-homology] to the scalar
endomorphism on R. Conjugation by the tensor-unit isomorphism identifies its tensor
with multiplication by a on M, since (a · r) ⊗ m maps to a · (r · m).
4. Kernels in the module-sheaf category [def-weil-sheaf-of-modules-category] are
sectionwise. Thus both scalar maps are injective on every U: a · s = a · t makes
s - t belong to their zero kernels. Conversely sectionwise injectivity implies
cancellation of morphisms componentwise. No domain or enough-points assumption is used. -/
theorem constantScalar_injective_of_flat
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J CommRingCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{max r m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}]
    (A : Type r) [CommRing A]
    (M : ringedSiteModules.{max r m}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        ((constantSheaf J CommRingCat.{r}).obj (CommRingCat.of A))))
    (hM : IsFlatOnSite M) (a : A) (ha : Function.Injective (fun x : A ↦ a * x)) :
    ∀ U : C,
      Function.Injective (fun s :
          (sheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).obj (op U) ↦
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app (op U)) a * s) ∧
      Function.Injective (fun s : M.val.obj (op U) ↦
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app (op U)) a • s) :=
  sorry

end SheafOfModules
