/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# The canonical extension-by-zero generator epimorphism

Source: Stacks Project, Modules on Sites, Lemma 18.28.8, Tag 03EW, clause (3)
(blueprint: lem-pc-sites-modules-quotient-j-shriek).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- On a small ringed site, the coproduct of `j_{U!} R_U`, indexed by all pairs
`(U,s)` with `s ∈ M(U)`, exists and its canonical section-evaluation map is epic.
Here the free Yoneda presheaf is `V ↦ ⨁ (V ⟶ U), R(V)`, and its sheafification
is `j_{U!} R_U`. The component map is the sheafification of the free Yoneda
map corresponding to `s`, followed by the sheafification counit.

Source: Stacks Project, Lemma 18.28.8 (03EW), clause (3)
(blueprint: lem-pc-sites-modules-quotient-j-shriek).

Proof: Mathlib's canonical coproduct of free Yoneda presheaves has a sectionwise
surjective evaluation map to `M.val`: the identity generator in the `(U,s)` summand
maps to `s`. Apply module sheafification to this coproduct and its evaluation map.
As a left adjoint, sheafification preserves both the coproduct and epimorphisms.
Compose the sheafified evaluation map with the sheafification counit at `M`,
which is an isomorphism. The component equations follow by functoriality from
the component equations of the presheaf evaluation map. This is the sheafification
alternative in the proof of Stacks Project, Tag 03EW, clause (3). -/
theorem exists_epi_coproduct_jShriek
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J RingCat.{u})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (M : SheafOfModules.{u} R) :
    ∃ (c : Cofan (fun m : M.val.Elements =>
        (PresheafOfModules.sheafification (𝟙 R.obj)).obj m.freeYoneda))
      (_hc : IsColimit c) (q : c.pt ⟶ M),
      Epi q ∧ ∀ m : M.val.Elements,
        c.inj m ≫ q =
          (PresheafOfModules.sheafification (𝟙 R.obj)).map m.fromFreeYoneda ≫
            (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app M := by
  let L := PresheafOfModules.sheafification (𝟙 R.obj)
  let c := Cofan.mk (L.obj M.val.freeYonedaCoproduct)
    (fun m : M.val.Elements => L.map (M.val.ιFreeYonedaCoproduct m))
  refine ⟨c, ?_, L.map M.val.fromFreeYonedaCoproduct ≫
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app M, ?_, ?_⟩
  · exact isColimitOfHasCoproductOfPreservesColimit L _
  · infer_instance
  · intro m
    change L.map (M.val.ιFreeYonedaCoproduct m) ≫
      (L.map M.val.fromFreeYonedaCoproduct ≫ _) = _
    rw [← Category.assoc, ← L.map_comp, M.val.ι_fromFreeYonedaCoproduct m]

end SheafOfModules
