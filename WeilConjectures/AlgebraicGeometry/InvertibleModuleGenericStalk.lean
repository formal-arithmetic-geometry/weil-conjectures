/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.LinearAlgebra.Dimension.Free
import WeilConjectures.AlgebraicGeometry.Modules.IntegralSections
import WeilConjectures.AlgebraicGeometry.InvertibleStalkLinearEquiv
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Invertible modules and their generic stalk

Source: Stacks Project, Divisors, Tags 01X5 (2) and 02OZ (1)
(blueprint: lem-sc-invertible-module-generic-stalk).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

private theorem invertible_germ_injective {X : Scheme.{u}} [IsIntegral X]
    (L : X.Modules) [L.IsInvertible] (U : X.Opens) (x : X) (hx : x ∈ U) :
    Function.Injective (L.presheaf.germ U x hx) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  obtain ⟨W, hxW, i, j, he⟩ := L.presheaf.germ_eq x hx hx s 0
    (hs.trans (map_zero _).symm)
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  exact eq_zero_of_presheaf_map_eq_zero L (leOfHom i) s (he.trans (map_zero _))

private theorem invertible_specializes_injective {X : Scheme.{u}} [IsIntegral X]
    (L : X.Modules) [L.IsInvertible] (x : X) :
    Function.Injective (L.presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes (Set.mem_univ x))) := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  obtain ⟨U, hx, s, rfl⟩ := L.presheaf.exists_germ_eq m
  have hs : L.presheaf.germ U (genericPoint X)
      (((genericPoint_spec X).specializes (Set.mem_univ x)).mem_open U.isOpen hx) s = 0 := by
    simpa only [← ConcreteCategory.comp_apply, L.presheaf.germ_stalkSpecializes] using hm
  have hs0 := (invertible_germ_injective L U (genericPoint X) _) (hs.trans (map_zero _).symm)
  rw [hs0, map_zero]

private theorem invertible_specializes_smul {X : Scheme.{u}} [IsIntegral X]
    (L : X.Modules) (x : X) (a : X.presheaf.stalk x) (m : L.presheaf.stalk x) :
    L.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ x))
      (a • m) = algebraMap (X.presheaf.stalk x) X.functionField a •
      L.presheaf.stalkSpecializes ((genericPoint_spec X).specializes (Set.mem_univ x)) m := by
  obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨V, hxV, m, rfl⟩ := L.presheaf.exists_germ_eq m
  have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx a,
    ← L.presheaf.germ_res_apply (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx m]
  have : Nonempty (U ⊓ V : X.Opens) := ⟨⟨x, hx⟩⟩
  let r : Γ(X, U ⊓ V) := X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op a
  let n : Γ(L, U ⊓ V) := L.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op m
  let f := TopCat.Presheaf.stalkSpecializes L.val.presheaf
    ((genericPoint_spec X).specializes (Set.mem_univ x))
  have hg (t : Γ(L, U ⊓ V)) :
      f (TopCat.Presheaf.germ L.val.presheaf (U ⊓ V) x hx t) =
        TopCat.Presheaf.germ L.val.presheaf (U ⊓ V) (genericPoint X)
          (((genericPoint_spec X).specializes (Set.mem_univ x)).mem_open
            (U ⊓ V).isOpen hx) t :=
    ConcreteCategory.congr_hom (TopCat.Presheaf.germ_stalkSpecializes _ hx _) t
  calc
    _ = f (TopCat.Presheaf.germ L.val.presheaf (U ⊓ V) x hx (r • n)) :=
      congrArg f (germ_smul L x hx r n).symm
    _ = _ := hg (r • n)
    _ = _ := germ_smul L (genericPoint X) _ r n
    _ = _ := congrArg₂ (fun (c : X.functionField)
        (t : ↑(TopCat.Presheaf.stalk L.val.presheaf (genericPoint X))) ↦ c • t)
      (Scheme.algebraMap_germ_eq_germToFunctionField X hx r).symm (hg n).symm

/-- An invertible module on an integral scheme embeds into its generic stalk; sections on
any nonempty open are precisely the generic germs lying in all its stalk images.
Source: Stacks Project, Divisors, Tags 01X5 (2) and 02OZ (1)
(blueprint: lem-sc-invertible-module-generic-stalk).

Proof:
1. Local trivializations from `def-sc-invertible-module` identify the module with the
structure sheaf on a neighborhood of each point. Every nonempty open contains the generic
point (`def-sc-generic-point`), so these neighborhoods all contain it.
2. The germ description in `def-weil-pbc-module-stalk` makes specialization well defined:
equal germs agree on a smaller neighborhood, which still contains the generic point.
The map is semilinear over the structure-sheaf specialization and commutes with germs.
3. A trivialization induces mutually inverse linear maps on stalks, commuting with these
specialization maps and with germs of sections.
4. Thus every stalk has a singleton basis. At the generic point the scalar ring is the
field from `def-sc-function-field`, giving dimension one.
5. Under the trivialization, specialization is the injective structure-sheaf map from
`lem-sc-integral-scheme-stalks-in-function-field`. A generator corresponds to a unit,
whose nonzero image is a basis over the function field; semilinearity gives the image formula.
6. A section with zero generic germ has zero germ at every point by step 5. It vanishes by
`lem-weil-pbc-sheaf-sections-determined-by-germs`, giving injectivity on sections.
7. Every section's generic germ belongs to each stalk image by compatibility of germs.
8. Conversely, trivialize on neighborhoods inside the given open. A generic element in all
stalk images corresponds there to a function in every local ring, hence to a section by
`lem-sc-function-field-sections-glue`; transport back through the trivialization.
9. These local sections have the same generic germ, so step 6 makes them agree on overlaps.
The sheaf equalizer condition (`def-weil-pbc-sites-and-cohomology`,
`def-weil-sheaf-of-modules-category`) glues them to the desired section. -/
theorem invertible_module_generic_stalk (X : Scheme.{u}) [IsIntegral X]
    (L : X.Modules) [L.IsInvertible] :
    let η := genericPoint X
    let lam := fun x : X ↦
      TopCat.Presheaf.stalkSpecializes L.val.presheaf
        ((genericPoint_spec X).specializes (Set.mem_univ x))
    let ρ := fun x : X ↦ algebraMap (X.presheaf.stalk x) X.functionField
    (∀ x : X, Nonempty (Module.Basis PUnit.{u + 1} (X.presheaf.stalk x)
      ↑(TopCat.Presheaf.stalk L.val.presheaf x))) ∧
    Module.rank X.functionField ↑(TopCat.Presheaf.stalk L.val.presheaf η) = 1 ∧
    (∀ x : X, Function.Injective (lam x) ∧
      ∀ e : ↑(TopCat.Presheaf.stalk L.val.presheaf x), Submodule.span (X.presheaf.stalk x) {e} = ⊤ →
        (∃ b : Module.Basis PUnit.{u + 1} X.functionField ↑(TopCat.Presheaf.stalk L.val.presheaf η),
          b PUnit.unit.{u + 1} = lam x e) ∧
        Set.range (lam x) = {τ : ↑(TopCat.Presheaf.stalk L.val.presheaf η) |
          ∃ a : X.presheaf.stalk x, τ = ρ x a • lam x e}) ∧
    (∀ (U : X.Opens) (hU : Nonempty U),
      let hη := ((genericPoint_spec X).specializes (Set.mem_univ hU.some.val)).mem_open
        U.isOpen hU.some.property
      let lamU := TopCat.Presheaf.germ L.val.presheaf U η hη
      Function.Injective lamU ∧
        Set.range lamU = {τ : ↑(TopCat.Presheaf.stalk L.val.presheaf η) |
          ∀ x : X, x ∈ U → τ ∈ Set.range (lam x)}) := by
  classical
  dsimp only
  have hb (x : X) : Nonempty (Module.Basis PUnit.{u + 1} (X.presheaf.stalk x)
      ↑(L.presheaf.stalk x)) := by
    obtain ⟨e⟩ := invertible_stalk_linearEquiv X L x
    exact ⟨(Module.Basis.singleton PUnit.{u + 1} (X.presheaf.stalk x)).map e.symm⟩
  have hr : Module.rank X.functionField ↑(L.presheaf.stalk (genericPoint X)) = 1 := by
    obtain ⟨e⟩ := invertible_stalk_linearEquiv X L (genericPoint X)
    exact Module.nonempty_linearEquiv_iff_rank_eq_one.mp ⟨e.symm⟩
  refine ⟨hb, hr, ?_, ?_⟩
  · intro x
    refine ⟨invertible_specializes_injective L x, ?_⟩
    intro e he
    let f := L.presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes (Set.mem_univ x))
    have he0 : e ≠ 0 := by
      obtain ⟨b⟩ := hb x
      intro h
      obtain ⟨a, ha⟩ := (Submodule.span_singleton_eq_top_iff _ e).mp he (b PUnit.unit)
      exact b.linearIndependent.ne_zero PUnit.unit (by simpa [h] using ha.symm)
    have hf0 : f e ≠ 0 := by
      exact fun h ↦ he0 ((invertible_specializes_injective L x) (h.trans (map_zero _).symm))
    let b := FiniteDimensional.basisSingleton PUnit.{u + 1}
      (Module.rank_eq_one_iff_finrank_eq_one.mp hr) (f e) hf0
    refine ⟨⟨b, ?_⟩, ?_⟩
    · exact FiniteDimensional.basisSingleton_apply _ _ _ _ _
    · ext τ
      constructor
      · rintro ⟨m, rfl⟩
        obtain ⟨a, rfl⟩ := (Submodule.span_singleton_eq_top_iff _ e).mp he m
        exact ⟨a, invertible_specializes_smul L x a e⟩
      · rintro ⟨a, rfl⟩
        exact ⟨a • e, invertible_specializes_smul L x a e⟩
  · intro U hU
    have hη : genericPoint X ∈ U :=
      ((genericPoint_spec X).specializes (Set.mem_univ hU.some.val)).mem_open
        U.isOpen hU.some.property
    refine ⟨invertible_germ_injective L U (genericPoint X) hη, ?_⟩
    ext τ
    constructor
    · rintro ⟨s, rfl⟩ x hx
      refine ⟨L.presheaf.germ U x hx s, ?_⟩
      exact ConcreteCategory.congr_hom (L.presheaf.germ_stalkSpecializes hx _) s
    · intro hτ
      have H (x : U) : ∃ (V : X.Opens) (hxV : (x : X) ∈ V) (hVU : V ≤ U)
          (s : L.val.obj (op V)),
          L.presheaf.germ V (genericPoint X)
            (((genericPoint_spec X).specializes (Set.mem_univ (x : X))).mem_open
              V.isOpen hxV) s = τ := by
        obtain ⟨m, hm⟩ := hτ x x.2
        obtain ⟨V, hxV, s, rfl⟩ := L.presheaf.exists_germ_eq m
        refine ⟨V ⊓ U, ⟨hxV, x.2⟩, inf_le_right,
          L.presheaf.map (homOfLE inf_le_left).op s, ?_⟩
        exact (L.presheaf.germ_res_apply _ _ _ s).trans
          ((ConcreteCategory.congr_hom
            (L.presheaf.germ_stalkSpecializes hxV _) s).symm.trans hm)
      choose V hxV hVU s hs using H
      let F : TopCat.Sheaf AddCommGrpCat X := ⟨L.val.presheaf, L.isSheaf⟩
      have hc : TopCat.Presheaf.IsCompatible F.obj V s := by
        intro i j
        have hηij : genericPoint X ∈ V i ⊓ V j :=
          ⟨((genericPoint_spec X).specializes (Set.mem_univ (i : X))).mem_open
              (V i).isOpen (hxV i),
            ((genericPoint_spec X).specializes (Set.mem_univ (j : X))).mem_open
              (V j).isOpen (hxV j)⟩
        apply invertible_germ_injective L (V i ⊓ V j) (genericPoint X) hηij
        exact (L.presheaf.germ_res_apply _ _ _ _).trans
          ((hs i).trans ((hs j).symm.trans
            (L.presheaf.germ_res_apply _ _ _ _).symm))
      obtain ⟨t, ht, -⟩ := F.existsUnique_gluing' V U (fun x ↦ homOfLE (hVU x))
        (fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV _⟩) s hc
      refine ⟨t, ?_⟩
      have hi := ht hU.some
      have hg := congrArg (L.presheaf.germ
        (V hU.some) (genericPoint X)
        (((genericPoint_spec X).specializes (Set.mem_univ hU.some.val)).mem_open
          (V hU.some).isOpen (hxV hU.some))) hi
      exact (L.presheaf.germ_res_apply _ _ _ t).symm.trans
        (hg.trans (hs hU.some))

end AlgebraicGeometry.Scheme.Modules
