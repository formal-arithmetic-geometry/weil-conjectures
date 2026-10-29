/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.CategoryTheory.RingedSiteModules

/-!
# Finite coefficients on the small pro-etale site

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange,
node def-weil-pbc-proetale-modules (blueprint: def-weil-pbc-proetale-modules).

## Main definitions

* `finiteCoefficientRingSheaf`: sheafified continuous functions on connected components.
* `FiniteCoefficientModules`: left modules over this ring sheaf.
* `FiniteCoefficientDerivedCategory` and `FiniteCoefficientDerivedCategoryPlus`: the
  unbounded localization and its strictly full bounded below subcategory.
* `finiteCoefficientEtaleRingSheaf` and `FiniteCoefficientEtaleDerivedCategory`: etale
  coefficients, using the canonical fixed-ring module-sheaf presentation.
* `finiteCoefficientDerivedComparison`: the exact module inverse image on complexes.
* `isBoundedConstructibleFiniteCoefficient`: the essential image of bounded constructible
  etale complexes, with its full subcategory `FiniteCoefficientBoundedConstructibleDerivedCategory`.
-/

@[expose] public section

universe u vC uC

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (T : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- Continuous functions on the quotient space of connected components, with pointwise
ring operations and restriction by precomposition. Source: blueprint,
`def-weil-pbc-proetale-modules` (blueprint: def-weil-pbc-proetale-modules). -/
noncomputable def finiteCoefficientPresheaf (T : Scheme.{u}) (Λ : Type (u + 1))
    [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    T.ProEtᵒᵖ ⥤ RingCat.{u + 1} where
  obj U := RingCat.of C(ConnectedComponents U.unop.left, Λ)
  map f := RingCat.ofHom
    { toFun := fun s ↦ s.comp
        ⟨f.unop.left.continuous.connectedComponentsMap,
          f.unop.left.continuous.connectedComponentsMap_continuous⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  map_id U := by
    ext s c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rfl
  map_comp f g := by
    ext s c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rfl

/-- The coefficient ring sheaf is the sheafification of continuous functions on connected
components. Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable def finiteCoefficientRingSheaf : Sheaf (Scheme.ProEt.topology T) RingCat.{u + 1} :=
  (presheafToSheaf (Scheme.ProEt.topology T) RingCat.{u + 1}).obj
    (finiteCoefficientPresheaf T Λ)

/-- Constant scalar sections of the continuous-function coefficient presheaf.
Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable def finiteCoefficientConstants :
    (Functor.const T.ProEtᵒᵖ).obj (RingCat.of Λ) ⟶ finiteCoefficientPresheaf T Λ where
  app U := RingCat.ofHom
    { toFun := fun r ↦ ContinuousMap.const _ r
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  naturality _ _ f := by ext r; rfl

/-- The canonical scalar map from the constant presheaf to the coefficient ring sheaf.
Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules). -/
noncomputable def finiteCoefficientScalarMap :
    (Functor.const T.ProEtᵒᵖ).obj (RingCat.of Λ) ⟶ (finiteCoefficientRingSheaf T Λ).obj :=
  finiteCoefficientConstants T Λ ≫
    toSheafify (Scheme.ProEt.topology T) (finiteCoefficientPresheaf T Λ)

/-- Constant scalar sections identify the coefficient sheaf with the sheafification of
constant scalars. Source: blueprint, `def-weil-pbc-proetale-modules`
(blueprint: def-weil-pbc-proetale-modules).

Proof: continuous functions to a discrete ring are locally constant. Their level sets,
pulled back along the quotient map to connected components, are open and give an open
cover of the scheme, hence a pro-etale cover. On each member the function is a constant
scalar. Two constant scalars with equal restrictions are equal locally, including the
empty object, whose empty cover is allowed. Thus the constants-to-functions map is
locally bijective. The sheafification unit is locally bijective and these properties
are closed under composition. This also treats the zero ring and disconnected schemes. -/
theorem finiteCoefficientScalarMap_locallyBijective :
    Presheaf.IsLocallyInjective (Scheme.ProEt.topology T) (finiteCoefficientScalarMap T Λ) ∧
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology T) (finiteCoefficientScalarMap T Λ) := by
  classical
  have hinj : Presheaf.IsLocallyInjective (Scheme.ProEt.topology T)
      (finiteCoefficientConstants T Λ) := by
    refine ⟨?_⟩
    intro U a b hab
    by_cases hU : Nonempty U.unop.left
    · obtain ⟨x⟩ := hU
      have hab' := congrArg (fun s : C(ConnectedComponents U.unop.left, Λ) ↦ s ⟦x⟧) hab
      change a = b at hab'
      subst b
      simpa only [Presheaf.equalizerSieve_self_eq_top] using
        (Scheme.ProEt.topology T).top_mem U.unop
    · have : IsEmpty U.unop.left := not_nonempty_iff.mp hU
      exact (Scheme.ProEt.topology T).superset_covering bot_le
        (Scheme.ProEt.bot_mem_topology U.unop)
  have hsurj : Presheaf.IsLocallySurjective (Scheme.ProEt.topology T)
      (finiteCoefficientConstants T Λ) := by
    refine ⟨?_⟩
    intro U s
    let f : C(U.left, Λ) := s.comp ⟨_, ConnectedComponents.continuous_coe⟩
    let O (x : U.left) : U.left.Opens :=
      ⟨f ⁻¹' {f x}, (isOpen_discrete _).preimage f.continuous⟩
    apply Scheme.ProEt.mem_topology_of_openImmersion _ (fun x ↦ (O x).ι)
    · intro x
      exact ⟨x, ⟨⟨x, rfl⟩, rfl⟩⟩
    · intro x
      refine ⟨f x, ?_⟩
      apply ContinuousMap.ext
      intro c
      obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
      change f x = f y.val
      exact y.property.symm
  constructor <;> dsimp only [finiteCoefficientScalarMap] <;> infer_instance

end AlgebraicGeometry.ProEtale
