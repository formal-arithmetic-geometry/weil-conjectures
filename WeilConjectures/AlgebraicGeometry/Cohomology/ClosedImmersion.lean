/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Cohomology.Pullback
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import WeilConjectures.Mathlib.Topology.Sheaves.Abelian

/-!
# Cohomology is invariant under pushforward along a closed immersion

Let `i : W₀ ⟶ W` be a closed immersion of schemes and let `F` be a sheaf of
`𝒪_{W₀}`-modules. This file constructs an isomorphism

`H^n(W, i_* F) ≅ H^n(W₀, F)`,

natural in `F`. The two sides are modules over `Γ(W, 𝒪_W)` and `Γ(W₀, 𝒪_{W₀})` respectively,
so the isomorphism is stated as a bijective map semilinear over
`i.appTop : Γ(W, 𝒪_W) ⟶ Γ(W₀, 𝒪_{W₀})`; when `W` and `W₀` are schemes over `Spec R` and `i`
is a morphism over `Spec R`, it is `R`-linear.

Cohomology of an abelian sheaf is an `Ext`-group out of the constant sheaf `ℤ`, so the
statement to prove is `Ext^n_W(ℤ_W, i_♭ G) ≅ Ext^n_{W₀}(ℤ_{W₀}, G)` for the pushforward
`i_♭` of sheaves of abelian groups. It is obtained from two ingredients:

* the adjunction `i^{-1} ⊣ i_♭`, whose left adjoint is exact and whose right adjoint is
  exact because `i` is a closed embedding
  (`TopCat.Sheaf.preservesFiniteColimits_sheafPushforwardContinuous`). For such an
  adjunction, `CategoryTheory.Adjunction.extAddEquiv` identifies `Ext^n(i^{-1} A, G)` with
  `Ext^n(A, i_♭ G)`;
* the identification `i^{-1} ℤ_W ≅ ℤ_{W₀}` of the pullback of the constant sheaf with the
  constant sheaf (`AlgebraicGeometry.Scheme.Hom.pullbackAbConstantSheafIso`).

## Main definitions and results

* `AlgebraicGeometry.Scheme.Modules.H.pushforwardAddEquiv` — the isomorphism of additive
  groups `H^n(W₀, F) ≃+ H^n(W, i_* F)`.
* `AlgebraicGeometry.Scheme.Modules.H.pushforwardMap` — its inverse
  `H^n(W, i_* F) ⟶ H^n(W₀, F)`, semilinear over `i.appTop`, and
  `H.bijective_pushforwardMap`, which says that it is bijective.
* `AlgebraicGeometry.Scheme.Modules.H.pushforwardAddEquiv_map` — naturality in `F`.
* `AlgebraicGeometry.Scheme.Modules.H.pushforwardMap_smul_over` — `R`-linearity for schemes
  over `Spec R`.

-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace Abelian

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {W₀ W : Scheme.{u}} (i : W₀ ⟶ W)

/-- The pushforward of sheaves of abelian groups along a closed immersion is right exact. -/
lemma preservesFiniteColimits_pushforwardAb [IsClosedImmersion i] :
    PreservesFiniteColimits i.pushforwardAb :=
  TopCat.Sheaf.preservesFiniteColimits_sheafPushforwardContinuous i.base i.isClosedEmbedding

end Scheme.Hom

namespace Scheme.Modules

variable {W₀ W : Scheme.{u}} (i : W₀ ⟶ W) [IsClosedImmersion i] (F G : W₀.Modules) (n : ℕ)

attribute [local instance] Scheme.Hom.preservesFiniteColimits_pushforwardAb

/-- The cohomology of the pushforward of a sheaf of modules along a closed immersion
`i : W₀ ⟶ W` is the cohomology of the sheaf itself: `H^n(W₀, F) ≃+ H^n(W, i_* F)`. -/
noncomputable def H.pushforwardAddEquiv : F.H n ≃+ ((pushforward i).obj F).H n :=
  (Ext.precompAddEquiv (i.pullbackAbConstantSheafIso (AddCommGrpCat.of (ULift ℤ)))
      ((toSheafAb W₀).obj F) n).trans
    (i.pullbackPushforwardAbAdjunction.extAddEquiv
      ((constantSheafAb W).obj (AddCommGrpCat.of (ULift ℤ))) ((toSheafAb W₀).obj F) n)

lemma H.pushforwardAddEquiv_apply (x : F.H n) :
    H.pushforwardAddEquiv i F n x =
      i.pullbackPushforwardAbAdjunction.extAddHom
        ((constantSheafAb W).obj (AddCommGrpCat.of (ULift ℤ))) ((toSheafAb W₀).obj F) n
        ((Ext.mk₀ (i.pullbackAbConstantSheafIso (AddCommGrpCat.of (ULift ℤ))).hom).comp x
          (zero_add n)) :=
  rfl

/-- `H^n(W₀, F) ≃+ H^n(W, i_* F)` is compatible with postcomposition by a morphism of
sheaves of modules. -/
lemma H.pushforwardAddEquiv_comp_mk₀ (φ : F ⟶ G) (x : F.H n) :
    H.pushforwardAddEquiv i G n (x.comp (Ext.mk₀ ((toSheafAb W₀).map φ)) (add_zero n)) =
      (H.pushforwardAddEquiv i F n x).comp
        (Ext.mk₀ ((toSheafAb W).map ((pushforward i).map φ))) (add_zero n) := by
  rw [H.pushforwardAddEquiv_apply, H.pushforwardAddEquiv_apply,
    ← Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by lia),
    Adjunction.extAddHom_comp_mk₀]
  rfl

/-- The isomorphism `H^n(W₀, F) ≃+ H^n(W, i_* F)` is natural in `F`. -/
lemma H.pushforwardAddEquiv_map (φ : F ⟶ G) (x : F.H n) :
    H.pushforwardAddEquiv i G n (H.map φ n x) =
      H.map ((pushforward i).map φ) n (H.pushforwardAddEquiv i F n x) := by
  rw [H.map_apply, H.mapAddHom_apply_eq_comp, H.pushforwardAddEquiv_comp_mk₀, H.map_apply,
    H.mapAddHom_apply_eq_comp]

/-- The isomorphism `H^n(W₀, F) ≃+ H^n(W, i_* F)` is semilinear over
`i.appTop : Γ(W, 𝒪_W) ⟶ Γ(W₀, 𝒪_{W₀})`. -/
lemma H.pushforwardAddEquiv_smul (r : Γ(W, ⊤)) (x : F.H n) :
    H.pushforwardAddEquiv i F n (i.appTop.hom r • x) = r • H.pushforwardAddEquiv i F n x := by
  rw [H.smul_def, H.mapAddHom_apply_eq_comp, H.pushforwardAddEquiv_comp_mk₀, H.smul_def,
    H.mapAddHom_apply_eq_comp, smulEnd_pushforward]

/-- The comparison map `H^n(W, i_* F) ⟶ H^n(W₀, F)` on the cohomology of a sheaf of modules
along a closed immersion `i : W₀ ⟶ W`, semilinear over the ring homomorphism
`i.appTop : Γ(W, 𝒪_W) ⟶ Γ(W₀, 𝒪_{W₀})`. It is bijective, see
`AlgebraicGeometry.Scheme.Modules.H.bijective_pushforwardMap`. -/
noncomputable def H.pushforwardMap :
    ((pushforward i).obj F).H n →ₛₗ[i.appTop.hom] F.H n where
  toFun := (H.pushforwardAddEquiv i F n).symm
  map_add' := (H.pushforwardAddEquiv i F n).symm.map_add
  map_smul' r y := by
    refine (H.pushforwardAddEquiv i F n).injective ?_
    rw [AddEquiv.apply_symm_apply, H.pushforwardAddEquiv_smul, AddEquiv.apply_symm_apply]

@[simp]
lemma H.pushforwardMap_apply (y : ((pushforward i).obj F).H n) :
    H.pushforwardMap i F n y = (H.pushforwardAddEquiv i F n).symm y :=
  rfl

/-- Cohomology is invariant under pushforward along a closed immersion. -/
lemma H.bijective_pushforwardMap : Function.Bijective (H.pushforwardMap i F n) :=
  (H.pushforwardAddEquiv i F n).symm.bijective

/-- The comparison map `H^n(W, i_* F) ⟶ H^n(W₀, F)` is natural in `F`. -/
lemma H.pushforwardMap_map (φ : F ⟶ G) (y : ((pushforward i).obj F).H n) :
    H.pushforwardMap i G n (H.map ((pushforward i).map φ) n y) =
      H.map φ n (H.pushforwardMap i F n y) := by
  refine (H.pushforwardAddEquiv i G n).injective ?_
  rw [H.pushforwardMap_apply, H.pushforwardMap_apply, AddEquiv.apply_symm_apply,
    H.pushforwardAddEquiv_map, AddEquiv.apply_symm_apply]

/-! ### Schemes over a base ring -/

section OverBase

variable (R : Type u) [CommRing R] [W.Over (Spec (.of R))] [W₀.Over (Spec (.of R))]
  [i.IsOver (Spec (.of R))]

/-- If `W₀` and `W` are schemes over `Spec R` and `i` is a morphism over `Spec R`, the
comparison map `H^n(W, i_* F) ⟶ H^n(W₀, F)` is `R`-linear. -/
lemma H.pushforwardMap_smul_over (r : R) (y : ((pushforward i).obj F).H n) :
    H.pushforwardMap i F n (r • y) = r • H.pushforwardMap i F n y := by
  rw [H.smul_over_def R W r y, H.smul_over_def R W₀ r (H.pushforwardMap i F n y),
    ← Scheme.appTop_overRingHom R i r]
  exact (H.pushforwardMap i F n).map_smulₛₗ _ y

end OverBase

end Scheme.Modules

end AlgebraicGeometry
