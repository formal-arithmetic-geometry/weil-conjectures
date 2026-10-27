/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q42
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Vanishing of an étale module sheaf on a covering family

Source: Weil conjectures blueprint, `thm-sf-hom-ctf`, proof, first sentence
"The assertion is local on X" and last sentence "Both assertions are local on the site"
(blueprint: lem-sf-sheaf-zero-on-open-cover).

Fixed-coefficient module sheaves use the `Sheaf ... (ModuleCat Λ)` encoding authorized
by `def-weil-pbc-etale-sheaves`. The restriction is literally `Sheaf.over` on the slice
site, without identifying it with a separately constructed inverse-image functor.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A module sheaf on the small étale site is zero if its restriction to the slice
at each member of an étale covering family is zero. The family may be infinite or empty;
open-immersion covers are particular cases.

Source: Weil conjectures blueprint, `thm-sf-hom-ctf`, proof, the first and last sentences
asserting locality on the scheme and on the site
(blueprint: lem-sf-sheaf-zero-on-open-cover).

Proof: Fix an étale test object U over X. By the base-change axiom for the small étale
site (`def-weil-pbc-etale-site`, `def-weil-pbc-sites-and-cohomology`), the objects
U ×_X V_i cover U. Each projection U ×_X V_i → V_i is an object in the slice at V_i,
so the vanishing of the restricted sheaf makes its section module F(U ×_X V_i) zero.
The underlying abelian sheaf satisfies the equalizer axiom
(`def-weil-sheaf-of-modules-category`, `def-weil-pbc-abelian-etale-sheaves`), so the
map F(U) → ∏_i F(U ×_X V_i) is injective. Its target is zero, including for the empty
family, and therefore F(U) is zero. This holds for every U. All components of a
morphism to or from F are consequently the unique linear maps to or from zero,
so F is a zero object. -/
theorem etaleSheaf_isZero_of_isZero_over_cover (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] (I : Type v) (V : I → Scheme.{u})
    (φ : ∀ i : I, V i ⟶ X) [∀ i : I, AlgebraicGeometry.Etale (φ i)]
    (hcover : ∀ x : X, ∃ (i : I) (y : V i), φ i y = x)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hzero : ∀ i : I, IsZero (F.over (Scheme.Etale.mk (φ i)))) : IsZero F := by
  -- The covering family generates a covering sieve on the identity object.
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let f (i : I) : Scheme.Etale.mk (φ i) ⟶ T :=
    MorphismProperty.Over.homMk (φ i) (Category.comp_id _)
  let R := Sieve.ofArrows (fun i ↦ Scheme.Etale.mk (φ i)) f
  have hR : R ∈ X.smallEtaleTopology T := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff f).2
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact hcover x
  apply (IsZero.iff_id_eq_zero F).2
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change 𝟙 (F.obj.obj U) = 0
  -- Separatedness detects the identity map on the pulled-back covering sieve.
  let a : U.unop ⟶ T := MorphismProperty.Over.homMk U.unop.hom (Category.comp_id _)
  apply F.property.hom_ext ⟨R.pullback a, X.smallEtaleTopology.pullback_stable a hR⟩
  intro W
  obtain ⟨_, b, _, ⟨i⟩, _⟩ := W.hf
  -- A factoring arrow supplies an object of the slice over the covering member.
  have hz := congrArg
    (fun e : F.over (Scheme.Etale.mk (φ i)) ⟶ F.over (Scheme.Etale.mk (φ i)) ↦
      e.hom.app (Opposite.op (Over.mk b)))
    ((IsZero.iff_id_eq_zero _).1 (hzero i))
  change 𝟙 (F.obj.obj (Opposite.op W.Y)) = 0 at hz
  have hobj := (IsZero.iff_id_eq_zero _).2 hz
  exact hobj.eq_of_tgt _ _

end AlgebraicGeometry.Scheme
