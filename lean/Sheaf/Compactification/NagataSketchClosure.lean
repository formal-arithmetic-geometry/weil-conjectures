/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Schematic closure and uniqueness

Source: blueprint main-20261015, sec-nagata-compactification,
`sk-lem-nagata-sketch-closure/_section.md`, order 4; Stacks Project, Tags 01R8, 01RG,
01RE and 01RH (blueprint: sk-lem-nagata-sketch-closure).

Density is expressed by injectivity on sections over every open. This is injectivity
of the structure-sheaf morphism into the direct image, including for an open immersion
which is not quasi-compact.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

-- The nested density hypothesis is used in the proof, but not in the forall conclusion.
set_option linter.unusedVariables false in
/-- Schematic closure of a quasi-compact immersion and uniqueness over a separated base.

Source: blueprint main-20261015, sec-nagata-compactification,
`sk-lem-nagata-sketch-closure/_section.md`, order 4; Stacks Project, Tags 01R8
(lemma-quasi-compact-scheme-theoretic-image), 01RG (lemma-quasi-compact-immersion),
01RE (lemma-characterize-scheme-theoretically-dense) and 01RH
(lemma-equality-of-morphisms) (blueprint: sk-lem-nagata-sketch-closure).

Proof, following the node's three steps:
1. Apply lemma-nagata-scheme-image-ideal-qc to construct the canonical closed
image `i.image` with inclusion `i.imageι` and factor `i.toImage`. The factorization
identity is `Scheme.Hom.toImage_imageι`. Apply lemma-nagata-scheme-image-universal:
any closed factorization receives the comparison from the image, compatible with
both maps; the closed inclusion is a monomorphism, so this comparison is unique.
This is precisely the smallest-closed-subscheme characterization of the image.
2. Apply lemma-nagata-immersion-open-in-scheme-image to the quasi-compact immersion
`i`. It makes `i.toImage` an open immersion and schematically dense. Equivalently,
its maps on sections over every open of `i.image` are injective (Stacks 01RE).
Quasi-separatedness of `T` is retained as in the blueprint, though this step does
not need it. There is no reducedness assumption.
3. For the independent uniqueness assertion, the equation `a ≫ s = b ≫ s` says
that `a` and `b` are maps over the same base. Injectivity of every `j.app V` makes
every local section of a closed-factor ideal of `j` zero. In particular its
quasi-coherent kernel ideal is zero, so `j` is scheme-theoretically dominant.
Apply lemma-nagata-ext-scheme-theoretically-dominant-separated with `(s,a,b,j)`
and the given equation `j ≫ a = j ≫ b`. No quasi-compactness of `j` is used.
-/
theorem nagata_sketch_closure :
    (∀ {U T : Scheme.{u}} (i : U ⟶ T) [QuasiCompact i] [IsImmersion i]
      [QuasiSeparatedSpace T],
      IsClosedImmersion i.imageι ∧
      IsOpenImmersion i.toImage ∧
      (∀ V : i.image.Opens, Function.Injective (i.toImage.app V)) ∧
      ∀ (Z : Scheme.{u}) (k : Z ⟶ T) (_hk : IsClosedImmersion k) (f : U ⟶ Z),
        f ≫ k = i →
        ∃! l : i.image ⟶ Z, i.toImage ≫ l = f ∧ l ≫ k = i.imageι) ∧
    (∀ {U T S Y : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
      (hj : ∀ V : T.Opens, Function.Injective (j.app V))
      (s : Y ⟶ S) [IsSeparated s] {a b : T ⟶ Y},
      a ≫ s = b ≫ s → j ≫ a = j ≫ b → a = b) := by
  constructor
  · intro U T i _ _ _
    refine ⟨inferInstance, inferInstance, i.toImage.app_injective, ?_⟩
    intro Z k hk f hf
    have H : k.ker ≤ i.imageι.ker := by
      rw [← hf]
      exact Scheme.Hom.ker_le_ker_imageι_comp f k
    refine ⟨IsClosedImmersion.lift k i.imageι H, ?_, ?_⟩
    · exact ⟨Scheme.Hom.toImage_lift f k hf H, IsClosedImmersion.lift_fac _ _ _⟩
    · intro l hl
      exact IsClosedImmersion.eq_lift k i.imageι H l hl.2
  · intro U T S Y j _ hj s _ a b hab hjab
    have : IsSchemeTheoreticallyDominant j := by
      constructor
      apply Scheme.IdealSheafData.ext
      funext V
      apply le_antisymm ?_ bot_le
      exact (j.ideal_ker_le V).trans_eq
        ((RingHom.injective_iff_ker_eq_bot _).mp (hj V))
    exact ext_of_isSchemeTheoreticallyDominant_of_isSeparated s hab j hjab

end AlgebraicGeometry
