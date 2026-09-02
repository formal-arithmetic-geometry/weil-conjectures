/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks

/-!

# A common refinement of two compactifications

Any two compactifications `c` and `d` of a quasi-compact morphism `f : X ⟶ Y` are refined
by a third one: the closure of the graph of `X` in `c.Z ×_Y d.Z`.

Concretely, the two open immersions `c.i` and `d.i` induce `γ : X ⟶ c.Z ×_Y d.Z`, and the
common refinement is the scheme-theoretic image of `γ`, with structure morphism the
projection to `c.Z` followed by `c.g` and with `X` embedded by `γ.toImage`. That this last
morphism is an open immersion is the graph-extension package of
`WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks`: the projection
`SIm(γ) ⟶ c.Z` is proper and restricts to an isomorphism over the open `X ⊆ c.Z`.

## Main results

- `AlgebraicGeometry.Compactification.exists_common_refinement`: two compactifications of a
  quasi-compact morphism admit a common refinement (blueprint:
  `GEO-BA43-PAIRWISE-COMMON-REFINEMENT`). This is what makes the `κ`-system
  `κ_{c,d} = ρ_{e → d} ρ_{e → c}⁻¹` of the proper base change chapter well-posed.
- `AlgebraicGeometry.Compactification.exists_common_refinement_isSchemeTheoreticallyDominant`:
  the refinement produced above is moreover scheme-theoretically dense, since its ambient
  scheme is by construction the scheme-theoretic image of `X`.

Finite presentation of the structure morphism of the common refinement, the remaining part
of `GEO-BA43-PAIRWISE-COMMON-REFINEMENT`, is not treated here.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Compactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]

/-- **Two compactifications admit a common refinement, densely**: the closure of the graph
of `X` in `c.Z ×_Y d.Z` is a compactification of `f` refining both `c` and `d`, in which `X`
is moreover scheme-theoretically dense. -/
theorem exists_common_refinement_isSchemeTheoreticallyDominant (c d : Compactification f) :
    ∃ e : Compactification f, IsSchemeTheoreticallyDominant e.i ∧
      Nonempty (e.Refinement c) ∧ Nonempty (e.Refinement d) := by
  have hqc : QuasiCompact c.i := c.quasiCompact_openImmersion ‹_›
  have hcomm : c.i ≫ c.g = d.i ≫ d.g := by rw [← c.comm, ← d.comm]
  -- the graph `γ : X ⟶ c.Z ×_Y d.Z` of the two open immersions
  set γ : X ⟶ pullback c.g d.g := pullback.lift c.i d.i hcomm with hγ
  have hfst : γ ≫ pullback.fst c.g d.g = c.i := by rw [hγ, pullback.lift_fst]
  have hsnd : γ ≫ pullback.snd c.g d.g = d.i := by rw [hγ, pullback.lift_snd]
  have hc : γ.toImage ≫ γ.imageι ≫ pullback.fst c.g d.g = c.i := by
    rw [γ.toImage_imageι_assoc, hfst]
  have hd : γ.toImage ≫ γ.imageι ≫ pullback.snd c.g d.g = d.i := by
    rw [γ.toImage_imageι_assoc, hsnd]
  -- the projection of the scheme-theoretic image of `γ` to `c.Z` is proper ...
  have hproper : IsProper (γ.imageι ≫ pullback.fst c.g d.g) :=
    isProper_imageι_comp_fst c.g d.g γ
  -- ... and restricts to an isomorphism over the open `X ⊆ c.Z`, hence `γ.toImage` is an
  -- open immersion.
  have hiso : IsIso ((γ.imageι ≫ pullback.fst c.g d.g) ∣_ c.i.opensRange) :=
    isIso_restrict_imageι_comp_fst c.g d.g c.i γ hfst
  have hopen : IsOpenImmersion γ.toImage :=
    isOpenImmersion_of_comp_of_isIso_restrict _ _ _ hc hiso
  refine ⟨{ Z := γ.image
            g := (γ.imageι ≫ pullback.fst c.g d.g) ≫ c.g
            i := γ.toImage
            comm := by rw [← Category.assoc, hc]; exact c.comm
            isProper := inferInstance
            isOpenImmersion := hopen }, ?_, ⟨?_⟩, ⟨?_⟩⟩
  · change IsSchemeTheoreticallyDominant γ.toImage
    have : QuasiCompact γ := quasiCompact_of_partialSection c.g d.g c.i γ hfst
    infer_instance
  · exact { hom := γ.imageι ≫ pullback.fst c.g d.g
            i_hom := hc
            hom_g := rfl }
  · exact { hom := γ.imageι ≫ pullback.snd c.g d.g
            i_hom := hd
            hom_g := by
              change (γ.imageι ≫ pullback.snd c.g d.g) ≫ d.g =
                (γ.imageι ≫ pullback.fst c.g d.g) ≫ c.g
              rw [Category.assoc, ← pullback.condition, Category.assoc] }

/-- **Two compactifications admit a common refinement**: for compactifications `c` and `d`
of a quasi-compact morphism `f`, there is a compactification `e` of `f` refining both.
(Blueprint: `GEO-BA43-PAIRWISE-COMMON-REFINEMENT`.) -/
theorem exists_common_refinement (c d : Compactification f) :
    ∃ e : Compactification f, Nonempty (e.Refinement c) ∧ Nonempty (e.Refinement d) :=
  let ⟨e, _, hc, hd⟩ := exists_common_refinement_isSchemeTheoreticallyDominant c d
  ⟨e, hc, hd⟩

/-! ### Axiom census

The common refinement is unconditional: the check below is run by the build, so a `sorry`
reappearing anywhere beneath it breaks compilation rather than going unnoticed. -/

/--
info: 'AlgebraicGeometry.Compactification.exists_common_refinement' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Compactification.exists_common_refinement

end AlgebraicGeometry.Compactification
