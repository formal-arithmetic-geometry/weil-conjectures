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

# Two compactifications admit a common refinement

Any two compactifications `c`, `d` of a quasi-compact morphism `f : X ⟶ Y` are dominated by a
third one: there is a compactification `e` of `f` together with refinements `e ⟶ c` and
`e ⟶ d`.

The compactification `e` is the closure of the graph of `f`, that is, the scheme-theoretic image
of the partial section `γ = (c.i, d.i) : X ⟶ c.Z ×_Y d.Z` of the first projection. It is proper
over `Y` because it is a closed subscheme of `c.Z ×_Y d.Z`, and `X` is open in it because the
first projection restricts to an isomorphism over the open `c.i(X) ⊆ c.Z`
(`AlgebraicGeometry.isIso_restrict_imageι_comp_fst`). The two projections of the fibre product
are the two refinements.

## Main results

- `AlgebraicGeometry.Compactification.exists_common_refinement`: two compactifications of a
  quasi-compact morphism admit a common refinement.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Compactification

/-- **Two compactifications admit a common refinement**: given compactifications `c` and `d`
of a quasi-compact morphism `f : X ⟶ Y`, there is a compactification `e` of `f` refining both.

The refinement is the closure of the graph of `f` in `c.Z ×_Y d.Z`, with the two projections as
refinement morphisms. (Blueprint: `GEO-BA43-PAIRWISE-COMMON-REFINEMENT`.) -/
theorem exists_common_refinement {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] (c d : Compactification f) :
    ∃ e : Compactification f, Nonempty (e.Refinement c) ∧ Nonempty (e.Refinement d) := by
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  -- the graph `γ = (c.i, d.i) : X ⟶ c.Z ×_Y d.Z`, a partial section of the first projection
  have hcomm : c.i ≫ c.g = d.i ≫ d.g := by rw [← c.comm, ← d.comm]
  obtain ⟨γ, hγfst, hγsnd⟩ : ∃ γ : X ⟶ pullback c.g d.g,
      γ ≫ pullback.fst c.g d.g = c.i ∧ γ ≫ pullback.snd c.g d.g = d.i :=
    ⟨pullback.lift c.i d.i hcomm, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  -- the two projections of the scheme-theoretic image of `γ`
  have htoIm₁ : γ.toImage ≫ γ.imageι ≫ pullback.fst c.g d.g = c.i := by
    rw [Scheme.Hom.toImage_imageι_assoc, hγfst]
  have htoIm₂ : γ.toImage ≫ γ.imageι ≫ pullback.snd c.g d.g = d.i := by
    rw [Scheme.Hom.toImage_imageι_assoc, hγsnd]
  -- the first projection is proper, hence so is the structure morphism of the closure
  have : IsProper (γ.imageι ≫ pullback.fst c.g d.g) := isProper_imageι_comp_fst c.g d.g γ
  -- the first projection is an isomorphism over `c.i(X)`, so `X` is open in the closure
  have hiso : IsIso ((γ.imageι ≫ pullback.fst c.g d.g) ∣_ c.i.opensRange) :=
    isIso_restrict_imageι_comp_fst c.g d.g c.i γ hγfst
  have hOI : IsOpenImmersion γ.toImage :=
    isOpenImmersion_of_comp_of_isIso_restrict γ.toImage _ c.i htoIm₁ hiso
  have hcond : (γ.imageι ≫ pullback.snd c.g d.g) ≫ d.g =
      (γ.imageι ≫ pullback.fst c.g d.g) ≫ c.g := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  refine ⟨{ Z := γ.image
            g := (γ.imageι ≫ pullback.fst c.g d.g) ≫ c.g
            i := γ.toImage
            comm := by rw [← Category.assoc, htoIm₁, ← c.comm]
            isProper := inferInstance
            isOpenImmersion := hOI }, ⟨?_⟩, ⟨?_⟩⟩
  · exact { hom := γ.imageι ≫ pullback.fst c.g d.g, i_hom := htoIm₁, hom_g := rfl }
  · exact { hom := γ.imageι ≫ pullback.snd c.g d.g, i_hom := htoIm₂, hom_g := hcond }

/-! ### Axiom census

The existence of a common refinement is unconditional: the check below is run by the build, so a
`sorry` reappearing anywhere beneath it breaks compilation rather than going unnoticed. -/

/--
info: 'AlgebraicGeometry.Compactification.exists_common_refinement' depends on
  axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Compactification.exists_common_refinement

end AlgebraicGeometry.Compactification
