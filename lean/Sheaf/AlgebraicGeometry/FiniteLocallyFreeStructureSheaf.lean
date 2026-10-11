/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Structure sheaves of finite locally free morphisms

Source: blueprint `sec-picard-framework/sk-the-hilbert-functor--definition-1`,
lemma `lem-pc-flf-properties`; Stacks Project, Tag 02KB
(blueprint: lem-pc-flf-properties).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace AlgebraicGeometry

noncomputable section

set_option quotPrecheck false

variable {X S : Scheme.{u}} (f : X ⟶ S)

local notation "P(" s ")" => (f.base _* X.presheaf).stalk s
local notation "R(" s ")" => S.presheaf.stalk s
local notation "K(" s ")" => S.residueField s

local instance (s : S) : Algebra (R(s)) (P(s)) :=
  ((TopCat.Presheaf.stalkFunctor CommRingCat s).map f.c).hom.toAlgebra

local instance (s : S) : Algebra (R(s)) (K(s)) := (S.residue s).hom.toAlgebra

/-- A finite locally free morphism of degree `d` has structure-sheaf pushforward locally
free of rank `d`, and its stalk tensored with the residue field canonically identifies with
sections of its scheme-theoretic fibre. The equations specify this canonical identification
on every germ and residue-field scalar, rather than asserting an unspecified isomorphism.
Source: blueprint `lem-pc-flf-properties`; Stacks Project, Tag 02KB
(blueprint: lem-pc-flf-properties).

Proof: (1) Apply `lem-pc-finite-flat-pushforward-locally-free` to the structure sheaf,
which is free of rank one over itself. The three morphism hypotheses follow from
`def-pc-finite-locally-free`. (2) On an affine neighbourhood `Spec A` of `s`, the preimage
is `Spec B`. By `lem-pc-finite-affine-fibre-sections` and
`lem-weil-pbc-fibre-product-affine-spectra`, both the stalk tensor and the fibre sections
identify with `B ⊗[A] κ(s)`. These identifications send germs and residue-field scalars to
their restrictions on the fibre, giving the displayed equations. (3) The degree condition
in `def-pc-finite-locally-free` gives dimension `d` to these fibre sections, hence the
locally free pushforward from step (1) has rank `d` at every point. -/
theorem finiteLocallyFree_structureSheaf_properties (d : ℕ)
    [f.IsFiniteLocallyFreeOfDegree d] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) d ∧
    ∀ s : S, ∃ e : (P(s) ⊗[R(s)] K(s)) ≃+* Γ(f.fiber s, ⊤),
      ∀ (U : S.Opens) (hs : s ∈ U)
        (hU : ⊤ ≤ (f.fiberι s) ⁻¹ᵁ (f ⁻¹ᵁ U))
        (a : Γ(X, f ⁻¹ᵁ U)) (k : K(s)),
        e (((f.base _* X.presheaf).germ U s hs).hom a ⊗ₜ[R(s)] k) =
          ((f.fiberι s).appLE (f ⁻¹ᵁ U) ⊤ hU).hom a *
            (f.fiberToSpecResidueField s).appTop.hom ((Scheme.ΓSpecIso (K(s))).inv.hom k) := by
  sorry

end

end AlgebraicGeometry
