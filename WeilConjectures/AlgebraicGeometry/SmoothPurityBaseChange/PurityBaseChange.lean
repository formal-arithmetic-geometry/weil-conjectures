/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExplicitSmoothComparison.ExplicitSmoothAdjunctionData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationExchange

/-! # Canonical smooth purity and arbitrary base change

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-trace/sec-base-change-and-composition/
sk-prop-sp-purity-bc/_section.md and sk-prop-sp-purity-bc.proof.md.
(blueprint: sk-prop-sp-purity-bc).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.PurityTransport
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.SmoothPurityBaseChange

/-- The literal Cartesian pullback, with the pulled-back compactification and
unchanged relative dimension. Source: the displayed square
(blueprint: sk-prop-sp-purity-bc). -/
def baseChange {k : Type u} [Field k] (s : ExplicitSmoothComparison.Datum k)
    (Y' : Over (Spec (.of k)))
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    (v : Y'.left ⟶ s.Y) : ExplicitSmoothComparison.Datum k :=
  { X := pullback s.map v
    Y := Y'.left
    base := Y'.hom
    map := pullback.snd s.map v
    dim := s.dim
    compactification := s.compactification.baseChange v }

/-- The canonical purity comparison with a specified exceptional adjoint is the
unique counit-preserving comparison of right adjoints. For the normalized family
its finite trace is the diagonal/DNC trace; its other traces are their normalized
coefficient transports. Source: the specified gamma maps and adjunction comparisons
(blueprint: sk-prop-sp-purity-bc). -/
def gamma (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    (b : ExplicitSmoothComparison.Family ell k) (c : Coefficient ell)
    (s : ExplicitSmoothComparison.Datum k)
    (G : c.ctf ell s.Y ⥤ c.ctf ell s.X)
    (adj : support ell c s.compactification (b c s).support_closed ⊣ G) :=
  (b c s).adjunction.rightAdjointUniq adj

/-- Restrict the actual total derived inverse image to the recorded full
subcategory. Only a membership proof is supplied; the functor is not chosen.
Source: the pullbacks in the Cartesian square (blueprint: sk-prop-sp-purity-bc). -/
def pull (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)
    {A B : Scheme.{u}} (v : A ⟶ B)
    (h : ∀ K : c.ctf ell B,
      property ell c A ((actualPull (c.obj ell) v).obj K.obj)) :
    c.ctf ell B ⥤ c.ctf ell A :=
  (property ell c A).lift ((property ell c B).ι ⋙ actualPull (c.obj ell) v) h

end AlgebraicGeometry.ProEtale.SmoothPurityBaseChange
