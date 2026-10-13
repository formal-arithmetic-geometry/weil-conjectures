/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic

/-! # A flat finite presentation has a flat Noetherian model -/

@[expose] public section

open scoped TensorProduct

universe u v

namespace RingHom

/-- A flat finitely presented ring map comes by base change from a flat map between
finitely presented integer algebras.
(blueprint: lem-weil-pbc-flat-finite-presentation-model)

Source: Stacks Project, Algebra, Tag 02JO (1), specialized to the module equal to
its top ring; the construction is Tag 00R0 and the local criterion is Tag 00R6.

Proof: approximate the given finite presentation by the same generators and
relations over finitely generated integer subalgebras of R. Their rings P and Q
are Noetherian, their transition squares are pushouts, and their colimits are R
and S. For each model the locus in Spec Q where Q is flat over P is open by
Tag 00RC. Its inverse image at any later model is contained in the later flat
locus, since localization commutes with base change and flatness is preserved by
base change and localization. For every prime of S, localize the approximation
at its contractions. The local rings are Noetherian; the localized top module is
cyclic, and transition rings are localizations of base changes. Tag 00R6 applied
to this system and the flat localized limit makes that prime lie in the inverse
image of one model's flat locus. These inverse images are directed open subsets
covering Spec S. Quasi-compactness gives a model whose flat locus pulls back to
all of Spec S. Write its closed complement as V(J). The image of J generates
the unit ideal in S. A finite unit-ideal relation descends to a later model,
including its coefficients and its equality to 1. Persistence of the flat loci
therefore makes the later model flat at every prime. The local criterion for
flatness makes P → Q flat. The original approximation supplies the displayed
base-change isomorphism and its compatibility with f. Both P and Q are finite
type over Noetherian rings, hence finitely presented over their stated bases.
-/
theorem exists_flat_finitePresentation_model
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hfp : f.FinitePresentation) (hflat : f.Flat) :
    ∃ (P Q : Type (max u v)) (_ : CommRing P) (_ : CommRing Q)
      (_ : Algebra P Q) (_ : Algebra P R),
      Algebra.FinitePresentation ℤ P ∧ Algebra.FinitePresentation P Q ∧
      (algebraMap P Q).Flat ∧
      ∃ e : R ⊗[P] Q ≃+* S,
        e.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom) = f := by
  sorry

end RingHom
