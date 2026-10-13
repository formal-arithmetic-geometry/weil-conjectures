/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

/-! # The affine-basis sheaf condition for a localizing module presheaf

Source: Stacks Project, Tag 01HV, with Tags 009N and 009Q.
(blueprint: lem-pc-affine-localizing-presheaf-basis-sheaf).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- The underlying abelian-group presheaf satisfies the sheaf condition on the
site of affine opens when all affine-to-principal restrictions are localizations.
Source: Stacks Project, Tag 01HV, and Tags 009N/009Q.
(blueprint: lem-pc-affine-localizing-presheaf-basis-sheaf).

Proof: For an affine W, identify W with Spec Gamma(W). The restriction from
P(W) to each principal D(a) is the numerator map of a localization by hypothesis.
The localization universal property therefore gives a unique isomorphism with
sections of the associated module sheaf of P(W) on D(a). For inclusions of
principal opens these isomorphisms commute with restriction: both composites
are linear over Gamma(W) and agree on P(W), so localization uniqueness applies.
Consequently P on the principal basis of W satisfies unique gluing, as does the
associated module sheaf (01HV). In particular it is separated on that basis.
For any affine V contained in W, use the principal basis of V and the same
argument with V in place of W to detect equality and glue sections. To glue a
compatible family for an affine covering sieve on W, refine it by principal
opens of W. Glue on these principal opens, then obtain a section of P(W).
Its restriction to each affine member V agrees with the given section: cover
V by principal opens contained in the principal refinement and use the
separatedness already established for V. The same refinement proves uniqueness.
The induced topology consists exactly of sieves whose image covers W, so this
proves its sheaf condition. Empty covers are included: localization at zero
forces P of the empty affine open to be zero. No affine-intersection assumption
on the ambient scheme is used; all refinements take place inside an affine. -/
theorem isSheaf_affineBasis_of_localizing
    (T : Scheme.{u}) (P : _root_.PresheafOfModules.{u} T.ringCatSheaf.obj)
    (hP : ∀ (W : T.Opens), IsAffineOpen W → ∀ a : Γ(T, W),
      IsLocalizedModule.Away a (P.map (homOfLE (T.basicOpen_le a)).op).hom) :
    CategoryTheory.Presheaf.IsSheaf
      (((Subtype.mono_coe T.affineOpens).functor).inducedTopology
        (Opens.grothendieckTopology T))
      (((Subtype.mono_coe T.affineOpens).functor).op ⋙ P.presheaf) := by sorry

end AlgebraicGeometry.Scheme.Modules
