/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Unpointed affine étale descent at a prime

Source: Stacks Project, Tags 01ZM, 07RP, 01Z6, 00CR and 00CP.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- An étale algebra over R_p comes from an étale R-algebra by localization.
Source: Stacks Project, Tags 01ZM (finite-presentation descent), 07RP
(descent of étaleness), 01Z6 (affineness at a finite stage), 00CR (localization as a colimit),
and 00CP (localization universal property).
(blueprint: new-lem-sbc-prime-localization-etale-algebra-model)

Proof: Index the principal localizations R_s, s outside p, by finite subsets
of R minus p, with s the product. Their filtered colimit is R_p. The affine
morphism Spec B → Spec R_p is étale and hence of finite presentation.
Tag 01ZM descends it to a finite-presentation scheme over some Spec R_s.
Tag 07RP makes the descended morphism étale after increasing the stage.
The transition maps on the descended schemes are affine, and their limit
Spec B is affine. By Tag 01Z6, increase the stage once more so that the
model is affine, say Spec C. The composite Spec C → Spec R_s → Spec R
is étale, since a principal localization is étale and étale morphisms compose.
Let a : R → C be its ring map. The base-change isomorphism over R_p gives
a map i : C → B with a followed by i equal to R → R_p → B.
The localization universal property identifies the base-change algebra B
with localization of C at the image M of R minus p under a. Transfer the
localization structure along the base-change isomorphism. Its C-algebra structure is exactly the one
induced by i, which gives the displayed IsLocalization assertion.

This statement has no field, prime over p in B, or residue-field pointing.
Those data and all pointing identities are constructed in the caller. -/
theorem primeLocalization_etale_algebra_model
    (R : CommRingCat.{u}) (p : Spec R) (B : CommRingCat.{u})
    (α : CommRingCat.of (Localization.AtPrime p.asIdeal) ⟶ B)
    (hα : Etale (Spec.map α)) :
    ∃ (C : CommRingCat.{u}) (a : R ⟶ C) (i : C ⟶ B),
      Etale (Spec.map a) ∧
      a ≫ i = CommRingCat.ofHom (algebraMap R (Localization.AtPrime p.asIdeal)) ≫ α ∧
      ∃ M : Submonoid C, (letI := i.hom.toAlgebra; IsLocalization M B) := by sorry

end AlgebraicGeometry.Scheme
