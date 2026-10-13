/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.FiniteAffineCechModel
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Universal cohomology comparison for the specified finite affine Čech complex

Source: Stacks Project, Tags 02KE, 01XD and 01XK.
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Ordinary pullback of the specified affine Čech model computes higher direct images.
The complex is fixed by F, U and V; no assertion about an arbitrary flat complex is made.
No relative flatness is needed for this comparison of ordinary section complexes.
Source: Stacks Project, Tag 02KE, affine termwise base-change calculation in the proof
of flat base change; Tags 01XD, 01XK and 01FK for the cohomology comparison.
(blueprint: lem-pc-finite-affine-cech-model-comparison).

Proof: Put Y=f^{-1}(U), p=f|_U and G=F|_Y. On an affine open W of a new base T',
the inverse images of the V_i form a finite affine cover of X'_W. Separatedness over
the affine U makes every nonempty finite intersection of the V_i affine, and their
base changes to W are affine as well. For such an intersection Z, affine pullback
identifies its new section module with Gamma(W,O) tensor over Gamma(U,O) Gamma(Z,G).
The pure-tensor formula commutes with every restriction. Since the products in each
degree are finite, these identifications assemble into an isomorphism of alternating
complexes between ordinary pullback of the specified model and the section complex
of the new cover. The GammaSpecIso scalar restriction and the final pullback along
the canonical affine chart identify exactly these scalar actions, not new choices.
Affine acyclicity and the Čech comparison (01XD), followed by the increasing-tuple
comparison (01FK), identify its homology with cohomology on X'_W. The affine-base
higher-direct-image comparison (01XK) identifies this with sections of R^q f'_*g'^*F
on W. Both identifications come from the augmented Čech resolution, so commute with
restriction to smaller affine opens. Glue them to the stated sheaf isomorphism on T'.
For a supplied cartesian square use its unique isomorphism to the standard pullback;
pullback composition identifies the restricted coefficient with g'^*F. For r=0 the
cover condition forces Y empty, hence X' empty and both complexes compute zero.
No step commutes tensor with homology: it commutes tensor with the finite section
terms before homology, which is why no flatness hypothesis on F or the new base is needed. -/
theorem finiteAffineCechModel_comparison {X T : Scheme.{u}} (f : X ⟶ T)
    [IsSeparated f] (F : X.Modules) [F.IsQuasicoherent]
    (U : T.Opens) (hU : IsAffineOpen U) {r : ℕ}
    (V : Fin r → (f ⁻¹ᵁ U).toScheme.Opens) (hV : ∀ i, IsAffineOpen (V i))
    (hcover : iSup V = ⊤) :
    ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
      [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
      Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj
          (finiteAffineCechModel (f ∣_ U) (F.restrict (f ⁻¹ᵁ U).ι) V)).homology q ≅
        (higherDirectImage f' q).obj ((Modules.pullback g').obj F)) := by sorry

end AlgebraicGeometry.Scheme.Modules
