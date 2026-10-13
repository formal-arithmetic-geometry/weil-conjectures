/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1, SHEAF group T3
-/
module

public import Sheaf.Algebra.Homology.RingHomExtensionDefs

/-! # Differential compatibility for normalized Hom degree maps

Source: Stacks Project, more-algebra.tex, equation-base-change-RHom;
sites-cohomology.tex, section-hom-complexes (Tag 0A8X).
(blueprint: lem-pc-ring-hom-extension-differential)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

open scoped ChangeOfRings

namespace CategoryTheory

/-- Any degree maps with the normalized tensor-Hom formula commute with differentials.
This is a compatibility assertion for supplied maps, with no existence assertion.

Source: Stacks Project, more-algebra.tex, equation-base-change-RHom;
sites-cohomology.tex, section-hom-complexes (Tag 0A8X).
(blueprint: lem-pc-ring-hom-extension-differential).

Proof: for nonadjacent n,m the source and target differentials vanish by complex shape.
For m=n+1, compose both sides with each of the chosen target product projections.
Evaluate on b tensor f in the extended source Hom term and c tensor x in the extended
source P term. Naturality of the extension unit and the specified formula for F.map
identify all extended differentials on pure tensors. The Hom-complex differential
formula from homComplex_exists gives bc tensor d_Q(f_p(x)) minus
(-1)^n bc tensor f_(p+1)(d_P(x)) on each side, using the normalization for t n and t m.
Linearity moves subtraction and the integer sign through the tensor and evaluation
maps. Equality on pure tensors in P gives equality of internal-Hom sections, since
the unique-object slice has only its identity object and morphism. Equality on pure
tensors in the source gives equality of coordinate morphisms: the bottom-topology
sheafification unit is invertible and pure tensors generate scalar extensions.
Finally the limiting target fan is jointly monic, so equality of all coordinates
gives the chain-map equation. No flatness or boundedness is used; zero rings and zero
complex terms satisfy the same generation and linearity argument. -/
theorem ringHomExtension_differential
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (hm : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (h M) ≫
      SheafOfModules.changeOfRingsHom (ringSiteMap φ) M f ≫ eqToHom (h N).symm)
    (hF : F.Additive) (P Q : CochainComplex (RingSiteModules A) ℤ)
    (t : ∀ n : ℤ,
      F.obj ((homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n) ⟶
        (homComplex (R := CochainComplex.onePointRingSheaf B)
          ((ringExtensionComplex F hF).obj P) ((ringExtensionComplex F hF).obj Q)).X n)
    (ht : ∀ (n p : ℤ) (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b c : B)
      (f : (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n |>.val.obj U)
      (x : (P.X p).val.obj U),
      ringHomEvaluate ((ringExtensionComplex F hF).obj P)
        ((ringExtensionComplex F hF).obj Q) n p U
        ((t n).val.app U (ringExtensionPure φ F h _ U b f))
        (ringExtensionPure φ F h (P.X p) U c x) =
      ringExtensionPure φ F h (Q.X (p + n)) U (b * c)
        (ringHomEvaluate P Q n p U f x)) :
    ∀ n m : ℤ,
      t n ≫ (homComplex (R := CochainComplex.onePointRingSheaf B)
        ((ringExtensionComplex F hF).obj P) ((ringExtensionComplex F hF).obj Q)).d n m =
      ((ringExtensionComplex F hF).obj
        (homComplex (R := CochainComplex.onePointRingSheaf A) P Q)).d n m ≫ t m := by
  sorry

end CategoryTheory
