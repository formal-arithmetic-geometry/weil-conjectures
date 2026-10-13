/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap

/-! # Finite-support assembly of normalized tensor-Hom comparisons

Source: Stacks Project, more-algebra.tex, Lemma 0A6A, clause (1),
bounded finite-projective computation.
(blueprint: lem-pc-bounded-ring-hom-extension-degree)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- In one degree, a normalized Hom comparison is invertible if the source complex has
finite support and the individual module Hom comparisons are invertible. No projectivity
hypothesis or chain-map equation is needed for this finite-product assembly step.

Source: Stacks Project, more-algebra.tex, Lemma 0A6A, clause (1), finite-product
computation (blueprint: lem-pc-bounded-ring-hom-extension-degree).

Proof: choose a,b bounding P. The shared Hom-complex projections are a limiting fan
by homComplex_exists. For p outside [a,b], P^p is zero, hence its internal Hom to
Q^(p+n) is zero; scalar extension preserves zero objects. The infinite product is
therefore canonically the finite product indexed by integers in [a,b]. The same holds
after extension. Scalar extension on this site is ordinary tensor product; it preserves
finite direct sums, and hence finite products, without any flatness assumption. Apply
this finite-product comparison, followed by the product of the given g_p isomorphisms.
The result is an isomorphism k with the displayed source and target. Each projection
of k sends b tensor f, evaluated on c tensor x, to bc tensor f_p(x), by the supplied
normalization of g_p and naturality of the scalar-extension unit. The assumed equation
for t gives the same values. Pure tensors generate scalar extension, pure tensors in
P^p generate its extension, and evaluation on the unique-object slice detects internal
Hom sections. Thus each product projection of t equals that of k. The product universal
property implies t=k, proving its invertibility. If a>b, both products are products of
zero objects and the same argument applies to the empty finite product. The argument
works for arbitrary Q, including unbounded Q, and for non-flat B. -/
theorem boundedRingHom_extension_degree_isIso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (hF : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (hadd : F.Additive) (P Q : CochainComplex (RingSiteModules A) ℤ) (n : ℤ)
    (hb : ∃ a b : ℤ, ∀ p : ℤ, p < a ∨ b < p → IsZero (P.X p))
    (hterms : ∀ p : ℤ,
      ∃ g : F.obj (SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A)
          (P.X p) (Q.X (p + n))) ⟶
        SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf B)
          (F.obj (P.X p)) (F.obj (Q.X (p + n))),
        IsIso g ∧ ∀ (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b c : B)
          (f : (SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A)
            (P.X p) (Q.X (p + n))).val.obj U) (x : (P.X p).val.obj U),
          ((g.val.app U (ringExtensionPure φ F hF _ U b f)).app
            (op (Over.mk (𝟙 U.unop)))) (ringExtensionPure φ F hF (P.X p) U c x) =
          ringExtensionPure φ F hF (Q.X (p + n)) U (b * c)
            ((f.app (op (Over.mk (𝟙 U.unop)))) x))
    (t : F.obj ((homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n) ⟶
      (homComplex (R := CochainComplex.onePointRingSheaf B)
        ((ringExtensionComplex F hadd).obj P) ((ringExtensionComplex F hadd).obj Q)).X n)
    (ht : ∀ (p : ℤ) (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b c : B)
      (f : (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n |>.val.obj U)
      (x : (P.X p).val.obj U),
      ringHomEvaluate ((ringExtensionComplex F hadd).obj P)
        ((ringExtensionComplex F hadd).obj Q) n p U
        (t.val.app U (ringExtensionPure φ F hF _ U b f))
        (ringExtensionPure φ F hF (P.X p) U c x) =
      ringExtensionPure φ F hF (Q.X (p + n)) U (b * c)
        (ringHomEvaluate P Q n p U f x)) : IsIso t := by
  sorry

end CategoryTheory
