/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1, SHEAF group T3
-/
module

public import Sheaf.Algebra.Homology.RingHomExtensionDefs
import Sheaf.Algebra.Homology.RingHomExtensionDegrees
import Sheaf.Algebra.Homology.RingHomExtensionDifferential

/-! # Scalar extension of the shared Hom complex

Source: Stacks Project, more-algebra.tex, equation-base-change-RHom, and
sites-cohomology.tex, section-hom-complexes (Tag 0A8X).
(blueprint: lem-pc-normalized-ring-hom-extension)

This is a chain-level construction. It requires neither derived categories nor
perfectness, and supplies only the normalized Hom map, not derived extension data.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Scalar extension gives a map of the shared Hom complexes with the normalized
pure-tensor evaluation formula at every product coordinate.
Source: Stacks, more-algebra.tex, equation-base-change-RHom; sites-cohomology.tex,
section-hom-complexes (Tag 0A8X).
(blueprint: lem-pc-normalized-ring-hom-extension)

Proof: write each Hom term as its specified product of internal Homs, using the limit
witness of `homComplex_exists`. For each coordinate, extend a linear map by scalars:
`b ⊗ f` acts on `c ⊗ x` as `bc ⊗ f(x)`. This is additive in each argument. The balanced
relation in the first tensor follows from A-linearity of f, and in the second tensor
from that same linearity and the identity `φ(a)bc = bφ(a)c`. Thus the tensor universal
property gives a B-linear map into the internal Hom of the extended modules. On the
one-object site the slice restrictions are identities up to the unique isomorphisms;
this construction commutes with them. Sheafify, using the sheafification units, and
transport along the given object equalities. Apply this to every product projection;
the target product's universal property gives the degree map, without claiming tensor
commutes with infinite products. For the differential, compose with each target product
projection and evaluate on pure tensors. The two terms are respectively
`bc ⊗ d_Q(f(x))` and `(-1)^n bc ⊗ f(d_P(x))` on both sides, since the given functor maps
are exactly scalar extension of maps. Their difference is therefore equal. Pure tensors
span the extended modules, and the product projections are jointly monic, proving the
chain-map identity. In degrees not adjacent the differentials are zero. This constructs
the map and proves its normalization, with no boundedness or flatness assumption. -/
theorem normalizedRingHomExtension_exists {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (F : RingSiteModules A ⥤ RingSiteModules B)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (hm : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (h M) ≫
      SheafOfModules.changeOfRingsHom (ringSiteMap φ) M f ≫ eqToHom (h N).symm)
    (hF : F.Additive) (P Q : CochainComplex (RingSiteModules A) ℤ) :
    ∃ χ : (ringExtensionComplex F hF).obj
        (homComplex (R := CochainComplex.onePointRingSheaf A) P Q) ⟶
      homComplex (R := CochainComplex.onePointRingSheaf B)
        ((ringExtensionComplex F hF).obj P) ((ringExtensionComplex F hF).obj Q),
      ∀ (n p : ℤ) (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b c : B)
        (f : (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n |>.val.obj U)
        (x : (P.X p).val.obj U),
        ringHomEvaluate ((ringExtensionComplex F hF).obj P)
          ((ringExtensionComplex F hF).obj Q) n p U
          (((χ.f n).val.app U) (ringExtensionPure φ F h _ U b f))
          (ringExtensionPure φ F h (P.X p) U c x) =
        ringExtensionPure φ F h (Q.X (p + n)) U (b * c)
          (ringHomEvaluate P Q n p U f x) := by
  classical
  choose t ht using ringHomExtension_degrees_exists φ F h hm hF P Q
  refine ⟨{ f := t
            comm' := fun n m _ ↦ ringHomExtension_differential φ F h hm hF P Q t ht n m },
    ?_⟩
  exact ht

end CategoryTheory
