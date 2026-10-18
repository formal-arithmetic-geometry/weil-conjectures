/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Projectivity of a flat finitely presented algebra with geometrically integral fibres

Source: Stacks Project, More on Flatness, Tag 05FT,
`lemma-fibres-irreducible-flat-projective-nonnoetherian`
(blueprint: lem-trf-affine-geometrically-integral-projective).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Algebra

/-- A flat finitely presented commutative algebra whose fibres remain domains after every
residue-field extension is projective over the base. Here `ι` specifies the field extension
and the equality specifies the induced `R`-algebra structure on `K`. The canonical map
`R → κ(p)` is global evaluation after `Scheme.ΓSpecIso`. Projectivity itself means that the
canonical surjection from the free module `B →₀ R` splits, so includes the direct-summand
formulation.

Source: Stacks Project, More on Flatness, Tag 05FT
(blueprint: lem-trf-affine-geometrically-integral-projective).

Proof plan:
1. Put `k = κ(p)` and `C = B ⊗[R] k`. The mutually inverse tensor maps send
   `(b ⊗ a) ⊗ t` to `b ⊗ (a * t)` and `b ⊗ t` to `(b ⊗ 1) ⊗ t`.
   Hence every `C ⊗[k] K` is a domain, by the hypothesis. The affine-spectrum
   fibre-product isomorphism `pullbackSpecIso` (lem-weil-pbc-fibre-product-affine-spectra)
   and integrality of the spectrum of a domain
   (lem-weil-pbc-spec-domain-stalks-function-field, clause (2)) show that `Spec C` is
   geometrically integral, in the sense of `GeometricallyIntegral`
   (def-pc-geometrically-irreducible). These are the scheme-interface bridges.
2. Apply lem-trf-local-fibres-integral-projective (the existing DAG version of Tag 05FT)
   with the given flatness and finite presentation and the fibre property from step 1.
   It concludes `Module.Projective R B`.
3. The characterization `Module.Projective.iff_split`
   (def-weil-pbc-projective-module) identifies this with being a direct summand of a
   free module. No finite generation as an `R`-module or Noetherian hypothesis is used.
-/
theorem projective_of_geometricallyIntegral_fibres
    (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B] (hflat : RingHom.Flat (algebraMap R B))
    (hfibres : ∀ (p : Spec (.of R)) (K : Type (max u v w)) [Field K] [Algebra R K]
      (ι : (Spec (.of R)).residueField p →+* K),
      algebraMap R K =
        ι.comp (((Scheme.ΓSpecIso (.of R)).inv ≫ (Spec (.of R)).Γevaluation p).hom) →
      IsDomain (B ⊗[R] K)) :
    Module.Projective R B := by
  sorry

end Algebra
