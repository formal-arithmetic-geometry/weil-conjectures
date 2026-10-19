/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q156
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.Topology.Constructible
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
import Sheaf.TraceFormula.GeometricReducedFibreLocusBaseChange
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.NoetherianConstructibleSubsetCriterion
import Sheaf.AlgebraicGeometry.GeometricallyReducedAlgebraicClosureTest
import Sheaf.AlgebraicGeometry.GenericConstancyGeometricReducedness

/-!
# The geometrically reduced fibre locus of a finitely presented algebra

Source: Stacks Project, More on Morphisms, Tags 0579 and 0576, in affine ring form;
Properties, Tag 054C (blueprint: lem-trf-geometrically-reduced-fibre-locus).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open scoped TensorProduct

namespace AlgebraicGeometry

/-- For a finitely presented commutative algebra, the geometrically reduced fibre locus
is constructible and pulls back exactly under every base ring map.
`p.asIdeal.Fiber B` is `κ(p) ⊗[A] B`, canonically the same `κ(p)`-algebra as
`B ⊗[A] κ(p)` by tensor symmetry. The residue field is identified with the scheme
residue field by `Spec.residueFieldIso`. The explicit `rightAlgebra` supplies the
canonical `A'`-algebra structure on `B ⊗[A] A'`; no extra algebra structure is assumed.
Empty fibres are included, and no flatness, injectivity or Noetherian condition is imposed.

Source: Stacks Project, More on Morphisms, Tags 0579 and 0576; Properties, Tag 054C.
(blueprint: lem-trf-geometrically-reduced-fibre-locus)

Proof, following the node:
1. The whole affine source and base show that `Spec B → Spec A` is locally of finite
   presentation by def-sbc-locally-finite-presentation and
   def-weil-pbc-finitely-presented-algebra. For empty source this is vacuous.
2. By lem-weil-pbc-affine-scheme-qcqs both spectra are qcqs. Apply clause (1) of
   lem-weil-pbc-qcqs-morphism-permanence to obtain quasi-compactness of the morphism.
3. By def-pc-scheme-fibre and lem-weil-pbc-fibre-product-affine-spectra the ordinary
   fibre is the spectrum of the residue-field tensor product, with its stated structure
   map. By def-weil-geometric-fibre and
   lem-trf-geometric-reducedness-algebraic-closure-test its geometric fibre is reduced
   exactly when this algebra is geometrically reduced. No finiteness is needed here.
4. Apply lem-weil-pbc-fibre-product-affine-spectra to the base change and identify its
   projection. Then lem-trf-geometric-reduced-fibre-locus-base-change, together with
   step 3 for both algebras, gives the asserted equality for every base map.
5. Choose finite generators and relations. Their finitely many coefficients belong
   to a finitely generated integer subalgebra `A₀`, by lemma-nagata-ring-finite-type-subalgebras.
   The zero-variable case of lem-trf-mvpolynomial-noetherian and
   lem-weil-pbc-finite-type-algebra-noetherian make `A₀` Noetherian.
6. The same relations define a finitely presented `A₀`-algebra `B₀`. Evaluation on
   generators and tensor balancing give `B₀ ⊗[A₀] A ≃ₐ[A] B`; the inverse sends each
   variable to its tensor with one. Use def-weil-pbc-module-tensor-product,
   def-weil-pbc-algebra-hom-quotient and def-weil-pbc-mv-polynomial-ring.
   Thus the original affine morphism is the base change of `Spec B₀ → Spec A₀`.
7. Give any irreducible closed subset of `Spec A₀` its reduced closed subscheme
   structure by lem-weil-pbc-reduced-induced-closed-subscheme and def-weil-closed-immersion.
   It has a generic point by lem-sc-scheme-sober. Base change preserves quasi-compactness
   and local finite presentation by lem-weil-pbc-qcqs-morphism-permanence.
   Apply lem-trf-generic-constancy-geometric-reducedness. Steps 3 and 4 identify its
   nonempty open alternative with containment in, or disjointness from, the fibre locus.
8. Apply lem-trf-noetherian-constructible-subset-criterion on `Spec A₀`. Pull the
   constructible locus back using step 4 and lem-pur-scheme-constructible-preimage.
   Step 3 identifies it with the required ring locus; step 4 already gives the equality. -/
theorem geometricallyReduced_fibre_locus_constructible_baseChange
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B] :
    Topology.IsConstructible
      {p : PrimeSpectrum A | GeometricallyReduced (Spec.map (CommRingCat.ofHom
        (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B))))} ∧
    ∀ (A' : Type u) [CommRing A'] [Algebra A A'],
      @_root_.id (∀ [Algebra A' (B ⊗[A] A')], Prop)
        (fun [Algebra A' (B ⊗[A] A')] ↦
          {q : PrimeSpectrum A' | GeometricallyReduced (Spec.map (CommRingCat.ofHom
            (algebraMap q.asIdeal.ResidueField (q.asIdeal.Fiber (B ⊗[A] A')))))} =
          PrimeSpectrum.comap (algebraMap A A') ⁻¹'
            {p : PrimeSpectrum A | GeometricallyReduced (Spec.map (CommRingCat.ofHom
              (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber B))))})
        (Algebra.TensorProduct.rightAlgebra (R := A) (A := B) (B := A')) := by
  sorry

end AlgebraicGeometry
