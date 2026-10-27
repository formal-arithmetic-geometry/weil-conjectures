module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
public import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Sheaf.AlgebraicGeometry.QcqsRelativeAffinizationMap
import Sheaf.AlgebraicGeometry.CanonicalAffineChartsQcOpenImmersion
import WeilConjectures.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.AlgebraicGeometry.Gluing

/-! # Relative quasi-affine group envelopes

Source: Stacks Project, Morphisms, Tag 01SM (4), and Constructions, Tag 01LY.
The group extension and generic comparison are agent-written consequences of
Tags 02KH and 0AUW, as detailed in the proof plan below.
(blueprint: lem-sfb-relative-quasiaffine-group-envelope).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- The canonical relative affinization of a quasi-affine group homomorphism over a
Dedekind domain carries compatible group operations. `IsDedekindDomain` includes fields.
The algebra is exactly `f_* O_G`, including its induced structure-algebra map. The
isomorphism `a` and its affine chart formula specify its relative spectrum; the chart
identity specifies the canonical map, not an arbitrary open embedding.
The last clause is the underlying morphism of presheaves of the canonical sheaf map
`O_(H_K) → (j_K)_* O_(G_K)`, where `Over.pullback` supplies the generic base change.
No finite generation of the algebra or finite type of the envelope is asserted.

Source: Stacks Project, Morphisms, Tag 01SM (4); Constructions, Tag 01LY;
Coherent, Tag 02KH; More Algebra, Tag 0AUW.
(blueprint: lem-sfb-relative-quasiaffine-group-envelope).

Proof:
1. Finite type and separatedness over the affine base give qcqs sources
   (lem-weil-pbc-qcqs-over-affine). The permanence lemmas give f qcqs
   (lem-weil-pbc-qcqs-morphism-permanence). Apply
   lem-trf-qcqs-relative-affinization-map to obtain the quasi-coherent algebra,
   its affine relative spectrum q, the algebra isomorphism a and the canonical j.
2. Each inverse image of an affine base open is quasi-affine. The chart identity
   and lem-trf-canonical-affine-charts-qc-open-immersion make j a quasi-compact
   open immersion. It is separated and hence quasi-separated by
   lem-weil-pbc-separated-cancellation and lem-pc-separated-quasi-separated.
3. On a chart H_W = Spec Gamma(G_W, O), the unit O_H → j_* O_G is the identity
   on coefficients, also after localization. By
   lem-sfb-qcqs-functions-local-comparison it is an isomorphism on each chart,
   hence on H, giving compatible function isomorphisms on every open of H.
4. Each G_W is flat over B, and its structure module is invertible. Thus
   lem-sc-flat-invertible-sections-torsion-free makes its sections torsion-free.
   By lem-sfb-dedekind-torsionfree-module-flat they are flat without a finite
   generation hypothesis. Lem-weil-pbc-flat-ring-map-iff-flat-affine makes
   every H_W flat over the base, hence H is flat by the local-ring definition.
5. Flat base change in degree zero (lem-pc-flat-base-change-cohom) preserves
   the unit isomorphism. Replace the factors one at a time in H squared and
   H cubed, using flatness of G and H. Permanence and composition
   (lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-flat-ring-map-comp,
   lem-weil-pbc-qcqs-morphism-permanence) verify all hypotheses. This gives
   the canonical function comparisons for j squared and j cubed.
6. Given a map H to the n-th power → J and a compatible map G to the n-th
   power → H, restrict to inverse images of affine W in J. The function
   comparison extends its ring map uniquely to the affine H_W by
   lem-weil-pbc-morphism-into-affine-scheme. These extensions remain over W.
   They agree on affine refinements of intersections and glue uniquely by
   lem-weil-pbc-scheme-morphism-gluing and
   lem-weil-pbc-morphism-factors-through-open-subscheme. Use n = 1, 2, 3.
7. Extend j composed with multiplication using n = 2 and with inverse using
   n = 1, over the corresponding operations of J. Set the identity to j e_G.
   The extension formulas make j and q preserve these three operations.
8. Associativity follows from uniqueness for n = 3 after restricting to G
   cubed. The unit and both inverse laws follow from uniqueness for n = 1.
   The prescribed maps to J coincide by its group laws. This proves every
   group diagram without an argument from density of underlying points.
9. B → K is localization at the nonzero elements, hence flat by
   lem-weil-pbc-localization-flat. Its spectrum and the projection H_K → H
   are flat by lem-weil-pbc-flat-ring-map-iff-flat-affine and
   lem-weil-pbc-flat-morphism-base-change. Apply degree-zero flat base change
   to j and the structure module, pulling back the unit isomorphism of step 3.
   This is exactly the canonical sheaf comparison on the generic fibre. -/
theorem relative_quasiAffine_group_envelope
    (B : Type u) [CommRing B] [IsDedekindDomain B]
    (K : Type u) [Field K] [Algebra B K] [IsFractionRing B K]
    (G J : Over (Spec (.of B))) [GrpObj G] [GrpObj J]
    [Flat G.hom] [IsSeparated G.hom]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [Flat J.hom] [IsSeparated J.hom]
    [LocallyOfFiniteType J.hom] [QuasiCompact J.hom]
    (f : G ⟶ J) [IsMonHom f] [IsQuasiAffineHom f.left] :
    (Scheme.CommAlgebraSheaf.toModule
      (Under.mk (⟨f.left.c⟩ : J.left.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} f.left.base).obj
          G.left.sheaf))).IsQuasicoherent ∧
    ∃ (H : Over (Spec (.of B))) (_ : GrpObj H) (q : H ⟶ J) (j : G ⟶ H)
      (hc : j.left ≫ q.left = f.left),
      IsMonHom j ∧ IsMonHom q ∧ IsAffineHom q.left ∧
      IsOpenImmersion j.left ∧ QuasiCompact j.left ∧
      ∃ a : (Under.mk (⟨f.left.c⟩ : J.left.sheaf ⟶
          (TopCat.Sheaf.pushforward CommRingCat.{u} f.left.base).obj G.left.sheaf) :
            J.left.CommAlgebraSheaf) ≅
        (Under.mk (⟨q.left.c⟩ : J.left.sheaf ⟶
          (TopCat.Sheaf.pushforward CommRingCat.{u} q.left.base).obj H.left.sheaf) :
            J.left.CommAlgebraSheaf),
        (∀ (W : J.left.Opens), IsAffineOpen W →
          IsIso ((q.left ⁻¹ᵁ W).toSpecΓ ≫ Spec.map (a.hom.right.hom.app (op W))) ∧
          j.left.resLE (q.left ⁻¹ᵁ W) (f.left ⁻¹ᵁ W)
              (by rw [← Scheme.Hom.comp_preimage, hc]) ≫
            (q.left ⁻¹ᵁ W).toSpecΓ ≫ Spec.map (a.hom.right.hom.app (op W)) =
          (f.left ⁻¹ᵁ W).toSpecΓ) ∧
        IsIso (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B K)))).map
          j).left.c) := by
  sorry

end AlgebraicGeometry
