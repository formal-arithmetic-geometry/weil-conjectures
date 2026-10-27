module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.FiniteType

/-! # A finite separable field of definition for an abelian subvariety

Source: Milne, Abelian Varieties (January 2, 2022), Section 12, second unnumbered lemma
following Proposition 12.1, printed p.19; its finite separable field may be enlarged to
its finite normal closure. Supporting source: Milne, Abelian Varieties (2008), I Section 10.
(blueprint: lem-sfb-abelian-subvariety-separable-definition)

The cartesian square in the conclusion identifies the scalar extension of the descended
variety with the given variety. The additional equality makes that identification commute
with the inclusions into the original ambient variety. Thus it is equality of closed
subgroup schemes after base change, including their scheme structures.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry

/-- An abelian subvariety over an algebraic closure descends as a closed subgroup scheme
of the ambient abelian variety to a finite Galois intermediate field.

Source: Milne, Abelian Varieties (2022), Section 12, second unnumbered lemma after
Proposition 12.1, printed p.19, followed by finite normal closure.
(blueprint: lem-sfb-abelian-subvariety-separable-definition)

Proof:
1. In the relative separable closure of k in Ω, all prime-to-characteristic torsion
points of C are rational as points of A: A[n] is finite etale, and its coordinate
algebra is a product of finite separable fields (lem-sc-mult-n-etale-kernel and
lem-weil-pbc-etale-algebra-over-field-product). These points are dense in C by
lem-sfb-abelian-prime-to-torsion-dense.
2. C is reduced by sbc-lem-smooth-geometrically-reduced. Apply
lem-sfb-dense-rational-closed-subscheme-descent over the relative separable closure to
descend its closed subscheme. The ambient base change is an abelian variety by
lem-sfb-abelian-field-extension. On a finite affine cover, its defining ideals have
finitely many generators by lem-wf-affine-noetherian-components. Collect their finitely
many coefficients in the relative separable closure.
3. Use lem-weil-pbc-finite-set-in-finite-galois-subextension to place the coefficients
in a finite Galois intermediate field E. Generate the corresponding ideals over E.
They agree on overlaps because extension to the separable closure is faithfully flat:
injectivity of V → V ⊗ L for vector spaces reflects each ideal inclusion. Glue the
ideals to the closed subscheme C_E; its scalar extension is C with the specified inclusion.
4. Multiplication, inverse and unit restrict to C_E: their factorization through the
closed subscheme can be checked after the faithful field extension. The closed immersion
is a monomorphism, so the group identities descend as well (def-sc-group-scheme-subgroup).
5. The extension Ω/E is faithfully flat and its spectrum map is surjective
(lem-weil-pbc-field-extension-base-change-faithfully-flat and
lem-weil-pbc-faithfully-flat-surjective-spectrum). Smoothness descends by
lem-trf-smooth-fpqc-base-descent. Properness follows from the ambient abelian variety
and lem-weil-pbc-closed-immersion-proper. Connectedness descends along the surjective
projection from C. Hence C_E is an abelian variety, and the constructed square and
compatibility equation express its prescribed scalar extension. -/
theorem IsAbelianVariety.exists_finiteGalois_subvariety_definition
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]
    (C : Over (Spec (.of Ω))) [GrpObj C] [IsAbelianVariety C]
    (i : C ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).obj A)
    [IsClosedSubgroupScheme i] :
    ∃ E : IntermediateField k Ω, FiniteDimensional k E ∧ IsGalois k E ∧
      ∃ (C_E : Over (Spec (.of E))) (_ : GrpObj C_E) (_ : IsAbelianVariety C_E)
        (j : C_E ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k E)))).obj A)
        (_ : IsClosedSubgroupScheme j) (q : C.left ⟶ C_E.left),
        IsPullback q C.hom C_E.hom (Spec.map (CommRingCat.ofHom E.subtype)) ∧
          q ≫ j.left ≫ pullback.fst A.hom (Spec.map (CommRingCat.ofHom (algebraMap k E))) =
            i.left ≫ pullback.fst A.hom (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) := by
  sorry

end AlgebraicGeometry
