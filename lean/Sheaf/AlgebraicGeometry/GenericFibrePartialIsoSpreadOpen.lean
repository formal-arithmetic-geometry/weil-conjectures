/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Spreading a partial isomorphism of generic fibres to a common open

Source: Stacks Project, Tag 0559, first proof, the common-open paragraph;
Tag 0552, the finite-generator common-localization argument;
Tag 01ZM, morphism descent and eventual equality.
(blueprint: lem-sbc-generic-fibre-partial-iso-spread-open)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- A partial isomorphism of nonempty generic fibres of finitely presented affine
families spreads to a common open over the original integral affine base.

Source: Stacks Project, Tag 0559, first proof, the common-open paragraph; Tag 0552;
Tag 01ZM, morphism descent and eventual equality.
Proof: Write the families as Spec B and Spec C over S = Spec A, and identify the
generic residue field with Frac(A). The supplied partial isomorphism identifies
dense opens of Spec(B tensor_A Frac(A)) and Spec(C tensor_A Frac(A)). Its source
open is nonempty by density and the nonempty generic source. Choose a point in
it and principal affine neighbourhoods U and T on the source and target sides,
contained in the supplied opens. Under the partial isomorphism, restrict U and
T to their common intersection. This intersection is affine: both U and the
inverse image of T are affine opens in the separated affine generic source.
Its target image is affine as well. These are quasi-compact opens of the generic
fibres, hence are finite unions of principal opens in the ambient affines.
Lift their finitely many defining functions to B and C after a nonzero base
localization. The resulting quasi-compact opens are of finite presentation over
the localized base, since the ambient affine families are finitely presented.
Their generic restrictions are exactly the two isomorphic affine opens chosen
above. Apply morphism descent and eventual equality (Tag 01ZM) to descend the
two inverse maps, their inverse identities, and their equations over the base.
In algebraic terms, finite presentations give finitely many generator images
and relations, and only finitely many equalities must be imposed.
Thus, after inverting one common nonzero element a of A, all these maps and
identities hold over A[1/a]. Generic equalities are killed by nonzero base
elements, and only finitely many equalities have to be imposed.
This gives isomorphic opens in
the restrictions of X and Y over D(a). These restrictions and their opens are
open subschemes of the original X and Y. Take their source open V and compose
the isomorphism with the target inclusion to get i. The maps are over S by the
same generator relations. The descended source still has the chosen nonempty
generic open, so eta is in the image of V -> S. Vertical components and
nilpotents in the special fibres cause no problem: generic equalities involving
them are killed by the same base localization. The empty generic fibre is
explicitly excluded by the nonempty hypothesis.

(blueprint: lem-sbc-generic-fibre-partial-iso-spread-open) -/
theorem exists_open_of_generic_fibre_partial_iso
    {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine S] [IsIntegral S]
    (f : X ⟶ S) (g : Y ⟶ S)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g]
    (η : S) (hη : IsGenericPoint η Set.univ) [Nonempty (f.fiber η)]
    (p : (f.fiber η).PartialIso (g.fiber η))
    (hp : p.IsOver (f.fiberToSpecResidueField η) (g.fiberToSpecResidueField η)) :
    ∃ V : X.Opens, η ∈ Set.range (V.ι ≫ f) ∧
      ∃ i : V.toScheme ⟶ Y, IsOpenImmersion i ∧ i ≫ g = V.ι ≫ f := by sorry

end AlgebraicGeometry
