module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

import Sheaf.AlgebraicGeometry.GenericFlatFinitePresentation

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry

/-- Affine radicial preparation with a universal homeomorphism onto the original
base-changed family, before the final generic-flat shrinking.

Source: Stacks Project, Tag 0559, second proof, through its finite purely inseparable
extension construction; Tags 051T and 052A for the first generic-flat shrinking.
Proof: the geometrically irreducible generic fibre is nonempty, so its image puts
η in V. Factor f through V and reduce both affine schemes. A map from a reduced
scheme factors through the reduction of its target. The reduced base is integral
because η is generic. Both reduction maps are surjective closed immersions and
hence universal homeomorphisms. The reduced family is locally of finite type and
quasi-compact, since its source and target are affine. Apply generic flat finite
presentation and choose a principal open containing the generic point inside the
resulting open. This principal open can be lifted to a principal open U of V:
its defining element lifts from the reduced coordinate ring. Its inverse image
in the affine source is affine. Write the resulting base ring as A, its fraction
field as K, and the reduced flat source ring as B. Flatness makes B inject into
B tensor_A K. That generic ring is a domain, since it is reduced and irreducible.
Let L be its fraction field. The field argument in Tag 0559 gives a finite purely
inseparable K'/K for which the reduction of L tensor_K K' is a separably generated
field. In characteristic zero take K'=K. Choose field generators b_i of K'/K with
b_i^q_i=a_i/d_i in K, and replace them by d_i*b_i. Their q_i-th powers now lie in
A. The A-subalgebra A' they generate inside K' is a finite integral domain with
fraction field K', and Spec A' to Spec A is a universal homeomorphism: the integral
extension is surjective on spectra and purely inseparable on all residue fields.
Set S=Spec A' and compose this map with the base reduction map to obtain q to U.
Set Y to the reduction of X tensor_T S, and let h be its canonical reduction map.
Then h is a universal homeomorphism and g=h followed by the pullback projection.
Affineness, reducedness, and local finite type follow from this construction.
At the generic point of S, the coordinate ring of Y is the reduction of the
original generic ring tensored with K'. Reduction and localization commute.
This ring embeds in the reduction of L tensor_K K': before reduction the tensor
map is injective, and an element of a subring is nilpotent exactly when its image
is nilpotent. The latter reduced tensor ring is a separably generated field,
hence geometrically reduced. Tensoring this injection with any extension of K'
remains injective, proving geometric reducedness of the generic fibre of Y.
The homeomorphism q uniquely lifts η to the generic point of S. No second flat
shrinking is made. Empty special fibres cause no problem. Every scheme here has
an explicit spectrum, pullback, or reduction construction; no definition chooses
an arbitrary object from this unproved existence theorem.

(blueprint: lem-sbc-radicial-preparation-construction) -/
theorem exists_radicial_preparation_construction
    {X T : Scheme.{u}} [IsAffine X] (f : X ⟶ T) [LocallyOfFiniteType f]
    (V : T.Opens) (hV : IsAffineOpen V) (himage : Set.range f ⊆ V)
    (η : T) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (f.fiberToSpecResidueField η)) :
    ∃ (U : T.Opens), η ∈ U ∧ IsAffineOpen U ∧
      ∃ (S Y : Scheme.{u}) (q : S ⟶ U.toScheme) (g : Y ⟶ S),
        IsAffine S ∧ IsIntegral S ∧ IsAffine Y ∧ IsReduced Y ∧
        IsUniversalHomeomorphism q ∧ LocallyOfFiniteType g ∧
        ∃ η' : S, IsGenericPoint η' Set.univ ∧ (q ≫ U.ι) η' = η ∧
          GeometricallyReduced (g.fiberToSpecResidueField η') ∧
          ∃ h : Y ⟶ pullback f (q ≫ U.ι),
            IsUniversalHomeomorphism h ∧ h ≫ pullback.snd f (q ≫ U.ι) = g := by sorry

end AlgebraicGeometry
