module

public import WeilConjectures.ConstructibleSheaf.Defs

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Finite constant local models exist on a trivializing cover.

Source: Stacks Project, Tag 03RV, local-model step, with the geometric stalk
comparison of Tag 03Q1.
(blueprint: lem-weil-pbc-finite-locally-constant-sets-local-models)

Proof: Choose the cover in hloc. The essential-image definition of IsConstant
supplies a value S and an isomorphism to the constant sheaf on the localized site.
For a nonempty member U, choose a point and an algebraic closure of its residue
field in universe u. This gives a geometric point of U and, by composition, of T.
The stalk of E restricted to U at this point is the stalk of E at the composed
point: pointed etale neighbourhoods are compared by fibre products. Sheafification
preserves stalks, and the filtered colimit of the constant diagram S over pointed
neighbourhoods is S. Thus the local isomorphism identifies S with a stalk of E.
The hypothesis hfin makes this stalk finitely generated as a set, equivalently
finite, so S is finite. Discard the empty members of the cover; its nonempty members
still jointly cover T. Their index set is a subtype in universe u, hence gives a
Cover of the required universe. If T is empty this subtype is empty, and the
conclusion is vacuous on the empty cover. Values may be empty, and different
members may have different finite cardinalities; no uniform bound is needed. -/
theorem finiteLocallyConstant_exists_local_models
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (hloc : ∃ 𝒰 : Cover.{u} etalePrecoverage T, ∀ i,
      (E.over (𝒰.etalePrecoverageToEtale i)).IsConstant
        (T.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i)))
    (hfin : IsFiniteSheaf E) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage T, ∀ i,
      ∃ S : Type (u + 1), Finite S ∧
        Nonempty ((E.over (𝒰.etalePrecoverageToEtale i)) ≅
          (constantSheaf (T.smallEtaleTopology.over
            (𝒰.etalePrecoverageToEtale i)) (Type (u + 1))).obj S) := by
  sorry

end AlgebraicGeometry.Scheme
