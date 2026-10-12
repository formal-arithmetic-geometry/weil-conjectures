module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.ConstructibleSheaf.Defs
import Sheaf.AlgebraicGeometry.ConstantSheafSetsRepresentable
import Sheaf.AlgebraicGeometry.FiniteEtaleDescent

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Effective descent glues finite constant local models into a finite etale scheme.

Source: Stacks Project, Tag 03RV, converse descent part.
(blueprint: lem-weil-pbc-finite-locally-constant-sets-descent)

Proof: Choose the cover and local values in hlocal. Replace each finite S in
universe u+1 by ULift of Fin n for its cardinality n, transporting the constant
sheaf by this equivalence. The equivalence between the site localized at U -> T
and the small etale site of U identifies the given restriction with this constant
sheaf. Apply constantSheaf_sets_representable to Fin n: its representative is the
coproduct of n copies of U with the codiagonal. This morphism is finite and etale,
including n=0. On overlaps the two restrictions both identify with the restriction
of E. Yoneda full faithfulness turns their comparison into a unique isomorphism of
representing schemes; its faithfulness gives the cocycle on triple overlaps.
Take the coproduct of the cover members. It is an etale surjection onto T. The
coproduct of the local representatives is finite etale over it, since the preimage
of each open component is the corresponding finite etale representative. The
overlap isomorphisms give a descent datum on this object. Apply finiteEtaleDescent
to obtain a finite etale scheme P over T with these local representatives.
The local isomorphisms of presheaves agree by the chosen datum; the sheaf condition
on E and the subcanonical small etale topology glue them and their inverses.
This yields the displayed isomorphism with uliftYoneda of Etale.mk pi. If the
cover is empty, T is empty; use the empty scheme and the unique sheaf on its
small etale site. No quasi-compactness of T or bound on the local ranks is used. -/
theorem finiteLocallyConstant_descent_of_local_models
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (hlocal : ∃ 𝒰 : Cover.{u} etalePrecoverage T, ∀ i,
      ∃ S : Type (u + 1), Finite S ∧
        Nonempty ((E.over (𝒰.etalePrecoverageToEtale i)) ≅
          (constantSheaf (T.smallEtaleTopology.over
            (𝒰.etalePrecoverageToEtale i)) (Type (u + 1))).obj S)) :
    ∃ (P : Scheme.{u}) (π : P ⟶ T) (_ : IsFinite π) (_ : Etale π),
      Nonempty (E.obj ≅ uliftYoneda.{u + 1}.obj (Etale.mk π)) := by
  sorry

end AlgebraicGeometry.Scheme
