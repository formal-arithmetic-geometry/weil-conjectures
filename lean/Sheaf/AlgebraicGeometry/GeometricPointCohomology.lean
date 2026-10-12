module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.AlgebraicGeometry.KInjectiveResolutions
import Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants
import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport

/-!
# Étale cohomology of one geometric point

Source: Stacks Project, Étale Cohomology, Theorem 03QT, Lemmas 03QU and 04JM,
Section 03QQ (specialized to an algebraically closed field)
(blueprint: lem-weil-pbc-geometric-point-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For the spectrum of an algebraically closed field, étale cohomology is concentrated
in degree zero, and degree zero is the geometric stalk. The isomorphism is natural in
an abelian étale sheaf. The proof follows Lemma 03QU using Lemma 04JM: the absolute
Galois group is trivial, global sections identify with the chosen geometric stalk,
and the stalk functor is exact; exactness gives the vanishing in positive degrees and
identifies degree zero with the displayed stalk.
(blueprint: lem-weil-pbc-geometric-point-cohomology)
-/
theorem geometricPoint_etaleCohomology
    (k : Type u) [Field k] [IsAlgClosed k]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (cbar : Spec (.of Ω) ⟶ Spec (.of k))
    :
    (∀ (q : ℤ), 0 < q →
      ∀ (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat),
        IsZero ((Etale.cohomology AddCommGrpCat (Spec (.of k)) q).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))) ∧
    ∃ α : ∀ F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat,
      (Etale.cohomology AddCommGrpCat (Spec (.of k)) 0).obj
          ((DerivedCategory.singleFunctor _ 0).obj F) ≅
        (Scheme.pointSmallEtale cbar).sheafFiber.obj F,
      ∀ (F G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat)
        (f : F ⟶ G),
        (α F).hom ≫ (Scheme.pointSmallEtale cbar).sheafFiber.map f =
          (Etale.cohomology AddCommGrpCat (Spec (.of k)) 0).map
              ((DerivedCategory.singleFunctor _ 0).map f) ≫ (α G).hom := by
  sorry

end AlgebraicGeometry
