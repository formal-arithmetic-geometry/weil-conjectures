module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Representatives of restricted cohomology classes from a supplied filtered colimit

Source: Stacks Project, Tag 03Q5 (lemma-colimit-cohomology), with the colimit
preservation and module compatibility used in the proof of Tag 03SA(3).
(blueprint: lem-weil-pbc-constructible-restriction-class-core).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- A class in the restriction of a supplied filtered colimit of module sheaves is
represented at one of its stages. The diagram objects need not be constructible.
Source: Stacks Project, Tag 03Q5 (lemma-colimit-cohomology); used after Tag 03SA(3).
(blueprint: lem-weil-pbc-constructible-restriction-class-core)

Proof:
1. Choose the colimit witness in `hc`. Forget the module structure of the cocone:
   forgetting modules preserves colimits (`lem-weil-pbc-module-sheaves-colimits-forgetful`).
2. Abelian inverse image is a left adjoint and preserves colimits
   (`lem-weil-pbc-inverse-image-preserves-colimits`). The natural compatibility of
   module inverse image with forgetting (`prop-weil-pbc-inverse-image-modules-exact`,
   clause 2) identifies this colimit cocone with the cocone whose legs are the underlying
   abelian restrictions of `ι.app a`. Naturality identifies every leg, not just the vertex.
3. Apply the canonical filtered-colimit cohomology comparison on the qcqs scheme X₀
   (`lem-weil-pbc-cohomology-filtered-colimit`, Tag 03Q5). In degree q this gives a
   colimit cocone of abelian groups, with vertex H^q of the underlying restriction of F
   and legs H^q of the underlying restrictions of `ι.app a`.
4. The forgetful functor from abelian groups to sets preserves filtered colimits.
   `CategoryTheory.Limits.Concrete.isColimit_exists_rep` (node
   `lem-category-theory-concrete-iscolimit-exists-rep`) therefore supplies a stage a
   and an element z whose image under that leg is c. By the identification of the legs
   in steps 2 and 3, its equality is exactly the displayed `Sheaf.H.map` equality.

Filteredness includes nonemptiness, so a zero class also has a stage (take z = 0).
For an empty X₀ or the zero coefficient ring all these cohomology classes are zero,
so the same argument applies. For a one-object identity presentation take z = c.
No properness, injectivity, or constructibility assumption is used. The remaining
formal work includes reconciling the u+1-sized index with the current u-sized derived
cohomology comparison, and its natural identification with `Sheaf.H`. -/
theorem exists_restriction_class_of_filtered_presentation
    {X X₀ : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace X₀] [QuasiSeparatedSpace X₀] (i : X₀ ⟶ X)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {A : Type (u + 1)} [SmallCategory A] [IsFiltered A]
    {D : A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (ι : D ⟶ (Functor.const A).obj F)
    (hc : Nonempty (IsColimit (Cocone.mk F ι)))
    (q : ℕ)
    (c : Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj ((i)^*[ModuleCat.{u + 1} Λ].obj F)) q) :
    ∃ (a : A) (z : Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj ((i)^*[ModuleCat.{u + 1} Λ].obj (D.obj a))) q),
      Sheaf.H.map ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
        AddCommGrpCat.{u + 1})).map ((i)^*[ModuleCat.{u + 1} Λ].map (ι.app a))) q z = c := by
  sorry

end AlgebraicGeometry.Etale
