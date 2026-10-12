module

public import Sheaf.Paper.LocalStalkSectionsComparisonMap

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

/-- A section on an affine neighbourhood that pulls back to zero on the local scheme
vanishes after shrinking the neighbourhood.
Source: Stacks Project, Tag 03Q6, Lemma 59.51.5, degree zero.
(blueprint: new-local-stalk-sections-affine-vanishing)

Proof: Write the affine neighbourhood A as Spec R and the point as a prime p.
The principal opens D(f), f outside p, form a directed system with coordinate-ring
colimit R_p. Restrict F to the small etale site of A. Apply degree-zero continuity
in Tag 03Q6 to the identity of A and the system R_f: this identity is quasi-compact
and quasi-separated. Restriction along an open immersion identifies sections of
the inverse image with F evaluated on that open. The continuity comparison sends
our section to its pullback on Spec R_p. Since this pullback is zero, the section
is zero at some principal-open stage. That principal open contains x and is the
required smaller neighbourhood. The identification Spec R_p = Spec(O_X,x) respects
the maps into A and X. For the arbitrary supplied left adjoint H, uniqueness of
left adjoints gives an isomorphism to the usual inverse image commuting with units;
therefore vanishing under the displayed cocone is precisely the vanishing used by
continuity. The zero section itself needs no shrinking, and an empty affine open
cannot be a neighbourhood of x. -/
theorem localStalkSections_affine_vanishing
    {X : Scheme.{u + 1}} (i : X.Opens ⥤ X.Etale)
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor) (x : X)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (Spec (X.presheaf.stalk x)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ (X.fromSpecStalk x).Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology
      (Spec (X.presheaf.stalk x)).smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (A : (OpenNhds x)ᵒᵖ) (hA : IsAffineOpen A.unop.1)
    (s : (LocalStalkSections.neighbourhoodDiagram i x F).obj A)
    (hs : (LocalStalkSections.cocone i hi x H hH F).ι.app A s = 0) :
    ∃ (W : (OpenNhds x)ᵒᵖ) (f : A ⟶ W),
      (LocalStalkSections.neighbourhoodDiagram i x F).map f s = 0 := by
  sorry
