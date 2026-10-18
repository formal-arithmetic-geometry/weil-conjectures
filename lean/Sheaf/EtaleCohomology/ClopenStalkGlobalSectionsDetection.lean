/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.FieldTheory.IsSepClosed
import Mathlib.CategoryTheory.Filtered.Final
import Sheaf.AlgebraicGeometry.ClopenEtaleNeighbourhoodCofinality

/-!
# Clopen computation of geometric étale stalks

Source: Stacks Project, Tags 03PN, 09AY and 0EZV (blueprint:
lem-weil-pbc-clopen-stalk-global-sections-detection).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The clopen neighbourhoods of a point of a scheme.

Source: the clopen refinement in Tags 03PN and 0EZV
(blueprint: lem-weil-pbc-clopen-stalk-global-sections-detection). -/
def ClopenNeighbourhood (E : Scheme.{u}) (z : E) :=
  {W : E.Opens // IsClopen (W : Set E) ∧ z ∈ W}

/-- Inclusion orders the clopen neighbourhoods.
Source: Tags 03PN and 0EZV
(blueprint: lem-weil-pbc-clopen-stalk-global-sections-detection). -/
instance clopenNeighbourhoodPartialOrder (E : Scheme.{u}) (z : E) :
    PartialOrder (ClopenNeighbourhood E z) where
  le a b := a.1 ≤ b.1
  le_refl := by intro a; exact le_rfl
  le_trans := by intro a b c h₁ h₂; exact le_trans h₁ h₂
  le_antisymm := by intro a b h₁ h₂; exact Subtype.ext (le_antisymm h₁ h₂)

/-- The étale site object associated with a clopen neighbourhood.
Source: Tags 03PN and 0EZV
(blueprint: lem-weil-pbc-clopen-stalk-global-sections-detection). -/
noncomputable def clopenEtaleObject (E : Scheme.{u}) (z : E)
    (W : ClopenNeighbourhood E z) : E.Etale :=
  Etale.mk W.1.ι

/-- The restriction arrow associated with an inclusion of clopen neighbourhoods
Source: the clopen refinement in Tags 03PN and 0EZV
(blueprint: lem-weil-pbc-clopen-stalk-global-sections-detection). -/
noncomputable def clopenEtaleMap (E : Scheme.{u}) (z : E)
    {W V : ClopenNeighbourhood E z} (f : W ⟶ V) :
    clopenEtaleObject E z W ⟶ clopenEtaleObject E z V := by
  refine MorphismProperty.Over.homMk (E.homOfLE f.le) ?_
  exact Scheme.homOfLE_ι E f.le

/-- The diagram of sections over clopen neighbourhoods of a point
Source: Tags 03PN and 040R
(blueprint: lem-weil-pbc-clopen-stalk-global-sections-detection). -/
noncomputable def clopenSectionDiagram (E : Scheme.{u}) (z : E)
    (G : Sheaf E.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (ClopenNeighbourhood E z)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj W := G.1.obj (Opposite.op (clopenEtaleObject E z W.unop))
  map f := G.1.map (Opposite.op (clopenEtaleMap E z f.unop))
  map_id W := by
    change G.1.map (Opposite.op (clopenEtaleMap E z (𝟙 W.unop))) = _
    have h : clopenEtaleMap E z (𝟙 W.unop) =
        𝟙 (clopenEtaleObject E z W.unop) := by
      apply MorphismProperty.Over.Hom.ext
      exact Scheme.homOfLE_rfl E W.unop.1
    rw [h]
    change G.1.map (𝟙 (Opposite.op (clopenEtaleObject E z W.unop))) = 𝟙 _
    exact G.1.map_id _
  map_comp f g := by
    change G.1.map (Opposite.op (clopenEtaleMap E z (g.unop ≫ f.unop))) = _
    have h : clopenEtaleMap E z (g.unop ≫ f.unop) =
        clopenEtaleMap E z g.unop ≫ clopenEtaleMap E z f.unop := by
      apply MorphismProperty.Over.Hom.ext
      change E.homOfLE (g.unop.le.trans f.unop.le) =
        E.homOfLE g.unop.le ≫ E.homOfLE f.unop.le
      exact (Scheme.homOfLE_homOfLE E g.unop.le f.unop.le).symm
    rw [h]
    rw [← G.1.map_comp]
    rfl

/-- The factorisation of a geometric point through a clopen neighbourhood
Source: Tags 03PN and 0EZV
(blueprint: lem-weil-pbc-clopen-stalk-global-sections-detection). -/
noncomputable def clopenPointLift {Ω : Type u} [Field Ω]
    {E : Scheme.{u}} {z : E} (W : ClopenNeighbourhood E z)
    (zbar : Spec (.of Ω) ⟶ E)
    (hzbar : zbar.toLRSHom.base =
      TopCat.ofHom ⟨fun _ : (Spec (.of Ω) : Type u) => z, continuous_const⟩) :
    Spec (.of Ω) ⟶ W.1.toScheme :=
  IsOpenImmersion.lift W.1.ι zbar (by
    rw [Set.range_subset_iff]
    intro x
    rw [hzbar]
    exact ⟨⟨z, W.2.2⟩, rfl⟩)

/-- The canonical marking of the clopen étale neighbourhood by the geometric point.
Source: Tags 03PN and 040R
(blueprint: lem-weil-pbc-clopen-stalk-global-sections-detection). -/
noncomputable def clopenPointMarking {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {E : Scheme.{u}} {z : E} (W : ClopenNeighbourhood E z)
    (zbar : Spec (.of Ω) ⟶ E)
    (hzbar : zbar.toLRSHom.base =
      TopCat.ofHom ⟨fun _ : (Spec (.of Ω) : Type u) => z, continuous_const⟩) :
    (pointSmallEtale zbar).fiber.obj (clopenEtaleObject E z W) :=
  Over.homMk (clopenPointLift W zbar hzbar) (by apply IsOpenImmersion.lift_fac)

/-- The canonical germ homomorphism from sections on a site object to its geometric stalk
Source: Tags 03PN and 040R
(blueprint: lem-weil-pbc-clopen-stalk-global-sections-detection). -/
noncomputable def geometricGerm {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {E : Scheme.{u}} (zbar : Spec (.of Ω) ⟶ E)
    (G : Sheaf E.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    G.1.obj (Opposite.op (Etale.mk (𝟙 E))) ⟶
      (pointSmallEtale zbar).sheafFiber.obj G :=
  (pointSmallEtale zbar).toPresheafFiber (Etale.mk (𝟙 E))
    (Over.homMk zbar) G.1

/--
Under the hypotheses of the clopen refinement, the clopen sections compute every
geometric stalk, and global sections surject onto it.  The final clause is the
one-point spectrum case.

Source: Stacks Project, Tags 03PN, 09AY and 0EZV; agent-written clopen refinement
of the stalk argument (blueprint: lem-weil-pbc-clopen-stalk-global-sections-detection).

Proof:
1. The clopen neighbourhoods form a cofiltered category.  The cofinality
statement [lem-weil-pbc-clopen-etale-neighbourhood-cofinality] and the
initial-functor criterion [lem-weil-pbc-initial-functor-cofiltered-criterion]
identify the colimit of the clopen section diagram with the geometric stalk
[def-weil-pbc-geometric-stalks].
2. A clopen section extends by zero across its clopen complement, using
[lem-weil-pbc-open-immersion-etale], [def-weil-pbc-etale-site], and the sheaf
condition [def-weil-pbc-abelian-etale-sheaves], so every clopen colimit component
lies in the image of the global germ map.
3. The colimit universal property and the quotient by that image show that the
global germ map is surjective; a zero global group therefore has zero stalk.
4. For the spectrum of the field itself there is one point and one clopen
neighbourhood, so the germ map is an isomorphism.
-/
theorem clopenStalkGlobalSectionsDetection
    (K C : Type u) [Field K] [CommRing C] [Algebra K C] [IsSepClosed K]
    (hlocal : ∀ z : PrimeSpectrum C,
      Function.Bijective
        (@algebraMap K (Localization.AtPrime z.1) _ _ _))
    (hclopen : ∀ (U : (Spec (.of C)).Opens) (z : PrimeSpectrum C), z ∈ U →
      ∃ W : (Spec (.of C)).Opens,
        IsClopen (W : Set (Spec (.of C))) ∧ z ∈ W ∧ W ≤ U)
    (G : Sheaf (Spec (.of C)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (∀ (z : PrimeSpectrum C) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (zbar : Spec (.of Ω) ⟶ Spec (.of C))
      (hzbar : zbar.toLRSHom.base =
      TopCat.ofHom ⟨fun _ : (Spec (.of Ω) : Type u) => z, continuous_const⟩),
      ∃ e : colimit (clopenSectionDiagram (Spec (.of C)) z G) ≅
          (pointSmallEtale zbar).sheafFiber.obj G,
        ∀ W : ClopenNeighbourhood (Spec (.of C)) z,
          colimit.ι (clopenSectionDiagram (Spec (.of C)) z G) (Opposite.op W) ≫ e.hom =
            (pointSmallEtale zbar).toPresheafFiber (clopenEtaleObject (Spec (.of C)) z W)
              (clopenPointMarking W zbar hzbar) G.1) ∧
    (∀ (z : PrimeSpectrum C) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (zbar : Spec (.of Ω) ⟶ Spec (.of C))
      (hzbar : zbar.toLRSHom.base =
      TopCat.ofHom ⟨fun _ : (Spec (.of Ω) : Type u) => z, continuous_const⟩),
      Function.Surjective (geometricGerm zbar G)) ∧
    (Subsingleton (G.1.obj (Opposite.op (Etale.mk (𝟙 (Spec (.of C)))))).carrier →
      ∀ (z : PrimeSpectrum C) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (zbar : Spec (.of Ω) ⟶ Spec (.of C))
        (hzbar : zbar.toLRSHom.base =
      TopCat.ofHom ⟨fun _ : (Spec (.of Ω) : Type u) => z, continuous_const⟩),
        Subsingleton ((pointSmallEtale zbar).sheafFiber.obj G).carrier) ∧
    (∀ (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (tbar : Spec (.of Ω) ⟶ Spec (.of K)),
      IsIso (geometricGerm tbar F)) := by
  sorry

end AlgebraicGeometry.Scheme
