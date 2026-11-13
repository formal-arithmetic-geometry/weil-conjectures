/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveSetDescentInjective
import WeilConjectures.AlgebraicGeometry.GabberH0EtaleCoverSection
import WeilConjectures.AlgebraicGeometry.GabberH0ZariskiGluing
import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement

/-! # Finite-cover sections before imposing the descent equation

## References

* Stacks Project, Tag 09ZF.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- A section on the closed subscheme lifts after a finite surjective cover. (Stacks, Tag 09ZF) -/
theorem gabber_h0_finite_section
    {X Z : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hZar :
      letI : ∀ P : X.Opensᵒᵖ ⥤ Type (u + 1),
          (Opens.map (i.base : Z.toTopCat ⟶ X.toTopCat)).op.HasPointwiseLeftKanExtension P :=
            fun P U ↦
              @Types.hasColimit.{u, u + 1, u}
                (CostructuredArrow.{u, u, u, u} (Opens.map i.base).op U)
                inferInstance (small_succ.{u} _) (CostructuredArrow.proj _ U ⋙ P)
      ∀ G : TopCat.Sheaf (Type (u + 1)) X.toTopCat,
      Function.Bijective
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Opens.map (i.base : Z.toTopCat ⟶ X.toTopCat)) (Type (u + 1))
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z)).unit.app G).hom.app
            (op (⊤ : X.Opens))))
    (hFinite : ∀ (X' : Scheme.{u}) (h : X' ⟶ X) [IsFinite h],
      let b : CategoryTheory.Functor.{u, u, u, u} X'.Opens (pullback i h : Scheme.{u}).Opens :=
        Opens.map
        ((pullback.snd i h : (pullback i h : Scheme.{u}) ⟶ X').base)
      letI : ∀ P : X'.Opensᵒᵖ ⥤ Type (u + 1), b.op.HasPointwiseLeftKanExtension P :=
        fun P U ↦
          @Types.hasColimit.{u, u + 1, u} (CostructuredArrow.{u, u, u, u} b.op U)
            inferInstance (small_succ.{u} _) (CostructuredArrow.proj b.op U ⋙ P)
      ∀ G : TopCat.Sheaf (Type (u + 1)) X'.toTopCat,
        Function.Bijective
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            b (Type (u + 1)) (Opens.grothendieckTopology X')
            (Opens.grothendieckTopology (pullback i h : Scheme.{u}))).unit.app G).hom.app
              (op (⊤ : X'.Opens))))
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (t : ((Scheme.etaleSetPullback i).obj F).obj.obj
      (op ((MorphismProperty.Over.pullback @Etale ⊤ i).obj (Scheme.Etale.mk (𝟙 X))))) :
    ∃ (X' : Scheme.{u}) (h : X' ⟶ X) (_ : IsFinite h) (_ : Surjective h)
      (s' : ((Scheme.etaleSetPullback h).obj F).obj.obj
        (op ((MorphismProperty.Over.pullback @Etale ⊤ h).obj (Scheme.Etale.mk (𝟙 X))))),
      etaleSetDescentComparison i (pullback.fst i h) F (Scheme.Etale.mk (𝟙 X)) t =
        eqToHom (congrArg
          (fun k : pullback i h ⟶ X ↦ ((Scheme.etaleSetPullback k).obj F).obj.obj
            (op ((MorphismProperty.Over.pullback @Etale ⊤ k).obj
              (Scheme.Etale.mk (𝟙 X))))) (pullback.condition (f := i) (g := h)).symm)
          (etaleSetDescentComparison h (pullback.snd i h) F (Scheme.Etale.mk (𝟙 X)) s') := by
  obtain ⟨U, q, hq, hqsurj, s, hs⟩ :=
    gabber_h0_etale_cover_section i (fun G ↦ (hZar G).injective) F t
  let : Etale q := hq
  let : Surjective q := hqsurj
  obtain ⟨X', h, hh, _, hsurj, J, _, W, phi, hW, hphi⟩ :=
    Scheme.exists_finite_surjective_refinement_of_etale q
  let : IsFinite h := hh
  obtain ⟨G, lift, compare, sigma, hsigma, hunit⟩ :=
    gabber_h0_zariski_gluing i q h F t s hs J W phi hW hphi
  obtain ⟨a, ha⟩ := (hFinite X' h G).surjective sigma
  refine ⟨X', h, hh, hsurj, lift a, ?_⟩
  exact hsigma.symm.trans ((congrArg compare ha).symm.trans (hunit a))

end AlgebraicGeometry
