/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Filtration


public import WeilConjectures.Topology.Sheaves.PushforwardCohomology
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.CategoryTheory.CanonicalFiltration
import WeilConjectures.Topology.TopologicalInducedCohomologyCocycle
import WeilConjectures.Topology.TopologicalLerayBottomRealization

/-! # Leray spectral sequence for a continuous map of spaces

The first-quadrant Leray spectral sequence `E₂^{a,b} = H^a(X, R^b f_* F) ⇒ H^{a+b}(Z, F)` of a
continuous map `f : Z ⟶ X`, with its canonical bottom edge.

## Implementation details

The spectral sequence lives in the abelian category of functors from abelian sheaves
on the source to abelian groups. Thus its differentials, page identifications, filtration
subobjects, graded isomorphisms and edge maps are all natural in the sheaf. It is the
Grothendieck spectral sequence for direct image followed by global sections: direct image
preserves injectives, which are acyclic for global sections.

## References

* [Stacks Project, Tags 01F2, 01DZ and 015N](https://stacks.math.columbia.edu/tag/01F2)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace CategoryTheory

/-- Direct image of abelian sheaves is additive, being precomposition on sections. -/
theorem topological_pushforwardAb_additive {Z X : TopCat.{u}} (f : Z ⟶ X) :
    (TopCat.Sheaf.pushforwardAb f).Additive := by
  constructor
  intro F G α β
  ext U
  rfl

attribute [instance] topological_pushforwardAb_additive

/-- The functorial first-quadrant Leray spectral sequence, including its canonical bottom edge.

`HX` and `HZ` are identified by equality with the recorded cohomology functors evaluated
at the terminal opens (their values are `Sheaf.H'`). They are not arbitrary abutments.
The bottom transition is specified by the cycles-to-homology projection and the spectral
sequence's own page isomorphism. Its iterates `b` start with the identity on page two.
The isomorphism `k` identifies the stable bottom term with the final nonzero filtration step,
compatibly with the graded quotient `g`. The resulting map `edge` is characterized on
injective-resolution cocycles using the canonical map `a` of free abelian terminal sheaves.
This is precisely the map induced by `f`, with no acyclicity hypothesis on the sheaf. -/
theorem exists_topological_leray_spectralSequence {Z X : TopCat.{u}} (f : Z ⟶ X) :
    ∃ HX : ℕ → (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}),
      ∃ HZ : ℕ → (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}),
        ∃ hX : ∀ n, HX n = Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n ⋙
          (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤),
        ∃ hZ : ∀ n, HZ n = Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Z) n ⋙
          (evaluation (Opens Z)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤),
        ∃ E : E₂CohomologicalSpectralSequenceNat
            (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u}),
          ∃ e₂ : ∀ a b : ℕ, (E.page 2).X (a, b) ≅
              (TopCat.Sheaf.pushforwardAb f).rightDerived b ⋙ HX a,
            (∀ a b : ℕ, ∃ (R : ℤ) (_hR : 2 ≤ R), ∀ (r : ℤ) (hr : R ≤ r),
              Nonempty ((E.page r (by omega)).X (a, b) ≅ E.pageInfinity (a, b))) ∧
            ∃ T : ∀ n : ℕ, DecreasingFiltration (HZ n),
              (∀ n, (T n).step 0 = ⊤) ∧
              (∀ n, (T n).step (n + 1) = ⊥) ∧
              ∃ g : ∀ p q : ℕ, (T (p + q)).gradedPiece p ≅ E.pageInfinity (p, q),
                ∃ e₀ : ∀ p : ℕ,
                    TopCat.Sheaf.pushforwardAb f ⋙ HX p ≅ (E.page 2).X (p, 0),
                  (∀ p, (e₀ p).hom =
                    Functor.whiskerRight (TopCat.Sheaf.pushforwardAb f).toRightDerivedZero
                      (HX p) ≫ (e₂ p 0).inv) ∧
                  ∃ t : ∀ (p : ℕ) (r : ℤ) (hr : 2 ≤ r),
                      (E.page r).X (p, 0) ⟶ (E.page (r + 1)).X (p, 0),
                    (∀ (p : ℕ) (r : ℤ) (hr : 2 ≤ r),
                      (E.page r).iCycles (p, 0) ≫ t p r hr =
                        (E.page r).homologyπ (p, 0) ≫ (E.iso r (r + 1) (p, 0)).hom) ∧
                    ∃ b : ∀ (p : ℕ) (r : ℤ) (hr : 2 ≤ r),
                        (E.page 2).X (p, 0) ⟶ (E.page r).X (p, 0),
                      (∀ p, b p 2 (by omega) = 𝟙 _) ∧
                      (∀ (p : ℕ) (r : ℤ) (hr : 2 ≤ r),
                        b p (r + 1) (by omega) = b p r hr ≫ t p r hr) ∧
                      ∃ k : ∀ p : ℕ, E.pageInfinity (p, 0) ≅ ((T p).step p :
                          Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u} ⥤
                            AddCommGrpCat.{u}),
                        (∀ p, cokernel.π (Subobject.ofLE ((T p).step (p + 1))
                          ((T p).step p) ((T p).antitone_step (by omega))) ≫
                            (g p 0).hom = (k p).inv) ∧
                        ∃ edge : ∀ p : ℕ, TopCat.Sheaf.pushforwardAb f ⋙ HX p ⟶ HZ p,
                          (∀ p, edge p = (e₀ p).hom ≫ b p (p + 2) (by omega) ≫
                            (k p).hom ≫ ((T p).step p).arrow) ∧
                          ∃ a : (presheafToSheaf (Opens.grothendieckTopology X)
                              AddCommGrpCat.{u}).obj
                              (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶
                            (TopCat.Sheaf.pushforwardAb f).obj
                              ((presheafToSheaf (Opens.grothendieckTopology Z)
                                AddCommGrpCat.{u}).obj
                                (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)),
                            (∀ (U : Opens X) (h : U ⟶ (⊤ : Opens X)),
                              a.hom.app (op U)
                                ((toSheafify (Opens.grothendieckTopology X)
                                  (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free)).app
                                    (op U) (FreeAbelianGroup.of h)) =
                                (toSheafify (Opens.grothendieckTopology Z)
                                  (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free)).app
                                    (op ((Opens.map f).obj U))
                                    (FreeAbelianGroup.of ((Opens.map f).map h ≫
                                      eqToHom (Opens.map_top f)))) ∧
                            (∀ (F : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
                              (I : InjectiveResolution F)
                              (J : InjectiveResolution ((TopCat.Sheaf.pushforwardAb f).obj F))
                              (φ : J.cocomplex ⟶
                                ((TopCat.Sheaf.pushforwardAb f).mapHomologicalComplex
                                  (ComplexShape.up ℕ)).obj I.cocomplex)
                              (_hφ : J.ι.f 0 ≫ φ.f 0 =
                                (TopCat.Sheaf.pushforwardAb f).map (I.ι.f 0)) (p : ℕ)
                              (s : (presheafToSheaf (Opens.grothendieckTopology X)
                                AddCommGrpCat.{u}).obj
                                (yoneda.obj (⊤ : Opens X) ⋙ AddCommGrpCat.free) ⟶
                                  J.cocomplex.X p)
                              (hs : s ≫ J.cocomplex.d p (p + 1) = 0)
                              (z : (presheafToSheaf (Opens.grothendieckTopology Z)
                                AddCommGrpCat.{u}).obj
                                (yoneda.obj (⊤ : Opens Z) ⋙ AddCommGrpCat.free) ⟶
                                  I.cocomplex.X p)
                              (hz : z ≫ I.cocomplex.d p (p + 1) = 0)
                              (_hsz : a ≫ (TopCat.Sheaf.pushforwardAb f).map z = s ≫ φ.f p),
                              (eqToHom (congrArg (fun Q ↦ Q.obj F) (hZ p)))
                                ((edge p).app F
                                  ((eqToHom (congrArg (fun Q ↦ Q.obj
                                    ((TopCat.Sheaf.pushforwardAb f).obj F)) (hX p)).symm)
                                    (J.extMk s (p + 1) rfl hs))) =
                                  I.extMk z (p + 1) rfl hz) := by
  refine ⟨_, _, fun _ ↦ rfl, fun _ ↦ rfl, ?_⟩
  exact (exists_topological_induced_cohomology_cocycle f _ _ (fun _ ↦ rfl)
    (fun _ ↦ rfl)).elim fun edge h ↦ h.elim fun a h ↦
      (exists_topological_leray_bottom_realization f _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)
        edge a h.1 h.2).imp fun E ↦
          Exists.imp fun e₂ ↦
            And.imp_right <|
              Exists.imp fun T ↦
                And.imp_right <| And.imp_right <|
                  Exists.imp fun g ↦
                    Exists.imp fun e₀ ↦
                      And.imp_right <|
                        Exists.imp fun t ↦
                          And.imp_right <|
                            Exists.imp fun b ↦
                              And.imp_right <| And.imp_right <|
                                Exists.imp fun k ↦
                                  And.imp_right fun he ↦ ⟨edge, he, a, h.1, h.2⟩

end CategoryTheory
