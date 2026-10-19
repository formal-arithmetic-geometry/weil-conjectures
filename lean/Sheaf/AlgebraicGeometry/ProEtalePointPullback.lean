module

public import Mathlib.Topology.Category.Profinite.AsLimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all Sheaf.Paper.ProfiniteTestObjectFunctor

/-!
# Pullback from the pro-étale point

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
  sk-def-sfb-pullback-from-point/_section.md (blueprint: sk-def-sfb-pullback-from-point).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite

namespace AlgebraicGeometry.ProEtale

/-- The inverse image from the pro-étale point to a scheme.

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
  sk-def-sfb-pullback-from-point/_section.md, parts 2--4
  (blueprint: sk-def-sfb-pullback-from-point).
-/
noncomputable abbrev sfbPullbackFromPoint (X : Scheme.{u}) :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⥤
      Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  upperStarFromPoint X

/-- The direct image corresponding to the inverse image from the point.

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
  sk-def-sfb-pullback-from-point/_section.md, parts 3--4
  (blueprint: sk-def-sfb-pullback-from-point).
-/
noncomputable abbrev sfbPullbackFromPointRightAdjoint (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⥤
      Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  ProEtale.lowerStar Ab.{u + 1} (toSpecZ X) ⋙ pointLowerStar

/-- The site, test-object, adjunction, monoidal, and braided clauses of the
pullback-from-point construction.

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
  sk-def-sfb-pullback-from-point/_section.md, parts 1--4
  (blueprint: sk-def-sfb-pullback-from-point).

The displayed formulas `Spec LC(S, ℤ) = lim_i ∐_{S_i} Spec ℤ` and
`X[S] = lim_i ∐_{S_i} X` are the canonical isomorphisms: the image of the cone
`(Profinite.asLimitCone S)` over the finite quotients `S_i` of `S` is a limit cone, the
functor preserves finite coproducts (a finite discrete `S_i` is the coproduct of
its points), and the value at the one-point space is `Spec ℤ`, resp. `X`, via the
structure morphism.  The monoidal structure of `p^*` is the oplax structure of
`pointUpperStarLowerStarAdjunction` with invertible comparisons, and the braiding
clauses are stated for the canonical (instance) monoidal structures.

Proof: The structure morphisms are unique because `specZ` is terminal.  The
weakly étale spectrum construction and its finite-limit, cover-preserving, and
continuity declarations give part 1.  The ring `LC(S, ℤ)` is the filtered
colimit of the rings `LC(S_i, ℤ) = ℤ^{S_i}`, and `Spec` sends it to the limit of
the spectra; `LC(-, ℤ)` sends a finite disjoint union to the product of rings,
which `Spec` sends to the coproduct; and `LC(*, ℤ) = ℤ`.  This is the
inverse-limit formula of part 1.  The relative test object is
`profiniteToProEtOf`, and its base-change definition gives part 2; base change
along `π_X` preserves the cofiltered limit and the finite coproducts, and
`Spec ℤ ×_{Spec ℤ} X = X`, which gives `X[S] = lim_i ∐_{S_i} X`.  The point
inverse image and its right adjoint are `pointUpperStar`, `pointLowerStar`, and
`pointUpperStarLowerStarAdjunction`; the comparisons of the adjoint oplax
structure are invertible, and their inverses with the published braiding
compatibility give the strong monoidal and braided structures.  Finally
`sfbPullbackFromPoint` is the
composite with the scheme pullback, while the composite of the two adjunctions
gives its displayed right adjoint and left-adjoint structure.  Evaluation of
that right adjoint is restriction to `(profiniteToProEtOf X).obj S`.
-/
theorem sfbPullbackFromPoint_spec :
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
      f ≫ toSpecZ Y = toSpecZ X) ∧
    (∀ (S : Profinite.{u}),
      Nonempty (IsLimit (profiniteToScheme.{u}.mapCone (Profinite.asLimitCone S)))) ∧
    PreservesFiniteCoproducts profiniteToScheme.{u} ∧
    IsIso (toSpecZ (profiniteToScheme.{u}.obj (Profinite.of PUnit.{u + 1}))) ∧
    (∀ (S : Profinite.{u}),
      WeaklyEtale (toSpecZ (profiniteToScheme.obj S))) ∧
    PreservesFiniteLimits profiniteToProEt.{u} ∧
    CoverPreserving (coherentTopology Profinite.{u})
      (Scheme.ProEt.topology specZ) profiniteToProEt ∧
    profiniteToProEt.IsContinuous (coherentTopology Profinite.{u})
      (Scheme.ProEt.topology specZ) ∧
    (∀ (X : Scheme.{u}) (S : Profinite.{u}),
      (profiniteToProEtOf X).obj S =
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).obj
          (profiniteToProEt.obj S)) ∧
    (∀ (X : Scheme.{u}) (S : Profinite.{u}),
      Nonempty (IsLimit ((profiniteToProEtOf X ⋙ Scheme.ProEt.forget X ⋙
        Over.forget X).mapCone (Profinite.asLimitCone S)))) ∧
    (∀ (X : Scheme.{u}),
      PreservesFiniteCoproducts (profiniteToProEtOf X ⋙ Scheme.ProEt.forget X ⋙
        Over.forget X)) ∧
    (∀ (X : Scheme.{u}),
      IsIso ((profiniteToProEtOf X).obj (Profinite.of PUnit.{u + 1})).hom) ∧
    Nonempty (pointUpperStar.{u} ⊣ pointLowerStar) ∧
    pointUpperStar.{u}.IsLeftAdjoint ∧
    IsIso (Functor.OplaxMonoidal.η pointUpperStar.{u}) ∧
    (∀ (F G : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}),
      IsIso (Functor.OplaxMonoidal.δ pointUpperStar F G)) ∧
    Nonempty pointUpperStar.{u}.Monoidal ∧
    (∀ (F G : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}),
      Functor.LaxMonoidal.μ pointUpperStar F G ≫ pointUpperStar.map (β_ F G).hom =
        (β_ (pointUpperStar.obj F) (pointUpperStar.obj G)).hom ≫
          Functor.LaxMonoidal.μ pointUpperStar G F) ∧
    (∀ (X : Scheme.{u}),
      sfbPullbackFromPoint X =
        pointUpperStar ⋙ (toSpecZ X)^*[Ab.{u + 1}]) ∧
    (∀ (X : Scheme.{u}), (sfbPullbackFromPoint X).IsLeftAdjoint) ∧
    (∀ (X : Scheme.{u}), Nonempty (sfbPullbackFromPoint X).Monoidal) ∧
    (∀ (X : Scheme.{u}) (F G : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}),
      Functor.LaxMonoidal.μ (sfbPullbackFromPoint X) F G ≫
          (sfbPullbackFromPoint X).map (β_ F G).hom =
        (β_ ((sfbPullbackFromPoint X).obj F) ((sfbPullbackFromPoint X).obj G)).hom ≫
          Functor.LaxMonoidal.μ (sfbPullbackFromPoint X) G F) ∧
    (∀ (X : Scheme.{u}) (G : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (S : Profinite.{u}),
      ((sfbPullbackFromPointRightAdjoint X).obj G).obj.obj (op S) =
        G.obj.obj (op ((profiniteToProEtOf X).obj S))) ∧
    (∀ (X : Scheme.{u}),
      Nonempty (sfbPullbackFromPoint X ⊣ sfbPullbackFromPointRightAdjoint X)) := by
  -- The existing test-object theorem gives limits over X; forgetting preserves
  -- these connected limits. Its Spec Z comparison gives the absolute formula.
  have hlim (X : Scheme.{u}) (S : Profinite.{u}) :
      Nonempty (IsLimit ((profiniteToProEtOf X ⋙ Scheme.ProEt.forget X ⋙
        Over.forget X).mapCone S.asLimitCone)) := by
    have : IsConnected (DiscreteQuotient S) := IsCofiltered.isConnected _
    have hs (i : DiscreteQuotient S) : Function.Surjective (S.asLimitCone.π.app i) :=
      i.proj_surjective
    exact ⟨isLimitOfPreserves (Over.forget X)
      ((profinite_test_object_functor X).2.2.2.1 _ S.fintypeDiagram
        S.asLimitCone S.asLimit hs).some⟩
  -- Use continuity into the subcanonical scheme site to preserve disjoint unions.
  have hcop (X : Scheme.{u}) :
      PreservesFiniteCoproducts (profiniteToProEtOf X ⋙ Scheme.ProEt.forget X ⋙
        Over.forget X) := by
    let F := profiniteToProEtOf X ⋙ Scheme.ProEt.forget X ⋙ Over.forget X
    have : (profiniteToProEtOf X).IsContinuous (coherentTopology Profinite)
        (Scheme.ProEt.topology X) := by
      have := Scheme.ProEt.isContinuous_overPullback (toSpecZ X)
      unfold profiniteToProEtOf
      exact Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology specZ) _
    have : F.IsContinuous (coherentTopology Profinite) Scheme.proetaleTopology :=
      Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology X) _
    refine ⟨fun n ↦ ?_⟩
    have : PreservesColimitsOfShape (Discrete (ULift.{u} (Fin n))) F :=
      coproducts_of_continuous F Scheme.proetaleTopology _
    exact preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) F
  -- Finite-limit preservation sends the singleton to the terminal object over X.
  have hpoint (X : Scheme.{u}) :
      IsIso ((profiniteToProEtOf X).obj (Profinite.of PUnit.{u + 1})).hom := by
    let F := profiniteToProEtOf X ⋙ Scheme.ProEt.forget X
    have : PreservesFiniteLimits F := by
      have := (profinite_test_object_functor X).1
      dsimp [F]
      infer_instance
    have hterm : IsTerminal (F.obj (Profinite.of PUnit.{u + 1})) :=
      Profinite.isTerminalPUnit.isTerminalObj F _
    have : IsIso (Over.homMk ((profiniteToProEtOf X).obj
        (Profinite.of PUnit.{u + 1})).hom : F.obj (Profinite.of PUnit.{u + 1}) ⟶
          Over.mk (𝟙 X)) := isIso_of_isTerminal hterm Over.mkIdTerminal _
    exact inferInstanceAs (IsIso ((Over.forget X).map
      (Over.homMk ((profiniteToProEtOf X).obj (Profinite.of PUnit.{u + 1})).hom :
        F.obj (Profinite.of PUnit.{u + 1}) ⟶ Over.mk (𝟙 X))))
  let e := (profinite_test_object_functor specZ.{u}).2.2.2.2.2.some
  refine ⟨fun _ _ f ↦ comp_toSpecZ f, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S
    exact ⟨IsLimit.mapConeEquiv e (hlim specZ S).some⟩
  · have := hcop specZ.{u}
    exact ⟨fun n ↦ preservesColimitsOfShape_of_natIso e⟩
  · have : PreservesFiniteLimits profiniteToScheme.{u} := by
      have : (Over.forget specZ.{u}).IsEquivalence :=
        (Over.equivalenceOfIsTerminal specULiftZIsTerminal).isEquivalence_functor
      change PreservesFiniteLimits
        (profiniteToProEt ⋙ Scheme.ProEt.forget specZ ⋙ Over.forget specZ)
      infer_instance
    exact isIso_of_isTerminal
      (Profinite.isTerminalPUnit.isTerminalObj profiniteToScheme _)
      specULiftZIsTerminal _
  · intro S
    infer_instance
  · infer_instance
  · exact coverPreserving_profiniteToProEt
  · infer_instance
  · intro X S
    rfl
  · exact hlim
  · exact hcop
  · exact hpoint
  · exact ⟨pointUpperStarLowerStarAdjunction⟩
  · exact pointUpperStarLowerStarAdjunction.isLeftAdjoint
  · infer_instance
  · intro F G
    infer_instance
  · exact ⟨inferInstance⟩
  · intro F G
    exact Functor.LaxBraided.braided F G
  · intro X
    rfl
  · intro X
    exact (pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).isLeftAdjoint
  · intro X
    exact ⟨inferInstance⟩
  · intro X F G
    exact Functor.LaxBraided.braided F G
  · intro X G S
    rfl
  · intro X
    exact ⟨pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))⟩

end AlgebraicGeometry.ProEtale
