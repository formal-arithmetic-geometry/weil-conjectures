module

public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry

/-! # Evaluation formula for the canonical internal compact-support adjunction

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
lem-asd-internal-adjunction-evaluation.md (blueprint: lem-asd-internal-adjunction-evaluation).

## Main statements

* `internalAdjunctionEvaluation` states the tensor--Hom transpose formula for the
  canonical compact-support internal adjunction.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

-- Prefer the direct monoidal-localization instance to the enough-points reconstruction.
attribute [local instance high] GrothendieckTopology.W.monoidal

private theorem transpose_conjugate
    {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (t : L₂ ⟶ L₁)
    (Q : C) (K : D) (h : Q ⟶ R₁.obj K) :
    (b.homEquiv Q K).symm (h ≫ (conjugateEquiv a b t).app K) =
      t.app Q ≫ (a.homEquiv Q K).symm h := by
  rw [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    conjugateEquiv_counit, ← Category.assoc, t.naturality, Category.assoc,
    Adjunction.homEquiv_counit]

private theorem transpose_composite
    {C D E B : Type*} [Category* C] [Category* D] [Category* E] [Category* B]
    {L : C ⥤ D} {R : D ⥤ C} {T : D ⥤ E} {H : E ⥤ D}
    {F : E ⥤ B} {G : B ⥤ E} {L₂ : C ⥤ B} {R₂ : B ⥤ C}
    (c : L ⊣ R) (d : T ⊣ H) (e : F ⊣ G) (b : L₂ ⊣ R₂)
    (t : L₂ ⟶ L ⋙ T ⋙ F) (Q : C) (K : B)
    (h : Q ⟶ R.obj (H.obj (G.obj K))) :
    (b.homEquiv Q K).symm
        (h ≫ (conjugateEquiv (c.comp (d.comp e)) b t).app K) =
      t.app Q ≫ F.map ((d.homEquiv (L.obj Q) (G.obj K)).symm
        ((c.homEquiv Q (H.obj (G.obj K))).symm h)) ≫ e.counit.app K := by
  rw [transpose_conjugate (c.comp (d.comp e)) b t Q K h]
  simp only [Adjunction.comp_homEquiv, Equiv.symm_trans_apply]
  exact congrArg (fun k ↦ t.app Q ≫ k)
    (e.homEquiv_counit (T.obj (L.obj Q)) K
      ((d.homEquiv (L.obj Q) (G.obj K)).symm
        ((c.homEquiv Q (H.obj (G.obj K))).symm h)))

private theorem tensor_conjugate_evaluation
    {C D : Type*} [Category* C] [Category* D]
    {TX : C ⥤ C ⥤ C} {HX : Cᵒᵖ ⥤ C ⥤ C}
    {TS : D ⥤ D ⥤ D} {HS : Dᵒᵖ ⥤ D ⥤ D}
    {L : D ⥤ C} {R : C ⥤ D} {F : C ⥤ D} {G : D ⥤ C}
    (tX : TX ⊣₂ HX) (tS : TS ⊣₂ HS) (a : L ⊣ R) (c : F ⊣ G)
    (t : F ⋙ TS ≅ TX ⋙ (Functor.whiskeringLeft _ _ _).obj L ⋙
      (Functor.whiskeringRight _ _ _).obj F)
    (M : C) (K Q : D) (h : Q ⟶ R.obj ((HX.obj (op M)).obj (G.obj K))) :
    ((tS.adj (F.obj M)).homEquiv Q K).symm
        (h ≫ ((((tX.comp a c).conjugateIso (tS.precomp F) t).app (op M)).app K).hom) =
      (t.hom.app M).app Q ≫ F.map
        (((tX.adj M).homEquiv (L.obj Q) (G.obj K)).symm
          ((a.homEquiv Q ((HX.obj (op M)).obj (G.obj K))).symm h)) ≫ c.counit.app K := by
  change ((tS.adj (F.obj M)).homEquiv Q K).symm
    (h ≫ (conjugateEquiv (a.comp ((tX.adj M).comp c))
      (tS.adj (F.obj M)) (t.hom.app M)).app K) = _
  exact transpose_composite a (tX.adj M) c (tS.adj (F.obj M)) (t.hom.app M) Q K h

/-- The tensor--Hom transpose of the canonical compact-support internal adjunction is
obtained by the compact-support projection map, evaluation, and the exceptional counit.
Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
lem-asd-internal-adjunction-evaluation.md (blueprint: lem-asd-internal-adjunction-evaluation).

Proof: compose the ordinary inverse-image adjunction, the tensor--Hom adjunction,
the canonical projection isomorphism, and the exceptional adjunction. Naturality of
these Hom-bijections identifies the resulting representative with the canonical
internal-adjunction isomorphism `derivedHomRightDerivedLowerShriekIsoOfFinite` (the
recorded declaration of prop-asd-internal-adjunction: the conjugate of the projection map
along these adjunctions, invertible by `isIso_projectionMap_of_finite`); evaluating at
`h` gives the displayed composite. The projection map is the canonical one, and the
exceptional last arrow is its adjunction counit. Precomposing both sides with the
canonical symmetry `Q ⊗ Rf_!M ≅ Rf_!M ⊗ Q` renders the node's tensor order; on the
right this is the node's `Π_{f,Q,M}` followed by `Rf_!(p)`, the two inner symmetries of
the reordered projection map cancelling against the reordering of `p`.
-/
theorem internalAdjunctionEvaluation
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} (f : X ⟶ S) [HasCompactification f]
    [IsLocallyNoetherian X] [CompactSpace X]
    [IsLocallyNoetherian S] [CompactSpace S]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat A)))
    (K Q : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat A)))
    (h : Q ⟶
      (R((f)_*[ModuleCat A])).obj
        (((RHom(X)[ModuleCat A]).obj (op M)).obj
          ((R(f)^![ModuleCat A]).obj K))) :
    ((derivedTensorSymmetry (ModuleCat A) S).hom.app Q).app
        ((R(f)_![ModuleCat A]).obj M) ≫
      ((derivedTensorHomAdjunction (ModuleCat A) ((R(f)_![ModuleCat A]).obj M)).homEquiv
        Q K).symm
      (h ≫ (((derivedHomRightDerivedLowerShriekIsoOfFinite A f).app (op M)).app K).hom) =
      ((derivedTensorSymmetry (ModuleCat A) S).hom.app Q).app
        ((R(f)_![ModuleCat A]).obj M) ≫
        ((projectionMap (ModuleCat A) f).app M).app Q ≫
        (R(f)_![ModuleCat A]).map
          (((derivedTensorHomAdjunction (ModuleCat A) M).homEquiv
              (L((f)^*[ModuleCat A]).obj Q)
              ((R(f)^![ModuleCat A]).obj K)).symm
            (((derivedUpperStarLowerStarAdjunction (ModuleCat A) f).homEquiv
                Q (((RHom(X)[ModuleCat A]).obj (op M)).obj
                  ((R(f)^![ModuleCat A]).obj K))).symm h)) ≫
        (rightDerivedUpperShriekAdjunction (ModuleCat A) f).counit.app K := by
  have := isIso_projectionMap_of_finite A f
  apply congrArg (fun k :
      ((-⊗ᴸ-(S)[ModuleCat A]).obj ((R(f)_![ModuleCat A]).obj M)).obj Q ⟶ K ↦
    ((derivedTensorSymmetry (ModuleCat A) S).hom.app Q).app
      ((R(f)_![ModuleCat A]).obj M) ≫ k)
  exact tensor_conjugate_evaluation (derivedTensorHomAdjunction₂ (ModuleCat A) X)
      (derivedTensorHomAdjunction₂ (ModuleCat A) S)
      (derivedUpperStarLowerStarAdjunction (ModuleCat A) f)
      (rightDerivedUpperShriekAdjunction (ModuleCat A) f)
      (asIso (projectionMap (ModuleCat A) f)) M K Q h

end AlgebraicGeometry.Etale
