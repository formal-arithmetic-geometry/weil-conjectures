/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q142
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.ConstructibleSheaf.Pullback

/-!
# Transfer of a constructible stratification through etale-local isomorphisms

Source: Stacks Project, Etale Cohomology, Tag 03RU, module-sheaf clause, and its
cover-refinement consequence on a fixed constructible stratification
(blueprint: lem-sf-etale-local-isomorphism-constructible).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Transport a constant model on the localized site to the small etale site. -/
private noncomputable def chartModelToPullback
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale)
    (M : ModuleCat.{u + 1} Λ)
    (e : H.over V ≅
      (constantSheaf (X.smallEtaleTopology.over V) (ModuleCat.{u + 1} Λ)).obj M) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom).obj H ≅
      (constantSheaf V.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M :=
  (overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} Λ) V H).symm ≪≫
    (Etale.overSheafEquiv V (ModuleCat.{u + 1} Λ)).functor.mapIso e ≪≫
    ((Etale.overEquiv V).constantSheafSheafCongrIso
      (X.smallEtaleTopology.over V) V.left.smallEtaleTopology
      (ModuleCat.{u + 1} Λ) Over.mkIdTerminal).app M

/-- Transport a constant model on the small etale site back to the localized site. -/
private noncomputable def pullbackModelToChart
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (V : X.Etale)
    (M : ModuleCat.{u + 1} Λ)
    (e : (Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom).obj H ≅
      (constantSheaf V.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :
    H.over V ≅
      (constantSheaf (X.smallEtaleTopology.over V) (ModuleCat.{u + 1} Λ)).obj M :=
  (Etale.overSheafEquiv V (ModuleCat.{u + 1} Λ)).functor.preimageIso
    (overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} Λ) V H ≪≫ e ≪≫
      (((Etale.overEquiv V).constantSheafSheafCongrIso
        (X.smallEtaleTopology.over V) V.left.smallEtaleTopology
        (ModuleCat.{u + 1} Λ) Over.mkIdTerminal).app M).symm)

/-- A fixed constructible stratification for `G` also trivializes `F` when the two
module sheaves are isomorphic after inverse image to each member of an arbitrary
jointly surjective etale family. The conclusion uses the same `S`, including its
stratum schemes and immersions, and the finite-constant-value clause of
`IsConstructibleEtaleModuleSheaf`. No overlap compatibility is assumed.

Source: Stacks Project, Tag 03RU, module-sheaf clause
(blueprint: lem-sf-etale-local-isomorphism-constructible).

Proof:
1. Fix a stratum `i : Z ⟶ X`. Its given trivialization supplies an etale cover
   `v_b : V_b ⟶ Z` and finite modules `M_b`. The inverse-image/restriction comparison
   of lem-weil-pbc-etale-inverse-image-restriction identifies the local restriction
   with `v_b⁻¹ i⁻¹ G`. Naturality for multiplication by each scalar makes this
   comparison module-linear, using prop-weil-pbc-inverse-image-modules-exact;
   constant sections generate the constant ring sheaf by sheafification.
2. Pull the supplied covering back to each `V_b`. The maps
   `q_bj : W_bj = V_b ×_X U_j ⟶ V_b` form a cover by
   lem-weil-pbc-etale-covering-base-change. Their composites with `v_b` cover `Z`
   by lem-weil-pbc-etale-covering-composition, without extracting a finite subcover.
3. Write `r_bj : W_bj ⟶ U_j`. The module-linear composition comparisons of
   lem-weil-pbc-inverse-image-composition-module-linear-core, the given local
   isomorphism pulled back along `r_bj`, and the trivialization of step 1 give
   `(v_b q_bj)⁻¹ i⁻¹ F ≅ r_bj⁻¹ u_j⁻¹ F ≅ r_bj⁻¹ u_j⁻¹ G
     ≅ q_bj⁻¹ v_b⁻¹ i⁻¹ G ≅ q_bj⁻¹ (constant M_b) ≅ constant M_b`.
   The last arrow is lemma-constructible-pullback-constant for `ModuleCat Λ`.
4. Convert inverse image along the etale chart back to restriction using step 1's
   comparison. The resulting finite constant models witness exactly clause (b)
   of def-weil-pbc-etale-constructible-sheaf on this stratum. Repeat for every
   `k : Fin S.n`. The partition and constructible parts are the given ones;
   no gluing equation for the independently chosen trivializations is needed. -/
theorem etaleLocalIsomorphismConstructible
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (S : Stratification X)
    (hSc : ∀ k : Fin S.n, Topology.IsConstructible (S.stratum k))
    (hG : ∀ k : Fin S.n,
      ∃ d : LocallyConstantDatum ((Etale.upperStar (ModuleCat.{u + 1} Λ)
          (S.immersion k)).obj G),
        ∀ b : d.cover.I₀, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
          Nonempty ((((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).obj G).over
              (d.cover.etalePrecoverageToEtale b)) ≅
            (constantSheaf ((S.domain k).smallEtaleTopology.over
              (d.cover.etalePrecoverageToEtale b)) (ModuleCat.{u + 1} Λ)).obj M))
    (J : Type v) (U : J → Scheme.{u}) (uMap : ∀ j : J, U j ⟶ X)
    (hEt : ∀ j : J, Etale (uMap j))
    (hcover : ∀ x : X, ∃ j : J, x ∈ Set.range (uMap j))
    (hiso : ∀ j : J, Nonempty
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (uMap j)).obj F ≅
        (Etale.upperStar (ModuleCat.{u + 1} Λ) (uMap j)).obj G)) :
    ∀ k : Fin S.n,
      ∃ d : LocallyConstantDatum ((Etale.upperStar (ModuleCat.{u + 1} Λ)
          (S.immersion k)).obj F),
        ∀ b : d.cover.I₀, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
          Nonempty ((((Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion k)).obj F).over
              (d.cover.etalePrecoverageToEtale b)) ≅
            (constantSheaf ((S.domain k).smallEtaleTopology.over
              (d.cover.etalePrecoverageToEtale b)) (ModuleCat.{u + 1} Λ)).obj M) := by
  classical
  have _ := hSc
  let A := ModuleCat.{u + 1} Λ
  let C₀ : Cover.{v} (precoverage @Etale) X :=
    Cover.mkOfCovers J U uMap (fun x ↦ by
      obtain ⟨j, y, hy⟩ := hcover x
      exact ⟨j, y, hy⟩) hEt
  let C := C₀.ulift
  intro k
  obtain ⟨d, hd⟩ := hG k
  let i := S.immersion k
  let H := (Etale.upperStar A i).obj F
  let K := (Etale.upperStar A i).obj G
  have : etalePrecoverage.{u}.IsStableUnderComposition :=
    inferInstanceAs (precoverage @Etale).IsStableUnderComposition
  let R (b : d.cover.I₀) : Cover.{u} etalePrecoverage (d.cover.X b) :=
    C.pullback₂ (d.cover.f b ≫ i)
  let D : Cover.{u} etalePrecoverage (S.domain k) := d.cover.bind R
  have models : ∀ p : D.I₀, ∃ M : A, Finite M ∧
      Nonempty (H.over (D.etalePrecoverageToEtale p) ≅
        (constantSheaf ((S.domain k).smallEtaleTopology.over
          (D.etalePrecoverageToEtale p)) A).obj M) := by
    rintro ⟨b, c⟩
    obtain ⟨M, hM, ⟨eM⟩⟩ := hd b
    let q := Limits.pullback.snd (C.f c) (d.cover.f b ≫ i)
    let r := Limits.pullback.fst (C.f c) (d.cover.f b ≫ i)
    let h := q ≫ d.cover.f b
    have w : h ≫ i = r ≫ C.f c := by
      dsimp [h, q, r]
      rw [Category.assoc, Limits.pullback.condition]
    let e (T : Sheaf X.smallEtaleTopology A) :
        (Etale.upperStar A h).obj ((Etale.upperStar A i).obj T) ≅
          (Etale.upperStar A r).obj ((Etale.upperStar A (C.f c)).obj T) :=
      ((Etale.upperStarComp A h i).app T).symm ≪≫
        eqToIso (congrArg (fun f ↦ (Etale.upperStar A f).obj T) w) ≪≫
        (Etale.upperStarComp A r (C.f c)).app T
    let eK := chartModelToPullback K (d.cover.etalePrecoverageToEtale b) M eM
    let eH : (Etale.upperStar A h).obj H ≅
        (constantSheaf _ A).obj M :=
      e F ≪≫ (Etale.upperStar A r).mapIso (hiso (C₀.idx c)).some ≪≫ (e G).symm ≪≫
        (Etale.upperStarComp A q (d.cover.f b)).app K ≪≫
        (Etale.upperStar A q).mapIso eK ≪≫ (upperStarConstantSheafIso A q).app M
    exact ⟨M, hM, ⟨pullbackModelToChart H (D.etalePrecoverageToEtale ⟨b, c⟩) M eH⟩⟩
  refine ⟨⟨D, fun p ↦ ?_⟩, models⟩
  obtain ⟨M, _, ⟨e⟩⟩ := models p
  exact Sheaf.isConstant_of_iso _ e

end AlgebraicGeometry.Scheme
