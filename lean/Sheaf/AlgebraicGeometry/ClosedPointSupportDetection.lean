/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Sheaf.AlgebraicGeometry.EtaleSupport
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Sheaf.AlgebraicGeometry.ClosedPointSupportGlobalGeneration
import Sheaf.AlgebraicGeometry.ClosedPointSupportVanishing
import Sheaf.AlgebraicGeometry.UnboundedEtaleCohomologyAcyclicBasis

/-!
# Detection of derived etale sheaves supported at closed points

Source: Stacks Project, Tag 0F1G, Lemma 59.97.4; blueprint
`sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-0f1g.md`
(blueprint: lem-kun-0f1g).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem support_upperStar_subset_closedPoints {X Y : Scheme.{u}}
    (f : Y ⟶ X) [Etale f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Scheme.etaleSheafSupport F ⊆ closedPoints X) :
    Scheme.etaleSheafSupport ((upperStar AddCommGrpCat.{u + 1} f).obj F) ⊆
      closedPoints Y := by
  rintro y ⟨Ω, hΩ, haΩ, s, hs, hn⟩
  have hx : f y ∈ closedPoints X := by
    apply hF
    refine ⟨Ω, hΩ, haΩ, s ≫ f, ?_, ?_⟩
    · simp [hs]
    · intro hz
      exact hn (hz.of_iso ((upperStarCompSheafFiberIso
        AddCommGrpCat.{u + 1} f s).app F))
  exact isClosed_of_subset_discrete_closed
    (Set.singleton_subset_iff.mpr (by simp))
    (f.isDiscrete_preimage_singleton (f y)) (hx.preimage f.continuous)

private theorem quasiCompact_cover (X : Scheme.{u}) (V : X.Etale) :
    ∃ (ι : Type (u + 1)) (W : ι → X.Etale) (f : ∀ i : ι, W i ⟶ V),
      (∀ i : ι, CompactSpace (W i).left) ∧
        Sieve.ofArrows W f ∈ X.smallEtaleTopology V := by
  let ι := ULift.{u + 1} V.left.affineCover.I₀
  let W : ι → X.Etale := fun i ↦
    Scheme.Etale.mk (V.left.affineCover.f i.down ≫ V.hom)
  let f : ∀ i, W i ⟶ V := fun i ↦
    MorphismProperty.Over.homMk (V.left.affineCover.f i.down)
  refine ⟨ι, W, f, ?_, ?_⟩
  · intro i
    change CompactSpace (V.left.affineCover.X i.down)
    infer_instance
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr
    ext y
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, hi⟩ := V.left.affineCover.exists_eq y
    exact ⟨⟨i⟩, hi⟩

private theorem subsingleton_H_of_isZero_cohomology (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ) (hp : 0 < p)
    (hz : IsZero ((cohomology AddCommGrpCat.{u + 1} X (p : ℤ)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F))) : Subsingleton (Sheaf.H F p) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  let G := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (Opposite.op (Scheme.Etale.mk (𝟙 X)))
  let e : G ≅ E := Sheaf.ΓNatIsoSheafSections _ _
    (MorphismProperty.Over.mkIdTerminal _ _)
  let d : G.rightDerived (n + 1) ≅ E.rightDerived (n + 1) :=
    { hom := e.hom.rightDerived (n + 1)
      inv := e.inv.rightDerived (n + 1)
      hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id,
        NatTrans.rightDerived_id]
      inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id,
        NatTrans.rightDerived_id] }
  have hz' := hz.of_iso (G.homologyRightDerivedFunctorObjSingleFunctorIso F (n + 1)).symm
  have hzE := hz'.of_iso (d.app F).symm
  obtain ⟨a⟩ := Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
    X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X))
    (MorphismProperty.Over.mkIdTerminal _ _) F n
  have := AddCommGrpCat.subsingleton_of_isZero hzE
  exact a.injective.subsingleton

private theorem isZero_of_globallyGenerated_sections (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hgen : Scheme.IsGloballyGeneratedAbelianEtaleSheaf F)
    (hz : IsZero (F.obj.obj (Opposite.op (Scheme.Etale.mk (𝟙 X))))) : IsZero F := by
  have hsec : Subsingleton (F.obj.obj (Opposite.op (Scheme.Etale.mk (𝟙 X)))) :=
    AddCommGrpCat.subsingleton_of_isZero hz
  change Subsingleton (F.obj.obj (Opposite.op (Scheme.Etale.mk (𝟙 X)))) at hsec
  let : Subsingleton (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat).obj F).obj
      (Opposite.op (Scheme.Etale.mk (𝟙 X)))) := hsec
  have heval : Scheme.etaleAbelianGlobalSectionsEvaluation F = 0 := by
    unfold Scheme.etaleAbelianGlobalSectionsEvaluation
    rw [Equiv.symm_apply_eq]
    rw [Adjunction.homAddEquiv_zero]
    ext t
    exact Subsingleton.elim _ _
  have : Epi (Scheme.etaleAbelianGlobalSectionsEvaluation F) := hgen
  rw [heval] at ‹Epi (Scheme.etaleAbelianGlobalSectionsEvaluation F)›
  exact Limits.IsZero.of_epi_zero
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of ((F.obj.obj (Opposite.op (Scheme.Etale.mk (𝟙 X)))) →₀ ℤ))) F

/-- Over a separably closed field, an unbounded derived abelian etale sheaf supported
at closed points vanishes if and only if all its global hypercohomology groups vanish.
The support hypothesis uses the union of the geometric-stalk supports of all cohomology
sheaves. Exactness of geometric stalks identifies this with the condition that the derived
stalk can be nonzero only at a closed point.

Source: Stacks Project, Tag 0F1G, Lemma 59.97.4
(blueprint: lem-kun-0f1g).

Proof plan:
1. If `Q` is zero, take its zero K-injective representative. Its complex of sections
   is zero, so every global hypercohomology group is zero (`def-kun-rgamma-unbounded`).
2. Set `F_q = H^q(Q)`. By `lem-kun-stalks-of-cohomology`, the stalk of `F_q` is the
   cohomology of the stalk of `Q`. Thus each `F_q` is supported at closed points, in
   the sense of `def-kun-support`.
3. Use the quasi-compact objects of the small etale site as a covering basis. Affine
   opens cover every object (`lem-weil-pbc-affine-opens-basis`) and are quasi-compact
   (`lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`). Their inclusions and
   composites are etale (`lem-weil-pbc-etale-composition-cancellation`), giving covers
   in `def-weil-pbc-etale-site`. Each such object is of finite type over the field:
   etale maps are locally of finite presentation (`lem-kun-etale-lfp`), finite-type
   algebras compose by adjoining their finite lists of generators, and the source is
   quasi-compact (`def-weil-finite-type-morphism`). The basis includes `X` itself.
4. For a basis object `j : U → X`, restriction is inverse image
   (`lem-weil-pbc-etale-inverse-image-restriction`), and the stalk at a geometric point
   of `U` equals the stalk at its image (`lem-kun-stalk-as-pullback` and
   `lem-weil-pbc-inverse-image-composition`). A nonzero stalk therefore maps to a
   closed point `x` of `X`. Passing to affine neighborhoods, etale composition and
   cancellation reduce to an etale algebra. Its residue-field extension is finite
   separable (`lem-weil-pbc-etale-algebra-residue-field-separable`). Since `κ(x)` is
   finite over the base field (`lem-kun-closed-point-field`), the residue field at
   the original point is also finite over it. The same closed-point criterion on
   the finite-type scheme `U` makes that point closed. Hence `F_q|_U` has closed-point
   support as well.
5. By `lem-kun-0f1f-vanish`, each restricted `F_q` has no positive-degree cohomology
   on every basis object. Apply `lem-kun-0bkz` to this basis and the unbounded object
   `Q` to identify `H^q(X,Q)` with `H^0(X,F_q)`. Degree-zero sheaf cohomology is ordinary
   sections: an injective resolution starts with the sheaf as the first kernel, and
   sections preserve kernels. Thus all the sections of every `F_q` vanish.
6. By `lem-kun-0f1f-gen` and `def-kun-global-generated`, the evaluation map from the
   sum indexed by global sections onto `F_q` is an epimorphism. All these sections
   are zero, so this evaluation is zero. Cancellation then gives `id(F_q) = 0`,
   hence `F_q` is zero for every integer `q`.
7. Finally `lem-kun-d-zero-cohomology` implies that `Q` is zero. No lower bound,
   torsion condition, or constructibility assumption is used. -/
theorem isZero_iff_cohomology_of_support_closedPoints
    {K : Type u} [Field K] [IsSepClosed K]
    (X : Scheme.{u}) [X.Over (Spec (.of K))]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))]
    (Q : _root_.DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hQ : X.etaleComplexSupport Q ⊆ closedPoints X) :
    IsZero Q ↔ ∀ i : ℤ, IsZero ((cohomology AddCommGrpCat.{u + 1} X i).obj Q) := by
  constructor
  · intro hz i
    let : (cohomology AddCommGrpCat.{u + 1} X i).PreservesZeroMorphisms := by
      dsimp [cohomology, rightDerivedGlobalSections]
      infer_instance
    exact (cohomology AddCommGrpCat.{u + 1} X i).map_isZero hz
  · intro hzero
    have hsupport (q : ℤ) : Scheme.etaleSheafSupport
        ((DerivedCategory.homologyFunctor _ q).obj Q) ⊆ closedPoints X := by
      intro x hx
      apply hQ
      exact Set.mem_iUnion.mpr ⟨q, hx⟩
    let B : Set X.Etale := {U | CompactSpace U.left}
    have hacyclic (U : X.Etale) (hU : U ∈ B) (p : ℕ) (hp : 0 < p) (q : ℤ) :
        Subsingleton (Sheaf.H ((upperStar AddCommGrpCat.{u + 1} U.hom).obj
          ((DerivedCategory.homologyFunctor _ q).obj Q)) p) := by
      let : CompactSpace U.left := hU
      let : LocallyOfFiniteType U.hom := inferInstance
      let : LocallyOfFiniteType (U.hom ≫ (X ↘ Spec (.of K))) := inferInstance
      let : U.left.Over (Spec (.of K)) := ⟨U.hom ≫ (X ↘ Spec (.of K))⟩
      have : LocallyOfFiniteType (U.left ↘ Spec (.of K)) := by
        change LocallyOfFiniteType (U.hom ≫ (X ↘ Spec (.of K)))
        infer_instance
      have hs := support_upperStar_subset_closedPoints U.hom
        ((DerivedCategory.homologyFunctor _ q).obj Q) (hsupport q)
      exact subsingleton_H_of_isZero_cohomology _ _ p hp
        (isZero_cohomology_of_support_subset_closedPoints (K := K) U.left _ hs p hp)
    apply DerivedCategory.isZero_of_forall_isZero_homology Q
    intro q
    obtain ⟨eq⟩ := cohomology_iso_sections_of_acyclic_covering_class X Q B
      (quasiCompact_cover X) hacyclic (Scheme.Etale.mk (𝟙 X))
      (QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of K))) q
    let ei := (cohomology AddCommGrpCat.{u + 1} X q).mapIso
      ((Functor.mapDerivedCategoryNatIso (upperStarId AddCommGrpCat.{u + 1} X)).app Q ≪≫
        (Functor.mapDerivedCategoryIdIso _).app Q)
    have hsections := ((hzero q).of_iso ei).of_iso eq.symm
    exact isZero_of_globallyGenerated_sections X _
      (Scheme.isGloballyGeneratedAbelianEtaleSheaf_of_support_subset_closedPoints (K := K) X _
        (hsupport q)) hsections

end AlgebraicGeometry.Etale
