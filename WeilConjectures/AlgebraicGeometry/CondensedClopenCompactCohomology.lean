/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedClopenCompactDecomposition
public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactCohomology
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-! # Degreewise compact cohomology of a finite clopen decomposition

Source: latest blueprint, sec-deligne-laumon-general/sk-p-dl-general-relative-line/
lem-zl-affine-curve-hc2-purity.proof.md, second paragraph and empty-curve clause
(blueprint: lem-zl-condensed-clopen-compact-cohomology).

The theorem applies the specified derived comparison to every integer homology functor.
The resulting map is the degreewise image of the same comparison, and its Frobenius
identity is the image of the derived Frobenius identity.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace WeilConjectures.CondensedClopenCompact

/-- The elementary biproduct calculation in step 3 of the cohomology proof.
Equality on inclusions proves naturality of the canonical biproduct comparison;
applying the functor to the supplied intertwining equation finishes the calculation.
Source: Stacks Tag 0DLP and the node's proof, step 3
(blueprint: lem-zl-condensed-clopen-compact-cohomology). -/
private theorem map_biproduct_intertwining
    {C E : Type*} [Category C] [Category E]
    [HasZeroMorphisms C] [HasZeroMorphisms E]
    {J : Type*} (B : J → C) [HasBiproduct B]
    (H : C ⥤ E) [H.PreservesZeroMorphisms] [PreservesBiproduct B H]
    {T : C} (d : (⨁ B) ⟶ T) (a : T ⟶ T) (f : ∀ i, B i ⟶ B i)
    (hd : d ≫ a = biproduct.map f ≫ d) :
    ((H.mapBiproduct B).inv ≫ H.map d) ≫ H.map a =
      biproduct.map (fun i ↦ H.map (f i)) ≫ (H.mapBiproduct B).inv ≫ H.map d := by
  have hn : (H.mapBiproduct B).inv ≫ H.map (biproduct.map f) =
      biproduct.map (fun i ↦ H.map (f i)) ≫ (H.mapBiproduct B).inv := by
    apply biproduct.hom_ext'
    intro i
    simp only [Functor.mapBiproduct_inv, biproduct.ι_desc_assoc, biproduct.ι_map_assoc]
    rw [← H.map_comp, biproduct.ι_map, H.map_comp]
    simp only [biproduct.ι_desc]
  rw [Category.assoc, ← H.map_comp, hd, H.map_comp, ← Category.assoc, hn,
    Category.assoc]

set_option maxHeartbeats 4000000 in
-- Elaborating the fixed geometric comparison requires more than the default heartbeats.
/--
Degreewise compactly supported cohomology is the direct sum over a finite clopen
partition, compatibly with geometric Frobenius.

Source: latest blueprint, sec-deligne-laumon-general/sk-p-dl-general-relative-line/
lem-zl-affine-curve-hc2-purity.proof.md, second paragraph and empty-curve clause
(blueprint: lem-zl-condensed-clopen-compact-cohomology).

Proof plan:
1. Put B_i = RΓ_c(X_i,K_i), S = ⨁ B_i, and B = RΓ_c(X,K). The recorded
   condensed_clopen_compact_decomposition supplies beta = biproduct.desc of the
   boundedInclusion components, its inverse, natural projections, and the geometric
   Frobenius equation. The compact cohomology definition identifies H^r(B_i) and
   H^r(B) with the cohomology groups in the statement. Functoriality makes H^r(beta)
   invertible, with inverse H^r(beta inverse).
2. The additive-cohomology lemma lem-zl-derived-cohomology-additive applies to the
   ordinary derived category of Qbar_ell modules. Applying H^r to the biproduct
   projection/inclusion identities proves that the canonical map from the sum of
   H^r(B_i) to H^r(S) is invertible. This is (Functor.mapBiproduct H^r _).inv.
   Compose it with H^r(beta). Its component at i is H^r of the specified component
   inclusion, so the map is precisely the cohomology image of beta, not a chosen
   isomorphism of vector spaces.
3. Write F_S for the sum of the component actions. The identities F_S u_i = u_i F_i
   give H^r(F_S) a_r = a_r (sum H^r(F_i)) by equality on summands. Apply H^r to
   beta ≫ F_X = F_S ≫ beta and use this identity to obtain the displayed equation.
   The actions are exactly action from the derived comparison, with the restricted
   Weil structure fixed by pullSquare. The same beta and restricted structures are
   used for every integer degree.
4. For an empty partition the derived comparison gives B = 0. Additivity implies
   H^r(0) = 0 since its identity is the image of the zero identity. Thus both the
   empty biproduct and the target cohomology object are zero.
-/
theorem condensed_clopen_compact_cohomology
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
    (X : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (I : Type w) [Finite I]
    (U : I → Over (Spec (.of D.k₀))) (j : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (j i).left] [∀ i, IsClosedImmersion (j i).left]
    (hdisjoint : Pairwise fun i k ↦ Disjoint (Set.range (j i).left) (Set.range (j k).left))
    (hcover : (⋃ i, Set.range (j i).left) = Set.univ)
    (c : Compactification X.hom) :
    ∃ (t : PointTransport ell D.k (fieldFrobenius D))
      (hg : compactificationFrobenius D c ≫ (geometricCompactification D c).g =
        (geometricCompactification D c).g ≫
          Spec.map (CommRingCat.ofHom (fieldFrobenius D).toRingHom))
      (hi : (D.geometricFrobenius X).hom ≫ (geometricCompactification D c).i =
        (geometricCompactification D c).i ≫ compactificationFrobenius D c)
      (e : OpenTransport ell (geometricCompactification D c).i
        (D.geometricFrobenius X).hom (compactificationFrobenius D c) hi)
      (hj : ∀ i, (schemeFrobenius D (U i)) ≫ geometricInclusion D (j i) =
        geometricInclusion D (j i) ≫ (D.geometricFrobenius X).hom)
      (hci : ∀ i, (schemeFrobenius D (U i)) ≫
          ((geometricCompactification D c).precomp (geometricInclusion D (j i))).i =
        ((geometricCompactification D c).precomp (geometricInclusion D (j i))).i ≫
          compactificationFrobenius D c)
      (ei : ∀ i, OpenTransport ell
        ((geometricCompactification D c).precomp (geometricInclusion D (j i))).i
        (schemeFrobenius D (U i)) (compactificationFrobenius D c) (hci i)),
      (∀ K : ProEtale.BoundedConstructible
          (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ell)
            (D.geometricFiber X).left),
        ∀ theta : (pull ell (D.geometricFrobenius X).hom).obj K.obj ≅ K.obj,
          ∃ theta_i : ∀ i,
            (pull ell (schemeFrobenius D (U i))).obj
                ((pull ell (geometricInclusion D (j i))).obj K.obj) ≅
              (pull ell (geometricInclusion D (j i))).obj K.obj,
            (∀ i, theta_i i = ((pullSquare ell (hj i)).app K.obj).symm ≪≫
              (pull ell (geometricInclusion D (j i))).mapIso theta) ∧
            ∀ r : ℤ,
              IsIso ((Functor.mapBiproduct
                (DerivedCategory.homologyFunctor
                  (ModuleCat.{u + 1} (PadicAlgCl ell)) r)
                (fun i ↦ (componentSections ell D.k (geometricCompactification D c)
                  (geometricInclusion D (j i))).obj K)).inv ≫
                (DerivedCategory.homologyFunctor
                  (ModuleCat.{u + 1} (PadicAlgCl ell)) r).map
                  (biproduct.desc (fun i ↦
                    (boundedInclusion ell D.k (geometricCompactification D c)
                      (geometricInclusion D (j i))).app K))) ∧
              ((Functor.mapBiproduct
                (DerivedCategory.homologyFunctor
                  (ModuleCat.{u + 1} (PadicAlgCl ell)) r)
                (fun i ↦ (componentSections ell D.k (geometricCompactification D c)
                  (geometricInclusion D (j i))).obj K)).inv ≫
                (DerivedCategory.homologyFunctor
                  (ModuleCat.{u + 1} (PadicAlgCl ell)) r).map
                  (biproduct.desc (fun i ↦
                    (boundedInclusion ell D.k (geometricCompactification D c)
                      (geometricInclusion D (j i))).app K))) ≫
                (DerivedCategory.homologyFunctor
                  (ModuleCat.{u + 1} (PadicAlgCl ell)) r).map
                  (action t (geometricCompactification D c)
                    (D.geometricFrobenius X).hom (compactificationFrobenius D c)
                    hg e K.obj theta) =
                biproduct.map (fun i ↦
                  (DerivedCategory.homologyFunctor
                    (ModuleCat.{u + 1} (PadicAlgCl ell)) r).map
                    (action t
                      ((geometricCompactification D c).precomp
                        (geometricInclusion D (j i)))
                      (schemeFrobenius D (U i)) (compactificationFrobenius D c)
                      hg (ei i) ((pull ell (geometricInclusion D (j i))).obj K.obj)
                      (theta_i i))) ≫
                (Functor.mapBiproduct
                  (DerivedCategory.homologyFunctor
                    (ModuleCat.{u + 1} (PadicAlgCl ell)) r)
                  (fun i ↦ (componentSections ell D.k (geometricCompactification D c)
                    (geometricInclusion D (j i))).obj K)).inv ≫
                (DerivedCategory.homologyFunctor
                  (ModuleCat.{u + 1} (PadicAlgCl ell)) r).map
                  (biproduct.desc (fun i ↦
                    (boundedInclusion ell D.k (geometricCompactification D c)
                      (geometricInclusion D (j i))).app K))) ∧
      (IsEmpty I → IsEmpty (D.geometricFiber X).left ∧
        ∀ K : ProEtale.BoundedConstructible
          (ProEtale.condensedRingObj (Profinite.padicAlgClRingObj ell)
            (D.geometricFiber X).left),
          ∀ r : ℤ,
            IsZero (⨁ fun i ↦ (DerivedCategory.homologyFunctor
              (ModuleCat.{u + 1} (PadicAlgCl ell)) r).obj
                ((componentSections ell D.k (geometricCompactification D c)
                  (geometricInclusion D (j i))).obj K)) ∧
            IsZero ((DerivedCategory.homologyFunctor
              (ModuleCat.{u + 1} (PadicAlgCl ell)) r).obj
                ((boundedSections ell D.k (geometricCompactification D c)).obj K))) := by
  let : Fintype I := Fintype.ofFinite I
  let : DecidableEq I := Classical.decEq I
  obtain ⟨t, hg, hi, e, hj, hci, ei, pi, hpi, hpisum, hK, hEmpty⟩ :=
    condensed_clopen_compact_decomposition D ell hell X I U j hdisjoint hcover c
  refine ⟨t, hg, hi, e, hj, hci, ei, ?_, ?_⟩
  · intro K theta
    obtain ⟨theta_i, htheta_i, hcoh⟩ := (hK K).2.2 theta
    refine ⟨theta_i, htheta_i, ?_⟩
    intro r
    refine ⟨?_, ?_⟩
    · have : IsIso (biproduct.desc (fun i ↦
          (boundedInclusion ell D.k (geometricCompactification D c)
            (geometricInclusion D (j i))).app K)) := (hK K).2.1
      infer_instance
    · exact map_biproduct_intertwining _
        (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (PadicAlgCl ell)) r)
        _ _ _ hcoh
  · intro hI
    let : IsEmpty I := hI
    refine ⟨(hEmpty hI).1, ?_⟩
    intro K r
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro Y
        refine ⟨⟨⟨biproduct.desc (fun i : I ↦ isEmptyElim i)⟩, ?_⟩⟩
        intro f
        change f = biproduct.desc (fun i : I ↦ isEmptyElim i)
        apply biproduct.hom_ext' f
        intro i
        exact isEmptyElim i
      · intro Y
        refine ⟨⟨⟨biproduct.lift (fun i : I ↦ isEmptyElim i)⟩, ?_⟩⟩
        intro f
        change f = biproduct.lift (fun i : I ↦ isEmptyElim i)
        apply biproduct.hom_ext f
        intro i
        exact isEmptyElim i
    · exact Functor.map_isZero _ ((hEmpty hI).2 K)

end WeilConjectures.CondensedClopenCompact
