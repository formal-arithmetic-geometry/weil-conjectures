/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap
import Sheaf.Algebra.Homology.PerfectRingHomTensorDualIso
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.Monoidal

/-! # K-flatness of a Hom complex with bounded finite-projective source

Source: Stacks Project, more-algebra.tex, lemma-base-change-RHom, clause (1).
(blueprint: lem-pc-perfect-ring-hom-kflat)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private theorem homObj_zero_source {A : Type u} [CommRing A]
    (M N : RingSiteModules A) (hM : IsZero M) :
    IsZero (SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) M N) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← SheafOfModules.homObjMap_id (R := CochainComplex.onePointRingSheaf A),
    hM.eq_zero_of_src (𝟙 M)]
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver _ X.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver _ X.unop).map (𝟙 N.val) = 0
  ext W x
  change (φ.app W).hom 0 = 0
  exact map_zero _

private theorem homObj_zero_target {A : Type u} [CommRing A]
    (M N : RingSiteModules A) (hN : IsZero N) :
    IsZero (SheafOfModules.homObj (R := CochainComplex.onePointRingSheaf A) M N) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← SheafOfModules.homObjMap_id (R := CochainComplex.onePointRingSheaf A),
    hN.eq_zero_of_tgt (𝟙 N)]
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver _ X.unop).map (𝟙 M.val) ≫ φ ≫
    (PresheafOfModules.restrictOver _ X.unop).map 0 = 0
  ext W x
  rfl

set_option backward.isDefEq.respectTransparency true in
private theorem perfectRingDual_boundedAbove {A : Type u} [CommRing A]
    (P : CochainComplex (RingSiteModules A) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) :
    ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero ((perfectRingDual P).X n) := by
  obtain ⟨a, b, hab⟩ := hb
  let O := SheafOfModules.unit ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (CochainComplex.onePointRingSheaf A))
  let L := (CochainComplex.singleFunctor (RingSiteModules A) 0).obj O
  obtain ⟨π, hπ, _, _⟩ := Classical.choose_spec
    (homComplex_exists (R := CochainComplex.onePointRingSheaf A))
  refine ⟨-a, ?_⟩
  intro n hn
  change IsZero ((homComplex (R := CochainComplex.onePointRingSheaf A) P L).X n)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (hπ P L n).some.hom_ext
  intro j
  by_cases hj : j.as < a
  · exact (homObj_zero_source _ _ (hab j.as (Or.inl hj))).eq_of_tgt _ _
  · exact (homObj_zero_target _ _
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 O (j.as + n)
        (by omega))).eq_of_tgt _ _

/-- The Hom complex from a bounded finite-projective complex to a K-flat complex is K-flat.

Source: Stacks Project, more-algebra.tex, lemma-base-change-RHom, clause (1), and
lemma-bounded-above-flat-K-flat (blueprint: lem-pc-perfect-ring-hom-kflat).

Proof: evaluate sheaves on the unique object of the bottom-topology one-object site;
this identifies the sheaf tensor and internal Hom with their module counterparts.
Put `Pᵛ = Hom(P,A)`, with the dual differential and reversed degrees. Finite projectivity
identifies `Hom(P^i,A) ⊗ M` with `Hom(P^i,M)`: the evaluation map is an isomorphism for
finite free modules, and restricting the map and its inverse along a projective splitting
proves the claim for their direct summands. Boundedness of P makes every diagonal finite,
so these identifications give a chain isomorphism `Tot(Pᵛ ⊗ Q) ≅ Hom(P,Q)`;
choose the signs to match `d_Q f - (-1)^n f d_P`. The dual Pᵛ is bounded with finite
projective, hence flat, terms. For acyclic F, `Tot(F ⊗ Pᵛ)` is acyclic by the
bounded-above flat K-flat lemma. Associativity of total tensor products gives
`Tot(F ⊗ Tot(Pᵛ ⊗ Q)) ≅ Tot(Tot(F ⊗ Pᵛ) ⊗ Q)`, with the usual Koszul signs;
Q being K-flat makes the latter acyclic. Transport acyclicity through these chain
isomorphisms and through the one-object evaluation equivalence. This is exactly the
predicate `IsKFlat` for the shared Hom complex. -/
theorem perfectRingHom_isKFlat {A : Type u} [CommRing A]
    (P Q : CochainComplex (RingSiteModules A) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hp : ∀ n : ℤ, Module.Projective A ((P.X n).val.obj (op ⟨PUnit.unit⟩)))
    (hf : ∀ n : ℤ, Module.Finite A ((P.X n).val.obj (op ⟨PUnit.unit⟩)))
    (hQ : Q.IsKFlat) :
    (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).IsKFlat := by
  let R := CochainComplex.onePointRingSheaf A
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := (SheafOfModules.tensorClosed R).1.some
  let := (SheafOfModules.tensorClosed R).2.1.some
  have hD : (perfectRingDual P).IsKFlat :=
    CochainComplex.isKFlat_of_boundedAbove_flat (perfectRingDual P)
      (perfectRingDual_boundedAbove P hb) (perfectRingDual_term_isFlat P hp hf)
  obtain ⟨e⟩ := perfectRingHom_tensorDual_iso P Q hb hp hf
  intro F hF i
  have ht := hQ _ (hD F hF)
  have ha := (ht i).of_iso (HomologicalComplex.associator F (perfectRingDual P) Q)
  let eF := (((MonoidalCategory.curriedTensor (RingSiteModules A)).mapBifunctorHomologicalComplex
    (.up ℤ) (.up ℤ)).obj F).mapIso e
  exact ha.of_iso (HomologicalComplex₂.total.mapIso eF (.up ℤ))

end CategoryTheory
