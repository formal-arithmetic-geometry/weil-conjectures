/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Connected.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.ConstructibleSheaf.LisseTrivialization

/-!
# Finite étale trivialization of a lisse sheaf

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/
fin2-lem-lisse-trivialized-finite-etale.md, node fin2-lem-lisse-trivialized-finite-etale,
order 1904 (blueprint: fin2-lem-lisse-trivialized-finite-etale).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry Scheme

namespace AlgebraicGeometry

/-- A finite locally constant module sheaf on a finite-type scheme over a field is
trivialized by a finite étale surjective cover.  On each connected component of the
cover the pullback is constant with a finite module value; when the base is connected,
one common finite module value works on the whole cover.
Source: blueprint node `fin2-lem-lisse-trivialized-finite-etale`, order 1904
(blueprint: fin2-lem-lisse-trivialized-finite-etale).

Proof. The connected and Noetherian cases are the proved theorems
`Scheme.exists_isConstant_upperStar_of_connectedSpace` and `Scheme.exists_isConstant_upperStar`
of `WeilConjectures.ConstructibleSheaf.LisseTrivialization` (Galois-object splitting of the
finite étale scheme representing the underlying sheaf of sets of `L`).
1. If X is connected, take the connected finite étale surjective cover p : P → X with
   p^*L ≅ M constant, M finite. Since P is connected, the connected component of every
   point is all of P = ⊤; restrict the isomorphism to ⊤ along the upper-star of the open
   immersion and the canonical pullback-of-constant-sheaf isomorphism. The connected-base
   clause is the isomorphism itself.
2. In general, X is Noetherian, being of finite type and quasi-compact over the Noetherian
   Spec k. The Noetherian theorem gives finitely many connected Q_i with finite étale
   q_i : Q_i → X, jointly surjective, and q_i^*L ≅ M_i constant with M_i finite. Put
   P = ∐ Q_i and p = (q_i). The coproduct morphism is finite (finitely many finite maps),
   étale (étaleness is local on the source), and surjective (the ranges cover X). Each
   summand ι_i(Q_i) is open, and closed since its complement is the union of the other
   summands; it is connected, so it is the connected component of each of its points. On
   U = ι_i(Q_i) ≅ Q_i we have U.ι ≫ p = (U ≅ Q_i) ≫ q_i, so the upper-star composition
   isomorphisms and the pullback of the constant sheaf of M_i give the constant value M_i.
   X is not connected in this case, so the last clause holds vacuously. -/
theorem exists_finite_etale_surjective_trivializing_lisse
    (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hL : Scheme.IsFiniteLocallyConstantSheaf L) :
    ∃ (P : Scheme.{u}) (p : P ⟶ X),
      IsFinite p ∧ Etale p ∧ Surjective p ∧
        (∀ (x : P),
          ∃ U : P.Opens, (U : Set P) = connectedComponent x ∧
            ∃ M : ModuleCat.{u + 1} Λ,
            Finite M ∧
              Nonempty
                ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
                  ((Etale.upperStar (ModuleCat.{u + 1} Λ) p).obj L) ≅
                  (constantSheaf U.toScheme.smallEtaleTopology
                    (ModuleCat.{u + 1} Λ)).obj M)) ∧
        (ConnectedSpace X →
          ∃ (M : ModuleCat.{u + 1} Λ), Finite M ∧
            Nonempty
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) p).obj L ≅
                (constantSheaf P.smallEtaleTopology
                  (ModuleCat.{u + 1} Λ)).obj M)) := by
  classical
  let : Scheme.IsFiniteLocallyConstantSheaf L := hL
  by_cases hX : ConnectedSpace X
  · let : ConnectedSpace X := hX
    obtain ⟨P, p, hpfin, hpet, hpsurj, hP, M, hM, ⟨eM⟩⟩ :=
      Scheme.exists_isConstant_upperStar_of_connectedSpace L
    let : ConnectedSpace P := hP
    refine ⟨P, p, hpfin, hpet, hpsurj, ?_, fun _ ↦ ⟨M, hM, ⟨eM⟩⟩⟩
    intro x
    refine ⟨⊤, ?_, M, hM, ?_⟩
    · simp [PreconnectedSpace.connectedComponent_eq_univ]
    · exact ⟨(Etale.upperStar (ModuleCat.{u + 1} Λ) (⊤ : P.Opens).ι).mapIso eM ≪≫
        (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) (⊤ : P.Opens).ι).app M⟩
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  obtain ⟨n, Q, q, hq, hcover, hconst⟩ :=
    Scheme.exists_isConstant_upperStar (X := X) L
  let (i : Fin n) : IsFinite (q i) := (hq i).1
  let P := ∐ Q
  let p : P ⟶ X := Sigma.desc q
  have hpfin : IsFinite p := by infer_instance
  have hpet : Etale p := IsZariskiLocalAtSource.sigmaDesc fun i ↦ (hq i).2.1
  have hpsurj : Surjective p := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, y, hy⟩ := hcover x
    exact Set.mem_iUnion.2 ⟨i, y, hy⟩
  have hclopen (i : Fin n) : IsClopen (Set.range (Sigma.ι Q i)) := by
    have hc : (Set.range (Sigma.ι Q i))ᶜ =
        ⋃ j : {j : Fin n // j ≠ i}, Set.range (Sigma.ι Q j.1) := by
      ext z
      constructor
      · intro hz
        let j := (sigmaOpenCover Q).idx z
        have hj : j ≠ i := by
          intro he
          exact hz (he ▸ (sigmaOpenCover Q).covers z)
        exact Set.mem_iUnion.mpr ⟨⟨j, hj⟩, (sigmaOpenCover Q).covers z⟩
      · intro hz hi
        obtain ⟨j, y, hy⟩ := Set.mem_iUnion.mp hz
        obtain ⟨w, hw⟩ := hi
        exact j.2 (congrArg Sigma.fst ((sigmaι_eq_iff Q _ _ _ _).mp
          (hy.trans hw.symm)))
    refine ⟨?_, IsOpenImmersion.isOpen_range _⟩
    rw [← isOpen_compl_iff, hc]
    exact isOpen_iUnion fun _ ↦ IsOpenImmersion.isOpen_range _
  refine ⟨P, p, hpfin, hpet, hpsurj, ?_, fun h ↦ False.elim (hX h)⟩
  intro x
  let i := (sigmaOpenCover Q).idx x
  have hxi : x ∈ Set.range (Sigma.ι Q i) := (sigmaOpenCover Q).covers x
  let : ConnectedSpace (Q i) := (hq i).2.2
  let U : P.Opens := (Sigma.ι Q i).opensRange
  have hUi : (U : Set P) = connectedComponent x := by
    apply Set.Subset.antisymm
    · exact (isConnected_range (Sigma.ι Q i).continuous).subset_connectedComponent hxi
    · exact (hclopen i).connectedComponent_subset hxi
  obtain ⟨M, hM, ⟨eM⟩⟩ := hconst i
  refine ⟨U, hUi, M, hM, ?_⟩
  let eiso : U.toScheme ≅ Q i := (Sigma.ι Q i).isoOpensRange.symm
  have heq : U.ι ≫ p = eiso.hom ≫ q i := by
    rw [← Sigma.ι_desc q i, ← Category.assoc]
    change U.ι ≫ p = ((Sigma.ι Q i).isoOpensRange.inv ≫ Sigma.ι Q i) ≫ p
    rw [Scheme.Hom.isoOpensRange_inv_comp]
  exact ⟨((Etale.upperStarComp (ModuleCat.{u + 1} Λ) U.ι p).app L).symm ≪≫
    (Etale.upperStarComp (ModuleCat.{u + 1} Λ) eiso.hom (q i) (U.ι ≫ p) heq).app L ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} Λ) eiso.hom).mapIso eM ≪≫
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) eiso.hom).app M⟩

end AlgebraicGeometry
