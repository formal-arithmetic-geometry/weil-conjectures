module

public import Sheaf.RingTheory.ClopenRestrictionCanonicalLocalization
public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import Mathlib.Topology.DiscreteQuotient
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesProduct
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.Algebra.Category.Ring.FinitePresentation
import WeilConjectures.Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # The coherent partition restriction diagram

Source: Stacks Project, Tag 097D, `lemma-construct-profinite`, and blueprint
`det-pe-wc-cover-second-stage`, Preliminaries and Step 1
(blueprint: lem-pe-partition-restriction-ind-zariski).

Finite clopen partitions are Mathlib's discrete quotients of a compact space. The
opposite category orders these by refinement. Their points index the nonempty parts,
so an empty space has the empty partition, without a distinguished empty part.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace WContractification.PartitionRestriction

variable {R P S : Type u} [CommRing R] [TopologicalSpace P] [TopologicalSpace S]

/-- The small poset of finite clopen partitions, with arrows towards finer partitions.
Source: blueprint Preliminaries and Stacks 097D
(blueprint: lem-pe-partition-restriction-ind-zariski). -/
abbrev Index (S : Type u) [TopologicalSpace S] := (DiscreteQuotient S)ᵒᵖ

/-- The part indexed by a quotient point. Surjectivity of the quotient map makes it
nonempty; these are exactly the clopen parts of the partition. Source: blueprint
Preliminaries (blueprint: lem-pe-partition-restriction-ind-zariski). -/
def part (Q : Index S) (a : Q.unop) : Set S := Q.unop.proj ⁻¹' {a}

/-- The prescribed product of the canonical closed-restriction algebras. Source:
blueprint Preliminaries (blueprint: lem-pe-partition-restriction-ind-zariski). -/
noncomputable abbrev stage (g : C(PrimeSpectrum R, P)) (f : C(S, P)) (Q : Index S) :
    CommAlgCat R :=
  ∏ᶜ fun a : Q.unop ↦ ClopenRestriction.algebra g (f '' part Q a)

/-- The simultaneous choices of clopen neighbourhoods, one for each part. Each
coordinate uses reverse inclusion. Source: blueprint Step 1
(blueprint: lem-pe-partition-restriction-ind-zariski). -/
abbrev NeighborhoodIndex (f : C(S, P)) (Q : Index S) :=
  (a : Q.unop) → ClopenRestriction.Index (f '' part Q a)

/-- The product diagram of principal idempotent localizations at the simultaneous
neighbourhood choices. Source: blueprint Step 1
(blueprint: lem-pe-partition-restriction-ind-zariski). -/
noncomputable abbrev neighborhoodDiagram (g : C(PrimeSpectrum R, P)) (f : C(S, P))
    (Q : Index S) : NeighborhoodIndex f Q ⥤ CommAlgCat R :=
  pointwiseProduct (fun a : Q.unop ↦ ClopenRestriction.diagram g (f '' part Q a))

/-- The actual canonical comparison, induced by the coordinate colimit coprojections.
Source: blueprint Step 1 (blueprint: lem-pe-partition-restriction-ind-zariski). -/
noncomputable abbrev comparison (g : C(PrimeSpectrum R, P)) (f : C(S, P))
    (Q : Index S) : colimit (neighborhoodDiagram g f Q) ⟶ stage g f Q :=
  colimitPointwiseProductToProductColimit
    (fun a : Q.unop ↦ ClopenRestriction.diagram g (f '' part Q a))

/-- The canonical restriction to the image of a refined part from the image of its
unique containing part. Source: blueprint Preliminaries
(blueprint: lem-pe-partition-restriction-ind-zariski). -/
noncomputable def refinementRestriction (g : C(PrimeSpectrum R, P)) (f : C(S, P))
    {Q Q' : Index S} (h : Q ⟶ Q') (a' : Q'.unop) :
    ClopenRestriction.algebra g (f '' part Q (DiscreteQuotient.ofLE h.unop.le a')) ⟶
      ClopenRestriction.algebra g (f '' part Q' a') :=
  ClopenRestriction.restriction g (fun _ ⟨s, hs, heq⟩ ↦
    ⟨s, (DiscreteQuotient.ofLE_proj h.unop.le s).symm.trans
      (congrArg (DiscreteQuotient.ofLE h.unop.le) hs), heq⟩)

-- Principal-localization blocks, used only to flatten the final presentation.
private def principalBlocks (A : Type u) [CommRing A] : ObjectProperty (CommAlgCat.{u} A) :=
  fun B ↦ ∃ (n : ℕ) (x : Fin n → A),
    Nonempty (B ≃ₐ[A] ((j : Fin n) → Localization.Away (x j)))

private theorem principalBlocks_fp (A : Type u) [CommRing A] :
    principalBlocks A ≤ ObjectProperty.isFinitelyPresentable.{u} (CommAlgCat.{u} A) := by
  intro B hB
  obtain ⟨n, x, ⟨e⟩⟩ := hB
  have : Algebra.Etale A ((j : Fin n) → Localization.Away (x j)) := inferInstance
  have : Algebra.Etale A B := Algebra.Etale.of_equiv e.symm
  have hfp : IsFinitelyPresentable.{u}
      ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj B) :=
    CommRingCat.isFinitelyPresentable_under _ _
      (RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale A B)).2
  have : Fact Cardinal.aleph0.{u}.IsRegular := Cardinal.fact_isRegular_aleph0
  exact (isCardinalPresentable_iff_of_isEquivalence B Cardinal.aleph0.{u}
    (commAlgCatEquivUnder (CommRingCat.of A)).functor).mp hfp

private theorem principal_colimit {A : Type u} [CommRing A]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CommAlgCat A) (h : ∀ i, Algebra.IsIndPrincipalZariski A (D.obj i)) :
    Algebra.IsIndPrincipalZariski A (colimit D : CommAlgCat A) := by
  change (principalBlocks A).ind (colimit D)
  rw [← ObjectProperty.ind_ind (principalBlocks_fp A)]
  exact ⟨I, inferInstance, inferInstance, ColimitPresentation.colimit D, h⟩

private noncomputable def refinementMap (g : C(PrimeSpectrum R, P)) (f : C(S, P))
    {Q Q' : Index S} (h : Q ⟶ Q') : stage g f Q ⟶ stage g f Q' :=
  Pi.lift fun a' ↦ Pi.π _ (DiscreteQuotient.ofLE h.unop.le a') ≫
    refinementRestriction g f h a'

/-- Finite clopen partitions give the coherent diagram with precisely the prescribed
coordinate restriction maps; simultaneous neighbourhood products present each term,
and both every term and the final filtered colimit are ind-Zariski in the finite
principal-product sense. The functor's object equalities fix the literal chosen products,
and its displayed coordinate equation fixes every transition map uniquely.

Source: Stacks 097D, `lemma-construct-profinite`, Stacks 096S,
`lemma-ind-ind-zariski`, and blueprint `det-pe-wc-cover-second-stage`,
Preliminaries and Step 1 (blueprint: lem-pe-partition-restriction-ind-zariski).

Proof:
1. Each part is clopen and hence compact. Its image under f is compact, hence closed
   in the Hausdorff space P. This requires no openness of f.
2. Discrete quotients encode partitions by their nonempty fibres. The indiscrete
   quotient exists also for the empty space (where its quotient is empty). The infimum
   of two quotients supplies their common refinement. Thus the opposite index is a
   small nonempty directed poset (def-weil-pbc-category-colimit).
3. On an a'-coordinate use projection to its parent a and the canonical restriction
   R_f(a) to R_f(a'). The identity and composition laws follow coordinatewise from
   lem-pe-clopen-restriction-canonical-localization. Products therefore give a functor
   with the stated object equalities and exactly the stated maps.
4. For a fixed partition, neighbourhood tuples have a top-clopen tuple and receive
   arrows from two tuples at their coordinatewise intersections. Their diagram is the
   product of the canonical localization diagrams. Its comparison is induced by the
   coordinate coprojections (lem-pe-clopen-restriction-canonical-localization,
   lem-weil-pbc-commutative-algebras-colimits-exist, def-weil-pbc-category-colimit).
5. The source library proves the IPC property for commutative algebras by transferring
   it along the forgetful functor to types. This functor preserves products and filtered
   colimits and reflects isomorphisms. Its comparison-isomorphism instance proves the
   specified comparison is an isomorphism, including for the empty product.
6. The coordinate formula is Mathlib's coprojection formula for the pointwise-product
   comparison. The refinement functor is constructed directly on the prescribed products.
   Quotient induction reduces the parent-of-parent identity to the same representative;
   canonical restriction naturality gives its identity and composition laws.
7. Enumerate the finitely many quotient points by Fin n. The categorical product is
   canonically the type-theoretic product of the principal localizations, so the
   neighbourhood diagram presents each partition stage as principal ind-Zariski.
8. Finite products of principal localizations are etale, hence finitely presented.
   Transfer finite presentability from rings under R to commutative R-algebras. Mathlib's
   ObjectProperty.ind_ind then flattens a filtered colimit of their filtered colimits,
   proving the final assertion. This also handles Fin 0 and the empty partition.
-/
theorem partition_restriction_ind_zariski
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    [CompactSpace S] [T2Space S] [TotallyDisconnectedSpace S]
    (g : C(PrimeSpectrum R, P)) (f : C(S, P)) :
    (∀ (Q : Index S) (a : Q.unop), IsClosed (f '' part Q a)) ∧
    Nonempty (Index S) ∧ IsFiltered (Index S) ∧
    (∀ Q : Index S, Nonempty (NeighborhoodIndex f Q) ∧
      IsFiltered (NeighborhoodIndex f Q) ∧ IsIso (comparison g f Q) ∧
      (∀ (U : NeighborhoodIndex f Q) (a : Q.unop),
        colimit.ι (neighborhoodDiagram g f Q) U ≫ comparison g f Q ≫
            Pi.π (fun b : Q.unop ↦ ClopenRestriction.algebra g (f '' part Q b)) a =
          Pi.π (fun b : Q.unop ↦
            (ClopenRestriction.diagram g (f '' part Q b)).obj (U b)) a ≫
              colimit.ι (ClopenRestriction.diagram g (f '' part Q a)) (U a)) ∧
      Algebra.IsIndPrincipalZariski R (stage g f Q)) ∧
    (∃ (D : Index S ⥤ CommAlgCat R) (hD : ∀ Q : Index S, D.obj Q = stage g f Q),
      (∀ (Q Q' : Index S) (h : Q ⟶ Q') (a' : Q'.unop),
        D.map h ≫ eqToHom (hD Q') ≫
            Pi.π (fun b : Q'.unop ↦ ClopenRestriction.algebra g (f '' part Q' b)) a' =
          eqToHom (hD Q) ≫
            Pi.π (fun b : Q.unop ↦ ClopenRestriction.algebra g (f '' part Q b))
              (DiscreteQuotient.ofLE h.unop.le a') ≫
            refinementRestriction g f h a') ∧
      Algebra.IsIndPrincipalZariski R (colimit D : CommAlgCat R)) := by
  classical
  have hc (Q : Index S) (a : Q.unop) : IsClosed (f '' part Q a) :=
    ((Q.unop.isClosed_preimage {a}).isCompact.image f.continuous).isClosed
  have hn (Q : Index S) (a : Q.unop) :=
    ClopenRestriction.canonical_localization g (f '' part Q a) (hc Q a)
  have hni (Q : Index S) (a : Q.unop) :
      IsFiltered (ClopenRestriction.Index (f '' part Q a)) := (hn Q a).2.1
  have hnn (Q : Index S) (a : Q.unop) :
      Nonempty (ClopenRestriction.Index (f '' part Q a)) := (hn Q a).1
  have hp (Q : Index S) : Algebra.IsIndPrincipalZariski R (stage g f Q) := by
    let : Fintype Q.unop := Fintype.ofFinite _
    let e := Fintype.equivFin Q.unop
    let E : colimit (neighborhoodDiagram g f Q) ≅ stage g f Q := asIso (comparison g f Q)
    have hb : Algebra.IsIndPrincipalZariski R (colimit (neighborhoodDiagram g f Q) :
        CommAlgCat R) := by
      refine ⟨NeighborhoodIndex f Q, inferInstance, inferInstance,
        ColimitPresentation.colimit (neighborhoodDiagram g f Q), ?_⟩
      intro U
      let T : Q.unop → CommAlgCat R := fun a ↦
        (ClopenRestriction.diagram g (f '' part Q a)).obj (U a)
      let ep : (∏ᶜ T) ≅ CommAlgCat.of R ((a : Q.unop) → T a) :=
        (limit.isLimit (Discrete.functor T)).conePointUniqueUpToIso
          (CommAlgCat.isLimitPiFan T)
      refine ⟨Fintype.card Q.unop,
        fun j ↦ ClopenRestriction.idempotent g (U (e.symm j)).unop.val, ?_⟩
      exact ⟨(CommAlgCat.algEquivOfIso ep).trans
        (AlgEquiv.piCongrLeft' R (fun a ↦ T a) e)⟩
    exact (principalBlocks R).ind.prop_of_iso E hb
  refine ⟨hc, inferInstance, inferInstance, ?_, ?_⟩
  · intro Q
    refine ⟨inferInstance, inferInstance, inferInstance, ?_, ?_⟩
    · intro U a
      exact ι_colimitPointwiseProductToProductColimit_π _ U a
    · exact hp Q
  · let D : Index S ⥤ CommAlgCat R :=
      { obj := stage g f
        map := refinementMap g f
        map_id Q := by
          apply Pi.hom_ext
          intro a
          refine Quotient.inductionOn a (fun s ↦ ?_)
          simp only [refinementMap, Pi.lift_π, Category.id_comp]
          change Pi.π (fun b ↦ ClopenRestriction.algebra g (f '' part Q b))
              (Q.unop.proj s) ≫
            ClopenRestriction.restriction g (Set.Subset.refl (f '' part Q (Q.unop.proj s))) = _
          rw [(ClopenRestriction.restriction_naturality g).1 _ (hc Q _)]
          simp only [Category.comp_id]
          rfl
        map_comp {Q Q' Q''} h h' := by
          apply Pi.hom_ext
          intro a
          refine Quotient.inductionOn a (fun s ↦ ?_)
          simp only [refinementMap, Category.assoc, Pi.lift_π, Pi.lift_π_assoc]
          unfold refinementRestriction
          rw [(ClopenRestriction.restriction_naturality g).2.1 _ _ _
            (hc Q'' _) (hc Q' _) (hc Q _) _ _]
          rfl }
    refine ⟨D, fun _ ↦ rfl, ?_, principal_colimit D ?_⟩
    · intro Q Q' h a'
      simp [D, refinementMap]
    · intro Q
      exact hp Q

end WContractification.PartitionRestriction
