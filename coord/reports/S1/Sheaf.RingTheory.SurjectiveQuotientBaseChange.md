## What changed

Completed the retirement item listed in coord/retire-items.tsv: withdrew the unused
Sheaf.RingTheory.SurjectiveQuotientBaseChange copy and attached
lem-sbc-surjective-quotient-base-change to the proved upstream
Algebra.quotientBaseChangeObjIso. The node statement is unchanged. Its proof now explains
how to construct the compatible B-action before applying the upstream explicit isomorphism.

The source scan found zero downstream modules. The retirement row's four old consumers
have already been retired, and all four upstream twins already import
WeilConjectures.RingTheory.SurjectiveQuotientBaseChange. There are no consumer edits.
The unit sk-prop-input-spreading and its route are unchanged.

Change record: coord/changes/retire-surjective-quotient-base-change-S1-20261020.md.

To verify the API difference, the following complete derivation of the original statement
was compiled on the server through lcompile.py. It is a scratch verification, not a new
library module: no consumer needs a compatibility declaration. Compilation succeeded in
2.3 seconds. Each of the three axiom checks printed only propext, Classical.choice and
Quot.sound.

```lean
module

public import WeilConjectures.RingTheory.SurjectiveQuotientBaseChange

@[expose] public section

universe u
open CategoryTheory
namespace Algebra

theorem quotientBaseChange_attachment_check
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A C]
    (π : A →+* B) (hπ : Function.Surjective π)
    (I : Ideal A) (hker : RingHom.ker π = I) :
    ∃ (_ : Algebra B (C ⧸ I.map (algebraMap A C))),
      Nonempty ((quotientBaseChange π).obj (CommAlgCat.of A C) ≅
        CommAlgCat.of B (C ⧸ I.map (algebraMap A C))) := by
  let J := I.map (algebraMap A C)
  let q := Ideal.Quotient.mk J
  have hk : RingHom.ker π ≤ RingHom.ker (q.comp (algebraMap A C)) := by
    rw [hker, ← RingHom.comap_ker, Ideal.mk_ker]
    exact Ideal.le_comap_map
  let β : B →+* (C ⧸ J) := π.liftOfSurjective hπ ⟨q.comp (algebraMap A C), hk⟩
  let : Algebra B (C ⧸ J) := β.toAlgebra
  refine ⟨β.toAlgebra, ⟨quotientBaseChangeObjIso A B C π hπ I hker ?_⟩⟩
  ext a
  change β (π a) = q (algebraMap A C a)
  exact π.liftOfSurjective_comp_apply hπ ⟨q.comp (algebraMap A C), hk⟩ a

end Algebra

#print axioms Algebra.quotientBaseChange_attachment_check
#print axioms Algebra.quotientBaseChangeObjIso
#print axioms Algebra.quotientBaseChange

```

## Proved and sorry left

This retirement item started with zero sorries. Holes closed: 0. Holes added: 0.
Sorries left in the delivery: 0. Split off: 0.
The already-proved Algebra.quotientBaseChange_obj_iso is retired with its unused module;
it is not counted as a newly closed hole. The compiled check above proves its complete
old statement from the upstream explicit isomorphism and Mathlib. No unproved theorem
or arbitrary existence witness is used to construct data.

## No longer needed

Pruned module: Sheaf.RingTheory.SurjectiveQuotientBaseChange. Its local copies of
Algebra.quotientBaseChange and the left-adjoint instance are replaced by the existing
upstream declarations. Its unused Algebra.quotientBaseChange_obj_iso needs no public
compatibility replacement. The original public Mathlib.Algebra.Category.CommAlgCat.Basic
import disappears with the copy; the upstream module already imports it publicly.

No proof-dependency nodes are pruned: proof_deps was empty and remains empty.
The existing node is preserved and attached to upstream, not deleted. No new modules
or nodes are introduced.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief says the item has a sorry or an assigned repair. The actual
queue marks it as retirement with zero holes. Its historical consumer list is stale:
none of the four Sheaf consumer files remains, and there are no imports of the copy.

Upstream renamed the existential quotient result to the data-producing
quotientBaseChangeObjIso and takes a compatible B-algebra structure explicitly. Repointing
the name alone would overlook this API difference. The compiled derivation above constructs
the B-action and its compatibility equation, preserving all original hypotheses and the
full original conclusion, including I = 0 and a zero quotient ring.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
