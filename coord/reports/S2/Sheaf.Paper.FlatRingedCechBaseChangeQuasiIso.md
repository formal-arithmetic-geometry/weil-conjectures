## What changed

Marked `CategoryTheory.flat_ringedCech_baseChange_data_quasiIso` as
`STATEMENT-DISPUTED`. The declaration claims that an arbitrary augmented model map
is a quasi-isomorphism from only the augmentation equation. No proof was added.

## Proved and sorry left

Closed 0 of 1 existing holes; added 0 holes. The existing sorry in
`CategoryTheory.flat_ringedCech_baseChange_data_quasiIso` remains, with node
`lem-weil-pbc-flat-ringed-cech-base-change-quasi-iso`.

## No longer needed

None. The module remains available because the already-landed parent module imports
its declaration.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the split node is false as stated. For any additive functor `F`, complex `K`, target
complex `T`, and map `a : K ⟶ F(T)`, suppose the displayed universal conclusion held
for every `L`, `δ`, and `u` satisfying `u ≫ F.map δ = a`. Applying it first to
`L = T`, `δ = 𝟙`, and then to `L = T ⊞ T`, `δ = biprod.fst`, with
`u = a ≫ F.map biprod.inl`, gives quasi-isomorphisms for both `a` and its first
biproduct injection. The second projection then has zero composite with the first
injection, while `biprod.inr ≫ biprod.snd = 𝟙`; cancellation forces the homology of
`F(T)` to be zero. This contradicts the intended arbitrary Cech target. The source
argument instead constructs a specific scalar-extended Cech complex and proves its
specific comparison map is a quasi-isomorphism; those data are absent from this
split declaration.

The concrete edge case is the one-object site with the trivial topology,
`R = B = ℤ`, `φ = 𝟙`, the zero ideal, and its empty-generator model
`K = ℤ[0]`, `ε = 𝟙`. All flatness and quotient hypotheses hold. Take
`L = ℤ[0] ⊞ ℤ[0]`, `δ = biprod.fst`, and `u = biprod.inl` (transported
through restriction by the identity). The augmentation equation holds, but the
map on degree-zero homology is the first injection `ℤ → ℤ ⊕ ℤ`, which is
not surjective. Even restricting `u` to be the scalar-extension unit would
require constructing that unit and its actual target; choosing `B[0]` in the
parent is not that construction.

The marked module compiled in 12.7 seconds. An independent Lean verification
of the biproduct argument, including its specialization to a single complex,
compiled in 5.1 seconds. Both obstruction theorems use only `propext`,
`Classical.choice`, and `Quot.sound`. The complete verification code follows;
it is evidence in this report, not an additional library obligation.

```lean
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.QuasiIso

@[expose] public section

set_option autoImplicit false
universe v u v' u'
open CategoryTheory CategoryTheory.Limits

/-- The asserted universal augmentation criterion would kill the target's homology.
The proof uses the two permissible codomains T and T biprod T. -/
theorem augmented_universal_quasiIso_forces_isZero
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F : B ⥤ A) [F.Additive] (K : CochainComplex A ℤ)
    (T : CochainComplex B ℤ)
    (a : K ⟶ (F.mapHomologicalComplex (.up ℤ)).obj T)
    (h : ∀ (L : CochainComplex B ℤ) (δ : L ⟶ T)
      (u : K ⟶ (F.mapHomologicalComplex (.up ℤ)).obj L),
      u ≫ (F.mapHomologicalComplex (.up ℤ)).map δ = a → QuasiIso u)
    (q : ℤ) :
    IsZero (((F.mapHomologicalComplex (.up ℤ)).obj T).homology q) := by
  let G := F.mapHomologicalComplex (.up ℤ)
  have ha : QuasiIso a := h T (𝟙 T) a (by simp)
  have hb : QuasiIso (a ≫ G.map (biprod.inl : T ⟶ T ⊞ T)) :=
    h (T ⊞ T) biprod.fst _ (by simp [G, ← Functor.map_comp])
  have hi : QuasiIso (G.map (biprod.inl : T ⟶ T ⊞ T)) :=
    quasiIso_of_comp_left a _
  let H := G ⋙ HomologicalComplex.homologyFunctor A (.up ℤ) q
  have he : Epi (H.map (biprod.inl : T ⟶ T ⊞ T)) := by
    change Epi (HomologicalComplex.homologyMap (G.map biprod.inl) q)
    infer_instance
  have hs : H.map (biprod.snd : T ⊞ T ⟶ T) = 0 := by
    apply (cancel_epi (H.map (biprod.inl : T ⟶ T ⊞ T))).mp
    simp [← Functor.map_comp]
  apply (IsZero.iff_id_eq_zero _).2
  change 𝟙 (H.obj T) = 0
  calc
    𝟙 (H.obj T) = H.map (biprod.inr : T ⟶ T ⊞ T) ≫ H.map biprod.snd := by
      simp [← Functor.map_comp]
    _ = 0 := by rw [hs, comp_zero]

#print axioms augmented_universal_quasiIso_forces_isZero

/-- The augmentation-only criterion for maps to a degree-zero module forces it to vanish. -/
theorem augmented_single_universal_quasiIso_forces_isZero
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F : B ⥤ A) [F.Additive] (K : CochainComplex A ℤ) (M : B)
    (a : K ⟶ (F.mapHomologicalComplex (.up ℤ)).obj
      ((HomologicalComplex.single B (.up ℤ) 0).obj M))
    (h : ∀ (L : CochainComplex B ℤ)
      (δ : L ⟶ (HomologicalComplex.single B (.up ℤ) 0).obj M)
      (u : K ⟶ (F.mapHomologicalComplex (.up ℤ)).obj L),
      u ≫ (F.mapHomologicalComplex (.up ℤ)).map δ = a → QuasiIso u) :
    IsZero (F.obj M) := by
  have hz := augmented_universal_quasiIso_forces_isZero F K
    ((HomologicalComplex.single B (.up ℤ) 0).obj M) a h 0
  exact hz.of_iso
    ((HomologicalComplex.homologyFunctor A (.up ℤ) 0).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app M) ≪≫
        HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).symm

#print axioms augmented_single_universal_quasiIso_forces_isZero
```

No parent declaration, target statement, definition, import, or DAG route was
changed. The original missing construction must be repaired before this false
universal statement can be replaced by the source's canonical comparison.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
