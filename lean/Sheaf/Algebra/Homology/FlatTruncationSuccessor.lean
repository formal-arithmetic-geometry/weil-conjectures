/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
import Sheaf.Algebra.Homology.BoundedFlatReplacement
import Sheaf.Algebra.Homology.RelativeFlatExtension
import Sheaf.Algebra.Homology.FlatAugmentationEpicification

/-!
# One extension of a flat replacement of a good truncation

Source: Stacks Project, Derived Categories, Lemma 06XX, induction step;
Cohomology on Sites, Lemma 077J
(blueprint: lem-pc-flat-truncation-successor).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A chosen bounded-above flat replacement of one good truncation extends to the next.
This is a single extension step, with the previous complex and augmentation prescribed;
it does not assert the existence of an infinite tower. The flat-cover hypothesis
is an explicit ingredient of the induction, supplied by the bounded replacement
theorem applied to complexes concentrated in degree zero.

Source: Stacks Project, Derived Categories, Lemma 06XX, induction step, specialized
as in Cohomology on Sites, Lemma 077J
(blueprint: lem-pc-flat-truncation-successor).

Proof: Compose q with the inclusion from the n-th to the (n+1)-st good truncation
and form its mapping cone C. Both its source and target are bounded above, so C is
bounded above. Resolve C by a bounded-above flat complex Q using the bounded flat
replacement theorem. The composite Q -> C -> E[1] defines a triangle with first
term E and middle term E'. Realize this triangle by a degreewise split extension
0 -> E -> E' -> Q -> 0. Thus E' is bounded above and its terms are finite sums of
flat objects. The morphism of triangles gives an augmentation f to the next
truncation; the identity on E and the quasi-isomorphism Q -> C show, by the long
exact cohomology sequences, that f is a quasi-isomorphism. The augmentation square
initially commutes up to homotopy. Extend that homotopy from E to E' along the
chosen degreewise retractions and subtract its differential from f. The resulting
chain map has the same cohomology maps and makes the square strictly commute.
The old termwise epimorphism implies that f is epic except possibly in degrees n
and n+1. Apply hcover to G^n to obtain a flat epimorphic cover P -> G^n. Add the
contractible complex P --id--> P in degrees n,n+1 to E', and augment it by the
cover in degree n and its composite with d_G in degree n+1 (which lands in cycles).
The added summand covers G^n and the boundaries in degree n+1. Since H^(n+1)(f)
is epic, f together with this boundary cover is epic onto the cycles in degree
n+1, the top term of the next truncation. All other components remain epic.
The contractible summand preserves quasi-isomorphy and boundedness, and finite sums
preserve flatness. Include E through the original summand. The strictly commuting
square, composed with the truncation inclusion into G, gives the claimed equality.
This argument also applies for n=0, for zero G or E, and for bounds on E larger
than n; only boundedness of the cone is used. -/
theorem exists_flat_truncation_successor
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    (hcover : ∀ M : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      ∃ (P : SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (p : P ⟶ M),
        SheafOfModules.IsFlat P ∧ Epi p)
    (G : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (n : ℕ)
    (E : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (q : E ⟶ G.truncLE (n : ℤ))
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (E.X i))
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (E.X i))
    (hquasi : QuasiIso q) (hepi : ∀ i : ℤ, Epi (q.f i)) :
    ∃ (E' : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (t : E ⟶ E') (q' : E' ⟶ G.truncLE ((n + 1 : ℕ) : ℤ)),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (E'.X i)) ∧
      (∀ i : ℤ, SheafOfModules.IsFlat (E'.X i)) ∧ QuasiIso q' ∧
      (∀ i : ℤ, Epi (q'.f i)) ∧
      t ≫ q' ≫ G.ιTruncLE ((n + 1 : ℕ) : ℤ) = q ≫ G.ιTruncLE (n : ℤ) := by
  -- The relative cone construction and all-degree disks do not need these assumptions.
  have _hq := hquasi
  have _he := hepi
  let m : ℤ := ((n + 1 : ℕ) : ℤ)
  have hstrict : (G.truncLE (n : ℤ)).IsStrictlyLE m := by
    rw [isStrictlyLE_iff]
    intro i hi
    exact (G.truncLE (n : ℤ)).isZero_of_isStrictlyLE (n : ℤ) i (by dsimp [m] at hi; omega)
  have : IsIso ((G.truncLE (n : ℤ)).ιTruncLE m) := inferInstance
  let j : G.truncLE (n : ℤ) ⟶ G.truncLE m :=
    inv ((G.truncLE (n : ℤ)).ιTruncLE m) ≫ truncLEMap (G.ιTruncLE (n : ℤ)) m
  have hj : j ≫ G.ιTruncLE m = G.ιTruncLE (n : ℤ) := by
    dsimp [j]
    rw [Category.assoc, ιTruncLE_naturality, ← Category.assoc, IsIso.inv_hom_id,
      Category.id_comp]
  have hH : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((G.truncLE m).X i) :=
    ⟨m, fun i hi ↦ (G.truncLE m).isZero_of_isStrictlyLE m i hi⟩
  obtain ⟨b, hbE⟩ := hbounded
  let N : ℤ := max b m
  let cone := mappingCone (q ≫ j)
  have hcone : ∀ i : ℤ, N < i → IsZero (cone.X i) := by
    intro i hi
    rw [mappingCone.isZero_X_iff]
    constructor
    · exact hbE (i + 1) (by dsimp [N] at hi; omega)
    · exact (G.truncLE m).isZero_of_isStrictlyLE m i (by dsimp [N] at hi; omega)
  obtain ⟨Q, ε, hQ⟩ := exists_functorial_boundedAbove_flat_replacement J R N
  let X : ObjectProperty.FullSubcategory
      (fun F : CochainComplex _ ℤ ↦ ∀ i : ℤ, N < i → IsZero (F.X i)) :=
    ⟨cone, hcone⟩
  obtain ⟨hflatQ, hboundQ, _, hquasiQ⟩ := hQ X
  obtain ⟨F, t, g, hb, hf, hg, ht⟩ :=
    exists_relative_boundedAbove_flat_extension E (G.truncLE m) (q ≫ j)
      ⟨b, hbE⟩ hflat (Q.obj X) (ε.app X) ⟨N, hboundQ⟩ hflatQ hquasiQ
  obtain ⟨F', s, g', hb', hf', hs, he', hsg⟩ :=
    exists_boundedAbove_flat_epicification hcover F (G.truncLE m) g hb hH hf
  have : QuasiIso s := hs
  have : QuasiIso (s ≫ g') := by rw [hsg]; exact hg
  have hg' : QuasiIso g' := quasiIso_of_comp_left s g'
  refine ⟨F', t ≫ s, g', hb', hf', hg', he', ?_⟩
  change (t ≫ s) ≫ g' ≫ G.ιTruncLE m = q ≫ G.ιTruncLE (n : ℤ)
  calc
    (t ≫ s) ≫ g' ≫ G.ιTruncLE m = t ≫ (s ≫ g') ≫ G.ιTruncLE m := by
      simp only [Category.assoc]
    _ = t ≫ g ≫ G.ιTruncLE m := by rw [hsg]
    _ = (q ≫ j) ≫ G.ιTruncLE m := by rw [← Category.assoc, ht]
    _ = q ≫ G.ιTruncLE (n : ℤ) := by rw [Category.assoc, hj]

end CochainComplex
