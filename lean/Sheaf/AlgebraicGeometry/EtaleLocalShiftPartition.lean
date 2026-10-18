/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.ProEtaleLocallyConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.AlgebraicGeometry.ProEtaleInverseImageStalk
import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
import Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
import Sheaf.Paper.SfCommonStageWeilCohomology
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

/-!
# Finite clopen shift loci for etale-local rank-one complexes

Source: Weil conjectures blueprint, main-20261015, sec-smooth-purity/sk-prop-a1-inv,
prop-pur-a1-invariance.proof.md, Step 1, lines 16--34, extracted shift-locus argument
(blueprint: lem-pur-etale-local-shift-partition).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The union of the images of precisely the cover members labelled by `n`.
Source: blueprint prop-pur-a1-invariance, Proof Step 1, shift-locus argument
(blueprint: lem-pur-etale-local-shift-partition). -/
def etaleLocalShiftLocus {Y : Scheme.{u}} {I : Type v} {U : I → Scheme.{u}}
    (f : ∀ i : I, U i ⟶ Y) (shift : I → ℤ) (n : ℤ) : Set Y :=
  {y | ∃ i : I, shift i = n ∧ y ∈ Set.range (f i)}

/-- Rank-one presentations of a bounded-cohomology complex determine finitely many
clopen shift loci. Local rank one is stated as actual module-sheaf trivializations on
pro-etale covering families, over the restricted constant ring. The last clause says
that discarding all empty members still gives a jointly surjective cover.

Source: blueprint main-20261015, prop-pur-a1-invariance.proof.md, Step 1, lines 16--34
(blueprint: lem-pur-etale-local-shift-partition).

Proof:
1. Exact constant-coefficient inverse image commutes with cohomology
   (prop-weil-pbc-proetale-constant-exact). By lem-pur-proetale-inverse-image-stalk,
   the geometric stalks of the pullback are those at the image geometric point.
   A shifted sheaf has cohomology only in degree minus its shift.
2. Trivialize each rank-one sheaf on a pro-etale cover. Lift a geometric point to a
   trivializing member: base change the fpqc cover (lem-galois-fpqc-covering-base-change),
   choose a nonempty fibre, and use lem-fix-weakly-etale-algclosed-section. Weakly etale
   maps remain weakly etale under base change and composition. Localized pointed
   neighbourhoods are cofinal, by fibre products and filteredness. Thus localization
   (lem-weil-proetale-weakly-etale-localization) and
   lem-weil-proetale-constant-sheaf-stalk identify its stalk with the nonzero ring A.
3. A point in two etale images admits lifts of the same geometric point to both
   members (lem-weil-pbc-etale-cover-geometric-point-lift). Its unique nonzero
   cohomology degree is both minus shifts, so the shifts are equal.
4. Etale morphisms are open (lem-weil-pbc-etale-morphism-open-map). The loci are
   therefore open, disjoint by Step 3, and exhaustive by joint surjectivity. Each
   complement is a union of the other open loci, so every locus is also closed.
5. A nonempty n-locus gives a nonzero stalk of H^(-n)(K). Its negative label lies
   in the finite cohomological support, proving finiteness of the nonempty loci.
   Each member maps into its labelled locus by definition. A member containing a
   lift of any point is nonempty, so deleting empty members preserves the cover. -/
theorem etaleLocalShiftPartition
    (A : Type u) [CommRing A] [Finite A] [Nontrivial A]
    (Y : Scheme.{u}) (K : proEtaleDerivedCategory Y A)
    (_hK : Set.Finite {q : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules Y (proEtaleConstantRing Y A)) q).obj K)})
    (I : Type v) (U : I → Scheme.{u}) (f : ∀ i : I, U i ⟶ Y)
    [∀ i : I, Etale (f i)]
    (_hcover : ∀ y : Y, ∃ i : I, y ∈ Set.range (f i))
    (shift : I → ℤ)
    (L : ∀ i : I, proEtaleRingModules (U i) (proEtaleConstantRing (U i) A))
    (_hlocal : ∀ i : I, IsLocallyConstantProEtaleModuleSheaf (U i) A (L i))
    (_hrank : ∀ i : I, ∃ (J : Type (u + 1)) (V : J → (U i).ProEt)
      (g : ∀ j : J, V j ⟶ ProEt.mk (𝟙 (U i))),
      Presieve.ofArrows V g ∈ (ProEt.precoverage (U i)).coverings _ ∧
        ∀ j : J, Nonempty ((L i).over (V j) ≅ SheafOfModules.unit
          (((sheafCompose (ProEt.topology (U i))
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (proEtaleConstantRing (U i) A)).over (V j))))
    (_hshape : ∀ i : I, Nonempty
      ((proEtaleConstantRingDerivedPullback A (f i)).obj K ≅
        ((DerivedCategory.singleFunctor
          (proEtaleRingModules (U i) (proEtaleConstantRing (U i) A)) 0).obj (L i))⟦shift i⟧)) :
    (∀ i j : I, (Set.range (f i) ∩ Set.range (f j)).Nonempty → shift i = shift j) ∧
    Pairwise (fun n m : ℤ ↦ Disjoint (etaleLocalShiftLocus f shift n)
      (etaleLocalShiftLocus f shift m)) ∧
    (∀ n : ℤ, IsClopen (etaleLocalShiftLocus f shift n)) ∧
    (⋃ n : ℤ, etaleLocalShiftLocus f shift n) = Set.univ ∧
    Set.Finite {n : ℤ | (etaleLocalShiftLocus f shift n).Nonempty} ∧
    (∀ n : ℤ, (etaleLocalShiftLocus f shift n).Nonempty →
      ¬ IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y A)) (-n)).obj K)) ∧
    (∀ i : I, Nonempty (U i) →
      Set.range (f i) ⊆ etaleLocalShiftLocus f shift (shift i)) ∧
    (∀ y : Y, ∃ i : {i : I // Nonempty (U i)}, y ∈ Set.range (f i.val)) := by
  sorry

end AlgebraicGeometry.Scheme
