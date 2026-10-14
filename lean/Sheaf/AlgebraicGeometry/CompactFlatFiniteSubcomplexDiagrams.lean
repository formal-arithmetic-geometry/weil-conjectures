/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap

public import Mathlib.CategoryTheory.Filtered.Basic

/-! # Compatible filtered diagrams of finite compact-flat subcomplexes

Source: the finite-subcomplex paragraph of
`lem-sc-compact-flat-telescope-bar-enlargement`.
(blueprint: lem-sc-compact-flat-finite-subcomplex-diagrams).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Inclusion of the objects appearing by stage n into the full indexing preorder. -/
def compactFlatStageInclusion {I : Type u} [Preorder I] (stage : I → ℕ) (n : ℕ) :
    {j : I // stage j ≤ n} ⥤ I where
  obj j := j.1
  map f := homOfLE (leOfHom f)

/-- A stage-filtered small diagram of finite compact-flat complexes whose stage
colimits are the given tower. The indexing order and the complexes are actual
data, and every augmentation is a specified cocone, not an existence choice. -/
structure CompactFlatFiniteSubcomplexDiagrams (Y : Scheme.{u})
    (L : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (l : ∀ n : ℕ, L n ⟶ L (n + 1)) where
  /-- Stage-labelled finite subcomplexes. -/
  index : Type u
  /-- The order includes transition-carried inclusions. -/
  [indexPreorder : Preorder index]
  /-- The first stage at which an object appears. -/
  stage : index → ℕ
  /-- Arrows never decrease the source-stage label. -/
  stage_mono : Monotone stage
  /-- The finite complexes and their inclusion maps. -/
  diagram : index ⥤ CochainComplex
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ
  /-- Every initial-stage diagram is filtered and nonempty. -/
  filtered : ∀ n : ℕ, IsFiltered {j : index // stage j ≤ n}
  /-- The stage n cocone, with vertex exactly L n. -/
  augmentation : ∀ n : ℕ, compactFlatStageInclusion stage n ⋙ diagram ⟶
    (Functor.const {j : index // stage j ≤ n}).obj (L n)
  /-- These cocones exhibit the stage colimits. -/
  isColimit : ∀ n : ℕ, IsColimit { pt := L n, ι := augmentation n }
  /-- The cocones commute strictly with the tower maps. -/
  compatibility : ∀ (n : ℕ) (j : index) (hj : stage j ≤ n),
    (augmentation n).app ⟨j, hj⟩ ≫ l n =
      (augmentation (n + 1)).app ⟨j, Nat.le_trans hj (Nat.le_succ n)⟩
  /-- Each finite piece has only finitely many nonzero degrees. -/
  finiteDegrees : ∀ j : index, ∃ lo hi : ℤ, ∀ i : ℤ,
    i < lo ∨ hi < i → IsZero ((diagram.obj j).X i)
  /-- All pieces appearing by stage n have a common upper bound. -/
  stageBound : ∀ n : ℕ, ∃ hi : ℤ, ∀ j : {j : index // stage j ≤ n}, ∀ i : ℤ,
    hi < i → IsZero ((diagram.obj j.1).X i)
  /-- The finite pieces really embed into their stage colimits. -/
  mono : ∀ (n : ℕ) (j : {j : index // stage j ≤ n}) (i : ℤ),
    Mono (((augmentation n).app j).f i)
  /-- Every term is a finite coproduct of coproduct-compact flat sheaves. -/
  generators : ∀ (j : index) (i : ℤ), ∃ (I : Type u), Finite I ∧
    ∃ G : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace),
      Nonempty ((diagram.obj j).X i ≅ ∐ G) ∧
      (∀ k : I, SheafOfModules.IsFlat (G k)) ∧
      ∀ (k : I) (K : Type u)
        (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (f : G k ⟶ ∐ H),
        ∃ (S : Finset K) (g : G k ⟶ ∐ (fun t : {t // t ∈ S} ↦ H t.1)),
          g ≫ Sigma.desc (fun t : {t // t ∈ S} ↦ Sigma.ι H t.1) = f

attribute [instance] CompactFlatFiniteSubcomplexDiagrams.indexPreorder

/-- Construct the finite-subcomplex diagrams before any target or bar construction
is introduced.

Source: `lem-sc-compact-flat-telescope-bar-enlargement`, the paragraph beginning
"Fix generator decompositions in each term" and ending with the colimit L_n.

Proof. Fix the summand decompositions in every term of L_m. For each generator
summand, choose a finite support for its differential in the next degree. A finite
set of summands in finitely many degrees can be enlarged to a finite subcomplex:
add those chosen supports, and repeat upwards. Boundedness above makes the
iteration terminate. The initial finite set bounds its nonzero degrees below.
Each term of this subcomplex is a finite coproduct of the original compact flat
summands; its differential is the restriction determined by these inclusions.

Index by labelled pairs (m, a finite summand subcomplex of L_m). Order two pairs
with labels m ≤ m' when the iterated transition carries the earlier subcomplex
into the later one. Inclusion maps into L_m' are monic, so this factorization is
unique, respects composition, and defines the diagram functor. The stage label
is monotone. At stage n keep all labels at most n. A finite collection can be
carried to stage n and included in one finite subcomplex: compactness factors
its finitely many generators through finite subcoproducts of L_n in each of its
finitely many degrees; close these supports under the differential. Thus the
stage-n subdiagram is cofinal and the stage diagram is filtered. The zero
subcomplex at stage zero supplies nonemptiness, including the zero tower.

The stage-n subcomplexes have union L_n, because every summand lies in one of
them. A compatible family of maps out of these subcomplexes defines the unique
map out of L_n termwise, using the original coproduct summands. It commutes with
the differentials since every finite collection is contained in a subcomplex.
This proves the stated cochain-complex colimit universal property. Carry the
cocones to later stages by the tower transitions to obtain strict compatibility.
Their components are monic: the finite summand inclusions are split monic and
the tower transitions are degreewise split monic. For stageBound, take the maximum
of the upper bounds of L_0 through L_n. The finite-degree and finite-generator
fields hold by construction, with the inherited compactness factorizations.
All these are existential witnesses; no definition selects an arbitrary object
from an unproved existence theorem.
(blueprint: lem-sc-compact-flat-finite-subcomplex-diagrams). -/
theorem exists_compact_flat_finite_subcomplex_diagrams (Y : Scheme.{u})
    (L : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (l : ∀ n : ℕ, L n ⟶ L (n + 1))
    (hb : ∀ n : ℕ, ∃ z : ℤ, ∀ i : ℤ, z < i → IsZero ((L n).X i))
    (hsplit : ∀ (n : ℕ) (i : ℤ), IsSplitMono ((l n).f i))
    (hgen :
      ∀ (n : ℕ) (i : ℤ), ∃ (I : Type u)
        (G : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace)),
        Nonempty ((L n).X i ≅ ∐ G) ∧
        (∀ j : I, SheafOfModules.IsFlat (G j)) ∧
        ∀ (j : I) (K : Type u)
          (H : K → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
          (f : G j ⟶ ∐ H),
          ∃ (S : Finset K) (g : G j ⟶ ∐ (fun k : {k // k ∈ S} ↦ H k.1)),
            g ≫ Sigma.desc (fun k : {k // k ∈ S} ↦ Sigma.ι H k.1) = f)
 :
    Nonempty (CompactFlatFiniteSubcomplexDiagrams Y L l) := by sorry

end AlgebraicGeometry
