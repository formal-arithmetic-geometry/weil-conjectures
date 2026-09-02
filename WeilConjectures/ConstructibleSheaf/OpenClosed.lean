/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.ConstructibleSheaf.Zero
public import WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion
public import WeilConjectures.SixFunctors.OpenClosed.Complex

/-!
# The open–closed dévissage of constructible sheaves

Let `(j : U ⟶ X, i : Z ⟶ X)` be a complementary pair: an open immersion and a closed
immersion with complementary ranges.

```
         j                 i
    U ────────→ X ←──────── Z        range i = (range j)ᶜ
```

A sheaf `F` on the small étale site of `X` is constructible if and only if `j^* F` and
`i^* F` are: one direction is the pullback stability of
`WeilConjectures.ConstructibleSheaf.Pullback`, the other concatenates stratifications of `U`
and `Z` to a stratification of `X`. Consequently the pushforward `i_* G` of a constructible
sheaf on `Z` and the extension by zero `j_! G` of a constructible sheaf on `U` are
constructible: their pullbacks to the other member of the pair vanish, and a zero sheaf is
constructible (`WeilConjectures.ConstructibleSheaf.Zero`).

## Main results

- `AlgebraicGeometry.Scheme.Stratification.openClosed` — stratifications of `U` and of `Z`
  concatenate to a stratification of `X`
  (blueprint: `lemma:constructible-openclosed-stratification`).
- `AlgebraicGeometry.Scheme.isConstructibleSheaf_iff_of_range_eq_compl` — `F` is
  constructible if and only if `j^* F` and `i^* F` are
  (blueprint: `prop:constructible-open-closed`).
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.openImmersionLowerShriek` — `j_! G` is
  constructible (blueprint: `lemma:constructible-lowerShriek-open`).
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.lowerStar` — `i_* G` is constructible
  (blueprint: `lemma:constructible-lowerStar-closed`).

-/

@[expose] public section

universe u u'

open CategoryTheory Limits
open scoped AlgebraicGeometry.Etale

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X U Z : Scheme.{u}}

section Stratification

variable (j : U ⟶ X) (i : Z ⟶ X) [IsImmersion j] [IsImmersion i]
  (hij : Set.range i.base = (Set.range j.base)ᶜ)

include hij in
/-- Stratifications of the members of a complementary pair `(j, i)` concatenate to a
stratification of `X`: the strata are the images of the strata of `U` and of `Z`, realized
by the composites `SU.immersion l ≫ j` and `SZ.immersion l ≫ i`. Both the domain and the
immersion of a stratum are read off a single `Sum.elim` valued in `Over X`, so that a case
split on `finSumFinEquiv.symm k` does not have to transport along the type of the domain.

```
         j                 i
    U ────────→ X ←──────── Z        range i = (range j)ᶜ
```

Only the immersion structure of `j` and `i` is used, not that one is open and the other
closed. The topological part is `Topology.Stratification.sum`.
(blueprint: `lemma:constructible-openclosed-stratification`) -/
@[simps! n stratum domain immersion]
def Stratification.openClosed (SU : Stratification U) (SZ : Stratification Z) :
    Stratification X where
  toStratification := .sum j.isEmbedding i.isEmbedding j.isLocallyClosed_range
    i.isLocallyClosed_range hij SU.toStratification SZ.toStratification
  domain k := (Sum.elim (fun l ↦ Over.mk (SU.immersion l ≫ j))
    (fun l ↦ Over.mk (SZ.immersion l ≫ i)) (finSumFinEquiv.symm k)).left
  immersion k := (Sum.elim (fun l ↦ Over.mk (SU.immersion l ≫ j))
    (fun l ↦ Over.mk (SZ.immersion l ≫ i)) (finSumFinEquiv.symm k)).hom
  isImmersion k := by
    obtain l | l := finSumFinEquiv.symm k
    · exact inferInstanceAs (IsImmersion (SU.immersion l ≫ j))
    · exact inferInstanceAs (IsImmersion (SZ.immersion l ≫ i))
  range_immersion k := by
    rw [Topology.Stratification.sum_stratum]
    obtain l | l := finSumFinEquiv.symm k
    · change Set.range (SU.immersion l ≫ j).base = j.base '' SU.stratum l
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, SU.range_immersion]
    · change Set.range (SZ.immersion l ≫ i).base = i.base '' SZ.stratum l
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, SZ.range_immersion]

end Stratification

section Criterion

variable (j : U ⟶ X) (i : Z ⟶ X)

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

variable [IsImmersion j] [IsImmersion i] (hij : Set.range i.base = (Set.range j.base)ᶜ)

include hij in
/-- **A sheaf is constructible if and only if its restrictions to the members of a
complementary pair `(j, i)` are.** The stratification of `X` witnessing constructibility of
`F` is the concatenation `Stratification.openClosed` of stratifications of `U` and of `Z`;
its strata are immersed in `X` through `j` or through `i`, so the restriction of `F` to a
stratum is a restriction of `j^* F` or of `i^* F`:

```
       κ_l          j
  W_l ─────→ U ─────→ X          (κ_l ≫ j)^* F ≅ κ_l^* (j^* F)
     \_______________↗
          κ_l ≫ j
```
(blueprint: `prop:constructible-open-closed`) -/
theorem isConstructibleSheaf_iff_of_range_eq_compl (F : Sheaf X.smallEtaleTopology A) :
    IsConstructibleSheaf F ↔
      IsConstructibleSheaf ((j)^*[A].obj F) ∧ IsConstructibleSheaf ((i)^*[A].obj F) := by
  refine ⟨fun _ ↦ ⟨IsConstructibleSheaf.upperStar j F, IsConstructibleSheaf.upperStar i F⟩,
    fun ⟨hU, hZ⟩ ↦ ?_⟩
  obtain ⟨SU, hSU⟩ := hU.exists_stratification
  obtain ⟨SZ, hSZ⟩ := hZ.exists_stratification
  have H : ∀ s : Fin SU.n ⊕ Fin SZ.n, IsFiniteLocallyConstantSheaf
      (((Sum.elim (fun l ↦ Over.mk (SU.immersion l ≫ j))
        (fun l ↦ Over.mk (SZ.immersion l ≫ i)) s).hom)^*[A].obj F) := by
    rintro (l | l)
    · have := hSU l
      exact IsFiniteLocallyConstantSheaf.of_iso
        (F := (SU.immersion l)^*[A].obj ((j)^*[A].obj F))
        ((Etale.upperStarComp A (SU.immersion l) j).app F).symm
    · have := hSZ l
      exact IsFiniteLocallyConstantSheaf.of_iso
        (F := (SZ.immersion l)^*[A].obj ((i)^*[A].obj F))
        ((Etale.upperStarComp A (SZ.immersion l) i).app F).symm
  exact ⟨Stratification.openClosed j i hij SU SZ, fun k ↦ H (finSumFinEquiv.symm k)⟩

end Criterion

section Devissage

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [PreservesLimit (Functor.empty.{0} A) (CategoryTheory.forget A)]

section LowerShriek

variable (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]

/-- **The extension by zero of a constructible sheaf along an open immersion is
constructible**: its restriction to `U` is the sheaf itself, and its restriction to the
complement `Z` vanishes.

```
      j^* j_! G ≅ G                 i^* j_! G = 0
   U ──────────────→ X ←────────────────── Z        range i = (range j)ᶜ
```

The closed complement `i` is data rather than a construction: the complement of the range of
`j` is closed, but turning it into a closed subscheme of `X` requires a choice of scheme
structure, and the statement is insensitive to that choice. Contrast
`IsConstructibleSheaf.lowerStar`, where the complementary open needs no choice.
(blueprint: `lemma:constructible-lowerShriek-open`) -/
theorem IsConstructibleSheaf.openImmersionLowerShriek
    (hij : Set.range i.base = (Set.range j.base)ᶜ) (G : Sheaf U.smallEtaleTopology A)
    [IsConstructibleSheaf G] : IsConstructibleSheaf ((j)_!open[A].obj G) := by
  rw [isConstructibleSheaf_iff_of_range_eq_compl j i hij]
  exact ⟨IsConstructibleSheaf.of_iso (F := G)
      (asIso ((Etale.openImmersionLowerShriekUpperStarAdjunction A j).unit.app G)),
    IsConstructibleSheaf.of_isZero
      (Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range A j i
        (disjoint_range_of_range_eq_compl j i hij) G)⟩

end LowerShriek

section LowerStar

variable (i : Z ⟶ X) [IsClosedImmersion i]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [hJ : Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

include hJ in
/-- **The pushforward of a constructible sheaf along a closed immersion is constructible**:
its restriction to `Z` is the sheaf itself, and its restriction to the open complement
vanishes.

```
    (W.ι)^* i_* G = 0               i^* i_* G ≅ G
   W ──────────────→ X ←────────────────── Z        W = (range i)ᶜ
```

Unlike in `IsConstructibleSheaf.openImmersionLowerShriek`, the complementary open immersion
needs no extra data: it is the inclusion of the open complement `W` of the range of `i`.
(blueprint: `lemma:constructible-lowerStar-closed`) -/
theorem IsConstructibleSheaf.lowerStar (G : Sheaf Z.smallEtaleTopology A)
    [IsConstructibleSheaf G] : IsConstructibleSheaf ((i)_*[A].obj G) := by
  let W : X.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hij : Set.range i.base = (Set.range W.ι.base)ᶜ := by
    rw [W.range_ι]
    exact (compl_compl _).symm
  rw [isConstructibleSheaf_iff_of_range_eq_compl W.ι i hij]
  exact ⟨IsConstructibleSheaf.of_isZero
      (Etale.isZero_upperStar_lowerStar_of_disjoint_range A W.ι i
        (disjoint_range_of_range_eq_compl W.ι i hij) G),
    IsConstructibleSheaf.of_iso (F := G)
      (asIso ((Etale.upperStarLowerStarAdjunction A i).counit.app G)).symm⟩

end LowerStar

end Devissage

end AlgebraicGeometry.Scheme

end
