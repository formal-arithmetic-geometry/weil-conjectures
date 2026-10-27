# AlgebraicTopology.BicosimplicialShuffle totalization definitions

## Reason

The finite-evaluation transfer statement needs to name the concrete totals, inclusions and
shuffle components. Keeping these definitions in the theorem module would make that module
import itself through the transfer lemma. Move the twelve definitions to
`Sheaf.Algebra.Homology.BicosimplicialShuffleObjects` and publicly import that module from
the original item. This is an acyclic statement-interface extraction, not a compile-time split.
All twelve names, universes, binders, visibility and definition bodies are preserved. The
theorem `exists_shuffle` keeps its complete original signature. No source-library file changes.

## Old

In `Sheaf.Algebra.Homology.BicosimplicialShuffleTotalization`:

```lean
/-- The diagonal alternating-coface bicomplex, before totalization.
Source: current blueprint, direct-images proof (3), diagonal differential.
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
def diagonalBicomplex (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ) :
    HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  AlternatingCofaceMapComplex.obj (CategoryTheory.Functor.diag SimplexCategory ⋙ X)

/-- The three nonnegative cochain indices, ordered first cosimplicial, second
cosimplicial, internal. Source: current blueprint, direct-images proof (3).
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
def tripleComplex (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ) :
    HomologicalComplex₂ (CochainComplex C ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  AlternatingCofaceMapComplex.obj
    (curry.obj X ⋙ alternatingCofaceMapComplex (CochainComplex C ℕ))

/-- First totalize the two cosimplicial indices in the category of internal complexes.
Source: current blueprint, direct-images proof (3); differential δ₁ + (-1)^a δ₂.
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
noncomputable def cosimplicialTotal
    (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ) :
    HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  (tripleComplex X).total (ComplexShape.up ℕ)

/-- The diagonal total D(X), with differential δ_diag + (-1)^n d_internal.
Source: current blueprint, direct-images proof (3).
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
noncomputable def diagonalTotal
    (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ) : CochainComplex C ℕ :=
  (diagonalBicomplex X).total (ComplexShape.up ℕ)

/-- The successive total T(X), with differential
δ₁ + (-1)^a δ₂ + (-1)^(a+b) d_internal.
Source: current blueprint, direct-images proof (3).
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
noncomputable def successiveTotal
    (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ) : CochainComplex C ℕ :=
  (cosimplicialTotal X).total (ComplexShape.up ℕ)

/-- Functoriality of D(X), using the existing alternating-coface and total map.
Source: current blueprint, direct-images proof (3), naturality in X.
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
noncomputable def diagonalMap
    {X Y : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ} (f : X ⟶ Y) :
    diagonalTotal X ⟶ diagonalTotal Y :=
  HomologicalComplex₂.total.map
    (AlternatingCofaceMapComplex.map
      (whiskerLeft (CategoryTheory.Functor.diag SimplexCategory) f)) (ComplexShape.up ℕ)

/-- Functoriality of T(X), totaling first the two cosimplicial indices and then the
internal index. Source: current blueprint, direct-images proof (3), naturality in X.
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
noncomputable def successiveMap
    {X Y : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ} (f : X ⟶ Y) :
    successiveTotal X ⟶ successiveTotal Y :=
  HomologicalComplex₂.total.map
    (HomologicalComplex₂.total.map
      (AlternatingCofaceMapComplex.map
        (whiskerRight (curry.map f) (alternatingCofaceMapComplex (CochainComplex C ℕ))))
      (ComplexShape.up ℕ)) (ComplexShape.up ℕ)

/-- The canonical inclusion X^(n,n,r) into D(X)^(n+r).
Source: current blueprint, direct-images proof (3), finite diagonal sum.
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
noncomputable def diagonalInclusion
    (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ)
    (n r m : ℕ) (h : n + r = m) :
    (X.obj (⦋n⦌, ⦋n⦌)).X r ⟶ (diagonalTotal X).X m :=
  (diagonalBicomplex X).ιTotal (ComplexShape.up ℕ) n r m h

/-- The canonical inclusion X^(a,b,r) into T(X)^(a+b+r), with the first direction
first. Source: current blueprint, direct-images proof (3), finite triple sum.
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
noncomputable def successiveInclusion
    (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ)
    (a b r m : ℕ) (h : a + b + r = m) :
    (X.obj (⦋a⦌, ⦋b⦌)).X r ⟶ (successiveTotal X).X m :=
  ((tripleComplex X).ιTotal (ComplexShape.up ℕ) a b (a + b) rfl).f r ≫
    (cosimplicialTotal X).ιTotal (ComplexShape.up ℕ) (a + b) r m h

/-- The monotone surjection α_μ(i) = #{j ∈ μ | j < i}. Taking the complement
produces α_ν. Source: current blueprint, direct-images proof (3), shuffle formula.
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
def shuffleSurjection (n : ℕ) (μ : Finset (Fin n)) : ⦋n⦌ ⟶ ⦋μ.card⦌ :=
  SimplexCategory.mkHom
    { toFun := fun i ↦ ⟨(μ.filter (fun j ↦ j.val < i.val)).card,
        Nat.lt_succ_of_le (Finset.card_filter_le μ _)⟩
      monotone' := fun _i _j hij ↦ Finset.card_le_card
        (Finset.monotone_filter_right μ (fun _k _ hk ↦ lt_of_lt_of_le hk hij)) }

/-- The sign of the permutation with increasing μ followed by increasing μᶜ:
its inversions are pairs (i,j) ∈ μ × μᶜ with j < i.
Source: current blueprint, direct-images proof (3), ε(μ,ν).
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
def shuffleSign (n : ℕ) (μ : Finset (Fin n)) : ℤ :=
  (-1) ^ ((μ.product μᶜ).filter (fun ij ↦ ij.2 < ij.1)).card

/-- A shuffle summand with its target inclusion. Every subset μ of Fin n gives
exactly one partition (μ,μᶜ); its two cardinalities sum to n.
Source: current blueprint, direct-images proof (3), specified shuffle component.
(blueprint: lem-sfb-bicosimplicial-shuffle-totalization). -/
noncomputable def shuffleTerm
    (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ)
    (n r m : ℕ) (h : n + r = m) (μ : Finset (Fin n)) :
    (X.obj (⦋n⦌, ⦋n⦌)).X r ⟶ (successiveTotal X).X m :=
  shuffleSign n μ • ((X.map (shuffleSurjection n μ, shuffleSurjection n μᶜ)).f r ≫
    successiveInclusion X μ.card μᶜ.card r m
      ((congrArg (fun k ↦ k + r)
        ((Finset.card_add_card_compl μ).trans (Fintype.card_fin n))).trans h))
```

## New

In `Sheaf.Algebra.Homology.BicosimplicialShuffleObjects`, with the same namespace and
`{C : Type u} [Category.{v} C] [Abelian C]` context:

```lean
/-- The diagonal alternating-coface bicomplex, before totalization.
Source: current blueprint, direct-images proof (3), diagonal differential.
(blueprint: def-sfb-bicosimplicial-shuffle-totalizations). -/
def diagonalBicomplex (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ) :
    HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  AlternatingCofaceMapComplex.obj (CategoryTheory.Functor.diag SimplexCategory ⋙ X)

/-- The three nonnegative cochain indices, ordered first cosimplicial, second
cosimplicial, internal. Source: current blueprint, direct-images proof (3).
(blueprint: def-sfb-bicosimplicial-shuffle-totalizations). -/
def tripleComplex (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ) :
    HomologicalComplex₂ (CochainComplex C ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  AlternatingCofaceMapComplex.obj
    (curry.obj X ⋙ alternatingCofaceMapComplex (CochainComplex C ℕ))

/-- First totalize the two cosimplicial indices in the category of internal complexes.
Source: current blueprint, direct-images proof (3); differential δ₁ + (-1)^a δ₂.
(blueprint: def-sfb-bicosimplicial-shuffle-totalizations). -/
noncomputable def cosimplicialTotal
    (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ) :
    HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  (tripleComplex X).total (ComplexShape.up ℕ)

/-- The diagonal total D(X), with differential δ_diag + (-1)^n d_internal.
Source: current blueprint, direct-images proof (3).
(blueprint: def-sfb-bicosimplicial-shuffle-totalizations). -/
noncomputable def diagonalTotal
    (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ) : CochainComplex C ℕ :=
  (diagonalBicomplex X).total (ComplexShape.up ℕ)

/-- The successive total T(X), with differential
δ₁ + (-1)^a δ₂ + (-1)^(a+b) d_internal.
Source: current blueprint, direct-images proof (3).
(blueprint: def-sfb-bicosimplicial-shuffle-totalizations). -/
noncomputable def successiveTotal
    (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ) : CochainComplex C ℕ :=
  (cosimplicialTotal X).total (ComplexShape.up ℕ)

/-- Functoriality of D(X), using the existing alternating-coface and total map.
Source: current blueprint, direct-images proof (3), naturality in X.
(blueprint: def-sfb-bicosimplicial-shuffle-totalizations). -/
noncomputable def diagonalMap
    {X Y : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ} (f : X ⟶ Y) :
    diagonalTotal X ⟶ diagonalTotal Y :=
  HomologicalComplex₂.total.map
    (AlternatingCofaceMapComplex.map
      (whiskerLeft (CategoryTheory.Functor.diag SimplexCategory) f)) (ComplexShape.up ℕ)

/-- Functoriality of T(X), totaling first the two cosimplicial indices and then the
internal index. Source: current blueprint, direct-images proof (3), naturality in X.
(blueprint: def-sfb-bicosimplicial-shuffle-totalizations). -/
noncomputable def successiveMap
    {X Y : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ} (f : X ⟶ Y) :
    successiveTotal X ⟶ successiveTotal Y :=
  HomologicalComplex₂.total.map
    (HomologicalComplex₂.total.map
      (AlternatingCofaceMapComplex.map
        (whiskerRight (curry.map f) (alternatingCofaceMapComplex (CochainComplex C ℕ))))
      (ComplexShape.up ℕ)) (ComplexShape.up ℕ)

/-- The canonical inclusion X^(n,n,r) into D(X)^(n+r).
Source: current blueprint, direct-images proof (3), finite diagonal sum.
(blueprint: def-sfb-bicosimplicial-shuffle-totalizations). -/
noncomputable def diagonalInclusion
    (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ)
    (n r m : ℕ) (h : n + r = m) :
    (X.obj (⦋n⦌, ⦋n⦌)).X r ⟶ (diagonalTotal X).X m :=
  (diagonalBicomplex X).ιTotal (ComplexShape.up ℕ) n r m h

/-- The canonical inclusion X^(a,b,r) into T(X)^(a+b+r), with the first direction
first. Source: current blueprint, direct-images proof (3), finite triple sum.
(blueprint: def-sfb-bicosimplicial-shuffle-totalizations). -/
noncomputable def successiveInclusion
    (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ)
    (a b r m : ℕ) (h : a + b + r = m) :
    (X.obj (⦋a⦌, ⦋b⦌)).X r ⟶ (successiveTotal X).X m :=
  ((tripleComplex X).ιTotal (ComplexShape.up ℕ) a b (a + b) rfl).f r ≫
    (cosimplicialTotal X).ιTotal (ComplexShape.up ℕ) (a + b) r m h

/-- The monotone surjection α_μ(i) = #{j ∈ μ | j < i}. Taking the complement
produces α_ν. Source: current blueprint, direct-images proof (3), shuffle formula.
(blueprint: def-sfb-bicosimplicial-shuffle-totalizations). -/
def shuffleSurjection (n : ℕ) (μ : Finset (Fin n)) : ⦋n⦌ ⟶ ⦋μ.card⦌ :=
  SimplexCategory.mkHom
    { toFun := fun i ↦ ⟨(μ.filter (fun j ↦ j.val < i.val)).card,
        Nat.lt_succ_of_le (Finset.card_filter_le μ _)⟩
      monotone' := fun _i _j hij ↦ Finset.card_le_card
        (Finset.monotone_filter_right μ (fun _k _ hk ↦ lt_of_lt_of_le hk hij)) }

/-- The sign of the permutation with increasing μ followed by increasing μᶜ:
its inversions are pairs (i,j) ∈ μ × μᶜ with j < i.
Source: current blueprint, direct-images proof (3), ε(μ,ν).
(blueprint: def-sfb-bicosimplicial-shuffle-totalizations). -/
def shuffleSign (n : ℕ) (μ : Finset (Fin n)) : ℤ :=
  (-1) ^ ((μ.product μᶜ).filter (fun ij ↦ ij.2 < ij.1)).card

/-- A shuffle summand with its target inclusion. Every subset μ of Fin n gives
exactly one partition (μ,μᶜ); its two cardinalities sum to n.
Source: current blueprint, direct-images proof (3), specified shuffle component.
(blueprint: def-sfb-bicosimplicial-shuffle-totalizations). -/
noncomputable def shuffleTerm
    (X : SimplexCategory × SimplexCategory ⥤ CochainComplex C ℕ)
    (n r m : ℕ) (h : n + r = m) (μ : Finset (Fin n)) :
    (X.obj (⦋n⦌, ⦋n⦌)).X r ⟶ (successiveTotal X).X m :=
  shuffleSign n μ • ((X.map (shuffleSurjection n μ, shuffleSurjection n μᶜ)).f r ≫
    successiveInclusion X μ.card μᶜ.card r m
      ((congrArg (fun k ↦ k + r)
        ((Finset.card_add_card_compl μ).trans (Fintype.card_fin n))).trans h))
```

The original module publicly imports this definitions module. Its original public imports
remain available transitively through the definitions module. Only the docstring ownership
node changes; every definition term is verbatim.

## Users

`python3 tools/downstream.py Sheaf.Algebra.Homology.BicosimplicialShuffleTotalization`
reported zero downstream modules on 2026-10-25. A source search also found no other Lean
use of these twelve names. DAG parents are preserved; none is withdrawn. There is no change
to the mathematical meaning of a target or to the unit route.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.BicosimplicialShuffleTotalization | E9 | Publicly imports unchanged definitions and proves the original theorem from the transfer lemma. |
| Sheaf.Algebra.Homology.BicosimplicialShuffleObjects | new, E9 | Owns the twelve unchanged definitions. |
| Sheaf.Algebra.Homology.UniversalShuffleEvaluation | new, E9 | Uses those definitions in its conditional transfer statement. |

## Status

landed 20261025T060817-L-2374026 2026-10-25 (merge of deliver/E9/Sheaf.Algebra.Homology.BicosimplicialShuffleTotalization)
