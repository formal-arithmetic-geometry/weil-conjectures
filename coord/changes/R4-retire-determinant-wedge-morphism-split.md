# AlgebraicGeometry.Scheme.Modules.determinant_wedgeMorphism_bijective_of_split

## Reason

Retire the duplicate assigned by coord/retire-items.tsv:918 and the human's
coord/changes/retire-sheaf-twins-20261020.md hand-off. Both implementations are
already proved; the queue lists a retirement rather than a proof hole. The adopted
theorem uses canonical exteriorPower objects; the duplicate used exteriorSheaf.
Existing exteriorSheafPowerIso comparisons identify the constructions and wedges.
No source-library file, target statement, or public consumer signature changes.
There is no current return or rework row for this item.

## Old

The withdrawn duplicate supplied the following legacy theorem:

```lean
theorem determinant_wedgeMorphism_bijective_of_split {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₃.IsFiniteLocallyFreeOfRank r₃]
    (φ : exteriorSheaf S.X₁ r₁ ⊗ exteriorSheaf S.X₃ r₃ ⟶ exteriorSheaf S.X₂ r₂)
    (hφ : ∀ (V : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op V))
      (b : Fin r₃ → S.X₃.val.obj (op V)) (c : Fin r₃ → S.X₂.val.obj (op V)),
      (∀ i, S.g.val.app (op V) (c i) = b i) →
      φ.val.app (op V)
        (tmulSection (exteriorSheafSection S.X₁ r₁ V a)
          (exteriorSheafSection S.X₃ r₃ V b)) =
        exteriorSheafSection S.X₂ r₂ V
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op V) (a j)) c (Fin.cast hr i)))
    (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g) :
    ∀ W ≤ U, Function.Bijective (φ.app W)
```

## New

The same DAG node is attached to the unchanged adopted theorem in
WeilConjectures.AlgebraicGeometry.Modules.DeterminantWedgeMorphismSplit:

```lean
theorem determinant_wedgeMorphism_bijective_of_split {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r₁ r₂ r₃ : ℕ) (hr : r₂ = r₁ + r₃)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₃.IsFiniteLocallyFreeOfRank r₃]
    (φ : exteriorPower S.X₁ r₁ ⊗ exteriorPower S.X₃ r₃ ⟶ exteriorPower S.X₂ r₂)
    (hφ : ∀ (V : X.Opens) (a : Fin r₁ → S.X₁.val.obj (op V))
      (b : Fin r₃ → S.X₃.val.obj (op V)) (c : Fin r₃ → S.X₂.val.obj (op V)),
      (∀ i, S.g.val.app (op V) (c i) = b i) →
      φ.val.app (op V)
        (tmulSection (wedge (M := S.X₁) (r := r₁) (U := V) a)
          (wedge (M := S.X₃) (r := r₃) (U := V) b)) =
        wedge (M := S.X₂) (r := r₂) (U := V)
          (fun i ↦ Fin.append (fun j ↦ S.f.val.app (op V) (a j)) c (Fin.cast hr i)))
    (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g) :
    ∀ W ≤ U, Function.Bijective (φ.app W)
```

Withdraw the duplicate through deleted.txt. The only direct consumer,
Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists, replaces its private
import with the adopted module and ExteriorSheafPowerComparison. Its declaration
signature and public imports stay verbatim. The declaration-local transparency
option supports the existing two exterior-sheaf constructions.

Its proof forms eA as the tensor of the outside comparison isomorphisms and eB
as the middle comparison, and conjugates phi to psi=eA.inv ≫ phi ≫ eB.hom.
The tensor section formula, inverse wedge comparison, original hphi, and the
inverse-hom identity prove the canonical wedge formula. The original splitting
cover and adopted theorem give local bijectivity of psi and hence IsIso psi.
The equality eA.hom ≫ psi ≫ eB.inv = phi transfers invertibility back to phi.
The original asIso construction gives the unchanged conclusion and wedge formula.
The comparisons and argument apply to zero ranks, empty opens and zero rings.

The parent node retains its dependency on this node and adds the comparison node.
The retired node keeps its mathematical statement, source and unit; its Lean
attachment and proof describe the adopted realization. No DAG node is deleted.

## Users

The downstream declaration scan and searches over Lean, nodes, notes and quarantine
find one direct consumer and three further transitive consumers. No claim exists
for the direct consumer at preparation time. No quarantined consumer was found.
The retained upstream declaration is not imported through the withdrawn file.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismSplit | R4 | Withdraw duplicate; attach node to adopted theorem. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists | unclaimed | Private imports and proof changed; signature preserved. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | Transitive consumer; unchanged. |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Transitive consumer; unchanged. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Transitive consumer; unchanged. |
| WeilConjectures.AlgebraicGeometry.Modules.DeterminantWedgeMorphismSplit | unclaimed | Adopted replacement; unchanged. |

## Status

landed 20261021T005748-L-1889502 2026-10-21 (merge of deliver/R4/Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeMorphismSplit)
