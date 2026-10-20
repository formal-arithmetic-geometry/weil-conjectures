## What changed

Retired the zero-hole duplicate module
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFlatEtale` with `deleted.txt`.
Node `lem-sbc-stalk-normalization-flat-etale` now records the adopted upstream
module `WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationFlatEtale`
and its existing proved declaration
`AlgebraicGeometry.Scheme.finiteEtale_stalk_normalization_etale_of_flat`.

Upstream drops only `hS` and `hηU`, the two unused hypotheses of the old copy.
The old mathematical node statement is unchanged. A scratch theorem with exactly
the old full signature applies the upstream theorem directly. The upstream proof
and its current consumer are also compiled independently. No library theorem,
definition, target, public import or proof in the adopted tree is edited.

Change record: `coord/changes/retire-stalk-normalization-flat-etale-G5-20261021.md`.

## Proved and sorry left

The assigned retirement item started with 0 holes. Holes closed: 0; holes added: 0;
split off: 0. There are no remaining declarations or holes in the withdrawn module.
The replacement theorem was already proved upstream. The scratch attachment proof
checks the old statement without introducing any new library declaration.

Server validation via `lcompile.py`, all without errors or warnings:

- Old-signature attachment theorem: 2.6 seconds.
- Unmodified adopted upstream proof: 6.4 seconds.
- Unmodified adopted consumer: 3.7 seconds.

`#print axioms` for the attachment theorem and the existing upstream theorem both
reports exactly `[propext, Classical.choice, Quot.sound]`, with no proof holes in
their dependency chains. The attachment proof, in a scratch file importing only
`WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationFlatEtale`, is:

```lean
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationFlatEtale

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

theorem old_statement_check {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := S.presheaf.stalk s) (S.presheaf.stalk s)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    IsFinite n → ∀ V : (pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
      (pullback.fst c a)).Opens, Flat (V.ι ≫ n) → Etale (V.ι ≫ n) := by
  have _ := hS
  have _ := hηU
  exact finiteEtale_stalk_normalization_etale_of_flat c U PA s hs hmin hdepth

end AlgebraicGeometry.Scheme

#print axioms AlgebraicGeometry.Scheme.old_statement_check
#print axioms AlgebraicGeometry.Scheme.finiteEtale_stalk_normalization_etale_of_flat
```

The proof and node were read against `literature/stacks-project/pione.tex`,
`lemma-extend-S2` (0EY6), especially assertion (3), and `lemma-extend-covering`
(0EYJ), its depth-two local claim. The source-open purity/depth argument remains
the same; this retirement replaces only its duplicate Lean attachment. Empty source
opens and arbitrary source opens retain exactly the old conclusion.

## No longer needed

Withdrawn module: `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFlatEtale`.
Its imports disappear with the duplicate:

- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.AlgebraicGeometry.FunctionField`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`
- `Mathlib.AlgebraicGeometry.Normalization`
- `WeilConjectures.RingTheory.Depth`
- `WeilConjectures.RingTheory.FlatLocalDepthFormula`
- `WeilConjectures.AlgebraicGeometry.Morphisms.FlatQuasiFiniteDepthPurity`

All mathematical nodes and dependencies are retained. In particular,
`lem-weil-pbc-flat-local-depth-formula` and
`lem-sbc-flat-quasi-finite-depth-purity` remain needed by the upstream proof.
The mathematical parent `lem-sbc-stalk-normalization-depth-two-section-source`
continues to cite this node and its unchanged conclusion through the upstream
attachment. Blueprint ancestry references and the unit `sk-prop-input-spreading`
are preserved. No dependency module is claimed globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a holed item; the current item is explicitly
listed as `retire` in `coord/retire-items.tsv` and already contains no `sorry`.
Its retirement row's historical Sheaf consumer is absent from the current source;
the adopted replacement already uses the upstream theorem's current signature.
The node's old Lean attachment pointed to the duplicate despite that replacement.
The upstream theorem is strictly more general only in omitting two unused premises;
this does not weaken the old node statement or bypass the depth-two purity route.

Searches made with `msearch.py`: LeanFinder on flat etaleness of a local
normalization returned eight general etale-localization/locus facts, with no closer
result; Loogle on the upstream declaration name returned unknown identifier;
Mathlib grep on normalization/flatness or etaleness/depth returned zero hits.
The repository declaration scan found the exact proved upstream theorem, so no new
lemma or node was necessary.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
