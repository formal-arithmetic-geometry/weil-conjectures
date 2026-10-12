## What changed

Proved `AlgebraicGeometry.exists_isColimit_residueField_of_isLimit` in
`Sheaf.AlgebraicGeometry.LimitResidueField`, with its signature unchanged.
Constructed the canonical diagram and cocone with equality transports; proved their
functoriality and the required heterogeneous equalities. Proved element descent using
Mathlib's basis of stage affine-open inverse images and descent of sections on the
restricted affine diagram. Injectivity of field maps gives the underlying type colimit;
reflection gives the ring colimit. Taking spectra and Mathlib residue-point naturality
finish all remaining clauses. All auxiliary declarations are private and proved.

Removed the unused proof imports `FilteredColimitLocalizationAtPrime`,
`WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC`, and
`Mathlib.Algebra.Category.Ring.FilteredColimits`.
The existing public imports stay to preserve the importer-visible interface.
Updated the existing node's proof, proof_deps and proof_origin to the implemented route.
The unit `sk-thm-p1` realized statements and steps are not bypassed or changed.

Source: Stacks 0CUG (1), read at https://stacks.math.columbia.edu/tag/0CUG.
Searches: launcher leanfinder, loogle and grep found residue-field definitions and
naturality but no direct colimit theorem. Reading Mathlib AffineTransitionLimit
identified the shorter section-descent route used here.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.exists_isColimit_residueField_of_isLimit`
(node `lem-weil-pbc-limit-residue-field`). No sorry remains in the delivered module.
Added zero holes; split off zero statements. This is a proof, not a decomposition.
All private helper declarations compile without sorry.

The theorem uses only Mathlib results in its proof, despite the retained existing
public import. Edge cases: the index remains an arbitrary nonempty directed preorder,
not a partial order or a preorder with a least element. No quasi-compactness hypothesis
is added to the original schemes: the restricted stages are affine. A point of an empty
limit cannot supply the input `s`; singleton and constant systems are covered by the
same construction. The equality transports retain precisely the canonical maps.

## No longer needed

Removed imports:
- `Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime`.
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC`.

Planned dependencies no longer used by this proof:
- `lem-weil-pbc-colimit-initial-full-subcategory`: no explicit upper-tail reduction;
  Mathlib's restricted affine diagram handles it.
- `lem-weil-pbc-filtered-colimit-localization-at-prime` and its module
  `Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime`.
- `def-weil-pbc-localization-at-prime`: no explicit localization construction.
- `lem-weil-pbc-spec-map-residue-field-naturality` and its PropertyC module:
  evaluation naturality replaces the prime/residue-field comparison.
- `lem-weil-pbc-limit-affine-transition`: the proof uses Mathlib's results for the
  already supplied limit cone, rather than constructing a limit. Its module remains
  publicly imported to preserve the existing interface.

These are pruning opportunities for this theorem, not claims that other targets
no longer reach the same modules.

## Where the brief, the DAG or earlier work was wrong

The plan is mathematically valid but longer than necessary: it asks for explicit
localization and residue-field identifications already avoided by Mathlib's local
section-descent results. No incorrect statement or definition was found. The local
literature checkout has only literature metadata, so the source was read on the
Stacks website. No target signature, intermediate signature or visibility changed.

## Second reading by K2

1. **Module comparison.** Compared the delivered module with the repository version. The
   theorem signature and all existing declarations are unchanged; only imports, proof text,
   and the proof body differ. Verdict: pass.
2. **Proof checks.** Compiled the module with `lcompile.py`; it has no `sorry`, `axiom`,
   `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof uses Mathlib declarations and
   the retained public interface import. Verdict: pass.
3. **Statements and nodes.** The target statement is unchanged and no statements were split
   off. The residue descent and filtered-colimit arguments apply to arbitrary nonempty directed
   preorders, including constant systems and singleton indices. The node proof steps record no
   library proof dependencies because the implementation uses Mathlib only. Verdict: pass.
4. **Pruning and route.** Removed all unused proof imports; retained `LimitAffineTransition`
   because it supplies the public `IsAffineHom` interface. The proof follows the unit's
   residue-field colimit route through affine-open section descent and does not bypass any
   realized unit statement or step. Verdict: pass.
5. **Axioms and delivery.** The local compile succeeds. No hollow definitions or accidental
   interface changes were found. Verdict: pass.

Changed during second reading: removed the unused filtered-colimit import and corrected the
node's proof dependency list to match the Mathlib-only proof.
