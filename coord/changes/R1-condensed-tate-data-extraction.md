# AlgebraicGeometry.Scheme.PurityIntegralTower data-module extraction

## Reason

The normalized local-model theorem and the source-unit reduction theorem use the existing
coefficient and strict-tower definitions, while the reconstruction theorem uses both
lemmas. Keeping the definitions with the reconstruction theorem would create an import
cycle. Move the existing data and proved coefficient lemmas into a public data module.
This extraction is for the dependency structure; the declarations retain their names,
signatures, visibility and mathematical bodies. Local irreducibility attributes limit
unnecessary elaborator unfolding and do not change the exported definitions.

## Old

`Sheaf.Paper.CondensedTateIntegralTower` declares every name through
`AlgebraicGeometry.Scheme.PurityIntegralTower.IdentifiesExceptional`, followed by
`ReconstructionResult` and `condensedTateIntegralTower`.

For example, the concrete coefficient datum is, verbatim:

```lean
def datum (ell : ℕ) [Fact ell.Prime] : AdicCoefficientDatum (Ring.{u} ell) where
  ideal := Ideal.span {(ell : Ring.{u} ell)}
  noetherian := (coefficientProperties ell).1
  finitelyGenerated := (coefficientProperties ell).2.1
  quotientTorsion := (coefficientProperties ell).2.2.1
  quotientPerfect := (coefficientProperties ell).2.2.2.1
  quotientFinite := (coefficientProperties ell).2.2.2.2
```

## New

`Sheaf.Paper.CondensedTateIntegralTowerData` declares those same existing names through
`IdentifiesExceptional`. `Sheaf.Paper.CondensedTateIntegralTower` publicly imports that
module and retains `ReconstructionResult` and `condensedTateIntegralTower` with their
original signatures. No definition is replaced by an existential choice or altered.
The data node's Lean record carries the relocated declarations; the original node
retains the result predicate and main theorem. The datum above is unchanged, verbatim,
in the new module:

```lean
def datum (ell : ℕ) [Fact ell.Prime] : AdicCoefficientDatum (Ring.{u} ell) where
  ideal := Ideal.span {(ell : Ring.{u} ell)}
  noetherian := (coefficientProperties ell).1
  finitelyGenerated := (coefficientProperties ell).2.1
  quotientTorsion := (coefficientProperties ell).2.2.1
  quotientPerfect := (coefficientProperties ell).2.2.2.1
  quotientFinite := (coefficientProperties ell).2.2.2.2
```

A token comparison after removing comments and local irreducibility attributes verifies
that all 46 extracted public declarations and their mathematical bodies are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedTateIntegralTower | R1 | Publicly reexports the data and assembles reconstruction. |
| Sheaf.Paper.CondensedTateIntegralTowerData | new, R1 | Receives the existing unchanged public interface. |
| Sheaf.Paper.NormalizedTateTensorTower | new, R1 | Imports data to state the normalized strict model result. |
| Sheaf.Paper.FinitePuritySourceUnitReduction | new, R1 | Imports data to state the source-unit coherence result. |

The live downstream scan finds no external Lean importer of the item. Public names
remain visible through the original module. Target statements and their definitions
have the same meaning; the extraction changes only module ownership. No other held
module needs a forced adaptation.

## ReconstructionResult binder form

In `Sheaf.Paper.CondensedTateIntegralTower` the body of the existing
`ReconstructionResult` binds its three instance arguments with `have` instead of `letI`:

```lean
-- old
  letI := c.hasCompactification
  letI := hX
  letI := hY
-- new
  have := c.hasCompactification
  have := hX
  have := hY
```

The body is a proposition; after instantiation the two forms are the same proposition
up to beta/zeta reduction (definitionally equal), so the meaning of the predicate and of
`condensedTateIntegralTower` is unchanged. Users: only `condensedTateIntegralTower` in the
same module; the item has no Lean importer. (Recorded by the reviewer.)

## Status

landed 20261025T002531-L-3126547 2026-10-25 (merge of deliver/R1/Sheaf.Paper.CondensedTateIntegralTower)
