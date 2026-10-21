## What changed

Repaired the returned duplicate-retirement packet against the current `sheaf-dag`
source, including the D6 determinant-pairing changes from `c1a6bc5699a`. `Sheaf.AlgebraicGeometry.KoszulSelfExtStalkBases` now
re-exports the existing
`WeilConjectures.AlgebraicGeometry.KoszulSelfExtStalkBases` theorem and keeps the
public `ExteriorSheaf` compatibility import. Its duplicate theorem and private
coordinate constructions remain removed.

The two direct consumers now privately import the official source theorem and
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafComparison`. At their existing
stalk-basis calls they unfold the let bindings, rewrite
`exteriorPower` to `exteriorSheaf` with the proved equality, and then continue
with their current proofs. Their public signatures and hypotheses are unchanged;
the current determinant-pairing and restriction arguments are preserved.

The three delivered modules compile with `lcompile.py` without errors or
warnings: the exterior consumer in 5.3s, the compatibility module in 0.1s, and
the repaired dual consumer in 9.6s. The dual consumer was taken from the current
source and changed only at its stalk-bases import and call. Its upstream pairing
construction, forward comparison transports, and local bijectivity proof are
preserved. The DAG copy also preserves D6’s power-comparison dependency and
review metadata.

## Proved and sorry left

This is a listed duplicate-retirement repair. The assigned item already had zero
holes: closed 0, added 0, split off 0. No `sorry` remains in any delivered
module. The source-library theorem
`AlgebraicGeometry.koszulRegularImmersion_self_ext_stalk_bases` supplies the
mathematical result; the two adapted declarations are
`AlgebraicGeometry.koszulRegularImmersion_self_ext_exterior` and
`AlgebraicGeometry.koszulRegularImmersion_self_ext_dual_exterior_conormal`.

## No longer needed

The duplicate Sheaf private cocone, additive and linear coordinate maps,
projection/inclusion maps, basis germs, coordinate identities, stalk equivalence,
restriction frame, and restricted-stalk-basis theorem are removed. The adopted
source-library implementation remains intact.

The compatibility module no longer needs the old direct proof imports: Koszul
regularity, tensor pullback, derived-category, internal-Hom, closed-immersion,
ideal-sheaf, flat-pullback, free-sheaf, conormal-frame, and local-free-comparison
imports are supplied by the official source module or are no longer used by this
module. `ExteriorSheafComparison` is used by the two consumers for the equality
transport. The dual consumer's current `ExteriorSheafPowerComparison` import is
retained because its remaining proof still uses declarations from that module.

The stalk-bases node now attaches to the official source declaration. The two
consumer nodes record the additional equality dependency. No unit statement or
route is bypassed, and no source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes an unfinished proof obligation, but this item is a
listed retirement of a duplicate whose official source theorem is already
complete. A bare re-export would leave the consumers with a basis of the
`exteriorPower` type while their public statements use `exteriorSheaf`; the
proved `exteriorSheaf_eq_exteriorPower` equality is therefore transported at each
consumer. The return requires applying this retirement to the current dual consumer after
D6 changed its determinant-pairing argument. Restoring that argument and adding
the basis-type rewrite repairs the conflict; the initial compile of the unchanged
current consumer against the retired interface confirmed the necessary mismatch. No statement, hypothesis,
unit route, axiom, or postponed theorem was introduced. The associated change record is
`coord/changes/retire-koszul-self-ext-stalk-bases.md`.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
