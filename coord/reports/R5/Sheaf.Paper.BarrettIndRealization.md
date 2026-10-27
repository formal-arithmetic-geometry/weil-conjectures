## What changed

Reduced `WeilConjectures.zlBarrettIndRealization` to the ordinary constructible
realization, preserving its complete signature, all localization universes, all
existing public declarations and both public imports. Added only proof imports
to the item. Re-enabled both transparency-respecting elaboration options.

The Frobenius comparison is proved. The private `freeTransportIso` lifts the
ordinary inverse-image adjunction along the prescribed Frobenius square and its
invertible right mate. The two free/pullback composites are left adjoint to
isomorphic underlying right adjoints, so adjoint uniqueness identifies them.
The exact-functor natural-isomorphism and composition APIs derive this comparison
and paste it with the ordinary realization comparison. The proof explicitly uses
the existing chosen abelian/preadditive structures, avoiding a different inherited
fixed-pair structure during instance search.

Added `Sheaf.CategoryTheory.IndDerivedRepresentableDetection`, with a complete
proof for every small abelian category. Colimit extensionality shows that
representables generate its ind-category. A pure derived object with no maps from
single representables is zero. Truncation then raises a lower bound repeatedly,
forcing every cohomology object to vanish. Shift full faithfulness and the exact
Hom sequence identify the cone of a tested arrow as such a zero object. The main
proof transports bijectivity from each realization object through the supplied
isomorphism to a single representable, explicitly proving injectivity and
surjectivity.

Added `Sheaf.Paper.BarrettOrdinaryIndRealization` for the remaining ordinary
construction. It has no Frobenius pairs, derived free induction, or detection
condition. Its additional single-object coverage is supplied by placing a heart
object in each degree. It is strictly the ordinary realization/inverse-image part
of the original proof, rather than another name for the original assertion.

The full dependency chain compiled cleanly: detection in 5.5 seconds, ordinary
realization in 7.9 seconds, and the item in 29.4 seconds. The detection theorem
uses only propext, Classical.choice and Quot.sound. The delivery also repeats
its required compile and axiom checks. No existing dependency or
consumer module is modified.

## Proved and sorry left

Original holes closed: `WeilConjectures.zlBarrettIndRealization`
(`lem-zl-barrett-ind-realization`), by decomposition. Its proof body is complete.

Added hole: `WeilConjectures.zlBarrettOrdinaryIndRealization`
(`lem-zl-barrett-ordinary-ind-realization`), in its own module, with the original
ordinary construction, source and full proof in words. This is the only `sorry`
in the delivery.

Also proved in full: `CategoryTheory.indDerived_singleYoneda_detects_iso`
(`lem-zl-ind-derived-representable-detection`), including every private helper.
There is no postponed detection or Frobenius-comparison step.

The item started with one hole and now has zero; the delivery introduces one
strictly smaller hole. This is one decomposition, with net hole change zero,
not a claim of one net hole proved. No definitions acquire postponed data.

## No longer needed

No module is withdrawn and no original import is removed. The adopted source
library is untouched. The original node's ordinary realization and detection
paragraphs are now tracked by their two explicit nodes; the free-comparison
paragraph is replaced by the proved adjunction argument. There are no abandoned
planned dependency modules to prune.

The new free comparison does not use a right-derived direct-image comparison.
The existing private import of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra`
remains needed for the exact free-functor infrastructure used by the existing
proofs and definitions, so its recorded dependency is retained.

## Where the brief, the DAG or earlier work was wrong

The shared build-error file records an old bad import of
`Sheaf.Paper.WeilIndSheafCategory`; the current server queue row instead assigns
one proof hole. The restored source compiles against the published dependencies.
This delivery makes an actual proof reduction, rather than a restoration-only or
compiling no-op delivery.

The DAG's claimed Frobenius summand calculation is unnecessary: adjoint
uniqueness proves the free comparison without choosing integer-iterate maps.
The previously only verbal detection argument is now a complete general Lean
proof and does not require representables to be projective.

Read Barrett's arXiv:2005.10859, Theorem 1.1 and the discussion of Theorem 1.3.
Theorem 1.1 covers separated varieties with finite or finite-extension l-adic
coefficients. The common-coefficient-stage and nonseparated finite-open-cover
assembly remains explicitly agent-written in the ordinary obligation; it is not
attributed as a verbatim assertion of Barrett.

WANTED: Kashiwara–Schapira, Categories and Sheaves, §15.3, for
`lem-zl-barrett-ordinary-ind-realization`. This reference is already in the
project's wanted list. The remaining proof is marked agent-written.

Edge cases checked: the empty geometric fibre and zero complexes; the zero
abelian category; tests in every integer degree, including negative degrees; a
bounded-below object with no global upper bound; and independent localization
universes. The detection proof uses only a lower bound and ordinary
representable generation, with no extra geometric or projectivity hypothesis.

## New nodes

`lem-zl-barrett-ordinary-ind-realization` records exactly the ordinary
realization, represented cohomology, coverage of single objects and normalized
ordinary inverse-image comparison used by the assembly. This is the one
remaining obligation.

`lem-zl-ind-derived-representable-detection` records the completely proved generic
bounded-below detection result. Its only statement dependencies are the existing
ind-category and bounded-derived-subcategory conventions. Both nodes inherit the
item's chapter and unit and refine the same composition-proof paragraph; the
unit route is unchanged. Mathlib searches of three kinds are recorded in each
node and in `searches.jsonl`; none supplies the remaining realization theorem.
No change record is needed: no existing statement, definition or public import
changes, and no other existing module or node is edited.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.CategoryTheory.IndDerivedRepresentableDetection": "7481d43e37048d1178173d474f1c010884a5641d", "Sheaf.Paper.BarrettIndRealization": "776300f7dc92df295b8d59ac2a4955e9c64bc53a", "Sheaf.Paper.BarrettOrdinaryIndRealization": "b6b12528ef1c7d49ecafa829b19ce0ad72bc38da"}, "results": {"Sheaf.Paper.WeilIndProperHigherRepresentability": {"hash": "82929ced385e0c4929385b5a0efebbbac7a66e78", "status": "OK"}}, "seconds": 37, "time": "2026-10-28T00:52:48+0800", "transitive": 0, "version": 1}
```

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
