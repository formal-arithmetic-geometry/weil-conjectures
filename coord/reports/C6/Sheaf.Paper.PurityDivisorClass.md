## What changed

Proved `WeilConjectures.PurityFiniteSetting.divisor_class` from the existing
unique normalized Cartier family, smooth codimension-one Cartier theorem,
Cartier-ideal multiplication and closed-immersion lifting, three strict compatibility
lemmas. The family declarations
precede the theorem so its proof can use them. Existing declaration signatures
and public imports are unchanged. The Chern definition
now specializes a generic existential predicate which unfolds to exactly its old
body; its new import is public for this reason. Other new imports are proof-only.

The local compatibility, sum compatibility, and ordinary forgetful compatibility
are separate new modules. Their input Ext classes and supported Hom classes are linked by explicit `HEq` witnesses,
matching the existing `DivisorEtaleClasses.realizes` interface and avoiding repeated
expansion of derived localization data. Each new lemma has one public named hole,
a source, a full proof in words, edge-case checks, and its own DAG node.

## Proved and sorry left

Closed the original hole
`WeilConjectures.PurityFiniteSetting.divisor_class` (node `lem-pur-divisor-class`).
The item had one hole and now has zero. This is a decomposition, not a net proof:
the delivery adds three holes, each a strict compatibility assertion:

- `WeilConjectures.PurityFiniteSetting.normalizedCartier_localEquation`, node
  `lem-pur-normalized-cartier-local-equation`.
- `WeilConjectures.PurityFiniteSetting.normalizedCartier_sum`, node
  `lem-pur-normalized-cartier-sum`.
- `WeilConjectures.PurityFiniteSetting.normalizedCartier_forget`, node
  `lem-pur-normalized-cartier-forget`.

The existing unique-family theorem stays proved. No hole is added to a definition,
private helper, or source-library declaration.

## No longer needed

The main theorem no longer directly invokes the frame-independence theorem:
its normalized relative representative is already fixed, and the local compatibility
lemma handles each presentation. The earlier planned smooth-coordinate/dimension
argument is already packaged in `SmoothCodimensionOneCartier`.

The normalized-realization, principal-Yoneda-sign, relative-cone, and tensor-pair
addition modules remain mathematical dependencies of the new compatibility nodes;
they are not globally pruned. No module is withdrawn. No existing public import is
removed, and no source-library declaration is removed. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The old theorem docstring described eight steps whereas the current DAG had five.
The proof now uses the already proved componentwise unique family and ordinary
Chern normalization rather than rebuilding the family. The ordinary normalization API exists, but
its identification with this supported-Hom restriction is isolated in the third
compatibility node. The required generic constant-unit identity was proved in a
scratch Lean probe; the concrete derived-instance conversions remained expensive.

The current blueprint distinguishes its positive frame class `cl(D)` from the
relative class `c_D=-cl(D)`. This module's existing normalization specifies `c_D`
(the dual Cartier ideal and its canonical complementary frame), so its displayed
negative local boundary and positive ordinary Chern class are retained verbatim.
The three compatibility statements concern exactly this relative class. No target
or existing theorem statement is changed; the Chern predicate has the equivalent
presentation described above.

## New nodes

`lem-pur-normalized-cartier-local-equation` isolates the etale local-equation
calculation for one normalized representative, including the singleton ordered
product. It does not construct a class family, establish Cartierness, prove
additivity, or assert the ordinary Chern comparison.

`lem-pur-normalized-cartier-sum` isolates the global equality of three normalized
representatives under product-ideal addition. It assumes the Cartier ideals and
specified support inclusions, which the main theorem constructs using proved
geometry. It does not give a family, local equations, or ordinary Chern classes.

`lem-pur-normalized-cartier-forget` isolates the ordinary Ext realization
and Chern identification of a single normalized supported representative, with
the published forget-support site-comparison law.
It has no family, geometry, local equation, or additivity assertion.

Change record: `coord/changes/C6-purity-divisor-proof-context.md`.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
