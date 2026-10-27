## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.isOpenImmersion_of_etale_cover` in the
assigned module without changing its signature, public imports, or existing docstrings.
A proved private helper constructs the algebraic-space property of a representable
fppf sheaf from its scheme diagonal and identity atlas. It introduces no chosen data.

For an arbitrary scheme test, the proof constructs the pulled-back scheme family
using representable etaleness. It proves joint surjectivity from the precise sieve
hypothesis, by lifting an arrow through the representing pullback square. Mathlib's
`Scheme.fppfPrecoverage_le_fpqcPrecoverage` makes this an fpqc family.
The sheaf pullback is an algebraic space by
`AlgebraicSpace.fibreProduct_isAlgebraicSpace`. Pullback pasting and cancellation
identify its local open representatives with the given scheme tests.
`AlgebraicSpace.exists_scheme_openImmersion_of_fpqc_cover` then supplies an open
scheme and an isomorphism. Transporting the original pullback square along its
inverse gives exactly the required representability witness.

This is shorter given the existing declarations than converting the fibre functor
between two slice categories and applying the separate support/representation
lemmas. The fpqc descent theorem is a generic tool for a space mapping to a scheme;
the assigned theorem concerns all scheme tests of a map to an arbitrary space.
Neither theorem restates the other, and the proof explicitly constructs the cover,
all local squares, and the final representing square. Neither new dependency
reaches this item in the DAG or Lean imports. The unit's recorded `realized` lists
contain no assertion replaced by this change; its mathematical route is preserved.

Added private proof imports of
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`,
`Sheaf.AlgebraicGeometry.SpaceFpqcOpenImmersionDescent`,
`Mathlib.CategoryTheory.Sites.SubcanonicalOver`,
`Mathlib.CategoryTheory.MorphismProperty.Representable`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc`.
Updated only `proof`, `proof_deps`, `proof_origin`, and removal of obsolete
`tool_uses` entries in the item's own DAG node.

Validation: the complete proof compiled through `lcompile.py` in 4.6 seconds.
The final import cleanup removes only `Mathlib.CategoryTheory.Limits.Yoneda`,
which is already publicly available through several retained imports.
The delivery checks compile and audit the final file. The argument includes empty
schemes and an empty index set: joint surjectivity is proved point by point, and no
inhabitedness, finiteness, separation, or quasi-compactness assumption is added.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.AlgebraicSpace.isOpenImmersion_of_etale_cover`
(node `lem-trf-space-open-immersion-etale-local`).

Added 0 holes and split off 0 statements. The assigned module has 0 remaining
`sorry`s. Its private helper `scheme_isAlgebraicSpace` is completely proved.

The proof uses existing statements with postponed proofs,
`AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace` and
`AlgebraicGeometry.AlgebraicSpace.exists_scheme_openImmersion_of_fpqc_cover`.
Their modules and declarations are unchanged; this is the stage-3 proof from stated
dependencies, not a claim that those lower mathematical obligations are closed.

## No longer needed

Removed the original private imports:

- `Sheaf.AlgebraicGeometry.FpqcFinerThanEtale`: the explicit fppf-to-fpqc
  precoverage inclusion suffices; no comparison with the etale topology is used.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: no direct use; the required site
  declarations remain available through the retained public algebraic-space import.
- `WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent`: no direct use;
  compatible-open descent remains a transitive dependency of the fpqc descent tool.

Removed the redundant new private import `Mathlib.CategoryTheory.Limits.Yoneda`.
Existing public imports are preserved.

The proof no longer directly needs
`lem-trf-local-open-representatives-support-descent`
(`Sheaf.AlgebraicGeometry.LocalOpenRepresentativesSupportDescent`) or
`lem-trf-prescribed-open-fppf-sheaf-representation`
(`Sheaf.AlgebraicGeometry.PrescribedOpenFppfSheafRepresentation`): the existing
scheme-target fpqc descent theorem packages both arguments.
It does not directly need `lem-weil-pbc-open-immersion-base-change`, because
`h_open` already supplies the open property for every scheme test used here.
Those declarations are not removed or modified. The support/base-change results
may still be needed by other consumers, including the fpqc descent theorem.

Removed both inherited top-level `tool_uses` entries:
`lem-weil-pbc-fpqc-finer-than-etale` and
`lem-weil-pbc-open-subscheme-fpqc-descent`. The former is unused; the latter is
encapsulated in the retained fpqc descent theorem rather than a direct step here.
No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The old plan was valid but
unnecessarily exposed separate support descent and representation assembly now
that the generic scheme-target descent theorem is stated. The proof and dependency
fields now follow the implemented route. Existing stage-2 docstrings are retained
verbatim; this report and the updated proof fields describe the completed proof.

Searches ran through `msearch.py`: Lean Finder returned scheme local
representability and scheme open-immersion results, Loogle returned no match for
`"IsOpenImmersion", "IsLocalAtTarget"`, and the Mathlib grep returned no match for
`IsRepresentableWith|isOpenImmersion_of_etale`. Local source searches found the
scheme-target fpqc descent theorem used above. Its statement, node, and the Stacks
Tag 041X proof were read, along with the fibre-product closure declaration and node.
The direct Mathlib statements for relatively representable diagonals, pullback
pasting/cancellation, and fppf-to-fpqc inclusion were also checked in source.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
