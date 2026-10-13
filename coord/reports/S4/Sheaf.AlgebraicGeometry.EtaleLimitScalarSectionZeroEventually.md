## What changed

Replaced the sorry in `AlgebraicGeometry.Etale.etale_limit_scalar_sections_zero_eventually`
with a compiling reduction. Construct the section diagram and cocone explicitly from the
map laws, apply the geometric colimit comparison, prove that the tail is directed and
nonempty, and use Mathlib `CategoryTheory.Limits.IsColimit.eq_iff'` on z and zero.
The theorem's signature and public import are unchanged. No other existing module changed.
The original node now records this route. Two new modules separate algebraic map coherence
from geometric section continuity. The former requires neither a limit nor qcqs assumptions.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.etale_limit_scalar_sections_zero_eventually`.
No sorry remains in the item's module.

Added two named holes, each with a source and complete proof in words:

- `AlgebraicGeometry.Etale.etale_limit_scalar_section_map_laws`
  (node `lem-weil-pbc-etale-limit-scalar-section-map-laws`).
- `AlgebraicGeometry.Etale.etale_limit_scalar_section_colimit`
  (node `lem-weil-pbc-etale-limit-scalar-section-colimit`).

This is a decomposition, not a proof with only standard axioms. One hole closed and two
added gives net -1 before any subsequent proof; no positive sorry-ledger progress is claimed.
The remaining obligations assert map laws and a colimit universal property respectively;
neither asserts the original eventual-zero conclusion. The combining proof constructs real
Lean data and uses Mathlib's equality criterion. All three delivered modules compile.

Edge cases checked mathematically: J contains i0 even when I has no strict later stage;
directedness gives a common upper bound in J. Gamma and delta cannot be arbitrary
noncanonical automorphisms because both projections determine them uniquely. An empty
T0 and zero coefficients give zero section groups and allow the identity arrow as witness.
No nonemptiness condition on schemes or etale objects is introduced. For singleton I,
the comparison reduces to the identity pullback comparison and an isomorphic cocone leg.

## No longer needed

Removed these direct proof imports from the item's module:

- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`
- `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`
- `Sheaf.AlgebraicGeometry.FullAffineEtaleTopos`
- `Sheaf.CategoryTheory.ColimitSiteSections`
- `Sheaf.CategoryTheory.ColimitSites`
- `Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit`

The affine site, topos, site-colimit and section-colimit nodes remain planned dependencies
of the new geometric comparison, so they are not globally pruned. The affine transition and
finite-limit imports are likewise retained there for its planned proof. No existing DAG
node or source module is claimed globally unnecessary. The top theorem now imports only
the two new obligations and Mathlib's filtered abelian colimits and concrete equality API.

## Where the brief, the DAG or earlier work was wrong

The node statement and inherited docstring discuss both representatives and eventual zero;
the actual declaration contains only eventual zero. Its signature is preserved.
The one-step plan omitted the Lean interface joining geometric scalar continuity to the
filtered-colimit equality theorem. `colimitSite_sections_isIso` only evaluates a diagram
already on the limit site. `exists_colimit_site` supplies presentations for a fixed sheaf;
the varying-system comparison still requires iterated-colimit flattening and qcqs gluing.
The source library's `unitComparison_app_isColimit_of_isLimit` also treats one fixed-base
sheaf, so applying it directly to arbitrary phi would be incorrect.

The listed Stacks TeX files are absent on this machine. Read the public source pages
https://stacks.math.columbia.edu/tag/09YN,
https://stacks.math.columbia.edu/tag/09YQ and
https://stacks.math.columbia.edu/tag/09YP instead. The cited source proves the comparison
for varying systems. There is no statement dispute or forced adaptation.

## New nodes

`lem-weil-pbc-etale-limit-scalar-section-map-laws`, module
`Sheaf.AlgebraicGeometry.EtaleLimitScalarSectionMapLaws`: identity, composition and cocone
laws for the specified maps, with no limit or finiteness hypotheses. This isolates the
unit/pullback coherence calculations from all geometric descent.

`lem-weil-pbc-etale-limit-scalar-section-colimit`, module
`Sheaf.AlgebraicGeometry.EtaleLimitScalarSectionColimit`: universal property of the explicit
section cocone, conditional on the map laws. Its proof is affine site descent, iterated
filtered-colimit flattening and finite matching-family gluing. No definition is sorry,
no arbitrary data are chosen from unproved existence, and no change record is needed.

## Second reading by S4

1. Compared the delivered target module with the repository version. The target theorem signature and all existing declarations are unchanged byte for byte; only its proof and proof-only imports changed. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`; they compile without errors. The target proof has no `sorry`, and the only remaining holes are the two named split-off theorems, each with a docstring and matching DAG node. No forbidden declarations or hollow definitions were introduced. Verdict: pass.
3. Checked both split-off statements against their edge cases and source descriptions. The map-laws theorem isolates identity, composition, and cocone laws; the colimit theorem isolates the universal property and does not restate eventual vanishing. The statements are true and strictly simpler than the target, with no Mathlib or existing Sheaf duplicate found. Verdict: pass.
4. Read the proof from the target downward. It uses the map-laws and colimit nodes, then the directed-tail and filtered-colimit equality argument; the five obsolete direct imports are removed and recorded above. The unit route `sk-thm-p1` remains represented by the split nodes. Verdict: pass.
5. Checked the DAG `proof`, `proof_deps`, `proof_origin`, Lean records, and realized unit metadata against the actual proof and declarations. Verdict: pass.

Changed only the target proof and its proof-only imports, and added the two required split modules and nodes. No statement, definition, or public interface was altered.
