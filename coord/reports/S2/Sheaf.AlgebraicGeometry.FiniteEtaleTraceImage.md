## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.finite_etale_trace_image` by a
complete Lean proof through the proved per-section descent and sheet-lifting
lemmas. The proof
constructs the trace as a natural linear map, proves its local-sum formula and
uniqueness, constructs the integral image by subfunctor saturation, and proves
both implications of the sheet-sum description.

Proved `AlgebraicGeometry.Scheme.finiteEtaleTrace_sheet_lifting`. Module pullback
is identified with restriction using the composition/base-change adjunction and
its coefficient triangle equations. Sheet units are bijective. Universal finite
coproducts pull the splitting back to the base, and the disjoint-cover sheaf axiom
glues integral sheet tuples. The proof includes empty index sets and arbitrary
base objects, with no quasi-compactness hypotheses.

Moved the sixteen existing supporting definitions, with identical signatures and
bodies, to `FiniteEtaleTraceDefinitions`; the original module publicly reexports
them. This avoids import cycles between the independent proof modules. The only
docstring changes to those definitions are their blueprint ownership annotations.
The original theorem statement and the blueprint unit route are unchanged.

Validation: `lcompile.py --all` compiled all four modules in dependency order;
the subsequently completed section-descent module also compiles with no errors
or warnings. The data extraction is documented in
`coord/changes/S2-finite-etale-trace-data.md`.

## Proved and sorry left

Closed the original single hole:
`AlgebraicGeometry.Scheme.finite_etale_trace_image` (one of one).

Both new intermediate theorems are proved without holes:

- `AlgebraicGeometry.Scheme.finiteEtaleTrace_sheet_lifting`, node
  `lem-sfb-finite-etale-trace-sheet-lifting`.
- `AlgebraicGeometry.Scheme.finiteEtaleTrace_section_sum_descent`, node
  `lem-sfb-finite-etale-trace-section-descent`.

The section-descent proof constructs unique sheet coordinates and proves their
restriction compatibility. The source geometric local-permutation theorem
compares sums on an open cover; separatedness proves independence of splitting.
The source small-etale splitting cover is converted into this item's splitting
data and pushed to the pro-etale site. The presieve of all arrows whose domain
maps to an etale splitting object is covering. Unique local sums form a matching
family, which the sheaf axiom glues. Every arrow in the desired formula belongs
to this same presieve, so its gluing equation gives the formula directly.

Holes added: zero. Holes remaining in all four delivered modules: zero. No
private theorem or definition contains a hole. All choices of trace values and
local sums are from proved existence-and-uniqueness statements. The net change
in direct holes of the delivered modules is minus one; the delivery is a proof,
not a decomposition.

## No longer needed

Removed original private proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`: its constant
  coefficient module comparison does not directly identify these continuous
  coefficient modules. The sheet proof uses the ringed adjunction directly.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: no tensor
  presentation is needed after uniqueness of left adjoints.
- `Sheaf.CategoryTheory.SetSheafCoverDescent`: the main proof uses sectionwise
  descent and Mathlib subfunctor saturation, rather than descent of sheaf maps.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: the required sheaf and sieve operations
  are already available from Mathlib and the statement imports.
- `Sheaf.AlgebraicGeometry.EtaleComparison`: no additional comparison theorem is
  needed; etale-to-weakly-etale instances suffice.
- `WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit`: moved out of the
  main proof's immediate obligations into the explicit section-descent node.
  That splitting result is still needed there and is not globally pruned.

Immediate original proof dependencies no longer used by the main Lean proof are
replaced by the data, sheet-lifting and per-section-descent nodes. Localization,
etale splitting and the etale-cover comparison remain needed below the new
nodes. The original object-inverse-image comparison, tensor-product route,
localized-ringed-site route, set-sheaf map-descent route, and their dedicated
modules are not needed by this proof. This does not withdraw or alter any source
library declaration, or claim that another consumer cannot need them.

Specific old proof-plan nodes no longer invoked by this argument are
`lem-sfb-proetale-object-inverse-image-restriction`,
`def-pur-sheaf-tensor-product`, `def-pur-localized-ringed-site`,
`lem-pe-set-sheaf-cover-descent`, and `det-pe-morphisms-etale-comparison`.
The coefficient-composition theorem is not used either; its defining module is
still retained for the actual continuous coefficient maps. The pro-etale site,
module-category, localization and covering facts remain in use through the data
and the proved intermediate lemmas.

No module is withdrawn. All existing public names remain available. The original
node's top-level tool-use approvals are removed because it now uses only the
three nodes of this delivery; required generic tools are recorded on those nodes.

## Where the brief, the DAG or earlier work was wrong

The source small-etale trace cannot be applied directly to arbitrary pro-etale
base objects or to these continuous coefficient module pullbacks. Its geometric
splitting cover and local-permutation lemma are reusable. The completed proof
uses these together with the actual continuous-coefficient sheet units.

The finite-coproduct sheaf-core lemma in the library assumes quasi-compact and
quasi-separated summands, although its proof does not use those hypotheses.
Our base objects need not satisfy them. A private version of that proved
argument omits those unused hypotheses; no source declaration was changed.

The original plan's tensor comparison and sheaf-map gluing are unnecessary for
the completed algebraic and image-sheaf argument. No false statement, target
change, forced adaptation, or source-library removal is involved.

## New nodes

`def-sfb-finite-etale-trace-data` owns the sixteen unchanged data declarations
relocated to `FiniteEtaleTraceDefinitions`. See
`coord/changes/S2-finite-etale-trace-data.md` for the old and new declarations and
the consumer audit.

`lem-sfb-finite-etale-trace-sheet-lifting` states the proved bijectivity of sheet
units and integral tuple gluing. Its proof uses the actual coefficient maps,
universal finite coproducts, the sheaf axiom and the empty-cover axiom.

`lem-sfb-finite-etale-trace-section-descent` states and proves per-section
geometric descent. The main proof supplies all subsequent linearity, naturality,
trace uniqueness and integral sheaf-image work in Lean.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
