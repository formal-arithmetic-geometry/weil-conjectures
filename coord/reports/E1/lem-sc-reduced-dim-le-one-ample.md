## Worker report

The module `Sheaf.AlgebraicGeometry.ExistsAmpleOfReducedDimLEOne` states
`AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_reduced_dim_le_one`.
Its proof is only `sorry`; its docstring gives all seven DAG proof steps and their uses.
No definition, dependency module, new node, or statement correction is needed.

Hypothesis and conclusion correspondence:

- Scheme X: `(X : Scheme.{u})`, with arbitrary explicit universe `u`.
- Noetherian, meaning locally Noetherian and quasi-compact:
  `[IsLocallyNoetherian X] [CompactSpace X]`.
- Reduced: `[IsReduced X]`, the sectionwise predicate equivalent to reduced local rings.
- Separated structure morphism to Spec Z: `[X.IsSeparated]`.
  Mathlib `Scheme.IsSeparated` is precisely separatedness of `terminal.from X`;
  the terminal scheme is isomorphic to Spec Z. This imposes absolute separatedness,
  with no field, finite-type, or properness hypothesis.
- Underlying topological Krull dimension at most one:
  `(hdim : topologicalKrullDim X ≤ 1)`, in `WithBot ℕ∞`.
- There exists an O_X-module L: `∃ L : X.Modules`.
- L is invertible: `∃ hL : L.IsInvertible`.
- The same L is ample: `@IsAmple X L hL`, passing that invertibility witness to
  the recorded absolute ampleness definition rather than adding a relative base.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`
  (available through imports; the former is the type binder).
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (available through imports).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`
  (available through Noetherian); read its stalk equivalence too.
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `AlgebraicGeometry.IsSeparated`
  and `AlgebraicGeometry.Scheme.IsSeparated`; the latter wraps the former on
  `terminal.from X` exactly as the dependency's separated clause requires.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (available through Ample).
- `Sheaf.AlgebraicGeometry.Ample`: `AlgebraicGeometry.Scheme.Modules.IsAmple`.
  Read the full definition: quasi-compactness plus a positive tensor-power section
  with affine nonvanishing locus at each point, exactly the dependency node.

Edge cases checked mathematically before writing: empty X has dimension bottom, so
satisfies the bound, and the structure module is invertible and ample with vacuous
point condition. Dimension-zero quasi-compact separated schemes are affine (0CKV),
so the structure module works. Finite disjoint reduced points are included. An integral
curve, two components meeting at closed points, and a curve disjoint union an isolated
point are included; no equidimensionality, connectedness, irreducibility, or nonemptiness
is imposed. All characteristics and schemes not over a field are allowed. The explicit
universe `u` admits schemes of every size covered by the project's Scheme type.

Source checked: [Stacks 09NX](https://stacks.math.columbia.edu/tag/09NX), full statement
and proof; [Stacks 0CKV](https://stacks.math.columbia.edu/tag/0CKV), dimension-zero
extension already in the node. Local literature/stacks-project/varieties.tex is absent
on this machine, so these primary-source pages were opened directly. No node fault or
STATEMENT-DISPUTED issue found. The isolated point component is already handled by
step 2's dimension-zero case.

Searches made with `/home/ubuntu/weil-launcher/msearch.py E1
lem-sc-reduced-dim-le-one-ample`:

- leansearch: `Noetherian reduced separated scheme of dimension at most one has an
  ample invertible sheaf`: unavailable, Internal Server Error.
- leanfinder: `a reduced Noetherian separated scheme of dimension at most one admits
  an ample invertible sheaf`: eight hits on integral affine schemes, reduced schemes,
  and Noetherianity, including `isIntegral_of_isAffine_of_isDomain`,
  `affine_isIntegral_iff`, `IsLocallyNoetherian`; no theorem giving ampleness.
- loogle: `AlgebraicGeometry.IsReduced, AlgebraicGeometry.IsLocallyNoetherian,
  topologicalKrullDim`: zero hits.
- grep: `ample|Ample` in `AlgebraicGeometry`: ten hits, all occurrences inside
  “example” or “examples”; no ample API in Mathlib.
- rg of `lem-sc-reduced-dim-le-one-ample|dim.*one.*ample|exists.*[Aa]mple|reduced.*ample`
  in the project's read-only WeilConjectures tree and lean/Sheaf: no matching theorem.
  Sheaf/ExistsAmpleOfDimLEOne cites this node but states the different finite-type-over-
  a-field result without reducedness. AbelianVariety/Projective has an unrelated result.
- Exact item id search in WeilConjectures: no hits.
- Exact proposed name `exists_isAmple_of_reduced_dim_le_one` in
  dag/lean_names_upstream.json, WeilConjectures, and lean/Sheaf: no hits.

Validation: server single-file compile and delivery dry run are run for this sandbox.
The independent second reader supplies its own reading before delivery.

## Second reading by E1

I independently read the sandbox node and module, all eight statement-dependency
nodes and the declarations they record, and the source statement and proof.
The local Stacks checkout is absent. I obtained the official Stacks `varieties.tex`
from https://raw.githubusercontent.com/stacks/stacks-project/master/varieties.tex
in the item's scratchpad and read lines 7737–7751 and 8069–8135. Section
`section-dimension-one` imposes no ambient field, characteristic or finite-type
hypothesis. Lemma 09NX explicitly assumes Noetherian, reduced, separated and
exact dimension one. The node already extends this to dimension at most one,
using the quasi-compact separated dimension-zero affineness statement of
[Stacks 0CKV](https://stacks.math.columbia.edu/tag/0CKV); this is valid and is
not a stage-2 correction. I also read [01PS](https://stacks.math.columbia.edu/tag/01PS).

The node's object/hypothesis/conclusion list, matched clause by clause:

- Object: scheme X, arbitrary size. `(X : Scheme.{u})` uses the recorded
  `AlgebraicGeometry.Scheme`: a locally ringed space locally isomorphic to a
  ring spectrum (Scheme.lean:42–47). Verdict: exact.
- Hypothesis: locally Noetherian. `[IsLocallyNoetherian X]` is the recorded
  Noetherian.lean:57 class requiring Noetherian sections on every affine open;
  its affine-cover equivalence is the one recorded by `pqf-def-locnoeth`.
  Verdict: exact, with no finite-type assumption.
- Hypothesis: quasi-compact (the other half of Noetherian).
  `[CompactSpace X]` uses Filter.lean:283, compactness of the whole space,
  without a Hausdorff requirement. Verdict: exact.
- Hypothesis: reduced. `[IsReduced X]` uses Properties.lean:69, reduced rings
  of sections on all opens; the stalk equivalence at lines 74–84 supplies
  exactly the dependency's local-ring formulation. Verdict: exact.
- Hypothesis: absolute separatedness, X to Spec Z.
  `[X.IsSeparated]` uses Separated.lean:338–339, separatedness of the terminal
  morphism. The underlying morphism predicate at lines 44–46 says its diagonal
  is a closed immersion, as in `def-weil-proper-morphism`. The terminal scheme
  is Spec Z up to isomorphism. Verdict: exact; properness is not assumed.
- Hypothesis: topological Krull dimension at most one, empty X allowed.
  `(hdim : topologicalKrullDim X ≤ 1)` uses KrullDimension.lean:39–40,
  `Order.krullDim (IrreducibleCloseds X)` in `WithBot ℕ∞`. Verdict: exact,
  including bottom and zero, rather than equality to one.
- Conclusion object: an O_X-module L. `∃ L : X.Modules` uses Mathlib
  Modules/Sheaf.lean:39, `SheafOfModules.{u} X.ringCatSheaf`. Verdict: exact.
- Conclusion clause: L invertible. `∃ hL : L.IsInvertible` uses the recorded
  upstream Modules/Invertible.lean:57–61, local triviality of L on a
  neighbourhood of every point. For open immersions the restriction pullback
  appearing in that existing definition is the required restriction, and local
  rank-one triviality entails quasi-coherence. Verdict: exact; no private copy.
- Conclusion clause: the same L ample. `@IsAmple X L hL` uses the recorded
  `Scheme.Modules.IsAmple` in Sheaf/AlgebraicGeometry/Ample.lean. I read its
  full body: quasi-compactness and, for every x, a positive tensor exponent and
  global section with an affine open exactly equal to its nonvanishing locus.
  Germs outside maximal-ideal times the stalk give precisely the dependency's
  fibre nonvanishing test. The invertibility witness hL supplies the required
  instance; the quantifier order is L, invertibility, ampleness of that L.
  Verdict: exact absolute ampleness, not the upstream field-relative predicate.

Edge cases: empty X has dimension bottom, and invertibility and the pointwise
ampleness criterion for its structure module are vacuous; it is quasi-compact.
Dimension-zero reduced points and finite disjoint unions are included. A curve
with an isolated zero-dimensional component is covered (docstring step 2
explicitly handles both component dimensions). For an integral curve the
intersection set T is empty and the same proof works with the other-component
ideal equal to O_X. No connectedness, nonemptiness, equidimensionality, field,
properness or characteristic binder excludes these cases. The tensor-power
API is defined at n = 0 by the monoidal unit, while ampleness correctly requires
n > 0. The single explicit universe u is arbitrary; rank-one invertible modules
have the same size as their structure sheaf, so the existential `X.Modules`
requires no independent larger universe. No variable or universe is unbound.

Independent searches (different terminology from the first reader):

- LeanFinder via msearch: `a separated reduced scheme with Noetherian topology
  and dimension bounded by one has a positive line bundle`. Eight hits: integral
  and reduced affine scheme results, zero-restriction/section results; none is
  the desired existence theorem.
- Loogle via msearch: `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
  Its index does not know this upstream identifier, so this search is unavailable
  for that identifier and is not evidence of absence.
- LeanSearch via msearch: `existence of an ample line bundle for reduced
  separated Noetherian schemes of Krull dimension at most one`. Service returned
  Internal Server Error; recorded as unavailable, with no absence verdict.
- rg of `ample|Ample|quasiProjective|QuasiProjective` in Mathlib's
  AlgebraicGeometry, upstream Modules, and the project's ExistsAmple modules;
  further rg of `exists.*[Aa]mple|[Aa]mple.*[Nn]oetherian|reduced.*[Aa]mple|[Aa]mple.*reduced`
  throughout upstream WeilConjectures and lean/Sheaf. Mathlib's matches are
  occurrences of 'example', with no ample API. Upstream `HasAmpleFamily` gives
  pullback, disjoint-union and reduction-in-characteristic-p results, not this
  theorem. Upstream `AlgebraicGeometry.IsAmple` (Ample.lean:184) requires a map
  to a field spectrum and a closed projective embedding after a power, and
  therefore is not the absolute notion needed here. The project's
  `exists_isAmple_of_dim_le_one` was opened: it requires finite type over a field
  and allows nonreduced X, so is a different theorem. Other existence results
  concern abelian varieties or globally generated modules and do not match.
- Exact proposed declaration search in dag/lean_names_upstream.json, upstream
  WeilConjectures and lean/Sheaf: absent. Thus no existing declaration replaces
  this module and all dependency notions are reused.

No H3/H4 mismatch found; no new definition nodes or dependency modules needed,
and no statement correction or citer audit is triggered. The seven docstring
proof steps render the seven node steps and name their dependencies. The only
proof is the named theorem's `sorry`; there are no new definitions or hollow
data. Header, namespace, imports and 100-character line convention are correct.
I left the correct Lean and node signature unchanged and added only this
independent second-reading report. Server single-file compilation and the
stage-2 delivery dry run are checked below before push.
