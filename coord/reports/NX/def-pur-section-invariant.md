## Worker report

Repair of the independent stage-2 return `f44f7bb99432` for
`def-pur-section-invariant` (H1 and H7). I supplied the missing Lean module,
the complete item `lean` record, the explicit statement correction and citer
audit, and a source-based second reading. The module defines the canonical
pro-etale object `Ls^*(Rg^! 1)`, using `ProEtale.upperStar` and
`ProEtale.rightDerivedUpperShriek`; it contains one postponed theorem asserting
constructible finite-Tor membership and tensor invertibility. The definition
has no existential or `sorry` data.

### Files written

- `dag/nodes/sec-smooth-purity/def-pur-section-invariant.json`: repaired item
  statement, `statement_change`, citer audit, and Lean declaration records.
- `lean/Sheaf/EtaleCohomology/Purity/Smooth/SectionInvariant.lean`: canonical
  pro-etale definition and the named postponed ctf/invertibility theorem.
- `report.md`: this report, including the exact correction and independent
  reading.

## Statement corrected

The old imported statement is preserved verbatim in `old-statement.txt` and in
`statement_change.old_statement`. It was too terse to type the intended
pro-etale object: it omitted the coefficient ring, the site, the separated
finite-type domain of the exceptional inverse image, and the finite-Tor
predicate, and it incorrectly described invertibility as a consequence of a
definition. The corrected node spells out the actual object and its
tensor-invertibility clause in the pro-etale `D^b_ctf` setting.

The complete citer audit required by H7 is recorded in the node:

- `def-pur-dnc-section-family` holds: its family object inherits the corrected
  section-invariant object and coefficient/site setting.
- `lem-pur-dnc-section-geometry` holds: its proof uses the object and the
  smooth closed-section hypotheses, with no dependence on the removed
  definitional invertibility inference.

The correction record includes the old statement, old dependencies, old proof
and proof dependencies, source place, and both citer entries.

### Lean declaration audit

I read the pro-etale source modules `SixFunctors/ProEtale/Derived/UpperShriek`,
`UpperLowerStar`, `UpperStarMonoidal/Comparison`, and `TorAmplitude`. The
definition uses exactly the source functors and lands in
`DerivedCategory (Sheaf (Scheme.ProEt.topology B) (ModuleCat Λ))`. The theorem
has the source hypotheses `[Smooth g]`, `[IsClosedImmersion s]`, and
`s ≫ g = 𝟙 B`, together with the finite coefficient and invertible-exponent
interfaces; its conclusion is the conjunction of
`DerivedCategory.constructibleFiniteTor` and `IsInvertible` for the defined
object. Its docstring records the complete proof route and identifies the one
postponed theorem, so no hollow definition is introduced.

The nearby source declaration
`AlgebraicGeometry.Etale.sectionInvariant` in
`EtaleCohomology/Purity/Smooth/Conventions.lean:327` was rejected as an
attachment: it is the ordinary small-etale ambient derived object and has no
pro-etale finite-Tor/Picard conclusion. This directly repairs H1's
small-etale mismatch.

### Sources and edge cases

The source blueprint definition, unit, chapter, and the pro-etale operation
modules were read. The empty base gives the empty derived category object;
for `g = 𝟙 B` and `s = 𝟙 B`, the object is the tensor unit by the operation
identity interfaces. A disjoint base with smooth components of different
relative dimensions is allowed; the statement therefore makes no global
dimension choice. No Tate orientation is assumed.

## Earlier second reading (a previous round; superseded)

I reread the module independently against the node and source. The namespace,
universes, coefficient category, site, and morphism orientations all match the
source functors. The definition is actual data, while the only `sorry` is the
named property theorem. I checked that `statement_change` names every base
citer and that both citers remain valid after the correction. The ordinary
etale declaration is not used as a substitute for the pro-etale object.

### Compilation evidence

The module was checked with the repository's single-file `scompile.py` wrapper;
the result and command transcript are retained in the delivery run output.
No global build, Lake invocation, live-source edit, or push was performed.

## Review by NX

Stage 1 is the only delivery in this round. The sections above describe a
historical stage-2 attempt; their Lean and compilation claims are not
verification evidence for this delivery. I have not written Lean or run a
compiler, Lake or build tool. The stage-1 packager delivers only the item JSON
and this report. The obsolete sandbox `lean` record was removed from the JSON;
the historical Lean file was neither changed nor delivered.

Read the actual archived blueprint node `def-pur-section-invariant.md`, the
`sk-def-purity-conv/_section.md` unit and `sec-smooth-purity/_section.md` chapter
under `/home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/`.
The shared checkout contains the citation indices but no document copies;
these existing local archived copies were read without modifying them.
The unit specifies the constructible exceptional inverse image for separated
finite-type morphisms and gives exactly the section-pullback formula. The node
adds Picard membership but incorrectly cites only the definition of
cohomological smoothness as its justification. The repaired argument uses the
existing theorem, preserving that membership and allowing varying relative
dimension. It chooses neither a Tate orientation nor a relative dimension
for all of V.

### STATEMENT-DISPUTED: domain and coefficient unit

With just the imported words “smooth” and “closed section”, take
`B = Spec(k)` and `V` the infinite disjoint union of copies of `Spec(k)`.
The map V to B is smooth, and inclusion of one component is a closed section,
but the map is not quasi-compact, hence not finite type. Consequently
`Rg^!` cannot be formed by `def-weil-exceptional-inverse-image`, whose domain
is separated finite-type morphisms between finite-type k-schemes. The
repaired statement explicitly adopts that operations setting, as required by
the unit's citation of `sk-def-sf-operations(vi)`. Absolute separatedness of
B and V, which the sandbox had added unnecessarily, was removed; separatedness
of g remains explicit. For integral coefficients the tensor unit is the
completed coefficient sheaf, not the discrete constant O_E sheaf. This is
now stated using `def-weil-completed-integral-coefficients`; the finite,
rational and common-stage units are specified separately. The old statement is reproduced below, and both actual direct citers are audited here. The historical stage-2 `statement_change` field is not delivered: stage-1 preflight reserves that field to the maintainer.

Opened both citer nodes: `def-pur-dnc-section-family` expressly inherits the
situation and uses the same formula and Picard conclusion;
`lem-pur-dnc-section-geometry` uses the formula in its proof through that
family and has an additional pure-dimension hypothesis. Both uses remain
valid under the operations setting. Neither citer is used to prove this item.

## Second reading by NX

- Item statement: checked against the archived blueprint definition and conventions unit, and the domains of `def-weil-exceptional-inverse-image`, `def-weil-derived-pullback-tensor-hom`, `def-weil-finite-tor-amplitude` and `def-weil-completed-integral-coefficients`; repaired the explicit domain and integral unit while retaining the formula, all coefficient stages and the full Picard conclusion.
- Step 1: checked `sbc-lem-smooth-relative-dimension-locally-constant` against Stacks 02G1, `morphisms.tex`, label `lemma-smooth-omega-finite-locally-free` (local freeness and the rank/fibre-dimension equality); checked `lem-weil-pbc-site-module-sheaf-gluing` against Stacks 04TR, `sites.tex`, label `lemma-glue-sheaves` (the actual compatible-tuples construction). Read every cited node statement, including the finite/integral constructibility and Tor definitions, compact-support definition, K-injective direct-image definition and exceptional adjunction. The finite clopen product construction, componentwise quasi-isomorphisms and finite common bounds justify the derived equivalence. Added the existing Nagata theorem for compactification existence; its qcqs base hypothesis holds. Wrote the finite-coproduct properness checks and the natural Hom calculation identifying the dualizing components. Verdict: valid; non-elementary, with its elementary subcalculations written explicitly.
- Step 2: checked the invertibility clause of `thm-pur-cohomological-smoothness` against its archived blueprint statement and proof, and read `def-weil-exceptional-inverse-image` for the ambient object. Each g_d satisfies the theorem's smooth, separated and pure-relative-dimension hypotheses. Finite product gluing produces one inverse with finite common bounds, including uniform integral reduction bounds. Verdict: valid; retained the first worker's argument unchanged, and no unjustified implication from the definition of cohomological smoothness is used.
- Step 3: checked `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` against Stacks 07A4, `sites-cohomology.tex`, label `lemma-pullback-tensor-product` (arbitrary derived inputs), and 0G7E, label `lemma-pullback-K-flat`; read all cited statements. The ambient comparison handles both the finite inverse pair and the arbitrary-module Tor test. The needed integral comparison is derived explicitly by the two reduction formulas and compatible pure-tensor maps. The earlier `lem-pur-derived-pullback-tensor-iso` citation was removed because its stated finite-level boundedness is false (see the dependency dispute below). Added `lem-pur-scheme-constructible-preimage`, checked against 054I, `morphisms.tex`, label `lemma-inverse-image-constructible`, and its exact Mathlib declaration at `Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean:172`. Pullback of locally constant finite modules is explained by the base-change covering and constant-sheaf construction, with both definition nodes cited. Read `lem-pur-integral-operations-preserve-constructible` against Bhatt–Scholze 6.5.3–6.5.5 and 6.5.9(5), and `lem-weil-constant-coefficient-objects-constructible` clause 2 for the completed unit. Applied the explicit Tor calculation separately to every finite reduction with one uniform interval for each input. Rationalization and the common-stage representative give the two field cases. Verdict: valid after filling these missing citations and arguments; non-elementary.
- New nodes: none. No elementary helper, duplicate, clause-restatement or unsearched child is introduced; B1–B7 are vacuous for new nodes. The existing constructible-preimage node is already a Mathlib leaf and is cited without creating a special case.

Changes and reasons:

- Filled the missing stage-1 review while retaining every earlier report section. Historical stage-2 compilation is explicitly excluded as evidence.
- Removed the sandbox's obsolete stage-2 `lean` record; no Lean source was changed or delivered.
- Recorded the statement dispute, explicit non-finite-type example and corrected exceptional-inverse-image domain. Removed unnecessary absolute separatedness and distinguished the completed integral unit from finite constant coefficients.
- Added compactification existence and componentwise derived/category checks to step 1; these were hidden facts in its compactification calculation.
- Added the existing constructible-preimage leaf and the inverse-image/local-constancy definitions to step 3; a pulled-back finite partition needs constructibility and local-constancy checks, not just boundedness.
- Added the existing completed-unit theorem and explicit uniform finite-reduction Tor calculations to step 3, replacing “the identical argument” and coefficient-stage shorthand by quantified formulas.
- Retained step 2 and its valid existing theorem dependency. No new nodes were necessary.
- Removed the overstrong finite-level bounded-tensor comparison citation and supplied the needed integral comparison using explicit tower maps and derived limits.
- Regenerated `citations.json` with a verbatim full statement for every citation in the repaired three steps.

Independent searches were run with msearch.py using different, more general
vocabulary: LeanFinder “A strong monoidal inverse image functor sends a tensor
invertible dualizing sheaf to an invertible object” returned eight nearby
sheaf/condensed monoidal declarations; Loogle `"Monoidal", "IsUnit"` returned
zero hits; source grep `dualizing|sectionInvariant|tensor.invertible` returned
ten unrelated comments. None states this exceptional-inverse-image or
finite-Tor/Picard construction. All actual results are appended to
`searches.jsonl` and recorded in the item. Blueprint search “section invariant”
found only this imported item; `blueprint_refs.py ancestor` returned this item.
The ordinary etale `AlgebraicGeometry.Etale.sectionInvariant` was read at
`/home/ubuntu/weil-src-slopmaster2/WeilConjectures/EtaleCohomology/Purity/Smooth/Conventions.lean:327`:
it defines the ambient small-etale object and does not assert pro-etale
constructible finite-Tor membership or invertibility, so it cannot close this
node. Upstream master is not used as proof evidence.

Edge cases checked: for B empty the existence of g forces V empty, and the
unique object is its tensor unit and its own inverse; the empty product in
step 1 therefore works. For g and s the identity, adjunction and pullback give
the coefficient unit with inverse itself. The same holds for a field base
and relative dimension zero. A disjoint union of smooth components of
different dimensions is admitted and handled by the finite clopen product;
no pure dimension is imposed on g. The argument uses arbitrary module
sheaves and applies to n=1 and n>1, including nonregular coefficient rings;
n=0 is outside the conventions and was not silently added. The zero input
passes the stated constructibility and Tor tests, but is not asserted to be
invertible on a nonempty scheme. Finally, following statement and proof
edges from every dependency found no path back to this item; the two direct
citers above are not dependencies of this delivery.

Off-unit tools requested for the maintainer's review, without setting the
maintainer-owned `tool_uses` field: `thm-pur-cohomological-smoothness` supplies
orientation-free invertibility; `lem-weil-pbc-site-module-sheaf-gluing` supplies
sheaf gluing on a finite clopen cover; `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` permits arbitrary modules
in the Tor test; `lem-pur-integral-operations-preserve-constructible` supplies
integral pullback preservation and its reductions; and
`lem-weil-constant-coefficient-objects-constructible` supplies the completed
unit. The conventions unit states none of these results. Nagata is an
existing Lean-closed tool, and constructible preimage is an existing Mathlib
leaf. These uses do not change the unit's section-pullback construction.

### STATEMENT-DISPUTED: existing bounded-tensor comparison dependency

The existing node `lem-pur-derived-pullback-tensor-iso` states its comparison
for every pair in finite-level D^b_c, as an isomorphism in D^b_c. On
`Y = Spec(k)` take `E = Q_l`, `n = 2`, `A = Z/l^2` and both inputs the
constant sheaf `A/(l)` in degree zero. The periodic free resolution with all
differentials multiplication by l becomes a complex with zero differentials
after tensoring with `A/(l)`. Its Tor_i is `A/(l)` for every i >= 0. Thus
the derived tensor is unbounded, and even for the identity morphism the
asserted D^b_c typing fails. Stacks 07A4 states the valid comparison in the
ambient derived category, with no boundedness claim. This delivery therefore
removes that dependency, uses the existing ambient comparison, and proves
its needed integral comparison by explicitly compatible finite reductions.
No other item's node was changed. The dependency should be corrected by its
owner to an ambient comparison or to inputs with a finite-Tor condition;
this report is the upward notification for that out-of-scope repair.

### Stage-1 preflight correction

The first dry run rejected the historical `statement_change` field as
maintainer-owned in stage 1. Removed it from the sandbox item; the statement
correction, counterexample and both direct-citer audits remain in this report.
The earlier worker's stage-2 discussion of that field is historical.
The imported statement being corrected, verbatim:

```text
In the purity conventions of this chapter ([def-pur-conventions] fixed setting), let $g:V\to B$ be
smooth and let
$s:B\hookrightarrow V$ be a closed section. The
*section invariant* is the invertible object of
$\operatorname{Pic}\bigl(D^b_{ctf}(B,\Lambda)\bigr)$

$$
C(g,s)\;=\;Ls^*\omega_g\;=\;Ls^*Rg^!\Lambda_B,
$$

invertible by [def-pur-co-smoothness].
```
