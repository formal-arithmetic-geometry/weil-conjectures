## What changed

Replaced the sole sorry of `Sheaf.AlgebraicGeometry.Morphisms.RootSplitCoverIndEtaleCharts`
by a compiling proof from three new, proof-only imports. The existing signature and public
imports are unchanged. The proof extracts the factor j, derives affineness and local finite
presentation by composition, obtains a pointed strict local limit, applies orbit classification,
and proves exponent invertibility by mapping the unit n and casting each orbit's divisibility.
The original node now records these three dependencies and the Lean assembly.

The new modules state only finite etale descent of j, existence of the regular strict local
limit (independent of Y and n), and classification over a supplied strict local limit
(independent of any point y or ind-etale property). None restates the original theorem.
All four modules compile together through lcompile.py with no warnings.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.Scheme.root_split_cover_indEtale_charts`
(lem-sbc-root-split-cover-ind-etale-charts). There is no sorry left in the item module.
This is a decomposition, not a proof free of sorry: one upper hole is closed and three
lower holes are added, giving a net increase of two holes before further proofs.

The three remaining named theorems, each with exactly `:= by sorry`, are:

- `AlgebraicGeometry.Scheme.root_split_factor_finite_etale`
  (lem-sbc-root-split-factor-finite-etale, RootSplitFactorFiniteEtale).
- `AlgebraicGeometry.Scheme.regular_divisor_strict_local_limit`
  (lem-sbc-regular-divisor-strict-local-limit, RegularDivisorStrictLocalLimit).
- `AlgebraicGeometry.Scheme.root_split_strict_local_orbits`
  (lem-sbc-root-split-strict-local-orbits, RootSplitStrictLocalOrbits).

Each has its complete sourced proof and edge cases in its docstring and a matching DAG node.
The existence theorem is eliminated only in a proof; no definition chooses arbitrary data
from it. No definitions, existing signatures, or target statements change.

## No longer needed

None. The original node had no proof dependencies and the original public imports are
needed by its signature. No existing module is pruned. Only the three proof imports are
added. Unneeded imports inherited while drafting new modules were removed before compilation:
RootSplitFactorFiniteEtale needs no regular-ring, regular-multiplication, ind-etale,
affine-morphism or finite-presentation imports; RegularDivisorStrictLocalLimit needs no
root-algebra, scheme-limit, etale-morphism, affine-morphism or finite-presentation imports;
RootSplitStrictLocalOrbits needs no ind-etale, affine-morphism or finite-presentation imports.
No downstream chart or finite-stage descent theorem is imported.

## Where the brief, the DAG or earlier work was wrong

The node labels its three non-elementary steps with empty uses lists. Thus there are no
stated dependencies from which to implement that plan directly. The three new modules
supply those steps. Existing strict-henselization local structure and ind-etaleness results
are available, but the searched interfaces do not also provide regularity of this affine
strict local ring and its quotient, or the required cyclic root model. Searches of both
library roots found no exact shorter route; later chart results depend on this module.

The ancestor script returns None because earlier created.item records use module names,
while its traversal expects node IDs. New records identify the mathematical blueprint
ancestor sbc-thm-spreading-finite-etale-galois, as the earlier cyclic-charts record does.
The unit's trait-case route through strict henselization and intermediate roots is preserved.
LeanSearch returned HTTP Internal Server Error; that search is recorded as unavailable.

Edge cases checked on the statements: d=0 gives m=0 and the empty cover; n=1 gives
orbit lengths one; existence of y rules out the zero ring, and hy excludes unit g.
The finite etale descent lemma also allows an empty basic open. The strict local orbit
lemma assumes a proper maximal-ideal divisor and hence a nonempty puncture.

## New nodes

`lem-sbc-root-split-factor-finite-etale` separates the descent of finiteness and etaleness
along the positive-rank punctured root cover (Stacks Tags 02LA and 02VN). It has no
regularity, divisor-point, strict-henselization or chart conclusion.

`lem-sbc-regular-divisor-strict-local-limit` isolates the pointed ind-etale strict local
base and regular-divisor properties (0EYG, 04GP, 04HX, 06LN, 05WS). It has no input cover,
root exponent, splitting or orbit classification.

`lem-sbc-root-split-strict-local-orbits` classifies the finite etale cover over a supplied
regular strictly henselian local base using cyclic descent and the intermediate-root
calculation (0EYG and 09EV). Orbit degrees are positive divisors of n; invertibility is
proved in the original module. It does not construct the base or assert properties of p.

No change records or forced adaptations are required.

## Second reading by S3

1. **Unchanged interface: pass.** Compared the complete item module with the repository
   using `diff -u`: only three plain proof imports and the replacement of `by sorry`
   changed. The existing theorem signature is byte-for-byte identical, including the
   factorization, regularity assumptions, supplied splitting and its projection equation,
   point over y, exponent units, and final projection equation. Existing public imports,
   definitions, docstrings and target statements are unchanged. Each new node's
   `lean.statement` was checked verbatim against its theorem signature. No adaptations
   or change records are needed.

2. **Proof and trust audit: pass as a decomposition.** Compiled all four modules in import
   order through `lcompile.py --all`, without errors or warnings. A separate scratch
   module imported all four and ran `#print axioms` on all four public declarations:
   each reports only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The only three syntactic holes are the named theorems listed above, each with its
   exact `by sorry` body. There are no data definitions or forbidden declarations.
   The arbitrary strict-local witness is eliminated solely inside the original theorem's
   proof. This closes one upper hole and adds three lower holes; none is claimed as a
   proof independent of sorry.

3. **Split statements and sources: pass.** Read
   [0EYG](https://stacks.math.columbia.edu/tag/0EYG),
   [02LA](https://stacks.math.columbia.edu/tag/02LA),
   [02VN](https://stacks.math.columbia.edu/tag/02VN),
   [04GP](https://stacks.math.columbia.edu/tag/04GP),
   [04HX](https://stacks.math.columbia.edu/tag/04HX),
   [06LN](https://stacks.math.columbia.edu/tag/06LN),
   [05WS](https://stacks.math.columbia.edu/tag/05WS), and
   [09EV](https://stacks.math.columbia.edu/tag/09EV).
   The finite-etale factor lemma uses the positive-rank monic root algebra over D(g);
   n and the root are units there, and the projection equation is needed to descend
   the finite-etale morphism. It needs neither regularity nor a divisor point.
   The strict-local-limit lemma uses regularity at y, quotient compatibility, and
   flatness to preserve the nonzerodivisor. Its conclusion is independent of Y, n and
   the splitting. The orbit lemma takes H as input and assumes j finite etale; it
   does not construct an ind-etale base or assert affineness of p. Its local quotient
   hypotheses make h=iota(g) prime. Localizing at (h) gives the DVR required for
   Eisenstein and the intermediate-root calculation. For an orbit of size e, the
   stabilizer has order n/e and fixes t^(n/e); this root field has degree e, so it is
   precisely the invariant field. Normality identifies the two finite algebras as
   the integral closure in that field, rather than merely equating fraction fields.
   These are three distinct smaller arguments, not a renamed copy of the item.
   Checked d=0 (empty product and cover), n=1 (only singleton orbits), empty D(g)
   for the factor lemma, and exclusion of g=0/unit g under the pointed regular-divisor
   hypotheses. All three have sourced proof docstrings and matching nodes.

   Repeated LeanFinder searches with different terms: faithfully flat descent after a
   finite locally free surjection; henselization preserving regularity and contracting
   the maximal ideal; and cyclic group actions on finite sets versus torsor covers.
   No exact match was returned (the last search found the finite-action
   `FintypeCat.isoQuotientStabilizerOfIsConnected`, which supplies only orbit structure).
   Searched both library roots and the upstream checkout for root splitting, strict
   henselization and cyclic orbits. In particular,
   `strictHenselization_regular_divisor_quotient` is an existing open theorem about
   the canonical ring: it does not construct a point over arbitrary y or supply the
   whole strict-local-limit statement. `strictHenselizationLocalStructure` and
   `strictHenselization_indEtale_of_affine_chart` supply other individual properties.
   No split statement duplicates those interfaces, and none can be closed in a few
   minutes from the available interfaces. No descendant cyclic-chart theorem was
   used, avoiding a circular proof.

4. **Top-down route and pruning: pass.** Read the Lean assembly from the original hole:
   first finite-etale descent, then the regular strict-local base, then cyclic orbit
   classification. Affineness and local finite presentation are obtained by instances
   and composition. The exponent-unit clause is proved directly from e|n, not split
   off. Every added proof import is actually applied and has plain `import` visibility;
   new public imports are needed by the new signatures. The original `proof_deps`
   is empty, so `No longer needed: None` is complete. The unit record
   `dag/units/sk-prop-input-spreading.json` retains its trait-case route through 0EYG;
   its existing `realized` lists are empty and were not altered. The referenced
   blueprint `_section.md` is not present on this machine, so the unit text was read
   from that JSON record. No unit or chapter step is bypassed.

5. **DAG agreement: pass.** The item's three proof steps correspond to the three
   applications in Lean, and `proof_deps` is exactly their union. The last step also
   records the explicit natural-number cast and `isUnit_of_dvd_unit` argument.
   `proof_origin` records this assembly. Each new node has its source, proof in words,
   actual recorded searches, chapter/unit, creation record, blueprint ancestry,
   status and matching Lean record; its empty proof-dependency list records the still
   unformalized sourced argument, not an asserted completed proof.

**Second-reader changes:** added source and blueprint references to the three new module
headers, removed an extra blank line after `module`, and corrected doubled TeX backslashes
in the three new mathematical node statements. No theorem signature, proof, dependency
route, hole count, or public import was changed. The Lean proof itself required no repair.
