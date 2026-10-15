## What changed

Proved `CommRingCat.etaleContraction_properties` with its original statement and all public
imports unchanged. Seven proved private helpers handle finite-tensor presentations, sequential
projections, singleton factors, and ring retractions. The proof uses the existing source
library's finite-wide-pullback and pro-morphism API, algebraic étale descent, and maximal-local
strict henselian criterion. The DAG now records this route.

## Proved and sorry left

Closed the one original hole, `CommRingCat.etaleContraction_properties`. No sorry remains in the
delivered module and no hole was added. All helpers are proved. `#print axioms` for the complete
theorem reports exactly `propext`, `Classical.choice`, and `Quot.sound`. The unchanged module
compiles through `lcompile.py` in approximately three seconds.

## No longer needed

Removed these nine proof imports:

- `Sheaf.RingTheory.IndEtaleStability`
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`
- `Sheaf.Paper.EtaleFiniteDataDescent`
- `Mathlib.AlgebraicGeometry.AffineTransitionLimit`
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Mathlib.AlgebraicGeometry.Limits`
- `Mathlib.RingTheory.TensorProduct.Basic`
- `Sheaf.RingTheory.DirectedColimitFaithfullyFlatAlgebras`

The following old direct proof dependencies are unnecessary for this proof:

- `lem-weil-pbc-directed-colimit-faithfully-flat-algebras` and its module
  `Sheaf.RingTheory.DirectedColimitFaithfullyFlatAlgebras`: the proved source theorem
  `CommRingCat.ind_faithfullyFlat_eq_faithfullyFlat` supplies the required colimit stability.
- `lem-weil-pbc-ind-etale-stability` and `Sheaf.RingTheory.IndEtaleStability`: generic
  multiplicativity and idempotence of pro-étale morphisms supply the relevant clauses.
- `lem-weil-pbc-limit-affine-transition` and `Sheaf.AlgebraicGeometry.LimitAffineTransition`.
- `lem-weil-pbc-etale-finite-data-descent` and `Sheaf.Paper.EtaleFiniteDataDescent`.
- `lem-weil-pbc-limit-affine-stage`: algebraic étale descent supplies an affine model directly.
- `lem-weil-pbc-affine-morphism-permanence`: no scheme-affineness conversion is needed.
- `lem-weil-pbc-algebra-tensor-base-change-universal-property`: the categorical pullback lift
  in opposite commutative rings implements the required tensor map.
- `def-weil-pbc-scheme-conventions`: no separate quasi-compact or quasi-separated scheme
  argument is needed to establish finite presentation.

These are removals from this node's direct proof route; shared modules can remain reachable
through other parents. All six public imports remain because they provide notions appearing
in the statement; the retraction-criterion proof import is retained.

## Where the brief, the DAG or earlier work was wrong

The planned detour through scheme descent and eventual affineness is unnecessary. The source
library has a proved `PreIndSpreads` instance for étale ring maps, which descends the algebra
and the pullback square directly. This is also the route in Stacks' `lemma-first-construction`:
faithful flatness of the descended étale map follows from surjectivity of the composite on
spectra and flatness of an étale map. The original construction is used unchanged, including
its skeleton of representatives; no identification with the separately defined
`IndEtaleContraction` is assumed. The unit statement and route are preserved, and no definition
or public signature changed. Zero rings, empty finite families, and the initial stage are
covered by the generic wide-pullback and pro-property proofs.

## Second reading by D4

1. **Unchanged interface: PASS.** Compared the delivered Lean file with the repository
   using `diff`. The only existing declaration, `CommRingCat.etaleContraction_properties`,
   has a byte-for-byte identical signature, visibility, and docstring. All six public
   imports are unchanged. The additions are seven private proved helpers; the other
   changes are the theorem proof and nine removed plain proof imports. No definition,
   target, other module, or statement changed; no change record is needed.
2. **Proof and axioms: PASS.** Independently compiled the delivered file with
   `lcompile.py`: no errors or warnings, approximately three seconds. Compiled a scratch
   copy with `#print axioms` for the public theorem and each of the seven private helpers.
   Every result lists exactly `propext`, `Classical.choice`, and `Quot.sound`. Scanned the
   delivered Lean source: no `sorry`, forbidden axiom, unsafe declaration, opaque
   declaration, external implementation, or kernel-check bypass. There is no new data
   definition or choice from an unproved existence theorem.
3. **Split-off statements and edge cases: PASS.** No statements were split off and no
   holes were added. Read each proved helper: the finite-tensor presentation uses the
   actual skeleton-based construction; the singleton projection is composed with the
   SmallModel and Skeleton comparison isomorphisms in the over-category. The empty
   finite family ensures the indexing category is nonempty, and the wide-pullback
   theorem explicitly handles the empty tensor. The sequential argument covers `n = 0`
   and lifts the countable index universe. No nonzero-ring hypothesis is introduced;
   for the zero ring the maximal-ideal assertion is vacuous.
4. **Shortest route, imports, and pruning: PASS.** Searched `lean/Sheaf/RingTheory` and
   the upstream pro-etale contraction modules by construction, retraction, and spectrum
   surjectivity terminology, and read `ProEtaleContraction`, `Contraction.Covers`, the
   etale `PreIndSpreads` instance, faithful-flat ind-stability, and the generic
   maximal-localization criterion. The upstream contraction theorem concerns a
   different construction, so applying it directly would require an additional
   comparison; the seven helpers instead use the existing generic API on this exact
   diagram. The descent square, faithful flatness of the stage projection, and
   surjectivity of a composite justify the descended cover before the singleton factor
   and pullback lift produce its section. The public imports supply statement notions;
   the remaining plain import supplies the maximal-localization criterion. Compared
   old and new `proof_deps`: all eight removed node IDs and all nine removed imports
   appear in `No longer needed`. These are direct-route removals, not claims of global
   unreachability. Read `dag/units/sk-thm-properbasechange.json`: this node is below its
   realized statement and steps; no unit route or realized node is bypassed.
5. **DAG agreement: PASS.** Parsed and compared both node records: only `proof`,
   `proof_deps`, and `proof_origin` differ. The new dependency list equals the union of
   the five steps' `uses`; all cited nodes exist and their Lean declarations match the
   construction, component notions, and final recognition criterion. The five steps
   describe the seven helpers and final assembly as implemented. There are no new
   nodes to validate. The unchanged Lean docstring retains the original proof plan;
   the updated DAG and this report record the shorter implemented proof.

Second reading changed only this report by adding the independent checks above. The Lean
proof and node record passed unchanged. Holes closed: `CommRingCat.etaleContraction_properties`
(one of one original holes). Holes added: none. This is a complete proof, not a decomposition.
