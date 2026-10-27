## What changed

The single original hole `WeilConjectures.extensionByZero_punctual` is reduced to
four strict parts of its argument, with a complete Lean assembly proof and
unchanged theorem statement. The parts are carrier realization, natural geometric
fibres, finite-stage Frobenius compatibility, and weight-independent spectrum
transport. Each is a public named theorem in its own new module, with a matching
node, its source, and a complete natural-language proof. They apply to any left
adjoint to the prescribed Weil restriction, so do not redefine the chosen
extension or move the whole original theorem under another name.

The adjunction construction now retains finite limits and finite colimits of
its underlying heart extension. The exact fixed-pair lift and the two equivalences
preserve these; uniqueness of left adjoints proves the new, fully proved
`WeilConjectures.zlOpenWeilShriek_exact`. It also supplies additivity by finite
products. The existing right-adjoint theorem is recovered from this same argument.
Its signature and the chosen left-adjoint definition are unchanged.

The last two clauses are proved by transporting each output eigenvalue to an
input closed point with the same residue cardinality, applying the original
bound or equality there, and rewriting that cardinality. This part is actual
Lean argument, with no remaining hole and no spectral-bound assumption built
into the intermediate statement.

To avoid a cycle, the existing carrier, finite-stage, closed-fibre and upper-bound
interface is moved verbatim to `Sheaf.Paper.OpenWeilCoefficientFibres` and publicly
re-exported by the original module. All ten moved public signatures and bodies
were compared mechanically and are identical; the private, proved transport
helper moves with them. This is required so the new intermediate statements can
refer to the same coefficient functors independently of the main theorem.
No adopted source-library file is edited. The change record is
`coord/changes/S8-open-weil-coefficient-interface.md`.

## Proved and sorry left

One original hole is closed by decomposition:
`WeilConjectures.extensionByZero_punctual`
(node `lem-zl-extension-by-zero-punctual`). Exactness and the weight-consequence
assembly are complete proofs, using the original adjunction dependencies and the
new comparison statements. The added theorem
`WeilConjectures.zlOpenWeilShriek_exact` and the private exact-adjunction lemma
are completely proved. No original proved declaration is replaced by a hole.

Four holes are added, each exactly the complete proof `:= by sorry`:

- `WeilConjectures.openWeilCarrierRealization`, node
  `lem-zl-open-weil-carrier-realization`, module
  `Sheaf.Paper.OpenWeilCarrierRealization`.
- `WeilConjectures.openWeilGeometricFibres`, node
  `lem-zl-open-weil-geometric-fibres`, module
  `Sheaf.Paper.OpenWeilGeometricFibres`.
- `WeilConjectures.openWeilFiniteStageFrobenius`, node
  `lem-zl-open-weil-finite-stage-frobenius`, module
  `Sheaf.Paper.OpenWeilFiniteStageFrobenius`.
- `WeilConjectures.openWeilPunctualSpectrum`, node
  `lem-zl-open-weil-punctual-spectrum`, module
  `Sheaf.Paper.OpenWeilPunctualSpectrum`.

Actual item holes: 1 before, 0 after. Actual delivered-set holes: 4.
Holes closed minus holes added: 1 - 4 = -3. This is a decomposition, not a claim
that the mathematical comparison work is finished. No hole occurs in a
definition, private declaration, or partial proof.

## No longer needed

No original module or import is pruned from the targets' closure. The normalized
coefficient-stage, open-unit, complementary-restriction, residue-Frobenius and
point-transport lemmas remain needed in the proof plans of the four split parts.
The parent no longer directly proves those parts, so its proof dependencies now
name the four new nodes. Their dependencies retain those existing nodes.

Exactness no longer requires an additional argument using
`lem-dl-a1-constructible-fibres-exact` (`Sheaf.Paper.DlConstructibleFibresExact`):
the existing exact common-stage open-heart adjunction and fixed-pair preservation
instances already prove it. This is a local proof-dependency pruning; no module
is withdrawn, and the lemma may remain needed by other parents. No source
upstream declaration or proof is removed. Geometry is supplied by the existing
base-change and Noetherian instances, not additional parent lemmas.

## Where the brief, the DAG or earlier work was wrong

The existing adjunction proof threw away exactness of its underlying left
adjoint. Retaining it gives the full exactness clauses without the additional
fibrewise short-exactness argument in the original DAG.

The named coefficient operations are not definitionally the chosen Weil-heart
left adjoint. Its construction proves existence of an adjunction, without
exporting its normalized compact-support carrier or local Frobenius comparison.
The split statements isolate exactly these bridges. They preserve the original
coefficient categories, universes, local operators and all hypotheses.

The earlier Z5 report says the open-unit package fixes the coefficient universe
to the scheme universe. The current shared source quantifies the coefficient
universe independently. This delivery follows the current source and keeps the
independent universes of the assigned theorem.

Edge cases were checked at the statement level: empty open, empty target,
identity open, zero sheaf, arbitrary real weights, zero/nonzero eigenvalues,
and geometric points over nonclosed scheme points. The spectrum statement
assumes an actual eigenvalue, so outside-open zero fibres make its conclusion
vacuous, rather than requiring a point in an empty open. The fibre statement
quantifies all algebraically closed geometric fields, not only Spec(k).

All five supporting modules have passed Lean elaboration, including the four
new theorem statements. The main module also compiled successfully (18.7 seconds). The final delivery
gates are run on the complete packet.

The unit route is preserved: these are parts of the open-extension argument in
proof (1) and (2) of `lem-zl-quasi-finite`, not a bypass of the quasi-finite unit.
The carrier/fibre interface node only records relocated existing constructions.

## New nodes

`def-zl-open-weil-coefficient-fibres` records the unchanged finite coefficient
inclusion and its normalized square, carrier and fibre interfaces. Its module
has zero holes and contains only the existing constructions and proved lemmas.

`lem-zl-open-weil-carrier-realization` records only the compact-support carrier
comparison for integral finite-stage presentations, using the existing
coefficient-stage t-exactness and normalized open-unit packages.

`lem-zl-open-weil-geometric-fibres` records the natural fibre comparison and
outside-open vanishing at arbitrary geometric points, using the existing adic
fibre and complementary-restriction results.

`lem-zl-open-weil-finite-stage-frobenius` records the finite Weil extension,
its scalar inclusion comparison and the actual local-Frobenius intertwining
identity, using the existing normalized coefficient and residue-pullback lemmas.

`lem-zl-open-weil-punctual-spectrum` records eigenvalue transport and unchanged
residue cardinality, independent of weights and of the complex embedding. Its
proof plan uses the finite-stage Frobenius comparison, empty-fibre formula,
finite Weil-diagram descent and local operator conjugacy. The parent derives
both weight clauses from it by an explicit pointwise Lean argument.

Change record: `coord/changes/S8-open-weil-coefficient-interface.md`.

## Second reading by S8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
