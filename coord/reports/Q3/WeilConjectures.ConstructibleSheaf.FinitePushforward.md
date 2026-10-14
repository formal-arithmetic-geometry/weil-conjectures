## What changed

Replaced the proof of
`AlgebraicGeometry.Etale.isIso_unit_constantSheaf_of_isIntegrallyClosed` by a constructor
using two strict conjunct declarations, and added those declarations in dedicated modules.
The finite-presentability and Noetherian-descent proofs were already complete in the repository
baseline and are unchanged. The wrapper's proof-only imports were adjusted while unused imports
were pruned. No theorem signatures or definitions changed.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.Etale.isIso_unit_constantSheaf_of_isIntegrallyClosed` is decomposed by a
constructor proof from two strict conjuncts; this is a decomposition rather than a direct
proof because both conjunct declarations remain open. The existing holes in
`AlgebraicGeometry.Etale.exists_mono_biproduct_lowerStar_of_isNoetherian` remains open.
`AlgebraicGeometry.Etale.isFinitelyPresentable_of_isConstructibleSheaf` and
`AlgebraicGeometry.Etale.exists_isNoetherian_upperStar_iso` were already proved before this
delivery and are not counted as newly closed holes. The following declarations remain sorry:

- `AlgebraicGeometry.Etale.exists_mono_biproduct_lowerStar_of_isNoetherian`
- `AlgebraicGeometry.Etale.isIso_unit_constantSheaf_generic_unit`
- `AlgebraicGeometry.Etale.isIso_unit_constantSheaf_open_unit`

## No longer needed

The following proof-only imports remain removed because the delivered proofs do not use them:

- `Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk`
- `Sheaf.AlgebraicGeometry.ConstructibleFiniteSelection`
- `Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePresentation`
- `Sheaf.AlgebraicGeometry.EtaleLocalRingTriples`
- `Sheaf.AlgebraicGeometry.EtaleSheaves`
- `Sheaf.AlgebraicGeometry.NormalScheme`
- `Sheaf.AlgebraicGeometry.StrictHenselization`
- `Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula`
- `Sheaf.RingTheory.EtaleColimitNormalLocalDomain`
- `Sheaf.RingTheory.StrictHenselizationTriples`
- `WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

No DAG node became unreachable; all remaining imports are used by a completed proof or a public
statement.

The previous full geometric proof recorded these proof dependencies for the normal-unit node;
the constructor route no longer uses them directly:

- `lem-weil-pbc-constant-sheaf-maps-global-sections`
- `lemma-constructible-pullback-constant`
- `def-weil-pbc-direct-image`
- `def-weil-pbc-inverse-image`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `def-weil-pbc-scheme-conventions`
- `def-weil-geometric-point`
- `def-pc-integral-scheme`
- `def-sbc-normal-dominant-galois`
- `def-weil-pbc-strict-henselization-limit`
- `lem-weil-pbc-etale-local-ring-triples`
- `lem-weil-pbc-strict-henselization-triples`
- `lem-weil-pbc-etale-colimit-normal-local-domain`
- `def-pc-fibre-product`
- `lem-weil-pbc-generic-fibre-localization-domain-irreducible`
- `prop-weil-pbc-strict-henselization-stalk-formula`
- `def-weil-pbc-etale-sheaves`
- `def-weil-pbc-geometric-stalks`
- `lem-weil-pbc-constant-sheaf-geometric-stalk`
- `lem-weil-pbc-constant-sheaf-sections-connected`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `lem-weil-pbc-inverse-image-composition`

## Where the brief, the DAG or earlier work was wrong

The worker report described two proofs as restored even though those proofs were already present
in the supplied repository baseline. The only proof change is the normal-constant wrapper and
its two explicit split obligations; no target statement was weakened.

## New nodes

- `lem-weil-pbc-normal-constant-generic-unit`: split-off generic-point unit theorem in
  `Sheaf.AlgebraicGeometry.NormalConstantGenericUnit`, still `sorry` and requiring the
  strict-henselian affine-etale section calculation from Tag 09Z5.
- `lem-weil-pbc-normal-constant-generic-open-unit`: split-off nonempty-open unit theorem in
  `Sheaf.AlgebraicGeometry.NormalConstantOpenUnit`, still `sorry` and requiring the same
  calculation after restriction to a nonempty open.

## Second reading by Q3

1. **Interface:** Compared the delivered module with the repository version using `diff`.
   Every existing declaration signature and definition is unchanged; the item changes only
   proof text and proof-only imports. The two added modules introduce the two explicitly
   split conjunct statements.

2. **Proof and trust:** Compiled all three delivered modules in sandbox import order with
   `lcompile.py`; compilation succeeds without warnings. A source scan found no forbidden
   declarations and no `sorry` in a definition. The finite-presentability theorem has only
   the permitted axioms; the normal-unit wrapper and Noetherian-descent helper inherit
   `sorryAx` solely through the three named open declarations listed above and existing
   imported descent/Noetherian lemmas.

3. **Split statements:** The generic-point and nonempty-open declarations are strict
   conjuncts of the original 09Z5 statement, with the same hypotheses and the corresponding
   single conclusion. Their statements spell out those hypotheses independently, so the DAG
   has no statement/proof dependency cycle through the parent node. Their docstrings give the
   Stacks source and the remaining geometric proof obligation; no duplicate library theorem
   was found.

4. **Route and pruning:** The wrapper proof is the direct constructor route through the two
   split declarations. The finite-presentability proof uses the affine-free presentation,
   filtered-colimit sections, and finite-colimit presentability route. Removed proof-only
   imports are unused by compilation, and the unit's generic/open route is retained.

5. **DAG agreement:** The new node records match the declarations, sources, statements and
   split status, and the existing normal-unit node now records the constructor route and its
   two split dependencies. Existing target statements remain unchanged. The delivery records
   the original normal-unit hole as a two-node decomposition and records the three remaining
   named holes without adding a hollow definition.

Changes by this reader: added this independent second-reading section; no Lean repair was
needed after compilation and signature comparison.


