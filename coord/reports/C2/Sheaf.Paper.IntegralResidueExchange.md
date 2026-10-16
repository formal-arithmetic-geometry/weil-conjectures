## What changed

The signature of `AlgebraicGeometry.ProEtale.CondensedRing.integralResidueExchange_comparison`
is byte for byte unchanged. Its proof equips the actual reduced object with bounded
constructibility, constructs the two endpoint isomorphisms, and applies `Arrow.isoMk`
to the actual specified exchange maps.

Seven new modules implement bounded constructibility of reduction, a typed coherent
coefficient-comparison interface, the abstract mate calculation, componentwise equality
transport, identification of bounded exchange with ambient exchange, and specialization
of the mate calculation. The wrappers contain the existing functors. Every definition
constructs its data explicitly; none chooses arbitrary data from an unproved existence
assertion. The existential coefficient comparison is eliminated only inside a theorem.

The second reader completed `boundedConstructibleBaseChange_hom_eq_ambient` using the
newly landed `boundedConstructibleBaseChange_adjunct` API. The sandbox's stale
`MorphismDefs` copy, proposed equation theorem, associated node, and change record were
removed. No existing source module besides the item's proof is delivered or adapted.
The unused private `bounded_unit_hom` helper was removed. The generic coefficient
calculation publicly imports `Adjunction.Basic`, which suffices for its signatures.

## Proved and sorry left

One original hole closed, one new named hole added: net zero locally. This is a
decomposition, not an unconditional proof or a net sorry reduction. Closure-wide
progress is determined by the maintainer's pinned sorry ledger.

Original hole closed:
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidueExchange_comparison`.

Completed supporting theorems:

- `AlgebraicGeometry.ProEtale.CondensedRing.integralReduction_restricted_mem`:
  restricted reduction is the cone of multiplication by ℓ and preserves triangulated
  properties.
- `AlgebraicGeometry.ProEtale.CondensedRing.integralReduction_boundedConstructible`:
  boundedness and constructibility, including reflection along quotient restriction.
  Uses existing `integralConstructible_serre`, `integralReduction_restrictTensor`,
  `_root_.localFinitePresentation_of_iso`, and `_root_.constructible_of_iso`.
- `CategoryTheory.Adjunction.coefficient_exchange_of_counit` and
  `CategoryTheory.Adjunction.composition_square_aux`: abstract exchange coherence and
  transport of composition compatibility.
- `CategoryTheory.transportedCompositeIso_eq`: componentwise transport agrees with
  ordinary equality transport of functors.
- `AlgebraicGeometry.ProEtale.CondensedRing.IntegralResiduePullComparisons.push_counit`
  and `AlgebraicGeometry.ProEtale.CondensedRing.residueExchangeBaseChange_counit`:
  counit identities of the explicitly constructed mates.
- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleBaseChange_hom_eq_ambient`:
  equality of the specified bounded exchange component and the ambient mate. The second
  reader closed this formerly split hole by comparing adjuncts and substituting the
  proved counit, composition, and square component identities.
- `AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_exchange_square`:
  coefficient compatibility of ambient exchange, without assuming invertible push mates.

The only new or delivered `sorry` is
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_comparisons`, node
`lem-weil-pbc-integral-residue-comparisons`. It asserts coherent pull comparisons and
invertibility of their specified push mates on ambient derived categories. It mentions
no square, exchange arrow, boundedness, or constructibility and does not restate the
item. Its docstring gives the complete mathematical argument: derive scalar-pull
associativity on K-flat resolutions, check composition coherence, identify the
restricted mate with the dualizable projection comparison, and reflect invertibility
through exact faithful restriction. The required formal comparison and coherence APIs
remain to be implemented. Identity morphisms, zero complexes, and empty schemes impose
no missing nonemptiness or positive-rank hypothesis.

## No longer needed

Pruned original modules: none. All three original public imports are retained for the
unchanged signature. The original proof dependency
`def-weil-pbc-continuous-integral-coefficients` remains a statement dependency and is used
by the actual constructions. No original proof-dependency module becomes unnecessary.
New proof-only imports are private; public imports supply public signatures or
construction bodies.

The proposed new `boundedConstructibleBaseChange_eq_steps` theorem and node were dropped
because the current library already supplies the stronger useful adjunct API. These
were never landed modules or original dependencies. The unused private bounded unit
helper was also dropped. Preflight conservatively treats the local transparency command as an interface edit.
`coord/changes/integral-residue-exchange-local-transparency.md` records its elaboration-only
effect and all six downstream modules; no existing signature or definition changes.

## Where the brief, the DAG or earlier work was wrong

The original plan had no Lean-attached dependencies for its coefficient and mate steps.
The delivery implements bounded constructibility and the mate algebra independently of
the remaining coefficient theorem. Flat-coefficient `derivedPullIso` and
`derivedPushHom` require exact extension of scalars and cannot directly handle reduction
modulo ℓ.

The previous sandbox assumed the old unexposed three-step bounded exchange definition.
The shared repository now has an equal adjunct presentation and a proved
`boundedConstructibleBaseChange_adjunct` API. Delivering the stale sandbox source would
have reverted these changes. The second reader removed the source edit entirely and
used the existing API to close the bounded-to-ambient equality.

The inherited unrestricted
`boundedConstructible_rightDerivedLowerStar_obj` is already marked
`STATEMENT-DISPUTED` in the shared library for general condensed coefficients. This
work compares the existing constructions and does not resolve or alter that assertion.
It adds no geometric hypothesis and changes no target statement or definition.

Checked Bhatt--Scholze v2, Lemma 6.5.9(3), Proposition 6.8.11(1),(3), and Remark 6.8.15
at [the paper](https://arxiv.org/pdf/1309.1198). The perfect projection and triangulated
constructibility arguments supply the mathematical content; the docstrings expand the
formal coefficient and adjunction coherence argument. Unit
`dag/units/sk-thm-properbasechange.json` and its realized statement and three steps are
unchanged; the delivery refines only the integral coefficient subargument.

## New nodes

All thirteen new nodes are under `dag/nodes/sec-proper-base-change/`:

- `def-weil-pbc-residue-exchange-ambient`: actual ambient square and its exchange mate.
- `def-weil-pbc-residue-exchange-comparison-interface`: typed actual functors, coherent
  pull comparisons, and their constructed push mates.
- `def-weil-pbc-transported-composite-iso`: componentwise equality transport.
- `lem-weil-pbc-bounded-exchange-ambient`: proved bounded-to-ambient identification.
- `lem-weil-pbc-coefficient-exchange-mates`: proved abstract counit calculation.
- `lem-weil-pbc-composition-square-cancellation`: proved composition transport.
- `lem-weil-pbc-integral-reduction-constructible`: proved bounded constructibility.
- `lem-weil-pbc-integral-reduction-triangulated-property`: proved cone reduction.
- `lem-weil-pbc-integral-residue-comparisons`: the sole remaining named hole.
- `lem-weil-pbc-integral-residue-exchange-algebra`: proved ambient specialization.
- `lem-weil-pbc-integral-residue-push-counit`: proved coefficient mate counit equation.
- `lem-weil-pbc-residue-exchange-counit`: proved ambient mate counit equation.
- `lem-weil-pbc-transported-composite-iso-eq`: proved transport equality.

Change record: `coord/changes/integral-residue-exchange-local-transparency.md`.

## Second reading by C2

1. **Interfaces — pass.** Compared every delivered module with the current read-only
   repository. Only `IntegralResidueExchange` already exists in the final delivery;
   its declaration signature is byte for byte identical. Its proof, private imports,
   and local elaboration attributes change. Removed the stale `MorphismDefs` adaptation
   completely, preserving the repository's new API, definitions, and visibility.

2. **Proofs and data — pass as a decomposition.** Read all eight modules, including
   quotient finite-presentation reflection and the generic counit calculation. Every
   definition has constructed data. Exactly one `sorry` remains, in the named public
   coefficient theorem with its node and full proof in words. No axiom, unsafe,
   opaque, implemented_by, extern, kernel bypass, or increased compilation limit occurs.
   The bounded-to-ambient equality is now proved by the current bounded adjunct API.

3. **Split statement — pass.** The sole remaining coefficient theorem omits all exchange
   and constructibility conclusions and is strictly a part of the argument. Tensor
   associativity and the dualizable projection argument give its stated mathematical
   proof. Checked identity maps, zero objects, empty schemes, and zero presentation
   ranks. Independently searched Lean Finder, Loogle, Mathlib grep and local `lean/`
   using scalar extension, inverse image, perfect projection, restriction, and mate
   terminology. Read the flat coefficient API, `MonoidalProjectionConjugate`, and
   `RingedExchangeTensorCoherence`; none constructs this coherent family for the actual
   quotient internal-module functors. Search evidence is added to the remaining-hole node.

4. **Route and pruning — pass.** The top proof constructs the actual reduced object and
   endpoint isomorphisms, identifies the specified exchange maps, and uses the proved
   ambient mate square. The original coefficient dependency remains used and reached.
   The unit's realized route stays unchanged. Proof imports are private, and public
   imports support public signatures or construction bodies. No old module is pruned.
   Reused the newly landed adjunct API and removed the proposed duplicate equation API.

5. **DAG — repaired, then pass.** Checked all fourteen primary Lean signatures against
   their node records, new-node required fields, all dependency references, and equality
   of `proof_deps` with the union of step uses. Updated the bounded-identification route
   to the actual adjunct proof and existing square-exchange node, removed its dependency
   on the dropped equation node, and corrected proof-origin notes to list only the
   coefficient theorem as unfinished. Definition nodes inventory all exposed wrappers
   and mate constructions. The original item's statement and unit record stay unchanged.

Second-reading changes: closed the bounded-identification hole; removed the stale source
adaptation, its equation theorem/node/change record, and the unused unit helper; updated
DAG routes, search evidence, and hole accounting. No existing signature or definition
changes are delivered.

Validation: `lcompile.py --all` compiled all eight delivered modules without errors or
warnings. The separate scratch `SecondReadingAxioms.lean` printed axioms for all 22
public declarations of the delivery and five existing exchange definitions. Only
`propext`, `Classical.choice`, `Quot.sound`, and inherited/new `sorryAx` occur. In
particular, the triangulated reduction theorem, generic mate calculation, ambient
exchange algebra, wrappers, and mate constructions have no `sorryAx`. The completed
bounded identification and constructibility theorem still inherit existing library
holes. A source scan found exactly the one reported named coefficient hole, and all
fourteen node signatures and dependency unions passed the independent audit.

The first current dry run passed compilation and declaration probes but requested a
change record for the local transparency attributes. Added the elaboration-only record
above with the complete downstream table; no Lean source changed in this repair.

The repaired delivery dry run printed `OK`: all delivered files and declaration probes
compiled and stage-3 preflight passed (review class CODEX, expected for new nodes/modules
and the declared local elaboration command). The final delivery repeats these checks
before pushing.
