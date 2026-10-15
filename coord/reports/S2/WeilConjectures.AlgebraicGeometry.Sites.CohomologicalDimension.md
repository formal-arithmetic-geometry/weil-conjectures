## What changed

The existing target module keeps both theorem signatures and all public imports unchanged.
Its main theorem now supplies the affine `d + c` bound to the comparison/Leray reduction.
Both imports of the new proof-stage modules are ordinary `import` declarations.

Two new modules state the remaining stages:
`Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension` and
`Sheaf.AlgebraicGeometry.Sites.AffineToGlobalTorsionCohomologicalDimension`.
Their public imports provide the finite-type, Krull-dimension, small-etale sheaf,
and cohomology definitions and the instances needed to elaborate their signatures.
The reduction assumes affine vanishing, so it does not import the affine theorem or
assume the ground-field cohomology bound. The latter is used only in the affine stage.
No existing declaration, definition, or target statement changes. No change record is required.

## Proved and sorry left

This delivery is a decomposition, not a completed proof of the cohomological-dimension bound.
There was one hole in the original module. One upper hole is closed by a Lean proof:
`AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_add_lt`
(node `thm-sc-finite-type-torsion-cd`). Two lower holes are added:

- `AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_add_lt_of_isAffine`
  (node `new-thm-sc-affine-torsion-cd-bound`);
- `AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_add_lt_of_affine_bound`
  (node `new-thm-sc-finite-type-torsion-cd-affine-reduction`).

These are the only delivered `sorry` proofs, each exactly `:= by sorry`, with its
source and a complete natural-language proof in its docstring. The first specializes
the affine theorem already planned in the blueprint, including the empty scheme.
The second records just the comparison/Leray step with affine vanishing as a hypothesis.
The local accounting is one hole closed, two added, net minus one: zero of one original
holes resolved without replacement assumptions. There is no claimed closure gain.

`AlgebraicGeometry.Scheme.subsingleton_H_of_two_mul_lt_of_isSepClosed` was already proved
by specialization in the repository; its proof is unchanged and is not newly closed.
It still depends on the open affine and comparison stages through the main theorem.

All three final modules compile through `lcompile.py --all`. A scratch copy prints axioms
for both original and both new theorems: each lists only `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx`. Thus none is claimed to meet the final no-sorry acceptance
criterion yet. The delivery preflight independently repeats the compilation and axiom checks.

## No longer needed

No existing source imports are removed, and no existing modules are claimed pruned.
The comparison module no longer publicly imports the new affine module; neither its
signature nor its hypothetical comparison proof requires that theorem.
The affine module no longer imports the large `FiniteSupport` module: its signature
uses the directly named cohomology and Grothendieck-sheaf infrastructure instead.

The parent node now directly uses only the two split nodes. Its former dependencies are
retained in their appropriate proof stages, rather than claimed globally unnecessary.
`thm-sc-affine-torsion-cd` is the affine stage's source dependency. These other former
parent dependencies are the reduction node's proof dependencies:

- `lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites`
- `def-weil-pbc-sites-and-cohomology`
- `lem-sp-right-adjoint-preserves-injectives`
- `def-sc-zariski-cohomology`
- `thm-sp-grothendieck`
- `def-weil-size-convention`
- `lem-pur-ringed-site-grothendieck-abelian`
- `def-weil-pbc-constant-sheaf`
- `def-weil-sheaf-of-modules-category`
- `def-sp-composite-acyclicity`
- `lem-weil-pbc-filtered-colimit-abelian-groups-exact`
- `lem-sc-abelian-sheaf-exact-iff-stalk-exact`
- `lem-weil-pbc-etale-cohomology-over-open`
- `pqf-lem-locnoeth-lft`
- `def-weil-pbc-scheme-conventions`
- `def-kun-topological-krull-dimension`
- `lem-sc-zariski-dimension-bound`
- `def-sc-etale-torsion-cd`
- `lem-weil-pbc-affine-opens-basis`
- `lem-weil-pbc-etale-site-localization-open`
- `lem-weil-pbc-site-extension-by-zero-presheaf-adjoint`
- `def-weil-pbc-etale-sheaves`

## Where the brief, the DAG or earlier work was wrong

The first report incorrectly credited the already-proved separably closed specialization
as a newly closed hole. It also failed to classify the two new holes as a decomposition.
The first new-node records depended on the parent theorem through `stmt_deps`, creating
cycles with the parent's new `proof_deps`. Those dependencies are replaced with the actual
cohomological-dimension, scheme, and topological-dimension definitions.

The first reduction node cited the affine calculation's source file and listed just the
affine theorem as a proof dependency, although the affine bound was a hypothesis. It now
cites the parent's comparison-site proof and retains the original comparison and vanishing
ingredients. The unused field-bound hypothesis and public affine-theorem import were removed
from this new statement. Both new Lean signatures are recorded verbatim in their nodes.

The original affine docstring only sketched its deep calculation. It now explicitly deduces
this bounded-dimension formulation from the existing blueprint affine theorem, covers the
empty case, and cites [Stacks Tag 0F0V](https://stacks.math.columbia.edu/tag/0F0V).
The comparison docstring now explains the site adjunction, injectives, filtered colimits,
torsion restriction, affine-neighbourhood dimension, and finite spectral-sequence filtration.

The original affine DAG theorem has no Lean declaration attached. Searches of repository
Lean, the upstream checkout, and Mathlib found no existing affine `d + c` theorem or matching
comparison reduction. The upstream version of the target still contains its original hole.
`FiniteAffineCoverRestrictionBound` instead assumes positive-degree affine acyclicity and a
finite separated cover; it does not supply either missing dimension theorem.

## New nodes

`new-thm-sc-affine-torsion-cd-bound` states the affine input with threshold `d + c`,
retains `thm-sc-affine-torsion-cd` as its mathematical source dependency, and lies strictly
below the global comparison step. It adds no field or sheaf hypothesis beyond the affine
specialization needed by the parent proof.

`new-thm-sc-finite-type-torsion-cd-affine-reduction` assumes the affine input uniformly
and proves only the global comparison step. It needs no cohomological-dimension hypothesis
on the field beyond that affine input. Its dependency union contains the comparison,
locality, and Zariski vanishing ingredients of the original parent proof.

## Second reading by S2

1. **Existing interfaces: pass.** Diffed the original target module and compared both
   declaration headers byte for byte up to `:=`. They are identical. No definitions or
   public imports change. The separably closed proof is unchanged. Only new, undelivered
   intermediate signatures were repaired; no existing interface change needs a record.

2. **Lean proof and trust: pass as a decomposition.** Compiled the three final modules in
   import order. A scratch copy checks axioms of all four declarations; the only extra axiom
   is `sorryAx` from the two explicitly listed open statements. Scanned the delivered sources:
   no forbidden axiom, unsafe, opaque, extern, or implementation hook; no definition holes.
   Removed the two temporary `#check` commands.

3. **New statements: pass.** The affine theorem is the blueprint affine bound expressed with
   a natural-number upper bound on dimension. It includes empty schemes, dimension zero,
   separably closed fields, disconnected schemes, and sheaves with no uniform annihilator.
   The comparison step is strictly separate: with affine vanishing supplied, it proves the
   Leray/Zariski conclusion and cannot supply the affine theorem itself. At `d = 0` its
   threshold is `c`; the spectral sequence argument still applies. No separatedness is
   assumed or used. The three fresh search modes (leanfinder, loogle, grep), broader library
   searches, and upstream inspection produced no matching existing Lean theorem. Neither
   split can be closed in a few minutes from the available APIs; even the relevant general
   spectral-sequence constructions remain open. No artificial proof by the parent's rename.

4. **Route and pruning: pass after repair.** Read `dag/units/sk-prop-sf-cbc.json`; its realized
   statement and step lists are empty, and this auxiliary theorem is not a recorded unit
   realization. The affine input followed by comparison, Leray, and Zariski vanishing is the
   original route. Both new target imports are proof-only; removed the unnecessary public
   affine-module dependency. No actual module pruning is claimed. All former parent proof
   dependencies remain accounted for in the two stages.

5. **Node agreement: pass after repair.** Existing-node edits are limited to `proof`,
   `proof_deps`, and `proof_origin`; the original metadata and split report are restored.
   Both new nodes have source, proof steps, dependency unions, searches, creation metadata,
   blueprint ancestry, chapter/unit, and verbatim Lean records. Replaced circular statement
   dependencies and checked that no combined statement/proof dependency cycle passes through
   any delivered node. Unrelated existing cycles deeper in the repository's graph were not
   changed by this delivery.

Second reading changed: removed two `#check` commands; replaced overly broad and unnecessary
public imports with signature dependencies; removed the unused field-bound hypothesis from
just the new reduction and adapted its sole proof caller; expanded the two proof docstrings;
fixed circular node statement dependencies, source attribution, and proof-dependency metadata;
restored untouched parent metadata; corrected the proof counts and pruning report.
