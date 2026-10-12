## What changed

Proved `AlgebraicGeometry.finiteEtaleDescent` with its signature unchanged.
The proof constructs the canonical functor and projection equations, obtains
full faithfulness and essential surjectivity separately, and assembles the
`Functor.IsEquivalence` structure. The three new modules are
`Sheaf.AlgebraicGeometry.FiniteEtaleDescentDataExistence`,
`Sheaf.AlgebraicGeometry.FiniteEtaleDescentFullyFaithful`, and
`Sheaf.AlgebraicGeometry.FiniteEtaleDescentEssentiallySurjective`.
All their theorems are proved. They make explicit Steps 2, 3, and 4--5 of the
existing plan. The unit `sk-prop-h2` has no realized statement or step at this
node; its route is unchanged.

The canonical datum is constructed directly using pullback lifts, with identity,
naturality and cocycle proved by pullback uniqueness. Canonical base change of
morphisms, the functor laws, and every projection equation are proved directly.
Full faithfulness uses Mathlib's effective epimorphism instance for surjective
flat locally finitely presented morphisms. The projection is a base change of
an etale surjection, so no quasi-compactness assumption is introduced.
Essential surjectivity applies existing affine fpqc effectivity, descends the
finite and etale properties, and explicitly builds the comparison isomorphism
and inverse in the descent-data category.

Added a narrowly scoped unused-variable linter setting for the original theorem's
existing unused `hq` binder. This keeps the signature and docstring unchanged.
Removed the earlier attempt's unfinished equivalence module. Updated the item's
node proof, proof dependencies and proof origin to match the actual proof.

## Proved and sorry left

The original module had one sorry. Proved:
`AlgebraicGeometry.finiteEtaleDescent` (`lem-galois-descent`).

Also proved all three new intermediate theorems:
`AlgebraicGeometry.finiteEtaleDescent_data`
(`lem-galois-descent-data-existence`),
`AlgebraicGeometry.finiteEtaleDescent_fullyFaithful`
(`lem-galois-descent-fully-faithful`), and
`AlgebraicGeometry.finiteEtaleDescent_essSurj`
(`lem-galois-descent-essentially-surjective`).

No sorry remains in any delivered module, including private helpers and
definitions. Zero unresolved statements are split off. The final theorem still
rests transitively on existing statements
`CategoryTheory.Over.DescentDatum.isEffective_of_isAffineHom_fpqc`
(`lem-galois-fpqc-affine-descent-effective`) and
`AlgebraicGeometry.etale_of_fpqc_cover`
(`lem-galois-fpqc-descend-etale`). Their modules are imported where used;
their proofs are subsequent items. `AlgebraicGeometry.isFinite_of_fpqc_cover`
is already proved in the library.

All four modules compiled together using the prescribed launcher, in import
order. Pullback, functor, full-faithfulness and isomorphism assembly proofs were
checked incrementally. Before writing new statements, checked the unrestricted
g case for canonical functor construction, identity/empty-base cases, and the
absence of any quasi-compactness assumption on the etale surjection. Lean checks
the proofs uniformly for all schemes and every declared universe.

## No longer needed

Pruned proof dependencies:

- `lem-galois-fpqc-morphisms-descend`: the proof uses effective epimorphisms
  directly instead of the tensor-overlap-style bijection. The direct import of
  `Sheaf.AlgebraicGeometry.FpqcMorphismsDescend` is removed. This module is still
  reached through the existing public definition module, so this delivery does
  not claim it is globally unreachable.
- `lem-weil-pbc-fpqc-finer-than-etale`: Mathlib's singleton fppf covering theorem
  and `fppfPrecoverage_le_fpqcPrecoverage` suffice. The import of
  `Sheaf.AlgebraicGeometry.FpqcFinerThanEtale` is removed. Its small-etale-site
  machinery, `def-weil-pbc-etale-site`, is not used in this proof.

Also no longer needed: `def-weil-pbc-etale-site`, whose small-site construction
is bypassed by Mathlib's fppf singleton covering lemma, and
`pqf-def-affine-morphism` as a separate proof dependency: the finite-morphism
instance already supplies affineness, recorded under
`def-weil-finite-integral-morphism` in the essential-surjectivity node.
The other original dependency nodes are retained in the new intermediate
nodes' proof dependencies, even when no longer direct dependencies of the item.

Other imports removed from the item's direct imports:
`Sheaf.AlgebraicGeometry.AffineFpqcDescent`,
`Sheaf.AlgebraicGeometry.FpqcDescentEtale`, and
`Sheaf.AlgebraicGeometry.IsFiniteOfFpqcCover` now belong to the essential
surjectivity proof module, where all three are used. These nodes are retained,
not pruned. The redundant direct import of
`WeilConjectures.CategoryTheory.Comma.Over.DescentDatum` is removed;
its definitions remain visible through `FiniteEtaleDescentData` and are used.
All original public imports are kept. The finite-etale, fibre-product, finite,
etale, affine and descent-datum definitions remain necessary.

The earlier sandbox-only `FiniteEtaleDescentEquivalence` module is not delivered;
its unproved conclusion is replaced by the explicit assembly in the original
module. There are no additional plan dependencies that the new proof needs.
No claim is made about whether modules elsewhere in the target closure become
unreachable: the maintainer computes that globally.

## Where the brief, the DAG or earlier work was wrong

The previous attempt had two bare sorry theorems, no node files, no proof
explanations and no report. It was not a ready delivery. Both remaining gaps
are now closed; full faithfulness and essential surjectivity are explicit
and independently proved, rather than an unfinished equivalence theorem.
The original DAG plan is mathematically usable once an fpqc covering is
understood as a covering family, not as a requirement that g itself be
quasi-compact. Mathlib supplies the singleton-cover argument directly.

LeanSearch returned HTTP Internal Server Error for all three attempted
natural-language queries. Recorded that unavailability without a verdict;
LeanFinder, Loogle, and local Mathlib/library/DAG searches were available.
No target statement, existing definition, or existing intermediate signature
is changed. No change record is needed.

## New nodes

`lem-galois-descent-data-existence` records the canonical base-change functor
and all projection equations, proved for every morphism g without covering
hypotheses. Its module also defines the exact conjunction of these equations,
`finiteEtaleDescentCompatible`, with no postponed data or proof.

`lem-galois-descent-fully-faithful` records full faithfulness for any functor
satisfying those canonical equations along an etale surjection. Its proof
constructs descended morphisms using effective epimorphisms and proves the
required hom-set bijections. It does not depend on a new sorry or on the
existing fpqc singleton full-faithfulness theorem.

`lem-galois-descent-essentially-surjective` records essential surjectivity
for such a functor. It applies the existing effective-affine-descent and
property-descent statements, then constructs the descent-data isomorphism.
Every new node has a complete proof in words, a proof dependency list, an exact
Lean signature, source attribution and search records. No change records.

## Second reading by V1

1. Compared the original module with the repository using `diff -u`, and
   separately checked the existing theorem signature byte for byte: unchanged.
   Only its proof, proof-only imports, and a local unused-binder linter setting
   changed. No existing definition or public import changed. The other three
   modules and nodes are new; no change record is required. Verdict: pass.
2. Compiled all four files in import order with `lcompile.py`: no errors or
   warnings. Scanned every delivered file: no sorry, axiom, unsafe, opaque,
   extern, implemented_by, or kernel-check bypass; no hollow definition.
   Scratch copies with `#print axioms` show exactly propext, Classical.choice,
   Quot.sound for the canonical-functor and full-faithfulness theorems.
   Essential surjectivity and the item additionally show sorryAx, from the
   existing affine fpqc effectivity and etale property descent statements.
   These remain explicitly open dependencies, so this is one local theorem
   body closed, not an axiom-free completed target. Verdict: pass.
3. There are zero unresolved split-off statements. Read every new intermediate
   statement and proof: construction works for arbitrary g; the other two
   assume precisely an etale surjection and canonical projection equations.
   Identity covers, empty bases, and non-quasi-compact etale surjections introduce
   no extra assumptions. In fullness, transport identifies two lifts with equal
   first projection; EffectiveEpi.desc and fac descend the compatible map, and
   cancellation checks the map is over Y. In essential surjectivity the two
   pullback squares give inverse comparison maps; compatible_hom checks both
   projections and proves transport compatibility in both directions.
   Docstrings give these arguments, sources, and blueprint ids; the new nodes
   name the same signatures. Searched again using LeanFinder for invariant
   projections and transport, Loogle for EffectiveEpi.desc, and rg in Mathlib,
   Sheaf, and upstream EffectiveDescent. Found the exact effective-epi APIs
   already used; abstract pseudofunctor descent does not replace this concrete
   construction, and upstream existsUnique_hom_of_isPullback requires
   QuasiCompact g. No shorter applicable equivalence theorem found. Verdict: pass.
4. The item assembles construction, Full/Faithful, and EssSurj directly.
   The proof preserves Stacks' canonical datum, affine effectivity and property
   descent route; it removes the unnecessary singleton morphism-descent theorem
   by using Mathlib's effective epi instance for flat surjections locally of
   finite presentation. Inspected sk-prop-h2.json: this node realizes no unit
   statement or step, so no fixed unit route is bypassed. Public imports expose
   only signature/definition requirements; proof imports are plain imports.
   Completed the pruning account for def-weil-pbc-etale-site and the redundant
   separate pqf-def-affine-morphism dependency. Other original dependencies
   migrate to the three intermediate nodes. Verdict: pass.
5. Compared node proof steps, uses unions, proof_deps and proof_origin with the
   actual Lean constructions. The item's three dependencies match its three
   applications. New-node records have source, creation, blueprint ancestry,
   chapter/unit, searches and exact Lean statements. Added def-pc-scheme to
   the construction node's stmt_deps because its statement explicitly cites it.
   No existing node statement or statement dependency changed. Verdict: pass.

Second reading changed only the report's pruning account, this review section,
and the new construction node's missing scheme statement-dependency entry.
No Lean proof repair was needed. Removed the scratch axiom-probe source copies.
