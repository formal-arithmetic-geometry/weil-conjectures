## What changed

Replaced the first worker's unlanded `ContinuousConstructibleIntegralSingleCore`
with two separate ordinary-module obligations, each in its own module:
`Sheaf.Paper.ContinuousConstructibleIntegralStratum` constructs a model for a
locally finitely presented restriction to one immersed stratum;
`Sheaf.Paper.ContinuousConstructibleIntegralGluing` assembles supplied models on
a finite stratification. Neither is a renamed copy of the item's derived statement.

The original theorem now unpacks the constructibility stratification, applies the
stratum theorem to every locally finitely presented restriction, and feeds these
models to the gluing theorem. It retains the first worker's correct proof that
placing a constructible integral module in degree zero is bounded constructible.
Finally it uses the already proved `integralScalarExtension_exact` and upstream
`Functor.singleFunctorCompLeftDerivedFunctorIso` to prove the comparison between
ordinary and derived extension of scalars. The parent imports the three proof
modules privately; its original public import and signature are unchanged.

Added the two new nodes and updated the parent's proof, proof dependencies and
proof origin to match the actual reduction. No definition or existing statement
changed, so no interface change record is required.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.continuousConstructible_integral_single_model`.
Its proof includes the finite-stratum reduction, bounded constructible degree-zero
packaging and ordinary-to-derived comparison.

Added two named holes:

- `AlgebraicGeometry.ProEtale.CondensedRing.continuousConstructible_integral_stratum`,
  node `lem-weil-pbc-continuous-constructible-integral-stratum`.
- `AlgebraicGeometry.ProEtale.CondensedRing.continuousConstructible_integral_gluing`,
  node `lem-weil-pbc-continuous-constructible-integral-gluing`.

Each has a complete proof in words and a source in its docstring and node. There
are no other holes in delivered modules. The unlanded
`continuousConstructible_integral_single_core` and its node were withdrawn from
the sandbox, rather than delivered as another restatement of the whole item.

This is a decomposition: one original hole closed, two smaller holes added; the
delivery's direct hole balance is -1, not a net proof gain. It does not claim a
sorry-free proof of the item or a measured improvement of the targets' closure.
The stratum construction and finite-filtration assembly each require substantial
geometric arguments; neither could be closed by an available theorem in a few
minutes. The existing scalar-localization exactness theorem is fully proved.

## No longer needed

Removed the parent's proof imports
`Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality` and
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`.

Every old proof dependency absent from the parent's new direct dependency list is:

- `lem-weil-pbc-condensed-lfp-local-triviality`;
- `lem-weil-pbc-lisse-e-constructible-integral-lattice`;
- `lem-weil-pbc-integral-constructible-bounded-below-compactness`;
- `lem-weil-pbc-proetale-ringed-open-closed`.

The old coefficient-definition dependency is retained. The new direct dependencies
are the stratum and gluing nodes and the proved scalar-exactness node. Local
triviality and open--closed localization remain mathematical ingredients of the
unfinished subproofs, and the existing integral-image closure theorem retains
its own localization argument. Thus these are removals from this proof's direct
imports/dependencies; no whole-project module pruning or ledger gain is claimed.

The broader topologically-noetherian stratum obligation cannot be replaced by
`exists_constructible_integral_lattice`: its recorded interface uses ordinary
`SheafOfModules`, canonical `WithAbs` coefficients, and the stronger assumptions
`IsNoetherian`, finite scheme dimension, and invertibility of ell. The old compactness
node likewise has stronger scheme hypotheses and no Lean declaration. The new gluing
node's plan instead uses the existing image-closure theorem with the correct
hypotheses, followed by exactness and degree-zero homology.

## Where the brief, the DAG or earlier work was wrong

The first worker's core assumed exactly the original constructibility input and
returned essentially the whole integral lattice and derived scalar-extension
claim. Its docstring did not contain the promised full proof, and the parent DAG
node was not updated. The revised reduction separates a genuinely locally finitely
presented case from reconstruction using already supplied stratum models; ordinary
to derived passage is proved using an existing exactness theorem.

The old lattice and compactness nodes are not directly applicable under this
item's hypotheses. No extra hypothesis was added to make them applicable. The
stratum node spells out the source's topologically-noetherian argument using
etale-local lattices, finite-etale stratification and lattice descent; the gluing
node uses triangulated closure and exact scalar localization.

Searches were rerun with different wording through LeanFinder, Loogle and grep,
including searches of the upstream checkout and existing project statements.
LeanSearch returned HTTP 500 and is recorded as unavailable, not as no match.
Loogle found the existing exact-functor/single-degree comparison, which the proof
now uses. The existing ordinary lattice interfaces do not supply the two new
internal-module statements directly.

## New nodes

`lem-weil-pbc-continuous-constructible-integral-stratum` records ordinary integral
models for locally finitely presented modules on an immersed stratum, including
the coefficient-interface transport. Its finite refinement is assembled using
the independent gluing node; there is no dependency in the opposite direction.

`lem-weil-pbc-continuous-constructible-integral-gluing` records reconstruction from
supplied ordinary models on a finite stratification. Its plan first uses the
existing triangulated essential-image theorem to get a bounded integral complex,
then takes degree-zero homology using exact localization.

Both new nodes inherit chapter `sec-proper-base-change` and unit
`sk-thm-properbasechange`. The unit's `realized` statement and three recorded steps
are untouched; this is a reduction strictly below that unit's route.

## Second reading by B4

1. Compared every delivered existing module against the shared version and checked
   the declaration tables. The original theorem signature is byte for byte identical;
   there are no removed declarations, altered definitions or changed public imports.
   All new proof imports are plain `import`; new statements have their own modules.
   Verdict: pass after replacing the unlanded broad core.
2. Compiled all three modules through `lcompile.py` in import order, with no errors
   or ordinary warnings. Inspected for forbidden constructs and for data chosen in
   definitions: none were added. The only literal `sorry`s are the two listed public
   named theorems. A scratch copy prints axioms of the item, the four private helpers,
   and the two new obligations. The item and the two obligations report exactly
   `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`; all four private helpers
   report only the three permitted axioms. Verdict: pass with the two reported holes.
3. Checked the two new statements against Bhatt--Scholze, Lemmas 6.8.12--6.8.13 and
   Proposition 6.8.14(2), in the arXiv paper, and checked existing project interfaces.
   The stratum theorem handles only locally finitely presented restrictions; gluing
   assumes the models and permits rescaling, rather than claiming arbitrary chosen
   lattices glue unchanged. Zero modules, rank-zero presentations, empty immersions,
   empty strata, a one-stratum partition, and an empty partition were checked in the
   informal argument; an empty partition forces the scheme empty. Neither statement
   strengthens the conclusion to a globally lisse integral model. Searches found no
   direct usable existing declaration. Verdict: genuine smaller obligations with
   source-backed proof docstrings, not a proof of their remaining geometric steps.
4. Read the proof from the item's hole downward. The finite-stratum reduction uses
   its actual constructibility hypothesis, and the derived comparison now takes the
   existing exact-functor route. Removed an unnecessary explicit import of the
   left-derived comparison module because the public coefficient interface already
   exposes that API. Retained the correct degree-zero packaging and its helpers.
   Checked `dag/units/sk-thm-properbasechange.json` and the exhaustive old-dependency
   list above. Verdict: pass; no global pruning or unit-route change is claimed.
5. Matched each new node's verbatim Lean signature, proof plan, source, three search
   kinds, provenance, chapter and unit to its module; updated the parent's proof and
   dependencies to the actual calls. The stratum node can depend on gluing, which
   uses the independent image-closure theorem and never depends on the stratum node
   or the item. Verdict: pass; the first worker's missing parent-node update is fixed.

Second reading changed: withdrew the broad core; introduced the separate stratum
and gluing obligations with complete source proofs and nodes; proved the
ordinary-to-derived comparison from existing exactness; corrected the parent DAG
and import list; replaced the inaccurate report with explicit decomposition counts.
