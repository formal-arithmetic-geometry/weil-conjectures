## What changed

Retired the duplicate Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootLimitPresentation
under its current coord/retire-items.tsv assignment. Its node now names the already proved
WeilConjectures twin. Adapted the sole direct consumer, PuncturedRootSectionEtaleDescent,
while preserving its complete theorem signature.

The consumer now proves the canonical comparison between the two strict henselization
rings over Spec R, then applies punctured_root_base_change along that ring isomorphism
to transport the adopted root-limit presentation to the original punctured chart.
The finite-presentation descent argument and every hypothesis remain unchanged.
The consumer and root-limit DAG proofs describe the actual route.

Change record: coord/changes/K2-retire-punctured-root-limit-presentation.change.md.

## Proved and sorry left

Retirement repair: 0 of 0 initial holes closed; 0 holes added; 0 holes left; 0 split off.
AlgebraicGeometry.Scheme.punctured_root_section_etale_descent remains fully proved.
Its private strictHenselization_colimit_comparison is fully proved, moved from the
retired module. The punctured-chart comparison and its structural equation are proved
inside the consumer. The adopted punctured_root_limit_presentation and
punctured_root_base_change are already proved and reused, not counted as new proofs.

Validation: the adapted consumer compiles cleanly in 4.4 seconds with lcompile.py.
Axiom probes for its private comparison, section-descent theorem, and both reused source
theorems show exactly propext, Classical.choice and Quot.sound. Its full theorem signature
matches the original text verbatim. Import-direction checks permit both new proof imports;
searches of live and quarantined Lean sources find no other direct importer of the retired
module. The source theorem and root-base-change argument cover n=0 and empty punctures.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.Morphisms.PuncturedRootLimitPresentation.
The consumer removes that private import and uses the WeilConjectures twin instead.
It replaces public Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap with its
two actual upstream statement dependencies, avoiding the duplicate structural-map
leg-lemma name. No source-library declaration is removed.

The ring-colimit and root-continuity nodes remain used by the adopted limit theorem.
The root-limit node remains used by section descent; only its duplicate realization
is withdrawn. No unit statement or step is bypassed. No new nodes.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an open proof. The current live queue instead
assigns retirement, and F3's preceding delivery already made this module sorry-free.
The two theorem versions are not definitionally interchangeable: their rings and
structural maps differ. The proved colimit and chart comparisons handle this difference
without changing the retained consumer's statement or any source-library interface.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
