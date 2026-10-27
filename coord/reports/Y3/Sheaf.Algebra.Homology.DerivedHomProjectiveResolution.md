## What changed

Completed `CategoryTheory.derivedHom_projectiveResolution` with its original signature.
The proof establishes both localized Hom maps for every K-injective replacement,
constructs the derived-object isomorphism using the canonical replacement, and applies
derived homology to obtain all integer-degree cohomology isomorphisms.

Private proved helpers show that restriction to a slice of the one-point site
preserves projectives, and prove that Hom from a bounded-above projective complex
preserves quasi-isomorphisms. The latter uses the existing sectionwise homotopy
comparison and Mathlib's K-projective localization bijection. The source library
is only imported; no source-library file is changed. The node records this proof route.

## Proved and sorry left

Closed: `CategoryTheory.derivedHom_projectiveResolution`
(node `lem-sc-derived-hom-projective-resolution`), one of one original holes.
Added: zero holes. Split off: zero. No sorry remains in the delivered module.
All private helpers are proved. The full proof compiled through `lcompile.py` in 42.3 seconds;
the diagnostic traces were then removed for delivery.

## No longer needed

Removed the proof import `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
the original small-site `derivedInternalHom_comparison` suffices on the one-point site.
No original DAG dependency is pruned: both the K-projectivity leaf and the derived
internal-Hom definition are used. No module is withdrawn or claimed globally unused.
The auxiliary degree-term calculation in the old plan is unnecessary: the existing
natural comparison with shifted homotopy-category maps proves the required quasi-isomorphism directly.

## Where the brief, the DAG or earlier work was wrong

The original plan omitted the formal bridge from Mathlib's null-homotopy definition
of K-projectivity to the sheaf-valued Hom complex. The delivery proves that bridge
on the one-point site, using restriction equivalences, the existing sectionwise
homotopy comparison, and detection of quasi-isomorphisms through sections. It does not assume the analogous
implication for arbitrary ringed sites. The unit route is unchanged.

The Stacks references were checked online at Tags 0A5W (Lemma 15.75.2) and 06XR;
the local Stacks source files are absent on this machine. The expanded DAG proof
records the existing section-comparison, restriction and invariance lemmas used
to formalize the original balancing argument. No new nodes or statements are added.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
