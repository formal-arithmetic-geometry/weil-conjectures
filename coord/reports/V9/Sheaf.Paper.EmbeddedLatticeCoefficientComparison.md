## What changed

Replaced the proof of `AlgebraicGeometry.ProEtale.EmbeddedLatticeComparison.embedded_lattice_coefficient_comparison` without changing its statement. The coefficient comparison square follows from the inverse-image adjunction. A compact-test bounded-denominator construction gives the coefficient colimit, transported through sheafification and inverse image. The image classifier is constructed as the sectionwise range of `pairEmbedding`; sheafness and local freeness follow from its explicit isomorphism with the pair module. The proof also establishes the stated image kernel, restriction formula, and every matrix label.

Added `Sheaf.Paper.LatticeScalarExtensionFractions` for scalar-extension telescope and local numerator formulas, and `Sheaf.Paper.FullEmbeddedLatticeRationalization` for the canonical rationalization of a full embedded lattice. The latter constructs scalar multiplication through the tensor and sheafification universal properties. No existing definition or statement changes, no source-library edits, and no forced adaptations. Import pruning and local slice-instance caching are recorded in `coord/changes/embedded-lattice-comparison-proof-interface.md`; the consumer scan found zero downstream modules.

## Proved and sorry left

The original module had one hole, in `AlgebraicGeometry.ProEtale.EmbeddedLatticeComparison.embedded_lattice_coefficient_comparison`. Its new proof has no internal holes. This is a decomposition through the named local scalar-extension result, not an unconditional proof of all localization theory.

One new named hole remains: `AlgebraicGeometry.ProEtale.lattice_scalar_extension_fractions` (node `lem-sfb-lattice-scalar-extension-fractions`). The canonical full-lattice rationalization is proved from that local-numerator assertion, and has no hole of its own. Thus the packet closes one original hole and adds one strictly narrower source result; it is a decomposition with net zero holes, rather than a claimed net closure. The new `AlgebraicGeometry.ProEtale.full_embedded_lattice_rationalization` compiles with no holes. All constructions of embedded lattice data are explicit sectionwise ranges. The only unfinished proof is exactly the public named theorem above. Validation: all three modules compiled through `lcompile.py`; the main theorem compiled in 24.0 seconds. Delivery preflight reruns the required checks on the exact packet.

## No longer needed

Removed `Sheaf.Paper.PadicIntegersInvertEll`, corresponding to `det-prop-sfb-qlbar-colimit-x-invert-ell`, from this proof. Its finite-subfield statement does not specialize to an arbitrary coefficient carrier `E : Type u`. The coefficient telescope here instead uses compactness and the norm-unit-ball description of the integral ring directly. The upstream module and declarations remain intact.

Removed redundant direct imports `Sheaf.CategoryTheory.SheafTensor` and `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` from the item; the required category structures are already present through statement imports. No withdrawal of a module is claimed. The unit's coefficient-comparison and lattice-image route is preserved. Removed obsolete top-level tool approvals for `det-prop-sfb-qlbar-colimit-x-invert-ell` and `def-weil-pbc-internal-abelian-sheaf-module-equivalence`: the latter encoding is already fixed in the statement's `continuousModule`, and no new transport theorem is required by this proof.

## Where the brief, the DAG or earlier work was wrong

The planned finite-subfield localization dependency has a more specialized carrier than this item's universally quantified `E`. Direct compact-test denominators repair that mismatch without changing a statement. The proof must use a covering sieve for local denominators; no global denominator on a non-quasi-compact object is asserted. The former informal steps about full embedded lattices require a canonical multiplication map, whose construction and unit equation are now explicit.

## New nodes

`lem-sfb-lattice-scalar-extension-fractions` states the slice module telescope with its forward and balanced inverse formulas, together with local numerator representatives. It is the module-localization part of Bhatt--Scholze Lemma 6.8.2(2) and the sheafified tensor construction of Stacks Tag 03EK. It does not include the coefficient comparison square, image classification, restriction classifier or matrix normalization of the original item. Edge checks: for ell-torsion modules both localization models vanish; a zero module gives the zero cocone; empty covering sieves are handled by sheaf separatedness; and the local exponent is allowed to vary for non-quasi-compact objects.

`lem-sfb-full-embedded-lattice-rationalization` isolates the scalar-multiplication isomorphism of a full embedded submodule. The comparison is explicitly constructed, and its injectivity and local surjectivity use local numerators and fullness. It does not classify pairs or construct the image of an arbitrary pair. The import and local-attribute change record is `coord/changes/embedded-lattice-comparison-proof-interface.md`.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
