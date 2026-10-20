## What changed

Restored Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite from
the quarantine archive named in coord/rework.tsv. Repaired the unknown flatness
identifier by replacing its withdrawn proof import with
WeilConjectures.RingTheory.ProEtale.FaithfullyFlat and proving flatness directly
from the existing small filtered ring-colimit presentation.

The natural stage maps are the neighbourhood structure maps on global sections,
precomposed with GammaSpecIso.inv. Etaleness makes them flat. The defining
common-composite equation for strictHenselizationStructuralMap, checked with
Spec.map_injective, identifies each composite with b. RingHom.Flat.of_isColimit
therefore supplies the Module.Flat instance used to preserve regularity of f.
The quotient equivalence, local root-algebra regularity argument and affine
integral-closure finiteness proof remain verbatim from the archive.

Updated the item's DAG proof, proof_deps and proof_origin to name the existing
etale-flatness and ind-flat tools used in this explicit subproof. These are a
Mathlib leaf and an already closed source-library node; no new mathematical
obligation or unit-route change is introduced. The statement, its Lean attachment,
all public imports, and all definitions retain their original signatures and bodies.

Validation: lcompile.py compiled the restored module without errors or warnings
in 7.8 seconds. A separate scratch import and #print axioms check compiled in
1.2 seconds and reported exactly propext, Classical.choice and Quot.sound for the
public theorem. A textual signature comparison with the quarantine archive passed.
All lines have at most 100 characters. The active consumer scan returned zero;
the archived StrictHenselRootTameNormalization application was checked separately
and retains the identical argument list. There are no forced adaptations.

Change record: coord/changes/F1-strict-hensel-root-normalization-finite-rework.md.

## Proved and sorry left

This is a zero-hole repair: the archive had zero sorry occurrences and the repaired
module has zero. Closed: none (0). Added: none (0). Split off: none (0).

AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_normalization_finite
again has a compiling complete proof, with the newly written flatness subproof.
The private root_quotient_equiv construction and finite_normalization_of_normal_open
proof are retained completely. No sorry is left in any delivered Lean file.
The printed axiom list of the public theorem contains no sorryAx; it has a
complete proof through its imported dependencies as well.

## No longer needed

Removed the proof import
Sheaf.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat, whose module
is now an empty withdrawn stub. Removed the direct proof-dependency edge to
lem-sbc-affine-strict-henselization-structural-flat: the flatness argument is now
proved in place from its already available foundational tools. The upstream
flatness module is not imported because it conflicts with a declaration exported
by the old structural-map API needed by the unchanged statement dependencies.

No module is withdrawn by this delivery. The flatness node and its upstream source
module remain needed by other consumers and are not claimed as globally pruned.
All other declared proof dependencies and the spreading unit's root-normalization
route remain needed. No additional imports were added and then retained unused.

## Where the brief, the DAG or earlier work was wrong

The item is an assigned quarantine repair with zero holes, rather than an unfinished
normalization theorem. The rework row's unknown identifier is reproduced by the
archive. Substituting the replacement upstream module alone is insufficient:
its public dependency StrictHenselizationStructuralMapExtension collides on
AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_eq with the Sheaf
structural-map module used by the existing statement and quotient theorem.
The upstream flatness signature also uses strictHenselization and
strictLocalizationToBase instead of the small-model ring and structural morphism.

The direct filtered-colimit flatness proof repairs both API issues without
changing the module's statement, adapting unrelated modules or introducing a new
public compatibility declaration. No source error or disputed statement was found.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
