## What changed

Added a proved categorical-Ext formulation of the supported integral Brown criterion,
`CategoryTheory.brownHypothesesFor_padicIntegers_iff_categorical_ext_bounded`, and its
proved obstruction corollary,
`CategoryTheory.not_brownHypothesesFor_padicIntegers_of_unbounded_categorical_ext`.
The added public import of Mathlib Ext.Basic supplies the public Ext signatures.
The criterion uses the canonical Ext/shifted-Hom equivalence and explicitly handles
the conversion between strict integer and inclusive natural bounds. The conversion
is proved once by a private lemma in a general abelian category, avoiding repeated
module-category instance inference. The existing local irreducibility setting for
the Brown bundle now also covers these API proofs.

Simplified `CategoryTheory.brownHypotheses_of_finiteFieldDatum` to assemble the
Noetherian Brown criterion from structural coproducts and the already proved
finite-field objectwise compactness theorem. This retains all hypotheses and avoids
re-elaborating its skeleton construction in the large item module. Its private
compactness import changes accordingly. Profiling exposed substantial instance
inference and a slow `refine`; profiling options are removed from delivered code.

No existing declaration signature or definition changes. The unresolved original
theorem is restored to the required whole named obligation `:= by sorry`, removing
the incomplete geometric setup in its body. Its statement and disputed warning stay
unchanged. The new theorems
use the already proved conditional integral criterion, never the disputed theorem.

Validation: the final item and both unchanged direct importers,
`Sheaf.Paper.LocalizingExceptionalAdjoint` and
`Sheaf.Paper.ExceptionalInverseImageExistence`, compiled successfully in import order
through lcompile.py. The temporary importer copies matched the current source and
were deleted after validation. No consumer adaptation is delivered.

## Proved and sorry left

Closed 0 of the original 1 holes. Added 0 holes; split off 0 obligations.
The two categorical-Ext declarations above are proved completely.
The sole remaining sorry is `CategoryTheory.brownHypotheses`, node
`sk-lem-brown-hypotheses`. This delivery is an extension of the supported conditional
criterion, not a proof or decomposition of that false unrestricted assertion.

The explicit HasExt binder fixes the size of the Ext model and is supplied by
`CategoryTheory.hasExt_of_hasDerivedCategory`; it does not assume any Ext vanishing.
Edge cases checked: empty schemes, zero source or target, negative integer bounds,
and the distinction between one nonzero Ext group and arbitrarily large nonzero groups.

## No longer needed

The direct private import of `BrownHypothesesFiniteFieldCompactness` is replaced by
`BrownHypothesesArbitraryFieldCompactness`, whose two remaining public results are
proved supported specializations. The finite-field assembly no longer directly uses
`a4-brown-finite-field-internal-compactness`, `det-brown-hypotheses-small`, or
`lem-sfb-brown-representative-compactness-criterion`: the objectwise specialization
and Noetherian criterion package these steps. These inputs remain transitively used;
no module is claimed globally pruned. The new Ext node uses only the existing
integral Brown criterion and the Mathlib Ext comparison (`def-pc-ext`).
The false unrestricted compactness splits retired by the maintenance rollback
remain unused; neither their Lean attachments nor their proof edges are restored.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the only remaining theorem asserts Brown compactness over an
arbitrary positive-characteristic field, although its finite-field input assumes
the geometric field of a finite-field datum and its integral input assumes an
explicit uniform Ext bound. The item DAG and the maintenance change record
`coord/changes/maintenance-K4-brown-false-split-rollback.md` already record this
mathematical problem and forbid recreating false splits. The new categorical-Ext
criterion exposes exactly the integral obstruction using the library's actual Ext
groups. It does not claim a formal cohomology counterexample for a particular field.
The original hole cannot honestly be closed by applying its stated dependencies.

## New nodes

`lem-sfb-brown-integral-categorical-ext-criterion` records the proved categorical-Ext
criterion and its unboundedness obstruction. It keeps the original unit route and
all geometric and coefficient hypotheses; no new unproved claim or changed existing
statement is introduced.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
