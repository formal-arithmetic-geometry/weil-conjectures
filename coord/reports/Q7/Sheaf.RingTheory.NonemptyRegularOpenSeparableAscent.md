## What changed

Proved `Algebra.exists_nonempty_open_regular_of_separable_fractionRing` in
`Sheaf.RingTheory.NonemptyRegularOpenSeparableAscent`, with its existing signature and
public imports unchanged. Updated its docstring and DAG proof to the implemented route.
Added proof imports of Mathlib's localization-of-localization and localization-ideal APIs.

The proof chooses a regular principal open D(f) of R, applies the already stated generic
smoothness theorem directly to R → S, then inverts the image of f in the smooth algebra
S_g. Formal smoothness descends through the localization of the base, and finite type over
the Noetherian ring R_f gives finite presentation. The existing smooth regularity ascent
therefore gives a regular ring T. It is a localization of S at image(f)*g; prime extension,
contraction, and uniqueness of localization transport its regular local rings to the
nonempty basic open D(image(f)*g).

Validation: the resumed, current-source module compiled cleanly through lcompile.py
(4.0 seconds, exit code 0). The required delivery dry run is checked separately. Search used
leanfinder, loogle, grep, and the existing source library; no direct theorem matching the
whole statement was found. No arbitrary data are chosen from an unproved theorem inside
a definition: all choices are existential eliminations within this theorem's proof.

## Proved and sorry left

Closed 1 of 1 original holes:
`Algebra.exists_nonempty_open_regular_of_separable_fractionRing`
(node `lem-exc-j0-separable-finite-type-ascent`).

Added zero holes. The delivered module has zero `sorry` declarations. No new modules or
intermediate statements were introduced. The proof intentionally uses the existing
`Algebra.exists_smooth_localization_of_separable_fractionRing` declaration from
`Sheaf.RingTheory.GenericSmoothDomain`; that dependency's existing hole is unchanged.
`Algebra.isRegularRing_of_smooth` is the other substantive existing proof input.

## No longer needed

Removed proof imports `Mathlib.AlgebraicGeometry.OpenImmersion` and
`Sheaf.AlgebraicGeometry.IsRegularScheme`. The proof uses basic-open topology and
localization APIs directly and only needs the ring clauses of `def-weil-regular-scheme`.
Removed the proof dependency `lem-weil-pbc-principal-localization-open-immersion`:
the proof directly uses the basic open and the prime extension/contraction API, without
constructing a scheme open immersion. Localization and regularity dependencies remain.
No whole module is claimed globally unreachable by this delivery.

The original plan's localized injection A → B, finite generating set for B over A, transport
of canonical fraction fields and separability, and clearing the numerator of a chosen h in B
are unnecessary. Applying generic smoothness before localizing the base avoids those steps.
The final element is simply image(f)*g, and Mathlib's iterated-localization API supplies T.

The updated node also names the already existing Mathlib leaves for iterated localization,
principal localization of smooth algebras, finite type over a Noetherian ring being finite
presentation, and the smooth-ring-map definition. It preserves the existing approved use
of smooth regularity ascent. The unit's realized statement and steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The resumed sandbox still imported `Sheaf.FieldTheory.SeparableExtension`; restored
the current source import `WeilConjectures.FieldTheory.SeparableExtension`, whose
declaration is the same one used by the current generic-smoothness dependency.

No statement error was found. The six-step plan is valid, but its order creates unnecessary
separability transport. Reordering the two localizations gives a shorter Lean proof using
the same generic smoothness and regularity-ascent inputs. Initial elaboration needed the
contracted ideal written explicitly for instance synthesis; this does not change any
mathematical statement or interface.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
