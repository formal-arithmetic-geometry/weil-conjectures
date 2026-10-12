## What changed

The unchanged equivalence `AlgebraicGeometry.smooth_on_open_iff_artinian_lifting`
is assembled with `constructor` from the two strictly smaller one-way implications.
The forward and reverse statements are in their own new modules with proof-only
imports in the parent. The parent DAG node records those two dependencies.
The child nodes carry the original plan's actual subarguments, without dependence
on the parent theorem. Their statements are self-contained and their docstrings
contain the complete natural-language subarguments.

## Proved and sorry left

Hole closed (1): `AlgebraicGeometry.smooth_on_open_iff_artinian_lifting`.
Holes added (2):

- `AlgebraicGeometry.smooth_on_open_artinian_lifting_forward`:
  `lem-weil-pbc-smooth-at-prime-artinian-lifting-forward`.
- `AlgebraicGeometry.artinian_lifting_smooth_on_open_reverse`:
  `lem-weil-pbc-smooth-at-prime-artinian-lifting-reverse`.

This is a decomposition, not a completed proof of the criterion. The local net
is minus one hole; the parent still depends on `sorryAx`. No lower hole was closed
in this second reading. No definitions were introduced or altered.

## No longer needed

Removed from the parent module and relocated to the reverse implication module,
whose open proof plan uses them:

- `Sheaf.Paper.ArtinianIdealLengthOneFiltration`
- `Sheaf.RingTheory.JacobiZariskiQuotientSmooth`
- `Sheaf.RingTheory.KaehlerDifferentialsModPowerIdeal`
- `Sheaf.RingTheory.SplitInjectionAfterCompletion`

No module is globally pruned: these four remain in the target import closure.
Every old direct proof dependency listed below is replaced at the parent by the
two implications; it is retained in the corresponding child proof plan rather
than discarded from the mathematical route:

- `def-weil-affine-spectrum`
- `lem-weil-pbc-principal-localization-open-immersion`
- `def-weil-open-immersion`
- `lem-weil-pbc-smooth-restrict-open-subschemes`
- `lem-weil-pbc-morphism-factors-through-open-subscheme`
- `def-sbc-smooth-morphisms`
- `lem-weil-pbc-smooth-ring-map-iff-smooth-affine`
- `def-weil-pbc-smooth-ring-map`
- `lem-weil-pbc-smooth-ring-map-square-zero-lifting`
- `lem-weil-pbc-finite-type-noetherian-finite-presentation`
- `lem-weil-pbc-polynomial-ring-kahler-basis`
- `def-weil-pbc-kahler-differentials`
- `lem-weil-pbc-polynomial-ring-h1-cotangent-vanishing`
- `lem-weil-pbc-jacobi-zariski-quotient-smooth`
- `lem-weil-pbc-finite-flat-local-free`
- `lem-weil-pbc-smooth-at-prime-naive-cotangent-criterion`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `lem-weil-pbc-localization-noetherian`
- `lem-weil-pbc-kahler-differentials-localization`
- `lem-weil-pbc-noetherian-local-quotient-artinian-local`
- `lem-weil-pbc-artinian-ideal-length-one-filtration`
- `lem-weil-pbc-square-zero-section-conormal-retraction`
- `lem-weil-pbc-artin-rees`
- `lem-weil-pbc-kahler-differentials-mod-power-ideal`
- `lem-weil-pbc-split-injection-after-completion`

## Where the brief, the DAG or earlier work was wrong

The first worker's child nodes cited the parent criterion as a proof dependency.
That was circular once the parent is proved from the children. The parent node
also still recorded the old proof, and the children's statements and docstrings
were insufficiently self-contained. This reading repairs those faults. The
reported searches were replaced with searches actually run in this session.
LeanSearch returned HTTP 500 and is recorded as unavailable, not as no match.

## New nodes

`lem-weil-pbc-smooth-at-prime-artinian-lifting-forward` carries original steps
1--3: identify a smooth principal neighbourhood, prove the kernel square-zero,
and use formal smoothness to lift. `lem-weil-pbc-smooth-at-prime-artinian-lifting-reverse`
carries original steps 1--2 and 4--12: the Artinian quotient construction,
conormal splitting modulo powers, and the completion argument. Both have
unchanged Lean signatures and independent, noncircular proof plans. No change
record is required: no existing statement or definition changes.

## Second reading by B2

1. PASS. Compared the delivered parent with the repository by `diff`; its
   existing theorem signature and all public imports are byte-for-byte unchanged.
   Only proof-only imports and the proof body change. The child modules are new;
   their signatures also remain unchanged from the first worker's sandbox.
2. PASS with two declared holes. Compiled all three modules locally with
   `lcompile.py`. No errors or unexpected warnings, no forbidden declarations,
   no hollow definitions. Explicit `#print axioms` checks show only `propext`,
   `Classical.choice`, `Quot.sound`, and the expected `sorryAx`.
3. PASS after repair. The children are opposite implications, each strictly
   part of the equivalence; neither restates the whole item. Their complete
   proofs in words follow the original twelve-step plan and Stacks Tag 02HT
   (https://stacks.math.columbia.edu/tag/02HT), (1) iff (3), not merely (1) iff (2).
   A prime excludes the zero source algebra; local test rings are nonzero;
   length zero kernels are excluded by length one; identity maps and polynomial
   algebras satisfy the forward claim. The reverse proof uses Artinian tests
   constructed at q and can lift their universe with ULift. No stronger residue
   field condition was added. Searched the Sheaf and upstream Lean sources and
   used Loogle, Lean Finder and Mathlib grep: only related formal smoothness and
   stalk-neighbourhood tools were found, not either full implication. Neither
   implication has a short direct application of the available tools.
4. PASS after repair. The parent contains the equivalence assembly and only its
   required imports. The four deeper dependency imports move to the reverse
   child, where they support its still-open proof plan. All displaced direct
   dependencies are accounted for above. Checked `dag/units/sk-thm-p1.json`:
   the parent is not a realized unit statement or step, and the decomposition
   preserves all original subarguments without bypassing any unit route.
5. PASS after repair. Parent proof/proof_deps/proof_origin now describe the Lean
   constructor proof. The child records have complete fields, verbatim Lean
   signatures, self-contained statements, actual searches, and the original
   noncircular step dependencies. The parent appears in neither child's
   statement dependencies nor proof dependencies.

Changed in this reading: circular child DAG plans, missing parent DAG update,
self-contained node statements, complete docstring proofs and correct Stacks
clause references, actual search records, relocation of unused parent imports,
and accurate decomposition/net-hole reporting. No existing signature changed.
