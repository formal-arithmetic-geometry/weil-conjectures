## What changed

Proved `DerivedCategory.affine_perfect_cut_degree_zero` with its original signature.
The cycle comparison is epic by the three lemma applied to boundaries, cycles and
cohomology. The four lemma then makes the residue extension of the image inclusion
`im(d0) -> K1` monic. Localize its cokernel to obtain projective degree-one opcycles.
The positive truncation itself is the bounded finite projective representative;
Mathlib's flat-model Tor-amplitude theorem supplies the tensor bound. The declared
`CategoryTheory.derivedSplittingUnique` supplies the splitting of the standard
truncation triangle.

Strengthened `Module.finiteProjectiveCokernel_residue_localization` by removing its
unused `[Module.Projective R P₁]` binder. Its existing proof is unchanged and already
works for a finite source and finite projective target. This is needed for the finite
image of the differential. All conclusions remain unchanged. The dependency module
was unclaimed. No definitions, target statements, or consumer signatures change.
The unclaimed direct consumer `CochainComplex.residue_bottom_differential` receives
one local instance binding from its existing `hp₀` hypothesis: the strengthened input
no longer uses it implicitly, so this prevents the new unused-variable warning while
preserving the consumer's complete signature. The original consumer's diagnostic was
`Variable name hp₀ is not explicitly referenced`; the only changed proof line is
`have : Module.Projective R (P.X a) := hp₀` at line 65. Both adapted modules were
unclaimed; no module held by another group is changed.
Change record: `coord/changes/E7-finite-source-cokernel-localization.md`.
Both corresponding DAG nodes now describe the argument and the strengthened input.

Added only proof imports of Mathlib's four lemma and the existing native-tensor to
extension-of-scalars equivalence. All public imports retain their original visibility.

## Proved and sorry left

Closed: `DerivedCategory.affine_perfect_cut_degree_zero`
(`lem-pc-affine-perfect-cut-degree-zero`), one of the item's one original holes.
Added: zero holes. Left in delivered Lean modules: zero holes.
`lcompile.py --all` compiled the dependency and item, and the final consumer compiled
separately without warnings. The dependency axiom probe shows exactly `propext`,
`Classical.choice`, and `Quot.sound`; the item additionally inherits `sorryAx` from
its existing splitting dependency.
The strengthened `Module.finiteProjectiveCokernel_residue_localization` remains proved.
The proof deliberately uses the existing stated dependency
`CategoryTheory.derivedSplittingUnique` (`lem-pc-derived-splitting-unique`), whose
pre-existing sorry is outside this delivery. This is a proof from the declared inputs,
not an axiom-free completion of their transitive dependencies.

## No longer needed

No original imports or proof-dependency modules are removed: both declared inputs are
used. The original explicit residue-field basis choices and two successive shrinkings
are replaced by the cycle/image diagrams and a single application of the strengthened
localization lemma. No new nodes or split-offs are required.

Removed the obsolete top-level `tool_uses` entry
`lem-weil-pbc-finite-projective-prime-local-free` from the localization node. The existing
proof already works directly through Mathlib local splitting and denominator clearing,
without this node; no library module is withdrawn by this metadata cleanup.

## Where the brief, the DAG or earlier work was wrong

LeanFinder found no matching affine-cut theorem; Loogle found the truncation API,
and grep/rg found the existing localization input and tensor equivalence. No duplicate
of the requested result was found.

No false statement was found. The localization theorem imposed projectivity on its
source even though its proof needs only finiteness. Removing that unused assumption
allows the shorter diagram argument. The former basis-based plan is valid but is
unnecessary for this implementation. The unit statement and its realized steps are
unchanged. Edge cases include zero image, zero positive truncation and original upper
bound below one: no basis/rank nonemptiness is assumed, and `max c 1` handles the bound.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
