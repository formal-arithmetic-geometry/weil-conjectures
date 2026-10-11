## Worker report

The module `Sheaf.RingTheory.FiniteProjectiveOfStandardCover` states
`Module.finite_projective_of_localizationAway_free`, with its only proof `by sorry`.
No definitions, dependency modules, or new nodes were needed. The item's JSON changes
only in `lean`.

Hypotheses and clauses:

- A commutative ring R: `{R : Type u} [CommRing R]`.
- An R-module N: `{N : Type v} [AddCommGroup N] [Module R N]`.
  The ring and module universes are independent and explicitly bound.
- Finitely many elements: `(t : Finset R)`. Replacing a finite list by its set of
  values neither changes its ideal nor its localization conditions; repetition and
  order carry no mathematical data in this statement.
- Generating the unit ideal: `(ht : Ideal.span (t : Set R) = ⊤)`.
- For each listed element f: `hlocal : ∀ f : t, ...`.
- The ring R_f: `Localization.Away (f : R)`.
- The module N_f: `LocalizedModule.Away (f : R) N`, using its canonical module
  structure over the localized ring.
- Each N_f is finite free: the conjunction of `Module.Finite` and `Module.Free`
  over that localized ring. No constant rank condition is imposed.
- N is finite projective: `Module.Finite R N ∧ Module.Projective R N`.

Dependency declarations read and used:

- `def-weil-pbc-module-localization-away` is a Mathlib leaf recorded by
  `LocalizedModule.Away` in `Mathlib.Algebra.Module.LocalizedModule.Basic`.
  Its complete abbreviation is `LocalizedModule (Submonoid.powers f) N`, exactly
  the prescribed localization. The additional canonical-map clauses of that
  definition are not needed to state this node.
- `def-weil-pbc-projective-module` is a Mathlib leaf recorded by
  `Module.Projective` in `Mathlib.Algebra.Module.Projective`. Its definition is
  splitting the canonical free-module surjection; its docstring identifies the
  direct-summand and lifting characterizations, as the node requires.
- Auxiliary existing Mathlib notions are `Module.Finite`
  (`Mathlib.RingTheory.Finiteness.Defs`), `Module.Free`
  (`Mathlib.LinearAlgebra.FreeModule.Basic`, imported through Projective),
  `Ideal.span`, and `Localization.Away` (`Mathlib.RingTheory.Localization.Away.Basic`).
  No replacement notions are introduced.

Source checked: https://stacks.math.columbia.edu/tag/00NX, Lemma 10.78.2.
The local algebra.tex copy is absent on this machine, so the published Stacks
statement and proof were opened. The stated conclusion is condition (2), finite
projective; the source-place metadata calls it (3), which is the equivalent
finite-free direct-summand form. This is only a numbering mismatch in metadata;
the statement itself requires no correction. The module identifies (7) ⇒ (2).
Its docstring carries the two DAG proof steps: descend finite presentation and
flatness along the standard cover, then use finitely presented flat ⇒ projective
and finite presentation ⇒ finite generation.

Edge cases checked before writing: an empty finite set generates the unit ideal
only over the zero ring, where every unital module is zero and the conclusion
holds; the zero module is permitted; f=0 gives zero localizations and creates no
spurious cover of a nonzero ring; the singleton {1} gives the finite-free case;
redundant elements and repeated elements cause no change. Over R=k×k, the cover
by the two complementary idempotents permits distinct local ranks (e.g. k×k²),
so a global freeness or constant-rank conclusion was deliberately not imposed.
No nontriviality, Noetherian, domain, or characteristic hypothesis is present.

Searches (2026-10-11):

- msearch.py leanfinder: "module finite free after localization at finitely many
  elements generating the unit ideal is finite projective". Eight hits: finite
  generation descent (`Module.Finite.of_localizationSpan_finite`), maximal-local
  projectivity under an existing finite-presentation hypothesis, and related
  localization results; none states the full implication here.
- msearch.py loogle: "Module.Projective, LocalizedModule". Two hits:
  `instProjectiveLocalizationLocalizedModule` and
  `Module.projective_of_localization_maximal`; neither is the standard-cover
  finite-projectivity implication.
- msearch.py grep in RingTheory:
  `projective_of_localization|freeLocus_eq_univ|of_localizationSpan`.
  Twenty-four hits, including separate finite-generation and finite-presentation
  descent, maximal-local projectivity, and free-locus results; no exact match.
- rg in WeilConjectures and lean/Sheaf:
  `lem-sc-affine-standard-cover-finite-projective|finite.*projective|projective.*localizationSpan`.
  No occurrence of the node id; other hits include the affine locally free
  sheaf section theorem and unrelated finite projectivity statements, none with
  this arbitrary-module standard-cover hypothesis.
- rg across Mathlib, WeilConjectures, and lean/Sheaf for the proposed declaration
  `finite_projective_of_localizationAway_free`: no collision.

Validation: server single-file compile via scompile.py; delivery preflight via
`deliver2.py M1 lem-sc-affine-standard-cover-finite-projective --no-push`.
The independent second reading is reserved for the next worker.

## Second reading by M1

I reread the node, its Stacks source, the dependency records, and the Lean file
independently. The item-by-item rendering is:

- The source's commutative ring (R) is `{R : Type u} [CommRing R]`; no
  Noetherian, domain, characteristic, or nonzero assumption is added.
- The (R)-module (N) is `{N : Type v} [AddCommGroup N] [Module R N]`, with
  independent universes, so the zero module and all allowed universe sizes remain
  included.
- The finite standard-open data is `(t : Finset R)` and
  `ht : Ideal.span (t : Set R) = ⊤`. This is exactly a finite family generating
  the unit ideal; the empty family is therefore still represented.
- For each family member, `hlocal : ∀ f : t, ...` quantifies over the subtype of
  elements of `t`, and the body uses
  `Localization.Away (f : R)` and `LocalizedModule.Away (f : R) N`.
  These are the Mathlib localization notions recorded by
  `def-weil-pbc-module-localization-away`, with no private replacement.
- The body requires the conjunction
  `Module.Finite (Localization.Away (f : R)) ... ∧
  Module.Free (Localization.Away (f : R)) ...`, exactly “finite free” over each
  localized ring, without a common rank or a constant-rank hypothesis.
- The conclusion is exactly
  `Module.Finite R N ∧ Module.Projective R N`, i.e. finite projective, using the
  Mathlib notion recorded by `def-weil-pbc-projective-module`.

The quantifier order (ring and module parameters, finite family and its unit-ideal
hypothesis, then the local condition, then the conclusion) agrees with the node.
The source's implication is (7) to (2), as the node states; the source's separate
(7) to (3) direct-summand implication is not silently substituted. No mismatch was
found and no Lean or node change was required.

Edge cases checked again: `t = ∅` can satisfy `ht` only in the zero ring; the zero
module is allowed; a member `f = 0` contributes the zero localization and cannot
cover a nonzero ring; `t = {1}` gives the finite-free case; repeated or redundant
cover elements do not change the ideal; and a product ring with complementary
idempotents permits different local ranks, confirming that global freeness and
constant rank must not be added.

Searches were reread from the worker record and repeated by concept: Mathlib
searches for finite-projective localization-cover criteria (LeanSearch,
LeanFinder/Loogle, and grep), plus `rg` in Mathlib, WeilConjectures, and
`lean/Sheaf` for the node and proposed declaration. They found only component
finite-generation, finite-presentation, flatness, maximal-local projectivity, and
free-locus results; no exact declaration exists. Thus the module is appropriately
new and its imports are used.
