## Worker report

The module `Sheaf.AlgebraicGeometry.FlatFamilyPerfectDirectImagePseudoCoherent` states
`AlgebraicGeometry.Scheme.isPseudoCoherent_directImage_of_perfect_flat_families`.
Its only theorem has proof `sorry`. No definitions or extra nodes are needed, and
only the assigned node's `lean` field is changed.

Clause-by-clause correspondence:

- An arbitrary base and the two families are `{S X Y : Scheme.{u}}`,
  `(x : X ⟶ S)` and `(y : Y ⟶ S)`.
- Flatness of each family is `[Flat x]` and `[Flat y]`.
- Local finite presentation of each family is `[LocallyOfFinitePresentation x]`
  and `[LocallyOfFinitePresentation y]`.
- The proper S-morphism is `(f : X ⟶ Y) [IsProper f] (_hOver : f ≫ y = x)`.
  The equality is precisely compatibility with the two structure maps.
- Every perfect object is `(P : schemeDerivedCategory X) (_hP : IsPerfect X P)`.
- The full conclusion is `IsPseudoCoherent Y ((schemeDerivedDirectImage f).obj P)`.
- There is no flatness assumption on `f`, no Noetherian assumption, and no
  quasi-compactness or quasi-separatedness assumption on `S`, `X` or `Y`.
  Properness includes its usual relative quasi-compactness and separatedness.
- Four explicit `HasDerivedCategory` instance binders supply the existing
  derived categories on X, Y and their localized open sites. They are the
  localization infrastructure required by the recorded definitions, not additional
  geometric finiteness conditions. The arbitrary morphism universes `wX` and `wY`
  are independent. There is no derived-category assumption on S.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`
  (publicly available through the morphism imports).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, whose
  docstring and `Flat.iff_flat_stalkMap` identify the affine and stalk definitions.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory` (public through the following modules).
- `WeilConjectures.AlgebraicGeometry.PerfectComplex`:
  `AlgebraicGeometry.Scheme.IsPerfect` (local strictly perfect models).
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `AlgebraicGeometry.schemeDerivedDirectImage` (ringed-space derived pushforward).
- `WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsPseudoCoherent` (local bounded-above finite free models).

Plain proof imports are `WeilConjectures.AlgebraicGeometry.PerfectPseudoCoherentLocallyFiniteTor`
(the recorded `Scheme.perfect_isPseudoCoherent_and_hasLocallyFiniteTorDimension`),
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` (`IsClosedImmersion`), and
`Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex`
(`Scheme.IsMPseudoCoherentRelativeTo`, `Scheme.IsPseudoCoherentRelativeTo`).
The ambient-chart, flat-lfp structure, relative-composition and Kiehl proof nodes
have no recorded Lean modules at the time of writing, so no imports are invented
for them. All four proof steps, with their node references, are in the docstring.

Source checked: `literature/stacks-project/perfect.tex`, the unnumbered Kiehl
relative-pseudo-coherence assertion immediately after
`lemma-flat-proper-pseudo-coherent-direct-image-general` (Tag 0CSD);
`more-morphisms.tex`, `lemma-composition-relative-pseudo-coherent` (09UT),
`lemma-flat-finite-presentation-pseudo-coherent` (0695), and
`lemma-permanence-pseudo-coherent` (0683); `duality.tex`, footnote to
`lemma-proper-noetherian` (0A9P). The relative assertion imposes no absolute
quasi-compactness or quasi-separatedness. The flat-family specialization is the
agent-formulated assembly explicitly described in the node, not the more
restrictive flat-proper statement alone.

Edge cases checked before writing: empty schemes and the zero complex are
included; identity maps give the usual perfect-implies-pseudo-coherent case.
A proper closed immersion of a point into a smooth curve over a field is allowed
although the immersion is not flat: flatness is imposed only on the two maps to
the field. Non-Noetherian bases and non-quasi-compact families are allowed, and
local perfect models may have different degree bounds on different components.
The conclusion introduces no global amplitude or boundedness hypothesis.
All schemes use arbitrary common size `u`, the existing scheme-category encoding.

Searches made using `msearch.py Q13 lem-sfb-flat-family-perfect-direct-image-pseudocoherent`:

- `leanfinder`: "A proper morphism between schemes flat and locally of finite
  presentation over a common base sends perfect complexes to pseudo-coherent
  complexes under derived direct image". Eight hits, including
  `AlgebraicGeometry.IsProper.isStableUnderBaseChange`, `UniversallyOpen.of_flat`,
  `Flat` and flatness stability. None is the required theorem.
- `loogle`: "AlgebraicGeometry.Scheme.IsPerfect,
  AlgebraicGeometry.Scheme.IsPseudoCoherent, AlgebraicGeometry.schemeDerivedDirectImage".
  Zero hits; the public service does not know the project-local `Scheme.IsPerfect`.
- `grep`: "IsPseudoCoherent|schemeDerivedDirectImage|IsPerfect" in Mathlib
  `AlgebraicGeometry`. Zero hits.
- Direct `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the node id, flat-family/perfect phrases,
  and pseudo-coherent direct-image combinations found no exact statement.
  Related results `properFlat_single_open_isPseudoCoherent` and
  `Space.isPseudoCoherent_derivedDirectImage_of_flat_proper` respectively concern a single
  relatively flat finitely presented module, or pseudo-coherent complexes on
  algebraic spaces with the map itself flat. Neither states this theorem. Existing notions are all reused.

No statement correction, unusable dependency interface, or mathematical dispute
was found. Validation: `scompile.py` compiled the sandbox and library forms
cleanly in 7.9 s and 7.5 s, respectively. Delivery preflight is recorded below
after completion.

## Second reading by Q13

This is a single-worker rereading; the independent maintainer review remains
separate, as specified by the dispatcher brief. Reread the node against the
signature: the two Flat and two LocallyOfFinitePresentation instances are on the
structure maps, while IsProper is on f. The equation is f followed by y equals x,
so it asserts exactly that f is over S. The input and output are the recorded
schemeDerivedCategory carriers and the recorded perfect/pseudo-coherent notions.
No base-change conclusion, uniform amplitude, or geometric hypothesis is added.
The derived-category morphism universes are independent and all variables are
explicitly bound with autoImplicit disabled. No mismatch required a change.

Validation completed: `deliver2.py Q13
lem-sfb-flat-family-perfect-direct-image-pseudocoherent --no-push` printed
`OK (dry run): commit 9191c733298 passes the preflight and compiles; nothing pushed`.
