## Worker report

The module `Sheaf.AlgebraicGeometry.AffineDerivedPushforwardConservative` states
`AlgebraicGeometry.schemeDerivedDirectImage_isIso_of_affine`, with `sorry` as its sole proof.
It states precisely the isomorphism-reflection assertion of the item, using the ambient
category and the predicate defining its quasi-coherent full subcategory. No definitions,
new nodes, dependency modules, or statement corrections are needed.

Clause-by-clause correspondence:

- Schemes X and Y: `{X Y : Scheme.{u}}`.
- Morphism f from X to Y: `(f : X ⟶ Y)`.
- f affine: `[IsAffineHom f]`, meaning inverse images of affine opens are affine.
  This does not assert that X or Y themselves are affine.
- The derived categories: `schemeDerivedCategory X` and `schemeDerivedCategory Y`,
  using explicitly bound `HasDerivedCategory.{wX}` and `HasDerivedCategory.{wY}` on
  the shared `SheafOfModules.{u} (moduleRings _.toRingedSpace)` carriers. These are
  the localization infrastructure required by the recorded dependency definitions;
  they impose no boundedness or geometric assumption.
- E and F in D_QCoh(X): `{E F : schemeDerivedCategory X}` together with
  `(hE : schemeDerivedQCohProperty X E)` and `(hF : schemeDerivedQCohProperty X F)`.
  The predicate means all integer-degree cohomology sheaves are quasi-coherent.
  Since D_QCoh is full, ambient morphisms between these objects are precisely its
  morphisms, and ambient invertibility is equivalent to invertibility in that
  full subcategory.
- A morphism u:E→F: `(u : E ⟶ F)`.
- Its derived direct image is invertible:
  `[IsIso ((schemeDerivedDirectImage f).map u)]`.
- Conclusion u is invertible: `IsIso u`.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom` (including their
  complete structure signatures and docstrings). Schemes are locally ringed
  spaces locally isomorphic to spectra; arrows are locally ringed space arrows.
- `def-pc-derived-category`: `Sheaf.AlgebraicGeometry.DerivedCategory`,
  `AlgebraicGeometry.schemeDerivedCategory`, `schemeDerivedQCohProperty`, and
  `schemeDerivedQCohCategory`. Their definitions and docstrings were read; the
  first two are used in the signature, and the third explains its full-subcategory
  interpretation. This module is imported through SchemeDerivedDirectImage.
- `def-pc-derived-direct-image`: `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`,
  `AlgebraicGeometry.schemeDerivedDirectImage`. Its signature and docstring were
  read, as was `RingedSpace.derivedModuleDirectImage` in
  `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage`, showing that the functor
  is the recorded unbounded K-injective right derived direct image, not an
  arbitrary functor or a bounded substitute.
- Mathlib `AlgebraicGeometry.IsAffineHom` in
  `Mathlib.AlgebraicGeometry.Morphisms.Affine` supplies the affine condition.

The module docstring names the source; the theorem docstring carries both node
proof steps: the affine derived equivalence of
`lem-sc-finite-affine-derived-equivalence` (Tag 0AVW), restriction-of-scalars
conservativity through acyclic cones, and reflection by the equivalence using
its quasi-inverse, unit and counit. No proof dependency is assumed as a binder.

Edge cases checked mathematically before writing: the empty scheme and zero
objects are admitted; the assertion on the zero derived category is valid.
Identity morphisms are affine and the conclusion agrees with identity direct
image. No hypothesis of finiteness, surjectivity, Noetherianness, characteristic,
separatedness of the schemes, boundedness, or perfection has been introduced.
An affine morphism with a nonaffine target is admitted. Degrees range over all
integers. The object universe u and derived morphism universes wX,wY are explicitly
bound; the localization universes need not coincide.

Sources checked: the local `literature/stacks-project/perfect.tex` is absent on
this machine, so the Stacks pages were opened directly:
[Tag 08I8](https://stacks.math.columbia.edu/tag/08I8) states exactly reflection on
D_QCoh; [Tag 0AVW](https://stacks.math.columbia.edu/tag/0AVW) supplies the equivalence
and its composition with restriction of scalars used in the node's proof.
Neither the node nor its source requires correction. No STATEMENT-DISPUTED flag.

Searches performed, recorded by msearch.py in searches.jsonl:

- LeanFinder: "An affine morphism of schemes has derived pushforward reflecting
  isomorphisms on the derived category of quasi coherent sheaves". Eight hits,
  concerning underived presheaf forgetful functors and affine morphism properties;
  no derived quasi-coherent conservativity theorem.
- Loogle: `CategoryTheory.Functor.ReflectsIsomorphisms`. Twelve hits describing the
  generic reflection predicate and elementary category-theoretic lemmas; none
  establish this property for affine derived direct image.
- LeanSearch: "affine scheme derived pushforward reflects isomorphisms".
  Service unavailable (Internal Server Error); no verdict drawn from it.
- Mathlib grep via msearch.py: `derived.*pushforward|pushforward.*[Rr]eflects|[Rr]eflects.*pushforward`
  in AlgebraicGeometry: zero hits.
- rg in the source WeilConjectures and project's lean/Sheaf with that pattern and
  the exact node id: source hits are pro-étale/étale derived pushforward and
  underived O_X-module higher direct images, not this statement. The project's
  PerfectGeneratorPullback docstring cites this item as a future input; it does
  not state it. Existing derived-category and derived-direct-image definitions
  are reused.
- rg for the chosen full declaration name in Mathlib, WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json: no existing name.

Validation: server single-file compilation and `deliver2.py --no-push` are run
before handoff. The second reading is left to the independent reader.

## Second reading by G1

I reread the node and the delivered Lean file clause by clause. The node introduces an affine
morphism of schemes `f : X ⟶ Y`, with no assumptions on either scheme beyond being schemes and
`[IsAffineHom f]`; the Lean binders `{X Y : Scheme.{u}}`, `(f : X ⟶ Y)`, and the instance
`[IsAffineHom f]` render exactly these objects and hypothesis. The node then works in the
quasi-coherent derived category of `X`; Lean renders this in the project's ambient derived
category as `{E F : schemeDerivedCategory X}` together with
`hE : schemeDerivedQCohProperty X E` and `hF : schemeDerivedQCohProperty X F`, the recorded
encoding of membership in the full quasi-coherent subcategory. The required derived-category
instances are explicit `HasDerivedCategory` binders for `X` and `Y`, as required by the
recorded definitions and carrying no geometric hypotheses.

The node's morphism `u : E ⟶ F` is Lean's `(u : E ⟶ F)`. Its hypothesis that derived direct
image `Rf_*u` is an isomorphism is exactly the typeclass assumption
`[IsIso ((schemeDerivedDirectImage f).map u)]`, using the recorded unbounded derived direct
image. The conclusion that `u` is an isomorphism is exactly `: IsIso u`. Quantifier order is
`X,Y`, derived-category instances, `f` and affine instance, `E,F` and their QCoh proofs, then
`u` and the isomorphism hypothesis, followed by the conclusion, matching the node's order up
to the necessary explicit encoding of `D_QCoh`.

No clause is missing or strengthened: there is no finiteness, Noetherian, separated, proper,
characteristic, boundedness, or perfectness assumption, and no surjectivity assumption. The
universes are explicit (`u`, `wX`, `wY`), with the sheaf categories at the scheme universe;
there is no independently quantified test-algebra or index universe. The empty scheme and zero
objects are allowed, as are identity affine morphisms and a non-affine target. All integer
cohomology is implicit in `schemeDerivedQCohProperty`; no degree restriction or `n = 0`
exception is introduced. The zero morphism/object cases therefore remain covered.

I checked the dependency node signatures and their source modules: `schemeDerivedCategory` and
`schemeDerivedQCohProperty` come from `Sheaf.AlgebraicGeometry.DerivedCategory`, while
`schemeDerivedDirectImage` comes from `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`; the
scheme and affine-morphism notions are Mathlib's `AlgebraicGeometry.Scheme` and
`AlgebraicGeometry.IsAffineHom`. Searches of Mathlib, the project source, and `lean/Sheaf`
found no existing theorem with this affine derived conservativity statement (the generic
`ReflectsIsomorphisms` declarations do not state it). Thus the item remains a new statement.

No mismatch was found and no Lean or node statement change was required. The only delivery
addition is the node's `lean` record pointing to
`AlgebraicGeometry.schemeDerivedDirectImage_isIso_of_affine`; the theorem proof remains the
single permitted `sorry`, and its module and theorem docstrings cite Tag 08I8 and the blueprint
node with both proof steps.
