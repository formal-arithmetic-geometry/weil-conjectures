## Worker report

The module `Sheaf.AlgebraicGeometry.ProperFlatGlobalSections` states
`AlgebraicGeometry.isIso_structureSheafMap_of_proper_flat_geometricallyReduced_connected_fibers`.
Its sole theorem has proof `sorry`; it introduces no definitions or auxiliary theorems.
The node is unchanged except for `lean`.

Source checked: [Stacks Tag 0E0L](https://stacks.math.columbia.edu/tag/0E0L), currently
Lemma 36.32.6 (the node's numerical reference 36.32.1 is stale; the stable tag is correct).
The hypotheses and conclusion agree with that source. Its proof applies the preceding
fibrewise criterion and the proper geometrically connected and reduced field theorem,
exactly the node's two proof steps, reproduced in the theorem docstring.

Hypothesis and clause correspondence:

- Schemes `X`, `S` and morphism `f : X → S`: `{X S : Scheme.{u}} (f : X ⟶ S)`.
  Specifying the map itself specifies the scheme over the base; no extra `Over` instance
  or compatibility hypothesis is necessary.
- Proper: `[IsProper f]`.
- Flat: `[Flat f]`, the recorded affine-local definition equivalent to flatness of every
  stalk map (`Flat.iff_flat_stalkMap`).
- Finite presentation: `[LocallyOfFinitePresentation f]` together with `[IsProper f]`.
  Properness implies quasi-compactness and separatedness, hence quasi-separatedness;
  thus this is exactly finite presentation, not merely its local version.
- Every point `s ∈ S` and the fibre over `κ(s)`:
  both explicit hypotheses quantify `∀ s : S` and use `f.fiberToSpecResidueField s`,
  whose source is `f.fiber s = pullback f (S.fromSpecResidueField s)` and target is
  `Spec (S.residueField s)`.
- Geometrically reduced over the residue field:
  `hred : ∀ s : S, GeometricallyReduced (f.fiberToSpecResidueField s)`.
- Geometrically connected over the residue field:
  `hconn : ∀ s : S, GeometricallyConnected (f.fiberToSpecResidueField s)`.
  These are the exact every-field-extension notions in the dependency record, not
  merely reducedness or connectedness of the unextended fibre.
- `f_* 𝒪_X ≅ 𝒪_S`: `IsIso f.c`. The inherited field `c` is explicitly
  `S.presheaf ⟶ f.base _* X.presheaf` (PresheafedSpace.Hom). It is the canonical
  structure-sheaf map. Invertibility in presheaves of commutative rings is equivalent
  to invertibility of this map of sheaves: the inverse respects the same sheaf data.
  Its inverse gives the isomorphism in the node's displayed direction. This records
  the canonical identification intended by the source, not an unrelated abstract iso.
- After every base change `T → S`: the second conjunct
  `∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (pullback.snd f g).c`.
  This uses the dependency's actual convention `X_T = pullback f g`, projection
  `pr_T = pullback.snd f g`; it places no properness, flatness or other restriction on `g`.
  It retains the original-base conclusion as an explicit first conjunct.

Dependency declarations read and used:

- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper` (full extends signature read).
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat` (docstring and affine-local signature read).
- `def-weil-scheme-over-base`: `Mathlib.AlgebraicGeometry.Over`,
  `AlgebraicGeometry.Scheme.Over`, `Hom.IsOver`, `asOver` read;
  the chosen binder `f : X ⟶ S` is the structure morphism described there.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField`, the stalk residue field; used through
  `Scheme.Hom.fiberToSpecResidueField` in `Mathlib.AlgebraicGeometry.Fiber`.
- `def-pc-geometrically-irreducible`: its mathlib_match explicitly includes
  `AlgebraicGeometry.GeometricallyReduced` in
  `Mathlib.AlgebraicGeometry.Geometrically.Reduced` and
  `AlgebraicGeometry.GeometricallyConnected` in
  `Mathlib.AlgebraicGeometry.Geometrically.Connected`. Both signatures and docstrings read.
- `def-pc-base-change`: imported `Sheaf.AlgebraicGeometry.BaseChangeConventions`;
  read its declarations and its record's note. Scheme base change is the existing
  `CategoryTheory.Limits.pullback` and `pullback.snd`, as the dependency explicitly
  directs. `Scheme.Modules.moduleBaseChange` concerns arbitrary modules and is not
  relevant to this structure-sheaf assertion; no replacement is defined.

Edge cases checked before writing:

- Empty base: all fibre hypotheses are vacuous and any scheme mapping to it is empty;
  the canonical sheaf maps over the empty spaces are isomorphisms. No nonempty-base
  binder is imposed.
- Empty `X` over nonempty `S`: excluded by geometrically connected fibres, which use
  `ConnectedSpace` (nonempty and preconnected); dropping nonemptiness here would make
  the theorem false. An empty base-change scheme `T` is allowed.
- Nonreduced bases and arbitrary field characteristics are allowed. No Noetherian,
  reduced-base, field-base, smoothness or characteristic hypothesis was introduced.
- Disconnected or reducible `X` is allowed whenever the specified fibres satisfy the
  two conditions. Geometrically integral or irreducible fibres were not substituted.
- Arbitrary base change, including nonflat morphisms and nonaffine `T`, is quantified.
  One explicitly bound arbitrary universe `u` covers the schemes and their pullbacks;
  no finite/countable/small-cardinality condition is imposed. All variables and universes
  are explicitly bound; no auto-implicit variables occur.

Searches for an existing statement (all msearch calls recorded in `searches.jsonl`):

- LeanSearch: query “Proper flat morphism of finite presentation with geometrically
  reduced connected fibres universally has structure sheaf pushforward equal to the
  base structure sheaf”; unavailable, Internal Server Error.
- LeanFinder: “proper flat geometrically reduced connected fibres pushforward structure
  sheaf isomorphism”; eight hits, Flat and flat morphism results, no matching theorem.
- Loogle: `AlgebraicGeometry.IsProper, AlgebraicGeometry.Flat,
  AlgebraicGeometry.GeometricallyConnected`; zero hits.
- Mathlib grep: `proper.*flat|flat.*proper|IsIso.*(toPushforward|\.c)` in
  `AlgebraicGeometry`; flat morphism infrastructure and unrelated isomorphisms, no match.
- Source and project grep: `lem-sc-proper-flat-global-sections|proper.*flat|flat.*proper`
  in `WeilConjectures/AlgebraicGeometry` and `lean/Sheaf/AlgebraicGeometry`; no exact
  theorem. Read the entire source `GlobalSectionsBijective.lean`: its field theorem
  and field-base-change results have field bases and do not state the general-base result.
- Collision search of the chosen declaration name in `dag/lean_names_upstream.json`,
  Mathlib, `WeilConjectures`, and `lean/Sheaf`: no hits.

Validation: server `scompile.py` accepted the module (exit 0, 1.9 seconds), without warnings.
No mathematical statement fault or disputed assertion was found; no new nodes or dependency
modules are needed.

## Second reading by G1

I independently opened the node and the module and matched the statement clause by clause.

- Objects: the node's schemes and morphism (f:X\to S) are rendered by
  `{X S : Scheme.{u}} (f : X ⟶ S)`; the single explicit universe `u` permits all
  schemes covered by the node.  The Lean morphism is the structure morphism over the
  base, with no extra `Over` object or compatibility datum.
- Properness and flatness: `[IsProper f]` and `[Flat f]` render exactly the two
  hypotheses, with no Noetherian, separated, field, or characteristic assumption.
- Finite presentation: `[LocallyOfFinitePresentation f]` is the local finite
  presentation hypothesis in the node; together with properness (hence
  quasi-compactness) it gives the stated finite-presentation condition.  No stronger
  finiteness hypothesis appears.
- Fibre hypotheses: the node quantifies every `s ∈ S` and asks that the fibre over
  `κ(s)` be geometrically reduced and geometrically connected.  These are rendered
  exactly by `hred : ∀ s : S, GeometricallyReduced
  (f.fiberToSpecResidueField s)` and `hconn : ∀ s : S,
  GeometricallyConnected (f.fiberToSpecResidueField s)`.  The dependency declaration
  uses the same geometric, all-field-extensions notions; this is not ordinary
  reducedness or connectedness.
- Original conclusion: `IsIso f.c` is the canonical structure-sheaf map
  `𝒪_S ⟶ f_*𝒪_X`, hence the node's identification of `f_*𝒪_X` with `𝒪_S`.
- Universal conclusion: `∀ (T : Scheme.{u}) (g : T ⟶ S),
  IsIso (pullback.snd f g).c` quantifies every base-change scheme and morphism,
  including nonflat and nonaffine maps, and uses the dependency convention
  `X_T = pullback f g` and projection `pullback.snd`.  The original-base clause is
  retained in the conjunction.

No mismatch was found and no code or node statement was changed in this reading.
I checked edge cases explicitly: an empty base makes the fibre hypotheses vacuous;
an empty fibre over a nonempty base cannot satisfy geometric connectedness; empty
base changes remain quantified; zero or nonreduced bases and arbitrary
characteristic are allowed; no finite/countable universe restriction is imposed.

I repeated the existing-declaration searches (LeanSearch, LeanFinder/Loogle, and
`rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf`) for the theorem and for
proper-flat structure-sheaf pushforward.  They found only the underlying proper,
flat, finite-presentation and geometric-fibre infrastructure, with no declaration
of this result.  Thus the module is genuinely new.  The file compiles cleanly with
`scompile.py`; its only proof is the required `sorry`.
