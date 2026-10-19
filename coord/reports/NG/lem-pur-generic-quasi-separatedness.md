## Worker report

The module `Sheaf.AlgebraicGeometry.GenericQuasiSeparatedness` states
`AlgebraicGeometry.exists_nonempty_open_quasiSeparated_restrict`, with `sorry` as its entire
proof. No definition or statement correction is needed.

Hypothesis and clause correspondence:
- Schemes Z and T: `{Z T : Scheme.{u}}`, with explicit universe `u`.
- The given morphism: `(h : Z ⟶ T)`.
- Finite type: `[LocallyOfFiniteType h] [QuasiCompact h]`, exactly the conjunction recorded
  by def-weil-finite-type-morphism, not merely locally finite type.
- Integral base: `[IsIntegral T]`, including nonemptiness and reduced irreducibility.
- An open subscheme of T: `∃ W : T.Opens`; Mathlib canonically equips this open with its
  restricted scheme structure.
- Nonempty: `(W : Set T).Nonempty`.
- The inverse-image morphism to W: `morphismRestrict h W`, whose source is
  `(h ⁻¹ᵁ W).toScheme` and target is `W.toScheme`.
- Quasi-separated conclusion: `QuasiSeparated (morphismRestrict h W)`.
- Neither scheme is assumed Noetherian. There is no separatedness or quasi-separatedness
  hypothesis on h, Z, or T. The conclusion introduces none of those extra requirements.

Dependency declarations read and used:
- def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType; `AlgebraicGeometry.QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact (available through QuasiSeparated).
- def-pc-integral-scheme: `AlgebraicGeometry.IsIntegral`,
  Mathlib.AlgebraicGeometry.Properties.
- def-weil-quasi-separated-morphism: `AlgebraicGeometry.QuasiSeparated`,
  Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated; the node's mathlib_match is usable.
- Mathlib.AlgebraicGeometry.Restrict: `AlgebraicGeometry.morphismRestrict`, the standard
  inverse-image open restriction, available transitively through the morphism imports.

Proof imports: QuasiSeparated also supplies the affine-cover and morphism-permanence
criteria; OpenImmersion supplies the principal-localization immersion, and
Mathlib.RingTheory.Localization.Away.Basic supplies localization away. The affine spectrum
is already available through these imports. The two proof dependencies
lem-pur-generic-finite-module-presentation and lem-pur-finitely-presented-support-complement
have no Lean records yet and therefore supply no import. Their proof steps remain fully
recorded in the theorem docstring, as do all four steps of the node's proof.

Source checked: local Stacks morphisms.tex, proposition-generic-flatness (Tag 052A),
including its assumptions and entire proof. Its final paragraph establishes precisely the
quasi-separatedness needed here; nonempty opens are dense on an integral base.

Edge cases: the source may be empty (empty affine cover and product 1 in the proof);
no nonemptiness assumption excludes it. An empty base is correctly excluded by IsIntegral.
For a field base the nonempty open can be the entire base. No characteristic restriction,
Noetherianity, affine-base hypothesis, or reducedness of Z is added. Both schemes inhabit
an arbitrary explicit universe, as in Mathlib's scheme morphism category.

Searches (msearch.py, group NG, this item):
- leanfinder: "A finite type morphism to an integral scheme is quasi separated over some
  nonempty open of the base": OK, eight hits. They give QuasiSeparated, its equivalence
  with source quasi-separatedness over a quasi-separated target, and permanence instances;
  none constructs the required nonempty open without an existing quasi-separatedness assumption.
- loogle: `"QuasiSeparated", "exists"`: OK, one hit,
  AlgebraicGeometry.exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated, about sections.
- grep: `generic.*[Qq]uasi|[Qq]uasi.*generic|exists.*[Qq]uasiSeparated` in AlgebraicGeometry:
  OK, five hits, all section-extension results in Morphisms/QuasiSeparated.lean.
- leansearch: "A finite type morphism to an integral scheme becomes quasi separated on a
  nonempty open": service unavailable, Internal Server Error.
- rg with the same generic/quasi-separated expression in WeilConjectures and lean/Sheaf:
  results concern existing quasi-separated hypotheses, generic points, and section extension;
  none states this theorem. Inspected GenericFlatFinitePresentation.lean: its theorem concludes
  flatness and local finite presentation, not this quasi-separatedness statement.
- grep -rn of the item id in WeilConjectures: no hits.
- rg for `exists_nonempty_open_quasiSeparated_restrict|GenericQuasiSeparatedness` in Mathlib,
  WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json: no hits, so the name is fresh.

Validation: scompile.py compiled the delivered file cleanly on the server in 1.3 seconds,
nice 19, two threads, 60 seconds per file. No local compilation was run. No node faults
or disputed statements were found. Only the item's lean field changes.

## Second reading by NG

I independently read the node, its three statement-dependency nodes and their actual
Mathlib declarations, the delivered module, and Stacks morphisms.tex,
proposition-generic-flatness (Tag 052A), from the section introduction through the
entire proof. The source assumes an integral base and a finite type morphism, with no
Noetherianity or separatedness assumption. The auxiliary finite type quasi-coherent
module in the full generic-flatness proposition is not needed for this extracted
quasi-separatedness assertion: its proof uses only the cyclic modules B_i/I_ij.

Object, hypothesis and conclusion checklist, in the node's order:

- Schemes Z and T: `{Z T : Scheme.{u}}`. Exact; the arbitrary declared universe u
  is the universe of Mathlib's scheme category and its morphisms.
- Given morphism h: Z → T: `(h : Z ⟶ T)`. Exact; no structure morphism or alternate
  base replaces h.
- Finite type h, as def-weil-finite-type-morphism defines it:
  `[LocallyOfFiniteType h] [QuasiCompact h]`. Exact. I read FiniteType.lean's
  class and module docstring and QuasiCompact.lean's class: these are locally
  finite type on affine pairs and compact preimages of compact opens, respectively.
  Their conjunction is the node's finite type, not a stronger finite presentation.
- Integral T, as def-pc-integral-scheme defines it: `[IsIntegral T]`. Exact.
  Properties.lean's class includes nonemptiness and domain-valued sections on every
  nonempty open; its equivalence with reduced irreducibility matches the node.
- Existence of an open subscheme W ⊆ T: `∃ W : T.Opens`. Exact. Each open comes
  with its canonical restricted scheme; the statement does not demand affine W.
- Nonempty W: `(W : Set T).Nonempty`. Exact, referring to the underlying open
  subset, without supplying an extra point or excluding any allowed nonempty open.
- The morphism h⁻¹(W) → W: `morphismRestrict h W`. Exact. I read Restrict.lean's
  definition, whose domain is `(h ⁻¹ᵁ W).toScheme`, and its pullback description;
  its target is W's restricted scheme and its composite with W.ι is the restriction
  of the given h.
- Quasi-separatedness of that morphism: `QuasiSeparated (morphismRestrict h W)`.
  Exact. I read QuasiSeparated.lean's class: its field is precisely
  `QuasiCompact (pullback.diagonal f)`, as def-weil-quasi-separated-morphism states.
- Neither scheme Noetherian and h neither separated nor quasi-separated in the
  hypotheses: no such binder or ambient instance occurs. Exact. All binders are
  visible in the three-line signature, in the same quantifier order as the node.

Edge cases: an empty Z and an empty inverse image of an affine base open are allowed;
there is no Nonempty Z, and the docstring explicitly treats the empty cover with
product 1. An empty T (including Spec of the zero ring) is correctly excluded by
IsIntegral T, exactly as in the node. For T the spectrum of any field, W may be all
of T. There is no characteristic restriction. The empty index set and n = 0 arise
only in the proof and are handled by the empty product. There are no finite-rank,
positive-dimension, or source-reducedness assumptions. The statement has no test
objects in an independent universe: both schemes and their Hom live in an arbitrary
common Scheme universe, so no scheme-size bound or vacuous quantifier is introduced.

Independent duplicate searches, using different wording from the worker:

- LeanFinder: "A morphism of finite type over an irreducible reduced scheme has
  quasi compact diagonal after shrinking the base to a dense open". Eight hits,
  all diagonal characterizations, absolute criteria or existing quasi-separatedness
  facts; none produces the nonempty open.
- Loogle: `"morphismRestrict", "QuasiSeparated"`. The one hit is
  instQuasiSeparatedMorphismRestrict, whose `[QuasiSeparated f]` hypothesis makes
  it a restriction-permanence result, not this statement.
- LeanSearch: "A finite type scheme morphism over an integral base has quasi compact
  diagonal over a dense open subset". Unavailable: Internal Server Error. Recorded
  as unavailable; no mathematical verdict inferred from it.
- rg in Mathlib/AlgebraicGeometry, WeilConjectures, and lean/Sheaf:
  `generic.{0,70}(quasi.?separ|diagonal)|(quasi.?separ|diagonal).{0,70}(generic|nonempty|dense)`
  (case insensitive). The upstream affine-neighbourhood theorems already assume
  QuasiSeparatedSpace; compactification results already assume separatedness.
  I opened their signatures. None matches this statement.
- Exact declaration and module-name search in WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json found no duplicate. I also opened the nearby
  GenericFlatFinitePresentation.lean: despite its filename, its conclusion is
  Flat plus LocallyOfFinitePresentation, and contains no QuasiSeparated clause.
  It therefore does not state this node.

Proof and module audit: the four docstring steps match all four node proof steps:
finite affine cover and cyclic complement modules; common nonzero localization;
identification of quotient support and compact intersections; affine-cover criterion
and source-to-morphism quasi-separatedness. I read the recorded Mathlib signatures
for the latter criterion and permanence, and the principal-localization immersion.
The imports provide the statement's dependency declarations and the available proof
inputs. The two pur module-presentation/support lemmas have no Lean records, so no
imports for them can be added yet. There are no new definition nodes or dependency
modules in this delivery and no missing notion in the statement. There is one named
public theorem with sorry as its entire proof, no data definition, no private notion,
no local notation or instance, no unbound variable or universe, and no proved lemma.
Both source-bearing docstrings have the required blueprint marker.

Mismatches and changes: none found. I preserved the Lean module and node as written;
only this independent second-reading report was appended. No statement correction
or citer review under §1(C) is needed. The node's lean.statement was checked verbatim
against the signature before `:= by`.
