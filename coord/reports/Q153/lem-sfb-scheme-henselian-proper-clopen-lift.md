## Worker report

The module `Sheaf.AlgebraicGeometry.HenselianProperClopenLift` states
`AlgebraicGeometry.Scheme.exists_proper_clopen_of_henselianPair`, with its entire
proof `sorry`. It defines no new notions. The statement is unchanged from the
DAG and from Stacks, More on Morphisms, Tag 0CT9,
`lemma-split-off-proper-part-henselian` (local source lines 15463 onward).
The docstring carries all five steps of the accepted Nagata-based proof.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A commutative ring and ideal: `{A : Type u} [CommRing A] (I : Ideal A)`.
- The pair is henselian: `[HenselianRing A I]`, using the recorded dependency's
  Mathlib predicate, not a new local-ring or idempotent predicate.
- An arbitrary scheme over the affine base: `{X : Scheme.{u}}` and
  `(f : X ⟶ Spec (.of A))`.
- Separated: `[IsSeparated f]`.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, the recorded conjunction.
- The closed fibre is exactly
  `pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))`.
  Its first projection maps to X; its second maps to `Spec (.of (A ⧸ I))`.
- Y is an open subscheme of this closed fibre: the binder `Y : (...).Opens`.
  `Y.toScheme` is the actual restricted scheme; `Y.ι` is its inclusion.
- Y is also closed: `hY : IsClosed (Y : Set ↥(...))`.
- Its structure morphism is proper:
  `[IsProper (Y.ι ≫ pullback.snd f (Spec.map ...))]`.
- A clopen W in X: `∃ W : X.Opens, IsClosed (W : Set X) ∧ ...`.
- W is proper over A: `IsProper (W.ι ≫ f)`.
- Its base change equals Y as an open subscheme of the closed fibre:
  `(pullback.fst f (Spec.map ...)) ⁻¹ᵁ W = Y`.
  This is equality in the type of opens, each carrying its restricted scheme
  structure, not equality of arbitrary subschemes based only on their supports.
  Mathlib `isPullback_morphismRestrict` in `AlgebraicGeometry/Restrict.lean:586`
  identifies the restricted scheme on this inverse image with the pullback of
  `W.ι`. Equality therefore identifies the restricted structure sheaves too.
- No assumption of ambient properness, Noetherianity, finite presentation,
  localness or nonemptiness occurs.

Dependency declarations read and used:

- `def-weil-pbc-henselian-terminology`: recorded module
  `WeilConjectures.Mathlib.RingTheory.Henselian`, which publicly exposes
  `HenselianRing` from `Mathlib.RingTheory.Henselian` (class at line 94).
  Its Jacobson and simple-root conditions are the standard henselian-pair
  notion recorded by that dependency. Strict/local variants are not assumed.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-weil-affine-spectrum`: same module, `AlgebraicGeometry.Spec` and `Spec.map`.
- `def-weil-proper-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `IsProper`, with `IsSeparated`
  and `UniversallyClosed` read in their defining modules. Properness implies
  quasi-compactness, so its locally-finite-type field gives finite type.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `QuasiCompact`.
- `def-pc-base-change`: publicly import its recorded module
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`; its docstring
  expressly records `pullback`, `pullback.fst` and `pullback.snd` as the scheme
  base change and projections (the main `moduleBaseChange` is for modules,
  which this node does not discuss).
- Restricted structure sheaves: existing `Scheme.Opens.toScheme` and
  `Scheme.Opens.ι` in `Mathlib.AlgebraicGeometry.Restrict`.

Proof dependencies with Lean records are imported privately:
`WeilConjectures.Compactification.NagataCompactification`,
`WeilConjectures.Compactification.Defs`,
`WeilConjectures.AlgebraicGeometry.HenselianClopenRestriction`,
`WeilConjectures.AlgebraicGeometry.HenselianConnectedness`, and
`Mathlib.AlgebraicGeometry.OpenImmersion`.
The proper-morphism dependency is already public. The Mathlib-only proof
matches (qcqs over an affine base, open-immersion base change, proper
permanence, proper over separated, closed immersion proper) use the existing
Mathlib APIs exposed through these imports. No proof prerequisite is restated.

Edge cases checked before writing:

- Y empty: the empty open W has the required conclusion; no nonempty binder.
- X empty: its only open and hence Y are empty, again permitted.
- I = 0: the closed-fibre map is an isomorphism; W is Y under this identification.
- A the zero ring: its spectrum and every scheme admitting a map to it are empty;
  no domain or nontrivial-ring condition excludes this case.
- X = Spec k[[t]] disjoint union Spec k((t)) over k[[t]], I = (t): the first
  component provides W for the whole closed fibre although X need not be proper.
  This verifies why ambient properness must not be added.
- A need not be local or Noetherian, I need not be finitely generated, and finite
  type is not replaced by finite presentation. The same universe u is the usual
  category of schemes and rings; every such datum can be placed in a common u.

Searches on 2026-10-24:

- `msearch.py ... leanfinder "For a separated finite type scheme over a henselian
  pair lift a proper clopen subscheme of the closed fibre to a proper clopen
  subscheme"`: 8 hits; separated diagonals, quasi-finite clopen singleton,
  proper global functions, HenselianRing and related declarations. None states
  this result.
- `msearch.py ... loogle "AlgebraicGeometry.IsProper, HenselianRing"`: 0 hits.
- `msearch.py ... grep "henselian|Henselian|splitOffProper" AlgebraicGeometry`:
  0 hits in Mathlib algebraic geometry.
- `msearch.py ... leansearch "A proper open and closed part of the special fibre
  of a separated finite type scheme over a henselian pair lifts to a proper open
  and closed subscheme"`: 8 hits, including `isProper_eq`, properness of an open
  base restriction, separatedness, and open-immersion lifting; no match.
- `rg -n "splitOffProper|split_off_proper|henselian.*(clopen|proper)|henselian_proper"`
  in `lean/WeilConjectures` and `lean/Sheaf`: the nearest result is
  `Scheme.henselian_clopen_restriction` in the recorded upstream module. Its full
  signature requires `[IsProper f]` for the ambient scheme, so it is strictly
  inapplicable to this node's nonproper ambient schemes. Other matches concern
  finite etale restriction, connectedness, sections or proof comments.
- Search for this item id in `lean/WeilConjectures`: no match.
- Search for `exists_proper_clopen_of_henselianPair` and
  `HenselianProperClopenLift` across Mathlib, both project Lean roots, and
  `dag/lean_names_upstream.json`: no pre-existing declaration/module match.

No new nodes, dependency repairs, statement corrections or disputed claims.

## Second reading by Q153

A second pass by the same worker, with the JSON node, Stacks source, and module
open, checked every binder and conjunct listed above. No second agent was
started: the dispatcher explicitly forbids sub-agents, and the maintainer's
independent delivery review supplies the independent reading.

The main potential mismatch was interpreting equality only topologically.
Here both Y and W are Mathlib opens whose scheme structure is definitionally
restriction; `isPullback_morphismRestrict` supplies the base-change identification.
Consequently equality of inverse-image opens is equality of the specified open
subschemes, with no nilpotent structure discarded. The finite-type hypothesis
contains quasi-compactness as well as locally finite type. The properness
hypothesis concerns Y, and the properness conclusion concerns W, never X.
No statement mismatch or correction was found. During compilation the explicit
carrier coercion `↥(pullback ...)` was added in the closedness binder so Lean
selects the scheme pullback rather than a type-category pullback.

Validation: prescribed `scompile.py Q153 lem-sfb-scheme-henselian-proper-clopen-lift`
compiled both the sandbox and library-name module successfully (3.2 s and 1.8 s),
with no unexpected warnings.
