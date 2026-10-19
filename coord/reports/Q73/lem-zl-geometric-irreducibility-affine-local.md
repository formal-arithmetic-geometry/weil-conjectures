## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricIrreducibilityAffineLocal` states
`AlgebraicGeometry.geometricallyIrreducible_affineLocal`, with a single `sorry` proof.
It renders Stacks Tag 038G (`literature/stacks-project/varieties.tex`,
`lemma-geometrically-irreducible-local`, lines 1405–1442), restricted to irreducible X,
including the final assertion about every nonempty open. The theorem docstring contains
all three proof steps from the node, including the surjectivity citations and the
pairwise-intersection argument. No node correction, new definition, or dependency repair
is needed. Only the item's `lean` field changes.

Hypothesis and clause correspondence:

- “k a field”: `(k : Type u) [Field k]`.
- “X a k-scheme”: `(X : Scheme.{u}) [X.Over (Spec (.of k))]`, with its recorded
  structure morphism `X ↘ Spec (.of k)`.
- “X irreducible”: `[IrreducibleSpace X]`, which includes nonemptiness.
- “X geometrically irreducible over k”: `GeometricallyIrreducible (X ↘ Spec (.of k))`.
- “if and only if”: the first conjunct is an `↔`.
- “every nonempty affine open subscheme U”: `∀ (U : X.Opens) (hU : IsAffineOpen U),
  (U : Set X).Nonempty → ...`. No chosen affine chart or cover restricts this quantifier.
- “Spec Γ(U,O_X) with the induced k-algebra structure”: `hU.fromSpec` has exactly the
  type `Spec Γ(X, U) ⟶ X`. Its definition is `hU.isoSpec.inv ≫ U.ι`, so the structure
  morphism `hU.fromSpec ≫ X ↘ Spec (.of k)` is the canonical induced k-structure,
  rather than an arbitrary map. The geometric irreducibility of this composite is
  the stated conclusion for each spectrum.
- “Moreover”: the second conjunct states that geometric irreducibility of X implies
  `∀ (V : X.Opens), (V : Set X).Nonempty →
  GeometricallyIrreducible (V.ι ≫ X ↘ Spec (.of k))`. This quantifies over all opens,
  with no affineness restriction, and uses the inherited structure morphism.
- No reducedness, quasi-compactness, finite-type, separatedness, or characteristic
  hypotheses occur. The universe `u` is explicitly bound, as are all variables.
  Scheme, ring, field, and test-extension universes follow Mathlib's existing
  `GeometricallyIrreducible` interface; no independent smaller test-field universe
  is introduced.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`, extends `CommRing` and
  `DivisionRing` with the nontriviality and inverse axioms.
- `def-weil-scheme-over-base`: `AlgebraicGeometry.Scheme.Over`,
  `Mathlib.AlgebraicGeometry.Over`; its structure map is the `↘` notation.
- `def-weil-irreducible-components`: the recorded `irreducibleComponents` and
  `IsIrreducible` definitions in `Mathlib.Topology.Irreducible` were read; the
  irreducibility clause here uses `IrreducibleSpace`, which includes `Nonempty X`.
- `def-pc-geometrically-irreducible`: `AlgebraicGeometry.GeometricallyIrreducible`,
  `Mathlib.AlgebraicGeometry.Geometrically.Irreducible`; its definition via
  `geometrically` and the field-extension specialization in
  `Mathlib.AlgebraicGeometry.Geometrically.Basic` were read.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; `Scheme.Opens`, `IsAffineOpen`,
  `IsAffineOpen.isoSpec`, and `IsAffineOpen.fromSpec` provide the actual opens and
  their canonical spectra in `Mathlib.AlgebraicGeometry.AffineScheme`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`. The spectrum occurs as the actual domain of
  `hU.fromSpec`, not as a replacement for the open subscheme in the moreover clause.
- Proof dependencies: `lem-pc-field-extension-surjective` uses the instance
  `[Nonempty X] [Subsingleton Y] (f : X ⟶ Y) : Surjective f` in
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`;
  `lem-weil-pbc-surjective-base-change` uses the instance
  `MorphismProperty.IsStableUnderBaseChange @Surjective` in
  `Mathlib.AlgebraicGeometry.PullbackCarrier`. Both source modules are imported
  without `public` for the future proof.

Edge cases checked against the mathematical statement and source:

- Empty X is excluded precisely by irreducibility, not by an extra hypothesis.
- Empty affine opens and the empty arbitrary open are excluded by their individual
  nonemptiness antecedents; otherwise a geometrically irreducible X would have to
  have a geometrically irreducible empty subscheme.
- `Spec k` and its unique nonempty open satisfy both conjuncts.
- `Spec k[t]/(t²)` is allowed and geometrically irreducible: the statement assumes
  no reducedness. No domain or integrality condition occurs in Lean.
- `Spec Q(√2)` over Q is irreducible but not geometrically irreducible; its whole
  affine open fails the right side, so the equivalence does not inadvertently
  assert that all irreducible k-schemes are geometrically irreducible.
- Nonseparated schemes (for example a doubled-origin affine line) are allowed.
  The intersection and base-change argument uses neither separatedness nor
  quasi-compactness, so arbitrary irreducible schemes are covered.

Searches for an existing statement (all via the prescribed tools/read-only trees):

- `msearch.py ... leanfinder`: “An irreducible scheme over a field is geometrically
  irreducible iff the spectra of sections of all nonempty affine opens are
  geometrically irreducible”. Eight hits, on integral/reduced schemes and ordinary
  irreducibility; none gives the geometric affine-local equivalence.
- `msearch.py ... loogle`: `AlgebraicGeometry.GeometricallyIrreducible,
  AlgebraicGeometry.IsAffineOpen`. Zero hits.
- `msearch.py ... leansearch`: “Geometric irreducibility is equivalent to geometric
  irreducibility of every nonempty affine open in an irreducible scheme”. Eight hits,
  including `IsAffineOpen`, `reduce_to_affine_nbhd`, `Scheme.affineOpens`, and
  `reduce_to_affine_global`; none states this theorem.
- `msearch.py ... grep`: `geometrically.*irreducib.*(open|cover)|GeometricallyIrreducible`
  under `AlgebraicGeometry/Geometrically`: hits concern the predicate, base change,
  fibres, and geometric integrality. Reading the complete `Irreducible.lean` finds
  the open-immersion inheritance instance, but no affine-local converse or combined
  theorem.
- `rg` for geometric irreducibility in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`
  and `/home/ubuntu/weil-newtargets-shared/lean/Sheaf` found image, product, smoothness,
  generic-fibre and other results. They do not state this affine-local equivalence.
  `grep -rn` for this node id in `WeilConjectures` returned no match.
- Exact proposed theorem names `geometricallyIrreducible_iff_of_nonempty_affineOpens`
  and `geometricallyIrreducible_affineLocal` were searched in Mathlib, the source
  project, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision.

No STATEMENT-DISPUTED issue or node fault was found. Validation uses only the
prescribed single-file `scompile.py` and delivery wrappers.

## Second reading by Q73

Author self-check (the dispatcher brief forbids starting another agent; the
maintainer supplies the independent review). I reread the node, the complete
Lean signature, the definitions of `IsAffineOpen.fromSpec`/`isoSpec`, and the
Stacks source. `Field`, `Scheme.Over`, and `IrreducibleSpace` match the three
hypotheses. The first conjunct uses precisely all nonempty affine opens and
geometric irreducibility of their actual section-ring spectra, with the inherited
structure morphism. In particular, `fromSpec` starts at `Spec Γ(X,U)`, while
`V.ι` in the second conjunct starts at the open subscheme itself. The final
assertion ranges over every nonempty open and is conditional only on geometric
irreducibility of X. No clause is missing and no additional geometric assumption
is present. No mismatch or correction was found during this reading.
