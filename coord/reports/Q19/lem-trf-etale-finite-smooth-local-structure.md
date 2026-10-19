## Worker report

This stage-2 delivery states `AlgebraicGeometry.exists_affine_etale_finite_smooth_local_structure`
in `Sheaf.TraceFormula.EtaleFiniteSmoothLocalStructure`.  It leaves the theorem proof as
`sorry` and does not add a definition.  The item was already split by Q29 (commit
`c4972041b0`); this delivery supplies its Lean statement and leaves the reviewed DAG proof
steps and statement text unchanged.

I read the item node, its Q29 proof steps, all ten statement dependencies, the recorded
bindings and their source declarations/docstrings, the stage-2 brief, stages/2-statements,
the worker role, SETUP, GOAL, coord/STATE, delivery-errors H, and the CompactObject example.
The item has no repair note.  The Q29 split is a stage-1 split, so it does not provide a Lean
statement to attach to this stage-2 delivery.

The theorem has the following Lean shape.  For schemes `Z S : Scheme.{u}`, a morphism
`p : Z ⟶ S` with `[LocallyOfFiniteType p]`, and `z : Z`, it existentially records the finite
natural number `n` equal to the local topological Krull dimension of the canonical fibre point
`p.asFiber z`.  It then existentially records affine schemes `W`, `Y`, `S₁`, points `w`, `y`,
`s₁`, and arrows `b`, `a`, `π`, `h` with exactly the domains and codomains in the node.

Each clause is rendered as follows.

- The input schemes and morphism are `{Z S : Scheme.{u}}`, `(p : Z ⟶ S)`,
  `[LocallyOfFiniteType p]`, and `(z : Z)`.
- The assignment `s = p(z)` is rendered by the explicit terms `p z`; the fibre point is
  `p.asFiber z`, and `n = dim_z(Z_s)` is rendered by
  `∃ n : ℕ, topologicalKrullDimAt (p.asFiber z) = (n : WithBot ℕ∞)`.  This existential is
  needed because Mathlib's dimension value is `WithBot ℕ∞`, while smooth relative dimension
  takes a natural number; it states exactly the finite natural value asserted by the source.
- Affineness of `W`, `Y`, and `S₁` is `IsAffine W ∧ IsAffine Y ∧ IsAffine S₁`.
- The marked points and arrows are bound as `(w : W) (y : Y) (s₁ : S₁)`,
  `(b : W ⟶ Z) (a : S₁ ⟶ S) (π : W ⟶ Y) (h : Y ⟶ S₁)`.
- `b(w)=z`, `π(w)=y`, and `h(y)=s₁` are the three displayed point equalities.
- The diagram identity `p b = a h π` is the categorical equality
  `b ≫ p = π ≫ h ≫ a`.
- Etaleness of `b` and `a` is `Etale b ∧ Etale a`.
- The residue-field maps induced by those arrows are isomorphisms:
  `IsIso (b.residueFieldMap w)` and `IsIso (a.residueFieldMap s₁)`.  These are the canonical
  maps in the direction `κ(z) → κ(w)` and `κ(s) → κ(s₁)`, rather than arbitrary unrelated
  field isomorphisms.
- Finiteness of `π` is `IsFinite π`; the singleton fibre is
  `π ⁻¹' ({y} : Set Y) = ({w} : Set W)`.
- Smooth relative dimension and geometric integrality are
  `SmoothOfRelativeDimension n h ∧ GeometricallyIntegral h`.  Mathlib's latter class is
  geometric integrality after every field-valued base change, hence says precisely that every
  fibre remains integral after every extension of its residue field.
- The final purely transcendental clause is
  `@Algebra.IsPurelyTranscendentalExtension (S₁.residueField (h y))
  (Y.residueField y) _ _ ((h.residueFieldMap y).hom.toAlgebra)`.  The preceding equality
  `h y = s₁` identifies the base with `κ(s₁)`, and the explicit algebra is the canonical
  residue-field map induced by `h`; no arbitrary algebra structure or map is introduced.  The
  predicate is the landed definition from `def-trf-purely-transcendental-extension`, and its
  empty independent set covers the case `r=0`.

The statement uses these dependency declarations.

- `AlgebraicGeometry.Scheme`, `Scheme.Hom`, and `Spec` from
  `Mathlib.AlgebraicGeometry.Scheme` supply schemes and morphisms (`def-pc-scheme`).
- `AlgebraicGeometry.LocallyOfFiniteType` from
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` supplies the finite-type hypothesis
  (`def-weil-finite-type-morphism`).
- `CategoryTheory.Limits.pullback` and the canonical fibre constructions from
  `Mathlib.AlgebraicGeometry.Fiber` realize `def-pc-fibre-product`.
- `AlgebraicGeometry.Scheme.residueField` and
  `AlgebraicGeometry.Scheme.Hom.residueFieldMap` from
  `Mathlib.AlgebraicGeometry.ResidueField` realize `def-weil-residue-field`.
- `topologicalKrullDimAt` from `WeilConjectures.Mathlib.Topology.KrullDimension` realizes
  `def-kun-dimension`.
- `AlgebraicGeometry.IsAffine`/`Spec` from the Mathlib affine-scheme interfaces realize
  `def-weil-affine-spectrum`.
- `AlgebraicGeometry.Etale` from `Mathlib.AlgebraicGeometry.Morphisms.Etale` realizes
  `def-weil-etale-morphism`.
- `AlgebraicGeometry.SmoothOfRelativeDimension` from
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth` realizes `def-sbc-smooth-morphisms`.
- `AlgebraicGeometry.IsFinite` from `Mathlib.AlgebraicGeometry.Morphisms.Finite` realizes
  `def-weil-finite-integral-morphism`'s finite clause.
- `AlgebraicGeometry.IsIntegral` as used by
  `AlgebraicGeometry.GeometricallyIntegral` from
  `Mathlib.AlgebraicGeometry.Geometrically.Integral` realizes `def-pc-integral-scheme` and
  the node's geometric-integrality convention.
- `Algebra.IsPurelyTranscendentalExtension` from the already landed
  `Sheaf.FieldTheory.PurelyTranscendentalExtension` is the canonical declaration for the
  purely transcendental notion.  It is already a DAG node and therefore no duplicate
  definition is written here; the item's reviewed `stmt_deps` is unchanged.

The proof-dependency steps in the Q29 split are represented in the theorem docstring in the
same order: affine reduction and dimension preservation; the refined quasi-finite chart and
smooth affine space; the elementary etale finite-neighbourhood construction; affine shrinking;
the smooth component; elementary etale spreading; fibre-product point and residue-field
identifications; finite pullback; affine refinement and openness; geometric-integrality of
nonempty opens; and final restriction.  The docstring names the source and blueprint id and
records that these are exactly the DAG proof dependencies; no fact is proved in this module.

Searches performed before writing:

- `msearch.py ... grep "local.*structure.*finite|finite.*smooth.*factor|geometricallyIntegral"`
  returned ten nearby Mathlib hits (AffineSpace, Geometrically/Integral, and related files),
  none stating this diagram; verdict no match.
- `msearch.py ... leanfinder "Elementary etale neighborhoods make a finite type morphism
  finite over a smooth scheme with a singleton fibre and purely transcendental residue field"`
  returned standard-smooth and etale declarations only; verdict no match.
- `msearch.py ... leanfinder "A locally finite type morphism of schemes is etale locally finite
  over a smooth morphism with geometrically integral fibres"` returned generic `IsEtale`,
  `IsSmooth`, and permanence declarations only; verdict no match.
- `msearch.py ... leansearch "Local structure theorem finite type schemes finite morphism smooth
  geometrically integral fibres elementary etale neighbourhoods"` returned generic
  `IsFinite`, `IsSmooth`, `IsEtale`, and affine-space declarations only; verdict no match.
- Project searches with `rg` for `finite.*smooth`, `purelyTranscendental`, and the exact item id
  found no pre-existing project theorem for the full assertion.  The exact id occurs only in
  the DAG proof citations and Q29 report.
- The existing DAG node `def-trf-purely-transcendental-extension` and its module were checked
  before use; its definition is the field-generated-by-an-algebraically-independent-set
  predicate, with no duplicate declaration here.

Edge cases checked before writing include `n=0`, the empty independent set for a trivial
purely transcendental residue extension, arbitrary characteristic, nonempty marked fibres,
nonreduced schemes, and arbitrary (not separately restricted) scheme universes.  The singleton
fibre equality forces `w` to be the marked point and does not silently allow an empty fibre;
`GeometricallyIntegral h` retains the source's all-field-extension requirement.

No statement correction or source error was found.  No new node or dependency repair is needed.
The source, Q29's reviewed statement and proof split, and the Lean signature agree clause by
clause.

## Second reading by Q19

I re-read the node statement and the generated Lean signature after compilation.  The only
hypothesis is the locally-finite-type morphism and marked point; the existential dimension
witness is tied to the canonical fibre point.  Every object in the conclusion is introduced once,
and each point equality, diagram equation, affineness, etale, finite, singleton-fibre,
smooth-relative-dimension, geometric-integrality, residue-field-isomorphism, and purely
transcendental clause appears in the signature.  The residue extension uses the canonical
`h.residueFieldMap` algebra and the already landed predicate.  The theorem compiles cleanly
with `scompile.py`; no warning remains other than the expected `sorry` declaration warning.
