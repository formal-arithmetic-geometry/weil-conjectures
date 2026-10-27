## Worker report

The module `Sheaf.AlgebraicGeometry.FlatGeometricFibreOpenCriterion` states the
node without changing its mathematical statement or dependencies. It contains
two theorems, both with exactly `sorry` for their proofs:

- `AlgebraicGeometry.isOpenImmersion_isIso_of_geometric_fibres_of_flat` states
  the two tests under the general flat-source hypotheses.
- `AlgebraicGeometry.isOpenImmersion_isIso_of_geometric_fibres_of_smooth` states
  both tests for locally finitely presented maps between smooth S-schemes.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Schemes S, X, Y | `{S X Y : Scheme.{u}}` |
| Structure maps X → S and Y → S | `(p : X ⟶ S) (q : Y ⟶ S)` |
| S-morphism f : X → Y | `(f : X ⟶ Y) (hcomm : f ≫ q = p)` |
| X → S flat | `[Flat p]` |
| X → S locally of finite presentation | `[LocallyOfFinitePresentation p]` |
| Y → S locally of finite type | `[LocallyOfFiniteType q]` |
| f locally of finite presentation | `[LocallyOfFinitePresentation f]` |
| Every algebraically closed field Ω and geometric point s | `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S), ...` |
| Induced map X ×_S Spec Ω → Y ×_S Spec Ω | `((Over.pullback s).map (Over.homMk (U := Over.mk p) (V := Over.mk q) f hcomm)).left` |
| All geometric fibre maps open immersions imply f open | First conjunct, with `IsOpenImmersion` on those canonical maps and conclusion `IsOpenImmersion f` |
| All geometric fibre maps isomorphisms imply f an isomorphism | Second conjunct, with `IsIso` on those canonical maps and conclusion `IsIso f` |
| Both tests between smooth S-schemes | Second theorem replaces the three general structure-map hypotheses with `[Smooth p] [Smooth q]`, retaining local finite presentation of f and both conclusions |
| Empty schemes and fibres allowed | No `Nonempty`, surjectivity, or inhabited-point hypotheses |
| Arbitrary base, without reducedness or Noetherianity | No hypotheses of either kind on S (nor on X or Y) |

The two implications have separate hypotheses, as the node requires. The open
test is not assumed in the isomorphism test. The smooth specialization does not
retain extra flatness or local-finiteness binders. Universes are explicit: Ω and
the schemes use the same arbitrary `u`, as in the recorded geometric-point
interface; in particular the algebraic closure of every residue field is an
available test field. There is no independent smaller test-field universe.

The full signatures and docstrings of all eight statement dependencies were
read. Their declarations are reused directly:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and its morphisms `Scheme.Hom`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat` (stalkwise equivalence `Flat.iff_flat_stalkMap`).
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`; only the locally finite type notion
  is used here, so quasi-compactness is not assumed.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, and the
  universal `pullback.lift` used by `Over.pullback`.
  `Mathlib.AlgebraicGeometry.Pullbacks` supplies scheme pullbacks.
- `def-weil-geometric-point`: `Mathlib.FieldTheory.IsAlgClosed.Basic`,
  `IsAlgClosed`, used with `Field Ω` and the actual morphism from `Spec Ω`.
  The alternate residue-field encoding is `Scheme.SpecToEquivOfField`, read in
  `Mathlib.AlgebraicGeometry.ResidueField`; no new point notion is introduced.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`.

`CategoryTheory.Over.homMk` (in `Mathlib.CategoryTheory.Comma.Over.Basic`) uses
the supplied commutative triangle. `CategoryTheory.Over.pullback` (in
`Mathlib.CategoryTheory.Comma.Over.Pullback`) has object `Over.mk
(pullback.snd g.hom s)` and map given by `pullback.lift` of the first projection
composed with the original arrow and the second projection. Thus its underlying
map is precisely the node's induced map on fibre products, with the prescribed
two projections; it is not an arbitrary comparison arrow.

Already recorded proof dependencies are imported with ordinary `import`,
including the upstream field-extension fpqc theorem, fpqc open-immersion
descent, unramified geometric-fibre criterion and upstream étale radicial open
criterion. Mathlib modules supply the fpqc covering axioms and representable
descent, open-immersion base change, algebraic closure, universal injectivity,
étaleness, and smooth-flat instances. The proof dependency
`lem-sfb-relative-flat-fibre-test` has neither a Lean record nor a Mathlib match;
it is not needed to type this statement, and its future proof import is left
for the maintainer. Its role is recorded explicitly in proof step 2. All seven
proof steps of the node are carried in the two theorem docstrings.

Sources checked locally: `more-morphisms.tex`, `lemma-morphism-between-flat`
(Tag 039E), lines 4682 ff.; `morphisms.tex`,
`lemma-etale-flat-etale-fibres` (Tag 02GM), lines 8214 ff.; `etale.tex`,
`theorem-etale-radicial-open` (Tag 025G), lines 1370 ff. The first source has
exactly flat and locally finitely presented source, fibrewise flat maps, and
locally finite type target, without a Noetherian hypothesis. The latter sources
give the stated recognition route.

Edge cases checked before writing and again against the compiled statements:

- Empty X gives an open immersion to any Y; empty fibres do not require
  choosing source points. The isomorphism hypothesis cannot hold if a target
  geometric fibre is nonempty and the source fibre is empty.
- Empty Y forces empty X for an actual f; both conclusions remain valid.
  Empty S likewise forces both schemes empty.
- The identity over a nonreduced base satisfies the hypotheses and conclusions;
  no reducedness is smuggled into the field tests.
- The reduction `Spec k → Spec k[ε]/(ε²)` over that base has misleading
  geometric fibres but fails the required flatness of p; the flatness binder
  is present.
- Neither quasi-compactness nor separatedness is imposed. The smooth test has
  only the smoothness and local-presentation hypotheses actually stated.

Searches made with the prescribed `msearch.py Q99
lem-sfb-flat-geometric-fibre-open-criterion` wrapper:

- LeanFinder: `A locally finitely presented morphism of schemes with flat
  source over a base and open immersions on every geometric fibre is an open
  immersion`. Eight hits, including `UniversallyOpen.of_flat` and
  `IsOpenImmersion.of_flat_of_mono`; none states this relative fibre test.
- Loogle: `"IsOpenImmersion", "Flat"`. Four hits: flatness of open immersions,
  fpqc descent, and the flat monomorphism criterion; none is this statement.
- Mathlib grep: `geometric.*(open|iso)|fibre.*(open|iso)|fiber.*(open|iso)`
  in `AlgebraicGeometry`. Twenty-five reported hits, concerning geometry of
  fibres, connectedness, and unrelated canonical fibre isomorphisms; no match.
- LeanSearch: `A morphism between flat finitely presented schemes over a base
  is an open immersion if every geometric fibre map is an open immersion`.
  Eight hits, including `IsOpenImmersion.of_flat_of_mono`, ordinary definitions
  and the stalk criterion; no match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for geometric/fibre open
  and isomorphism criteria found sheaf-stalk tests and canonical fibre
  comparisons, not this scheme-morphism statement. Narrower searches for
  `geometric_fibres`, `geometricFibres`, and open-immersion/fibre combinations
  likewise found no duplicate. Searching the exact node id in
  `lean/WeilConjectures` found no declaration. Both proposed declaration names
  were absent from Mathlib, both project roots, and `dag/lean_names_upstream.json`.

Validation: prescribed `scompile.py` compiled the sandbox and real module
separately on the server, successfully (2.4 s and 9.6 s). No errors or warnings
were printed. Both public theorems have whole proofs `by sorry`; no definition,
helper theorem, new node, dependency repair, or statement correction is needed.
No statement dispute was found.

## Second reading by Q99

This is the dispatcher's single worker's own second reading; the maintainer's
independent review follows delivery. I reopened the node and the complete Lean
module and compared both theorem signatures to the node clause by clause.
The general theorem retains p flat and locally finitely presented, q locally
finite type, f locally finitely presented, and the equation f ≫ q = p. I read
the `Over.pullback` implementation: its left arrow is the canonical map between
the two scheme pullbacks along the same s, with f on the first coordinate and
the identity on the field coordinate. Each universal hypothesis explicitly
binds Field Ω, IsAlgClosed Ω, and s. The two conjuncts have separate antecedents
and conclude exactly `IsOpenImmersion f` and `IsIso f`. The second theorem
states both tests with Smooth p and Smooth q and local finite presentation of f;
it adds no flatness assumption. No nonemptiness, Noetherianity, reducedness,
finite type in place of locally finite type, or quasi-compactness occurs.
The proof docstrings cover steps 1–6 and the smooth step 7 respectively. No
mismatch was found and no mathematical statement was changed.
