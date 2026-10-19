## Worker report

The module `Sheaf.AlgebraicGeometry.FineLogStalkChartSpreading` states
`AlgebraicGeometry.EtaleLogStructure.exists_affine_chart_of_isStalkChart`, with
`sorry` as its entire proof. It introduces no definitions and changes only the
item's `lean` record. Source read: ILO, Exposé VI 1.1, printed p. 69, and 3.7(a),
printed p. 75, especially the last sentence extending the splitting restricted
to the characteristic monoid to a chart near the geometric point. The item
isolates the fine-log input to that sentence. Its seven proof steps are carried
in the theorem docstring, including the construction of both local inverses.

Clause-by-clause rendering:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Locally Noetherian scheme X | `{X : Scheme.{u}} [IsLocallyNoetherian X]` |
| Log structure with its map to the multiplicative structure sheaf and the log unit condition | `M : EtaleLogStructure X`; its inherited `alpha`, `reflectsUnits`, and `unitsBijective` are precisely the recorded interface |
| Fine, without saturation: étale-locally a chart from a finitely generated integral commutative monoid | `hM` quantifies over every algebraically closed field and geometric point, and gives an étale `V`, a lift `_v`, a commutative monoid `Q`, a map `q`, `Monoid.FG Q`, injectivity of `Algebra.GrothendieckGroup.of`, and `M.IsChart V q` |
| Specified geometric point | `{Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)` |
| A is the étale ring stalk; M_x is the geometric monoid stalk | `M.toEtalePrelogStructure.stalk t`, and the strict-local ring inside the recorded `M.IsStalkChart t h` |
| Finitely generated integral commutative monoid P | `{P : Type u} [CommMonoid P]`, `hPfg : Monoid.FG P`, and `hPint : Function.Injective (Algebra.GrothendieckGroup.of (M := P))` |
| Specified monoid homomorphism h | `h : P →* M.toEtalePrelogStructure.stalk t` |
| Pushout map [p,u] maps to h(p)u and is an isomorphism | `hh : M.IsStalkChart t h` |
| E is exactly the inverse image of the ring units, with the prescribed identification | `IsStalkChart` uses the existing `divisorialChartCongruence` for `(stalkAlpha t).comp h`, range-restricted without changing any value; its generating relations are `(e,1) ∼ (1,alpha(h(e)))` whenever that value is a unit |
| Affine pointed étale neighbourhood | `W : X.Etale`, `w : (Scheme.pointSmallEtale t).fiber.obj W`, and `IsAffine W.left` |
| A chart from the same P to the restricted log structure | `hW : P →* M.monoidSheaf.obj.obj (op W)` and `M.IsChart W hW` |
| The entire prescribed germ, under the canonical identification | `(M.toEtalePrelogStructure.germ t W w).hom.comp hW = h` |

`IsStalkChart` is the existing exact pushout-isomorphism interface: the product
map `h.coprod (M.unitsIn t)` is surjective and its kernel congruence is exactly
the congruence defining the pushout. Thus no arbitrary comparison is substituted
for the canonical map. A map from `P` to the sections on `W` specifies the chart
of the restricted sheaf by restriction to all étale objects over `W`.
`IsChart` checks its stalk-chart property at all geometric points of `W`.
The germ equation uses the actual colimit injection at `(W,w)`, so the canonical
identification of the restricted stalk with the original stalk is built into
the equation rather than supplied as an arbitrary isomorphism.

Fineness is expanded in `hM` using the existing chart, finite-generation, and
group-completion notions. No additional notion, private copy of the log
structure, or separate fine-log predicate is defined. In particular the fs
predicate in the dependency is not used as the hypothesis: it would impose
saturation absent from this node.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`:
  `AlgebraicGeometry.EtaleLogStructure`, `EtalePrelogStructure.stalk`,
  `EtalePrelogStructure.germ`, `EtalePrelogStructure.stalkAlpha`,
  `EtaleLogStructure.unitsIn`, `EtaleLogStructure.IsStalkChart`, and
  `EtaleLogStructure.IsChart`.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`:
  `AlgebraicGeometry.pointedEtaleStalk`, `pointedEtaleStalkDiagram`, and
  `pointedEtaleGerm`, used through the log interface. Its specific
  commutative-monoid colimit instance is already provided.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points are
  the recorded inline scheme morphisms. The full signature and docstring of
  `Scheme.SpecToEquivOfField` in Mathlib's `ResidueField` were also read.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale` and
  `Scheme.Etale`, used through `X.Etale`.
- `Mathlib.GroupTheory.Finiteness`: `Monoid.FG` is the existing finite-generation
  notion, equivalent to a finite set whose submonoid closure is top.
- The integral condition uses the existing canonical group-completion map
  `Algebra.GrothendieckGroup.of`, exactly as the log dependency does.

The module privately imports the recorded stated proof dependencies:
`WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization` (source read with
`scompile.py --source`, including `AffinePointedEtaleNeighborhood.initial_ι`),
`Mathlib.AlgebraicGeometry.Sites.AffineEtale`,
`Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit`,
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, and
`Sheaf.TraceFormula.FgCommutativeMonoidFinitePresentation`. The remaining stated
proof dependencies are already publicly imported through the log interface
(étale points, Noetherian schemes, and charts). The associated-log universal
property node is stated by the dependency module of this delivery
(`Sheaf.AlgebraicGeometry.AssociatedLogUniversalStalks`), which the item module
imports privately as a proof dependency (added by the maintainer's reviewer); none
of its objects are needed to state this item.

Edge cases checked by reading the complete signature:

- A trivial monoid, the empty finite generating family, and unit-valued h are
  permitted. There is no positivity, nonunit, or sharpness hypothesis.
- Non-saturated integral monoids and monoids with torsion in their group
  completion are permitted: only canonical injectivity and finite generation
  are assumed, for both `P` and local `Q`.
- Units need not form a finitely generated group. The pushout condition uses
  every strict-local unit, and the proof separates them from finite chart data.
- The empty scheme cannot have the supplied geometric point; no unjustified
  nonemptiness of X is assumed separately. W is automatically nonempty because
  w is a lift of a spectrum of a field.
- The conclusion concerns a chart on all of W, not only an isomorphism at the
  one marked stalk, and the equality is of homomorphisms on all of P.
- All schemes, geometric fields, and chart monoids live in the common arbitrary
  universe `u` required by the recorded dependency interfaces. Every universe
  and variable is bound explicitly, with `autoImplicit false`.

Searches for an existing statement (all through the prescribed tools):

- LeanFinder: `A chart of a fine log structure at a geometric stalk extends to
  a chart on an affine pointed etale neighborhood`. Eight hits, including
  `spread_out_of_isGermInjective'`, `exists_lift_of_germInjective`, and the étale
  category. These concern scheme morphisms and ring maps, not log monoid charts;
  none states this result.
- Loogle: `"LogStructure"`: zero hits.
- Mathlib grep: `LogStructure|logarithmic.*chart|stalkChart|chart_spreading`:
  zero hits.
- LeanSearch: `A specified chart of a fine logarithmic stalk extends to an
  affine pointed etale neighborhood`: eight hits about manifold charts and
  locally ringed-space stalk maps, no matching statement.
- Direct rg with the same logarithmic patterns in `WeilConjectures` and
  `lean/Sheaf`: the latter supplies the reused log interface; no chart-spreading
  theorem. Upstream has no matching log-structure theorem.
- The prescribed upstream grep for this node's ID: no hits.
- Exact declaration-name rg over Mathlib, upstream `WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision.

No statement correction, disputed statement, dependency repair, or new node is
needed. The final module passed `scompile.py Q150
lem-trf-fine-log-stalk-chart-spreading <module path>` with exit status zero:
both sandbox and library-path checks completed without errors or warnings.
The source has one `sorry`, no lines over 100 characters, and a signature
matching the node record. The delivery's only node-field change is `lean`.

## Second reading by Q150

This is the author's separate self-check, not an independent review; the
maintainer supplies the independent review under this dispatcher's brief.
I reread the node and complete theorem together. The `hM` binder is fineness,
not fs: it contains finite generation and integrality with no saturation.
`hPfg` and `hPint` impose exactly the same requirements on the specified P.
The log condition comes from `EtaleLogStructure`, and `hh` is precisely the
canonical pushout isomorphism, not merely an arbitrary bijection of carriers.
I checked the actual congruence definition: its unit-identification generators
generate also the node's relations after multiplying by arbitrary `(p,u)`.
The conclusion includes affinity, a lift of this very geometric point, a chart
on the whole neighbourhood, and equality with this very h after taking germs.
It therefore does not just extend an unspecified characteristic chart.
During this reading the finite-generation formulas were replaced by Mathlib's
`Monoid.FG`, avoiding needless expansion of an existing notion. No hypothesis
or conclusion changed, and no mismatch with the node remains.

## Dependency modules

The returned review identified `lem-trf-associated-log-universal-stalks` in this item's
`proof_deps` as lacking a Lean declaration. The DAG node already exists, so this is a
§1(B) dependency-module repair rather than a new node. I copied its complete node
record into `dag/nodes/sec-trace-formula/lem-trf-associated-log-universal-stalks.json`
and changed only its `lean` field. The supplied module is
`lean/Sheaf/AlgebraicGeometry/AssociatedLogUniversalStalks.lean`, declaring
`AlgebraicGeometry.associatedLog_universal_stalks` together with the real associated
log presheaf, restriction, presentation, stalk, and chart helper interfaces. The
recorded dependency had no usable Lean declaration; the module therefore states its
full construction and theorem interface, with data-bearing definitions and named
`sorry` theorems carrying source and proof docstrings. The item’s existing theorem
uses this declaration in proof steps 3, 5, 6, and 7; no statement or `proof_deps`
entry was changed.
