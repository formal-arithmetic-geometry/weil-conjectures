## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceConstantDegreeEtaleFinite` states
`AlgebraicGeometry.AlgebraicSpace.finiteLocallyFreeOfDegree_of_constant_geometric_cardinality`.
Its only theorem has proof `sorry`. No definition, dependency module, new node,
or change to the natural-language statement is needed. Only the item's `lean`
record is changed. The source was read in `literature/stacks-project/decent-spaces.tex`,
Tag 07S8, `lemma-quasi-compact-reasonable-stratification`, and its scheme input
in `more-morphisms.tex`, Tag 07RY, `lemma-stratify-flat-fp-lqf-universally-bounded`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| S a scheme | `{S : Scheme.{u}}` |
| X an algebraic space over S | `(X : AlgebraicSpace S)` |
| W a scheme, with its induced S-structure | `(W : Over S)`; the scheme is `W.left`, with structure map `W.hom` |
| f : W → X | `(f : yoneda.obj W ⟶ X.obj.obj)`, the natural-transformation form of a scheme-to-space morphism |
| representable étale | `(hf : IsEtale f)`, the recorded scheme-test definition, which includes representability |
| quasi-compact on scheme tests | `hqc : IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left) f` |
| separated, its representable diagonal a closed immersion | `hsep : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) (pullback.diagonal f)`; this is the diagonal itself, rather than an additional assumption on W or S |
| integer d ≥ 0 | `(d : ℕ)` |
| every algebraically closed field Ω and geometric point Spec Ω → X | `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (b : Spec (CommRingCat.of Ω) ⟶ S) (a : yoneda.obj (Over.mk b) ⟶ X.obj.obj)`; `b` is precisely the composite structure map to S |
| geometric fibre W ×_X Spec Ω | `(U : Over S) (p : U ⟶ Over.mk b) (q : yoneda.obj U ⟶ yoneda.obj W)` with `IsPullback q (yoneda.map p) f a`; this square represents the scheme fibre product, by the recorded algebraic-space scheme-test interface |
| exactly d points | `Nonempty (U.left ≃ Fin d)`; this is existence of a bijection of underlying point sets, without a chosen enumeration, and includes finiteness even at d = 0 |
| finite locally free of degree d on every scheme test | `IsRepresentableWith (fun _ _ p ↦ p.left.IsFiniteLocallyFreeOfDegree d ∧ Etale p.left) f`, first conjunct of the tested property |
| remains étale | `Etale p.left`, the second conjunct of the same property |
| no Noetherianity or finite type over S | no such binders, typeclasses or hidden structure-map assumptions occur |

The geometric cardinality hypothesis ranges over every representing square. This is
exactly the usual geometric-fibre condition because representability follows from
`hf` and any two representing squares are uniquely isomorphic. Conversely, applying
it to any chosen representative recovers the usual fibre cardinality. `IsPullback`
asserts the actual universal property, not merely commutativity of a square.
Similarly `IsRepresentableWith` supplies a representing scheme with the stated
property on each test; this is invariant under changing the representing scheme.

All schemes and tests use the same arbitrary universe `u`, as in the recorded
`AlgebraicSpace S` interface. In particular geometric fields also use `Type u`:
residue fields and their algebraic closures exist in that universe, so the tests
are nonvacuous. There is no independent smaller field universe. Quantifying `W`
as `Over S` adds no mathematical restriction: any morphism from W to an S-space
has its composite structure morphism W → S.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (recorded `def-pc-scheme`).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace.IsEtale`, and
  `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith`
  (recorded `def-trf-algebraic-space`). These give the actual presheaf model and
  scheme-test pullback squares. No second definition of representability is introduced.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`
  (recorded `def-weil-etale-morphism`), used by `IsEtale` and in the conclusion.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (recorded `def-weil-closed-immersion`).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, with inline spectrum
  maps as prescribed by `def-weil-geometric-point`. Also read the recorded
  `Scheme.SpecToEquivOfField` signature and docstring in
  `Mathlib.AlgebraicGeometry.ResidueField`; the residue-field equivalence need
  not occur in this signature.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace` and
  `AlgebraicGeometry.AlgebraicSpace.etale_fibreProduct_isScheme`, imported for
  the scheme-test fibre-product interpretation and the proof plan of
  `lem-trf-space-fibre-products-etale-covers`. The signature uses the same
  Yoneda `IsPullback` representation as these recorded declarations.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFreeOfDegree`, including its
  `IsFiniteLocallyFree` parent and `fiberDegree_eq`, exactly as recorded by
  `def-pc-finite-locally-free`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`:
  `AlgebraicGeometry.QuasiCompact`, whose signature was read: inverse images
  of compact open subsets are compact.

The other stated proof dependencies are plain imports: the Mathlib finite,
affine, affine-scheme and ring-finiteness modules; and the recorded upstream
`EtaleFibreDiscreteSeparablePoints`, `FiniteFiberDegreeBaseChange`,
`FlatFpLqfBoundedStratification` and `UnramifiedQuasiFinite` modules.
The closed-immersion and quasi-compact base-change modules are already public
statement imports. Every proof step in the DAG appears in the theorem docstring,
including ordinary-fibre finiteness, geometric degree comparison, and the
stratification universal property on all residue points and then the identity test.

Edge cases checked before writing:

- d = 0: equivalence with `Fin 0` requires the geometric fibre to be empty;
  it cannot accidentally accept an infinite fibre. The section algebra is zero,
  so the same degree comparison and stratification argument applies.
- W empty with nonempty X: the degree hypothesis holds for d = 0 only; the
  empty test projection is finite locally free of degree zero and étale.
- X empty: a map W → X forces W empty; every test to X is empty. The degree
  condition and the rank condition are both vacuous for every d, as required.
- Empty scheme tests: their represented fibre is empty; fibre rank equality
  has no target points to test. No nonemptiness assumption is introduced.
- Nonreduced tests and arbitrary non-Noetherian bases: the source's universal
  property is set-theoretic on the target and applies to arbitrary tests. The
  Lean adds neither reducedness nor a finiteness hypothesis on the base.
- Positive characteristic and d = 1: all characteristics and every natural
  degree are retained. No separable-closure choice is part of the statement.

Searches performed through the prescribed wrapper and direct repository reads:

- `msearch.py ... leanfinder "A quasi compact separated representable etale morphism to an algebraic space with exactly d geometric fibre points is finite locally free of degree d"`:
  eight hits, including `IsFinite`, `Scheme.Etale`, and étale permanence
  declarations; none is this implication or an algebraic-space version.
- `msearch.py ... loogle "AlgebraicGeometry.Etale, AlgebraicGeometry.IsFinite"`:
  one hit, `AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt`, an
  étale-neighbourhood splitting result, not this statement.
- `msearch.py ... grep "constant.*degree|card.*[Ff]ib|[Ff]ib.*card" AlgebraicGeometry`:
  zero hits in that wrapper's Mathlib search.
- `msearch.py ... leansearch "A quasi compact separated etale morphism with constant finite geometric fibre cardinality is finite locally free of that degree"`:
  eight hits giving definitions, finite-implies-quasi-finite and permanence
  results, with no constant-cardinality finiteness implication.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for constant degree,
  constant étale, fibre cardinality and the item ID: many unrelated sheaf and
  degree results. Narrowed searches in the algebraic-geometry sources found
  the bounded stratification and maximal-degree-locus theorem, and
  `AlgebraicSpaceDenseSchemeOpen` citing this still-unstated item in its proof.
  Read the latter and the finite-locally-free definitions; none duplicates
  this theorem. Searching the exact item ID in upstream `WeilConjectures`
  found no declaration. Searching the proposed theorem name in both source
  roots and `dag/lean_names_upstream.json` found no collision.

No `STATEMENT-DISPUTED` issue, statement correction, or dependency-record fault
was found. The initial module compiled cleanly with `scompile.py` on the server;
expected sorry warnings alone are allowed. The final module is compiled again
by the prescribed dry run and delivery checks.

## Second reading by Q06

Performed a separate manual rereading of the node, source text and complete
module after the first successful compile. This was the dispatched worker's
own second pass; no other agent was started, as required by the brief.

Checked each row of the correspondence table against the actual binders:
`S`, `X`, `W`, `f`, `hf`, `hqc`, the diagonal in `hsep`, `d`, the algebraically
closed geometric tests in `hdegree`, and both conclusion conjuncts. The
pullback orientation is correct: q goes from the representing scheme into W,
and `yoneda.map p` goes to Spec Ω, so its bottom arrows are f and a. The
underlying points of U, not the Ω-valued sections of U, are counted.
No hypothesis is supplied by a local instance or notation. `autoImplicit false`
checks that all variables are bound. The source's arbitrary base and empty
cases remain present. No mismatch of statement was found. Added explicit
plain imports for the affine-scheme, affine-morphism and ring-finiteness
modules appearing in the recorded proof dependencies; no signature change
was needed.
