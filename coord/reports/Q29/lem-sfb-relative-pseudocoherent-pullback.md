## Worker report

The module `Sheaf.AlgebraicGeometry.RelativePseudoCoherentPullback` states
`AlgebraicGeometry.Scheme.isMPseudoCoherentRelativeTo_derivedPullback`, with `sorry`
as its entire proof. It introduces no definitions and makes no statement correction.
The source is Stacks Project, More on Morphisms, Tag 09US,
`lemma-pull-relative-pseudo-coherent` (read in `more-morphisms.tex`, lines 17155ff).

Hypothesis and conclusion correspondence:

- Schemes X → Y → S: `{X Y S : Scheme.{u}} (h : X ⟶ Y) (f : Y ⟶ S)`.
  The structure map X → S is the composite `h ≫ f`, so the required compatibility
  is built into the notation and no independently supplied map needs an extra equation.
- All three maps locally of finite type: `[LocallyOfFiniteType h]`,
  `[LocallyOfFiniteType (h ≫ f)]`, and `[LocallyOfFiniteType f]`.
- O_X[0] pseudo-coherent relative to Y: `hOX : IsPseudoCoherentRelativeTo h
  ((DerivedCategory.singleFunctor (SheafOfModules.{u}
  (moduleRings X.toRingedSpace)) 0).obj
  (SheafOfModules.unit (moduleRings X.toRingedSpace)))`.
  Mathlib's unit is the structure module, and its singleFunctor places that module
  in precisely degree zero. The relative predicate quantifies over every integer,
  allowing the covers and embeddings to vary with the degree.
- Every integer m: `(m : ℤ)`, without a sign restriction.
- Every K in D(O_Y): `(K : schemeDerivedCategory Y)`, the full unbounded module
  derived category, without a QCoh subcategory or a boundedness binder.
- K relatively m-pseudo-coherent over S: `hK : IsMPseudoCoherentRelativeTo f m K`.
- Lh* K relatively m-pseudo-coherent over S: the conclusion is
  `IsMPseudoCoherentRelativeTo (h ≫ f) m ((derivedPullback h).obj K)`.
  Its degree is exactly the input m.
- The universally quantified `HasDerivedCategory.{w}` instance binder is the common
  localization infrastructure required by the recorded relative-pseudo-coherence
  definition, including all its affine charts. Universes u and w are explicit and
  independent, and `set_option autoImplicit false` forbids unbound implicits.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- The convention node `def-pc-morphism-conventions` directs consumers to the actual
  property declarations. Here that is `AlgebraicGeometry.LocallyOfFiniteType`,
  from `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, whose full affine-open
  definition was read.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory`, on the shared `SheafOfModules`
  category. The QCoh property in that module is deliberately not a hypothesis.
- `Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex`:
  `AlgebraicGeometry.Scheme.IsMPseudoCoherentRelativeTo` and
  `AlgebraicGeometry.Scheme.IsPseudoCoherentRelativeTo`. Both definitions and
  their docstrings were read in full; their recorded interfaces are usable.
- `WeilConjectures.AlgebraicGeometry.DerivedPullback`:
  `AlgebraicGeometry.derivedPullback`, the transported canonical derived module
  pullback, including its K-flat characterization. No arbitrary functor is supplied.
- Mathlib's `DerivedCategory.singleFunctor` and `SheafOfModules.unit` supply
  the existing canonical encoding of O_X[0]; no new notion or node is needed.

All recorded proof-dependency modules are imported privately, as prescribed.
The three proof dependencies with no recorded Lean declaration are
`lem-sfb-relative-pseudocoherence-all-affine-charts`,
`lem-sfb-relative-pseudocoherence-local-on-source`, and
`lem-sfb-relative-pseudocoherence-flat-base-change`; they are named in the proof
plan but have no module to import. Mathlib proof leaves are imported through
FiniteType, AffineSpace, ClosedImmersion and Flat. The docstring follows all six
accepted proof steps: affine reduction, polynomial chart factorization, nonpositive
finite-free model, relative flat base change, closed projection formula and tensor
filtration, and assembly from the composite chart. No proof has been supplied.

Edge cases checked before writing:

- Empty source: every chart condition over source points is vacuous, and the
  statement imposes no nonemptiness binder. Empty base forces empty sources and
  causes no excluded case.
- Zero K: its derived pullback is zero and satisfies every degree of relative
  pseudo-coherence; no nonzero hypothesis appears.
- Identity h and arbitrary open immersions are included, and the statement does
  not impose properness, flatness or finite Tor dimension on h.
- Negative, zero and positive m are all admitted, including the exact same cutoff
  in the output. No uniform covers over all m are required.
- An arbitrary complex K may have non-quasi-coherent cohomology. The source's
  proof observes a local upper bound as a consequence of relative m-pseudo-coherence,
  so there is no need to add a separate boundedness assumption. Finite-degree
  pseudo-coherence in the recorded dependency includes the needed local
  approximation condition. Nothing restricts K to a bounded derived category.

Searches for existing declarations:

- `msearch.py ... leanfinder` with query "Derived pullback preserves m pseudo
  coherent complexes relative to a base when the structure module is relatively
  pseudo coherent": eight hits, comprising ordinary module pullback,
  PresheafOfModules.pullbackObjIsDefined, and pullback pseudofunctor coherence;
  none states relative derived m-pseudo-coherence.
- `msearch.py ... leansearch` with query "Relative m pseudo coherence of complexes
  preserved by derived pullback along a pseudo coherent scheme morphism": eight
  hits on ordinary module pullback, functor composition, stability under base change,
  and quasi-compact covers; none states the theorem.
- `msearch.py ... loogle '"PseudoCoherent"'`: zero hits.
- `msearch.py ... grep 'pseudo.?coher.*pull|pull.*pseudo.?coher'`: zero Mathlib hits.
- `rg -n 'relative.*[Pp]seudo|[Pp]seudo.*[Rr]elative' lean/WeilConjectures lean/Sheaf`
  finds the relative definition and the existing closed-support theorem, not this
  pullback assertion. Searching the intended theorem name in both source roots
  gives no declaration. A grep for the item id in `lean/WeilConjectures` gives
  no hit. The upstream-name index gives no matching theorem name either.

No STATEMENT-DISPUTED fault was found. The source's printed tensor-filtration-tail
inequality error is already handled by the accepted proof split; this delivery
preserves that split and the node's statement verbatim.

Validation: the prescribed `scompile.py` compiled the delivered module successfully
against the live library (sandbox 2.4 s, library 1.9 s), with no errors or unexpected
warnings. The prescribed `deliver2.py --no-push` then passed server preflight and
compilation (dry-run commit d82f40ce644). The final delivery uses the same statement.

## Second reading by Q29

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
