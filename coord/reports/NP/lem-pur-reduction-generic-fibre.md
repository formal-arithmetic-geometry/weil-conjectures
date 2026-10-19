## Worker report

The module `Sheaf.AlgebraicGeometry.ReductionGenericFibre` states
`AlgebraicGeometry.Scheme.Hom.reduction_generic_fibre`, with its entire proof `sorry`.
The node is unchanged except for its `lean` record. No new definitions, dependency
modules, statement corrections, or disputed statements are needed.

Source read: `literature/stacks-project/more-morphisms.tex`, Tag 054Z,
`lemma-reduction-generic-fibre`, statement and proof, lines 6685–6722.
The source states the result for arbitrary scheme morphisms and a generic point of
an irreducible component, without additional assumptions.

Hypotheses and clauses:

- Schemes Z and T: `{Z T : Scheme.{u}}`, with the universe explicitly declared.
- Any morphism h: Z → T: `(h : Z ⟶ T)`, with no property instances imposed.
- A point η of T: `(η : T)`.
- η is generic in an irreducible component: `hη : closure ({η} : Set T) ∈
  irreducibleComponents T`. This is precisely the assertion that its closure is an
  irreducible component; no irreducibility assumption is imposed on T itself.
- The fibre of Z_red → T is `(Z.nilradical.subschemeι ≫ h).fiber η`.
- The reduction of Z_η is `(h.fiber η).nilradical.subscheme`.
- The identification is an actual scheme isomorphism, the existential `e` between
  these two schemes.
- The canonical map to Z_η is obtained by following `e.hom` with the reduction
  inclusion `(h.fiber η).nilradical.subschemeι`. The first equation gives its
  projection to Z as the source fibre projection followed by `Z.nilradical.subschemeι`.
- The second equation gives its projection to Spec κ(η) as the source fibre
  structure map, using `fiberToSpecResidueField`. Thus e is over κ(η).
  Together the two equations determine the composite uniquely by the pullback
  universal property, so the statement identifies the canonical map, rather than
  asserting only an abstract isomorphism.
- No finite type, reducedness, flatness, nonempty fibre, quasi-compactness,
  Noetherian, or irreducible-base assumption is present.

Statement dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `AlgebraicGeometry.Scheme.Hom` (scheme structure and morphisms).
- `def-weil-irreducible-components`: its Mathlib match is `irreducibleComponents`
  in `Mathlib.Topology.Irreducible`, defined as maximal irreducible subsets.
  Read also `IsIrreducible` and the generic-point definition in `Topology/Sober`:
  `IsGenericPoint η C` means `closure {η} = C`.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `AlgebraicGeometry.Scheme.Hom.fiber`, `fiberι`, `fiberToSpecResidueField`.
  Read their complete definitions and docstrings: the fibre is the pullback along
  `T.fromSpecResidueField η`, with the two pullback projections.
- `def-weil-pbc-scheme-reduction`: `AlgebraicGeometry.Scheme.nilradical` in
  `Mathlib.AlgebraicGeometry.IdealSheaf.Basic` (radical of the zero ideal sheaf),
  and `AlgebraicGeometry.Scheme.IdealSheafData.subscheme` and `subschemeι` in
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.

The statement imports are public; extra imports for the node's proof are private:
`Mathlib.AlgebraicGeometry.Pullbacks`, `Mathlib.RingTheory.Localization.BaseChange`,
`Mathlib.RingTheory.LocalRing.ResidueField.Fiber`, and
`Mathlib.RingTheory.KrullDimension.Zero`. These expose the recorded affine-chart,
localization, residue-field, and minimal-prime proof dependencies. Scheme, affine
opens, prime-spectrum components, and localization-at-prime modules are also
available transitively from these imports. The docstring records all five proof
steps, including the canonical quotient calculation and gluing.

Edge cases checked:

- Empty Z or empty fibre: the two reduced schemes and fibres are empty; the
  projection equations remain valid. The zero ring chart calculation applies.
- Empty T: there is no point η, as in the source; no artificial nonempty condition
  is added to the theorem.
- Reducible T: η is required only to be generic in one component.
- Nonreduced T (e.g. dual numbers over a field): the maximal ideal of the minimal
  prime localization is nil, and the proof's J ⊆ K calculation applies.
- Arbitrary, even non-finitely generated nilradicals: the argument only uses a
  finite sum for each particular element, with no uniform nilpotence exponent.
- Z already reduced: its generic fibre is reduced by the source's localization
  argument. No flatness or finite type condition is needed.
- No characteristic restriction; both schemes live in arbitrary explicit universe u.

Searches for an existing declaration:

- `msearch.py` LeanFinder, query “Reduction of schemes commutes with the fibre over
  a generic point of an irreducible component”: eight results on generic points,
  fibres, and stalks, including `genericPoints.component_ofComponent` and
  `Scheme.Hom.fiberToSpecResidueField_apply`; none states this reduction comparison.
- `msearch.py` Loogle, query `"fiber", "nilradical"`: zero hits.
- `msearch.py` grep of Mathlib, query
  `reduction.*fiber|fiber.*reduction|nilradical.*fiber|fiber.*nilradical`: zero hits.
- `msearch.py` LeanSearch, query “Reduction of schemes commutes with taking generic
  fibres”: unavailable (Internal Server Error), recorded as unavailable.
- `rg` in the upstream `WeilConjectures` and project `lean/Sheaf` for the same
  comparison expressions and the item id: no exact statement. The project has
  specialised radicial-preparation fibre statements, which do not give this result
  for arbitrary morphisms. The item-id search found no upstream declaration.
- `rg` of Mathlib, upstream, project and `dag/lean_names_upstream.json` for the
  proposed name `reduction_generic_fibre` and module `ReductionGenericFibre`:
  no pre-existing declaration or module.

Validation: server-only `scompile.py` accepted the module (nice 19, two threads,
60 seconds per file) without errors or warnings. The final module and node record
are checked again by the dry-run delivery tool. No local compiler or library build
was run.

## Second reading by NP

I independently read the node, the sandbox module, its four statement dependency
nodes and the recorded Mathlib declarations, and Stacks `more-morphisms.tex`,
Tag 054Z, `lemma-reduction-generic-fibre` (statement and entire proof). The source
introduces an arbitrary morphism and a generic point of one component; it assumes
no finiteness, reducedness, flatness, or irreducibility condition throughout this
lemma. Its equality is the canonical reduced closed subscheme identification.

Object/hypothesis/conclusion checklist (H3):

1. Schemes Z and T are `{Z T : Scheme.{u}}`. `Scheme` is Mathlib's locally ringed
   space with local affine charts, and `Scheme.Hom` its locally ringed space
   morphisms (Scheme.lean, lines 42 and 74). Verdict: exact objects, no added
   property instances.
2. An arbitrary h: Z → T is `(h : Z ⟶ T)`. Verdict: exact; no finite type,
   Noetherian, separated, flat, or reduced assumption.
3. The point is `(η : T)`. Its generic-component hypothesis is
   `closure ({η} : Set T) ∈ irreducibleComponents T`. I read `IsGenericPoint` in
   Topology/Sober.lean: it means precisely that the singleton closure equals the
   subset. `irreducibleComponents` is maximal `IsIrreducible` subsets, where
   `IsIrreducible` includes nonemptiness. Thus this is equivalent to the existence
   of a component with generic point η; the component is uniquely its closure.
   Verdict: exact, including reducible bases.
4. Z_red and its canonical inclusion are `Z.nilradical.subscheme` and
   `Z.nilradical.subschemeι`. I read `Scheme.nilradical := .radical ⊥` in
   IdealSheaf/Basic.lean and the glued quotient subscheme and its inclusion in
   IdealSheaf/Subscheme.lean. These are the dependency's reduction, with no
   private substitute. Verdict: exact.
5. The source fibre is `(Z.nilradical.subschemeι ≫ h).fiber η`; the target reduced
   fibre is `(h.fiber η).nilradical.subscheme`. In Fiber.lean, `fiber` is the
   pullback along `T.fromSpecResidueField η`, `fiberι` is its first projection,
   and `fiberToSpecResidueField` its second. I also read `fromSpecResidueField`,
   defined using the stalk residue map. Verdict: the same scheme-theoretic fibres
   and residue field as the node.
6. The existential `e : ... ≅ ...` is an actual isomorphism of these schemes.
   Verdict: the full scheme identification, not a point-set identification.
7. The first equation prescribes the projection to Z of
   `e.hom ≫ (h.fiber η).nilradical.subschemeι`: it equals the source fibre's
   projection followed by `Z.nilradical.subschemeι`. Verdict: the canonical map's
   first projection is correct.
8. The second equation prescribes its projection to `Spec (T.residueField η)`
   as the source fibre's structure map. Verdict: the isomorphism is over κ(η).
   Together the equations uniquely specify the canonical map into the pullback
   `h.fiber η`. Conversely, a canonical reduction identification satisfies both.
   Thus these clauses neither strengthen nor weaken the node's conclusion.
9. Quantifier order is arbitrary Z, T, h, then η and its hypothesis, then the
   isomorphism with both compatibilities. Verdict: exact.

Edge cases: empty Z and empty fibres are admitted, and the canonical maps between
empty reductions satisfy the same equations. Empty T has no η, exactly as in the
source. Reducible and nonreduced T are admitted: the minimal-prime localization's
maximal ideal is nil, so the J ⊆ K argument does not assume reducedness of T.
Arbitrarily large nilradicals are allowed; each element of J uses only a finite
sum and its own nilpotence exponent. Zero rings and denominators mapping to zero
are covered by the localization calculation. There is no index family, integer n,
or characteristic condition to restrict. Universe u is explicitly bound and
arbitrary, with no test-object quantifier in a smaller universe; both schemes
inhabit the same scheme category as required for their morphism. All variables
are explicitly bound.

Independent H4 searches, with queries different from the worker's:

- LeanFinder via msearch: “For a scheme morphism the fiber at a minimal prime of
  the base commutes with quotienting the source by its nilpotent ideal”. Eight
  results, including `Scheme.Hom.fiber`, `fiberToSpecResidueField`,
  `fiberOverSpecResidueField`, and prime-spectrum fibre homeomorphisms. None is
  this comparison theorem.
- Loogle via msearch: `"fiber", "IsReduced"`. One result:
  `AlgebraicGeometry.instIsReducedFiberOfGeometricallyReduced`. It requires
  geometrically reduced h and only concludes reducedness; not this statement.
- LeanSearch via msearch: “The fiber over a generic point of the reduction of a
  scheme is canonically the reduced fiber”. Service unavailable (Internal Server
  Error); no mathematical verdict assigned to this unavailable search.
- Direct rg in Mathlib AlgebraicGeometry, upstream WeilConjectures and project
  lean/Sheaf for reduction/fibre in both orders and nilradical/fiber in both
  orders, plus the proposed declaration and module names in those sources and
  dag/lean_names_upstream.json. No exact declaration. I opened the nearby private
  `reduced_generic_fibre` in `ReducedGenericFibreMapCore.lean`: it assumes affine
  reduced source and affine integral base and concludes only fibre reducedness,
  so it cannot replace this theorem. The field-embedding and radicial-preparation
  modules concern specialized constructions and do not state this comparison.

H5–H9: no definitions, hollow data, private copies or extra claims are delivered.
The only theorem's entire proof is `sorry`. Both docstrings name Tag 054Z and the
blueprint id. The theorem docstring follows all five DAG proof steps: affine
covering; nilpotence of J; localization kernel K and the fraction zero criterion;
canonical quotient D → C with nilradical kernel; and gluing with both projections.
Statement imports expose the recorded Mathlib notions; the private imports carry
the DAG's affine pullback, localization, residue-field and minimal-prime proof
plan. No new node, dependency module or statement correction is needed (H12/H13
not applicable). The natural statement is unchanged. I checked that lean.statement
is verbatim the signature in the module, and every line is at most 100 characters.

Mismatches found: none. Changes: appended this independent review only; the
correct Lean module and node record are retained unchanged. Server-only scompile
compiled the delivered file cleanly in 1.2 seconds, reporting nice 19, two threads,
and a 60-second file limit. No local compiler or global build was run.
