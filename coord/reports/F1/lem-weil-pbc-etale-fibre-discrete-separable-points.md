## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints` states
`AlgebraicGeometry.Scheme.Hom.etale_fibre_discrete_separable_points`, with proof `sorry`.
No definitions, auxiliary theorems, new nodes, dependency modules, or statement corrections
are needed. The existing node is unchanged except for its `lean` record.

Hypotheses and clauses, individually:

- Schemes X and S: `{X S : Scheme.{u}}`, with arbitrary explicitly bound universe `u`.
- The morphism f: `(f : X ⟶ S)`; etaleness: `[Etale f]`.
- A base point s with residue field: `(s : S)` and `S.residueField s`.
- The scheme-theoretic fibre: `f.fiber s`, with structural morphism
  `f.fiberToSpecResidueField s`.
- Its underlying space is discrete: `DiscreteTopology (f.fiber s)`.
  This is equivalent to all singleton sets being open and closed; there is no finiteness
  assumption on the set of points.
- Every fibre point: `∀ y : f.fiber s`.
- Its residue field: `(f.fiber s).residueField y`, the quotient of its local ring by its
  maximal ideal, with Mathlib's canonical field instance.
- Its specified extension structure over κ(s): `i` is `Spec.homEquiv` applied to
  `(f.fiber s).fromSpecResidueField y ≫ f.fiberToSpecResidueField s`.
  This is exactly the canonical base-field ring map (the point map followed by the
  structural map, read contravariantly). `letI := i.hom.toAlgebra` installs this map as
  the algebra structure, rather than choosing an arbitrary extension structure.
- Finiteness of that field extension:
  `Module.Finite (S.residueField s) ((f.fiber s).residueField y)`.
- Every element is a root of a separable polynomial:
  `∀ a, ∃ p : Polynomial (S.residueField s), p.Separable ∧ Polynomial.aeval a p = 0`.
  Evaluation uses exactly the canonical algebra structure just specified.
- The singleton open subscheme: `∃ U : (f.fiber s).Opens, (U : Set (f.fiber s)) = {y}`;
  its scheme structure is Mathlib's `U.toScheme`, namely restriction of the structure sheaf.
- The isomorphism to the spectrum of this same residue field:
  `∃ e : U.toScheme ≅ Spec ((f.fiber s).residueField y)`.
- It is over κ(s): `e.hom ≫ Spec.map i = U.ι ≫ f.fiberToSpecResidueField s`.
  The right side is the structural map of the singleton open subscheme.
  The discreteness and these isomorphisms express precisely the disjoint-union description
  in the node: the open singleton components cover the fibre and are pairwise disjoint.

Dependency declarations read and used (all recorded as Mathlib leaves):

- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale` (affine-locally etale ring maps).
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField`,
  `Mathlib.AlgebraicGeometry.ResidueField`, and its canonical point map
  `Scheme.fromSpecResidueField`. Read also `Scheme.Hom.residueFieldMap` and
  `Scheme.Spec.residueFieldIso`; no replacement residue field is introduced.
- `def-pc-scheme-fibre`: `AlgebraicGeometry.Scheme.Hom.fiber`,
  `Mathlib.AlgebraicGeometry.Fiber`, and `fiberToSpecResidueField`.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; open subschemes use `Scheme.Opens.toScheme` and
  `Scheme.Opens.ι` from `Mathlib.AlgebraicGeometry.Restrict`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`; `Spec.homEquiv` from
  `Mathlib.AlgebraicGeometry.GammaSpecAdjunction` identifies the canonical ring map.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`, constructed
  from the given map using `RingHom.toAlgebra`.
- `def-pc-separable-polynomial`: `Polynomial.Separable`,
  `Mathlib.FieldTheory.Separable`, literally coprimality with the derivative.

The module imports Fiber, Etale, and Separable; their transitive imports supply the
remaining declarations. The declaration docstring carries all five proof steps from the
node, with their named inputs; no part of that proof is implemented at this stage.

Source checked: https://stacks.math.columbia.edu/tag/02GL, Lemma 29.37.7(2).
The repository's literature/stacks-project/morphisms.tex is not present locally, so the
Stacks page was read directly. It states arbitrary disjoint unions, not only finite ones.

Edge cases checked: empty fibre (discrete and pointwise clauses vacuous); empty base
(no s to bind); a single separable extension; an infinite disjoint union (no quasi-compactness
or finite-point hypothesis); all characteristics, including imperfect base fields (separability
is explicitly required, not inferred from characteristic); arbitrary scheme universe.
The zero polynomial cannot serve as a separable polynomial, by Mathlib's definition.
There is no additional smoothness, connectedness, affineness or separatedness hypothesis.
No statement dispute or mathematical node fault was found.

Searches performed via `/home/ubuntu/weil-launcher/msearch.py`:

- leanfinder: `etale scheme fibre discrete finite separable residue fields`.
  Eight hits: notably `Algebra.Etale.iff_exists_algEquiv_prod`,
  `Algebra.FormallyEtale.iff_exists_algEquiv_prod`, and residue-field separability for
  formally unramified local rings. These are ring-level pieces, not this combined statement.
- loogle: `AlgebraicGeometry.Scheme.Hom.fiber, DiscreteTopology`: zero hits.
- grep in AlgebraicGeometry:
  `residueField.*(Separable|FiniteDimensional)|[Ee]tale.*[Dd]iscrete`:
  one unrelated purely inseparable result in UniversallyInjective.lean:111.
- leansearch: `etale scheme over field discrete finite separable residue field`:
  unavailable (Internal Server Error). Other search kinds were available.
- rg in project `lean/Sheaf` and source `WeilConjectures/Mathlib/AlgebraicGeometry`:
  `etale.*fibre|etale.*fiber|discrete.*fiber|DiscreteTopology|singleton.*residueField`.
  Found the source's quasi-finite discreteness proof and unrelated uses of discrete
  topology, plus proof-docstring references to this node; no combined declaration.
- grep of this exact node id in `WeilConjectures`: no matches.
- Additional rg for `residueField.*[Aa]lgebra|algebra.*[Rr]esidueField|fromSpecResidueField|residueFieldMap`
  found source `Scheme.Hom.etale_residueFieldMap` and `finite_residueFieldMap`, again
  only parts of the conclusion. Read the relevant canonical residue-field signatures.
- Read `Spec.homEquiv` and open-subscheme signatures directly. The new theorem's full
  name is absent from the searches; the delivery preflight also checks name collisions.

Validation: `scompile.py F1 lem-weil-pbc-etale-fibre-discrete-separable-points` on the module
completed in 1.7 seconds, exit code 0, without warnings. The delivery dry run follows.


## Second reading by F1

Read independently against the repository node, all seven statement-dependency nodes,
their actual Mathlib declarations, and the delivered module. The node copy differs from
the repository only in `lean`; there is no statement correction, new definition node,
or dependency module. The existing declaration is retained unchanged.

Source: [Stacks 02GL(2)](https://stacks.math.columbia.edu/tag/02GL).
The local Stacks .tex is absent. I also opened the upstream
[morphisms.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/morphisms.tex),
label `lemma-etale-over-field`, and the beginning of section `section-etale`.
The latter imposes no standing restriction on schemes and explicitly excludes separation
and quasi-compactness requirements from the definition. Part (2) assumes exactly an etale
morphism and a base point. Part (1) and its affine-open proof explain the arbitrary
(possibly infinite or empty) disjoint union. Current upstream line numbers differ from the
node's snapshot, but the label and mathematical statement agree.

My object/hypothesis/conclusion checklist, with verdicts:

1. Arbitrary schemes X and S: `{X S : Scheme.{u}}`. PASS. `Scheme` is the locally ringed
   space with local affine neighbourhoods, and `Scheme.Hom` gives its actual category.
   Universe `u` is explicitly declared and arbitrary; no small-universe specialization.
2. A morphism f, etale, and no additional hypothesis: `(f : X ⟶ S) [Etale f]`. PASS.
   I read the affine-ring-map definition of `Etale` and its
   `iff_flat_and_formallyUnramified`, which includes local finite presentation as in
   `def-weil-etale-morphism`. There are no hidden Noetherian, finite, proper, separated,
   connected, or affine assumptions.
3. A point s and its residue field: `(s : S)`, `S.residueField s`. PASS. The recorded
   `Scheme.residueField` is literally `IsLocalRing.ResidueField` of the structure-sheaf
   stalk, with its field instance, not a chosen field or a geometric point.
4. Fibre X_s and structural map to Spec kappa(s): `f.fiber s` and
   `f.fiberToSpecResidueField s`. PASS. The actual definitions are the pullback of f
   along `S.fromSpecResidueField s`, and its second projection.
5. Discreteness, including every point being both open and closed:
   `DiscreteTopology (f.fiber s)`. PASS. This class says the topology equals the discrete
   topology, so all subsets are open and their complements are open. There is no finite
   cardinality requirement.
6. Every point y of the fibre and its residue field: `∀ y : f.fiber s`,
   `(f.fiber s).residueField y`. PASS. This is the fibre's residue field, not the base's
   residue field or an unrelated extension.
7. The specified field extension over kappa(s):
   `let i := Spec.homEquiv ((f.fiber s).fromSpecResidueField y ≫
   f.fiberToSpecResidueField s)` and `letI := i.hom.toAlgebra`. PASS. I read
   `Spec.homEquiv : (Spec S ⟶ Spec R) ≃ (R ⟶ S)`, `fromSpecResidueField`, and
   `RingHom.toAlgebra`. Thus i is the canonical ring map from the base residue field
   into the point residue field; it is not an existential choice of algebra structure.
   Both rings are fields, so its injectivity needs no extra hypothesis. The let-bound
   algebra is used by both module finiteness and polynomial evaluation.
8. Finite extension: `Module.Finite (S.residueField s) ((f.fiber s).residueField y)`.
   PASS. The class means finitely generated as a module, hence finite-dimensional over
   this field. It does not mean a finite underlying set.
9. Every element is a root of a separable polynomial over the base:
   `∀ a : (f.fiber s).residueField y, ∃ p : Polynomial (S.residueField s),
   p.Separable ∧ Polynomial.aeval a p = 0`. PASS. I read `Polynomial.Separable`,
   literally coprimality with its derivative, as required by the dependency node.
   Quantifier order and coefficient field match; `aeval` uses the canonical map i.
10. The singleton open subscheme: `∃ U : (f.fiber s).Opens,
    (U : Set (f.fiber s)) = {y}`. PASS. I read `Scheme.Opens.toScheme` as restriction
    to the open subset and `U.ι` as its inclusion; no private subscheme definition.
11. Isomorphism to the spectrum of the same residue field:
    `∃ e : U.toScheme ≅ Spec ((f.fiber s).residueField y)`. PASS. `Spec` and its
    contravariant map are exactly the dependency declarations.
12. Isomorphism over kappa(s):
    `e.hom ≫ Spec.map i = U.ι ≫ f.fiberToSpecResidueField s`. PASS. Both sides are
    maps from the singleton open subscheme to the base residue-field spectrum.
    This is the commuting triangle required for an isomorphism over the base, not only
    an isomorphism of abstract schemes. The open singletons cover the fibre and are
    pairwise disjoint, so the pointwise description plus discreteness is exactly the
    node's disjoint-union description, with no stronger or weaker clause.

Edge cases: the empty fibre satisfies discreteness and vacuous pointwise conclusions;
an empty S leaves no point s; infinite disjoint unions are allowed since neither a
finite index type nor quasi-compactness is bound. The zero ring gives an empty affine
scheme, so it is not excluded at scheme level; the residue fields at actual points are
nontrivial fields as they should be. A zero-factor product (n = 0) corresponds to the
empty case, with no positive-n restriction. Every characteristic and imperfect base
fields are covered: separability is asserted explicitly. A zero polynomial cannot
satisfy `Separable` over a field, and a nonzero constant cannot vanish at a field element,
so the root clause cannot accidentally become vacuous. The arbitrary scheme universe u
is the universe of the category of schemes used by the dependency definitions; all
variables and universes in the signature are bound.

Independent searches (different wording from the first worker):

- `msearch.py ... leanfinder "scheme etale morphism fiber singleton open subscheme
  spectrum residue field"`: eight hits, notably `fiberToSpecResidueField_apply`,
  `SpecToEquivOfField`, and residue-field preimmersion instances. These describe canonical
  maps or points, not the combined conclusion.
- `msearch.py ... loogle "AlgebraicGeometry.Etale, AlgebraicGeometry.Scheme.residueField"`:
  only `Scheme.instEtaleFiberToSpecResidueField`, the base-change etaleness piece.
- `msearch.py ... grep "fiber.*[Ss]eparable|[Ss]eparable.*fiber|singleton.*residueField"`:
  eight ring-level spectrum/quasi-finite/local-ring hits, no combined scheme theorem.
- `msearch.py ... leansearch "An etale morphism has discrete fibres and singleton open
  subschemes isomorphic to spectra of finite separable residue field extensions"`:
  service unavailable (Internal Server Error); no verdict inferred from that failure.
- Direct `rg` in Mathlib/AlgebraicGeometry, source `WeilConjectures`, and repository
  `lean/Sheaf` for etale/residue, etale/fiber, discrete/fiber, singleton/spectrum, and
  separable/residueField combinations. I opened the relevant candidates:
  source `Scheme.Hom.etale_residueFieldMap` proves only finite separable residue field
  extensions, and source `LocallyQuasiFinite.of_etale` plus Mathlib fibre discreteness
  gives only the topology clause. Neither includes the singleton subscheme isomorphisms.
  Existing project hits refer to other statements or to this node in proof docstrings.
  No declaration matches all clauses, so H4 does not require dropping this module.

No mathematical or Lean mismatch was found, and nothing correct was rewritten. The
module has only one named theorem, with proof `sorry`; there is no hollow definition
and nothing proved. The header and both docstrings have the source and blueprint id.
The five proof paragraphs follow the node: base change, affine etale algebra and its
finite separable factors, singleton components, discreteness, and residue-field
identification with compatible base maps. Imports serve fibre/scheme constructions,
etaleness, and separable polynomials respectively. All lines are at most 100 characters.
The node's `lean.statement` is byte-for-byte the signature before `:= by` in the file.

Validation: independent `scompile.py` with the absolute sandbox module path returned
exit code 0, compiled in 1.7 seconds, without warnings. An initial call with a relative
sandbox path from the repository directory failed to locate the input; supplying the
absolute path fixed that invocation, without changing files. Only this second-reading
report was appended; the Lean and node remain unchanged. Delivery preflight follows.
