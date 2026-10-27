## Worker report

The module `Sheaf.AlgebraicGeometry.UnpointedStableCoarseProjective` states
`AlgebraicGeometry.unpointed_stable_coarse_projective`, with `sorry` as its sole
proof. It introduces no definitions, axioms, alternative moduli objects, or new
nodes. The item changes only in `lean`; its mathematical statement, dependencies,
and proof plan are unchanged.

### Hypotheses and clauses

- Any field: `(k : Type u) [Field k]`, with `universe u` explicitly declared and
  `set_option autoImplicit false`. There is no characteristic, perfection,
  algebraic-closure, invertibility, or marking hypothesis on k.
- Genus at least two: `(g : ℕ) (hg : 2 ≤ g)`. Natural genera express the
  nonnegative integral geometric arithmetic genus already used by the dependency.
- The unpointed stable moduli groupoid, with exactly the dependency's objects and
  arrows: `BasedCategory.ofFunctor (StablePointedModuli.forget (Spec (.of k)) g 0)`.
  The final argument `0` is the empty ordered marking set, not a forgotten or
  chosen section. The dependency's stable family includes its projective-bundle
  condition and its geometric arithmetic genus. Its total category has cartesian
  family arrows and retains automorphisms.
- Deligne--Mumford stack: the first conjunct is precisely
  `IsDeligneMumfordModuliStack` of this based category. This includes the recorded
  fibred-in-groupoids, étale descent, algebraic-space diagonal, and surjective
  étale scheme-atlas conditions.
- Smooth over k: the last conjunct chooses an actual `U : Over (Spec (.of k))`
  and an actual based atlas functor `a` into this same moduli groupoid. Its
  universal test-scheme clauses are literally the atlas clauses in
  `IsDeligneMumfordModuliStack`: each two-base change has `HasSpaceBaseChange`,
  `SpaceMapIsEtale` and `SpaceMapIsSurjective` for its specified projection `p`.
  The extra clause `Smooth U.hom` says that the composite of this étale (hence
  smooth) atlas with the structure morphism is smooth. This is exactly stack
  smoothness, written out without introducing a second stack definition. Requiring
  this property for a chosen étale atlas is equivalent to smoothness of a DM
  stack, since smoothness descends along smooth surjective scheme/space maps.
- A coarse moduli k-scheme Q_g: the second conjunct chooses
  `Q : Over (Spec (.of k))` and the based map `π` from the actual stable groupoid
  into `discreteModuli (yoneda.obj Q)`. The predicate
  `IsCoarseModuliScheme ... Q π` is the dependency's full definition: bijectivity
  on maps to every algebraic space and the geometric-isomorphism-class bijection
  induced by π. Neither scheme representability of the stack nor an arbitrary
  bijection on geometric points is substituted for this.
- Finite type: `LocallyOfFiniteType Q.hom ∧ QuasiCompact Q.hom`, exactly the
  conjunction specified by `def-weil-finite-type-morphism`'s recorded interface.
- Projective: `IsHProjective Q.hom`, using the canonical upstream finite
  projective-space-embedding convention recorded in `def-kun-projective`.
- Smooth-family subcategory is open: the third conjunct quantifies over every
  stable family X and gives an open `V : X.base.left.Opens` such that, for every
  test k-scheme T and map `b : T ⟶ X.base`,
  `Smooth (pullback.snd X.projection b.left) ↔ Set.range b.left ⊆ V`.
  Factoring a scheme morphism through an open subscheme is equivalent to this
  range containment. This is the functor-of-points characterization of the
  base change of the full smooth-family subcategory. Its arrows are already
  the full subcategory's arrows (`StablePointedModuli.Smooth`). The condition
  determines the open uniquely and implies its compatibility with base change;
  no independently chosen open-substack datum is assumed.
- Density: for the actual surjective étale atlas `a` in the last conjunct,
  there is an open `V : U.left.Opens` with `Dense (V : Set U.left)`. Its universal
  characterization is smoothness of
  `(a.toFunctor.obj (CostructuredArrow.mk (yoneda.map b))).projection` for every
  `b : T ⟶ U`. The costructured-arrow object is exactly the map `h_T → h_U`
  associated to b, so applying a pulls the actual atlas family back to T. The
  `BasedFunctor.w` condition identifies its base with T; cartesian arrows supply
  its canonical comparison with the family pullback. Thus this V is exactly the
  inverse image of the already identified smooth open. Density on a surjective
  étale atlas is equivalent to density in the stack: the atlas is an open
  surjection, so every nonempty open of the atlas meets the preimage of a dense
  open of the stack, and conversely its dense image has dense closure. We do not
  erroneously require density after an arbitrary map from a scheme.

### Dependency interfaces read and used

Read the full 529-line `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`
module, including declaration docstrings and signatures. The used declarations
are `AlgebraicGeometry.StablePointedModuli`, its `forget` functor (and its
cartesian arrows), `StablePointedModuli.Smooth`, and the CategoryTheory
`discreteModuli`, `IsCoarseModuliScheme`, `IsDeligneMumfordModuliStack`,
`HasSpaceBaseChange`, `SpaceMapIsEtale`, `SpaceMapIsSurjective` interfaces.
No prerequisite is copied or repaired.

Read Mathlib's `Field` in `Algebra/Field/Defs.lean`,
`AlgebraicGeometry.LocallyOfFiniteType` in `Morphisms/FiniteType.lean`,
`AlgebraicGeometry.QuasiCompact` in `Morphisms/QuasiCompact.lean`,
`AlgebraicGeometry.Etale` in `Morphisms/Etale.lean`, and
`AlgebraicGeometry.Smooth` in `Morphisms/Smooth.lean`.
Read the full upstream
`WeilConjectures.AlgebraicGeometry.Morphisms.Projective` module:
`AlgebraicGeometry.IsHProjective` supplies exactly the project's finite
projective-space convention, not the more general projective-bundle convention.
The recorded explanation handles the empty-coordinate presentation by an
embedding of the empty scheme into P^0.

The four already stated, non-public proof imports are
`Sheaf.AlgebraicGeometry.StablePointedCurve`,
`Sheaf.AlgebraicGeometry.MarkedNodalInfinitesimalFields`,
`Sheaf.AlgebraicGeometry.NodalCurveLCICriterion`, and
`Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular`.
The other seven proof-only nodes have no recorded Lean module at the time of
writing: curve-stack-infinitesimal-dm-locus, gieseker-ten-canonical-hilbert-stability,
isolated-lci-curve-smoothing, nodal-curve-stack-smooth,
projective-pgl-stable-quotient, stable-and-smooth-family-open-loci, and
ten-canonical-hilbert-parameter (all with the `lem-sfb-` prefix). They introduce
no missing notion needed to type this statement. Their full proof obligations
are retained by name in the theorem's seven-step source/proof docstring.
The projectivity and moduli definitions are already public statement imports.

### Source and edge cases

Read `literature/stacks-project/moduli-curves.tex`,
`theorem-stable-smooth-proper` (Tag 0E9C) and
`lemma-smooth-dense-in-stable` (Tag 0E87), as well as the item's seven proof steps.
The former states smoothness and the DM property over Z and the dense smooth
open; the item's trait-smoothing argument supplies density in each field fibre.
Read Mumford's primary author scan, printed p.462 (PDF page 6):
https://www.dam.brown.edu/people/mumford/alg_geom/papers/1970b--ICMNice-IMU.pdf .
It asserts that the stable coarse moduli scheme is projective over Z; the
opening convention on printed p.457 specifies coarse moduli and finite type.
This supports the field-fibre projectivity and finite-type clauses. The proof
plan follows the node's more explicit ten-canonical Hilbert/GIT route, not a
replacement properness argument.

Checked the minimal genus g=2; no branch assumes g>2. In characteristic 2 or 3,
and over imperfect fields, every stated binder and clause remains available.
Wild finite automorphisms are retained: the stack is not asserted to be
represented by Q. The empty marking set is literally `Fin 0`. For an empty
base T, the pullback is empty, smoothness holds, and the empty range lies in V;
the open characterization therefore does not exclude it. A constant singular
family need not have dense smooth locus, so density is asserted on an atlas
only. Universes use the same u for the field and test schemes and the recorded
moduli universe conventions, with no extra size equality or smaller test
universe. No STATEMENT-DISPUTED flag or node correction is needed.

### Searches

All external searches used the authorized `msearch.py Q20
lem-sfb-unpointed-stable-coarse-projective` wrapper; its raw responses are in
`searches.jsonl` in this sandbox.

- LeanFinder: "The moduli stack of stable unpointed curves has a projective coarse
  moduli scheme and is smooth with dense smooth locus". Eight hits on ordinary
  scheme smoothness, smooth relative dimension, and compositions; no moduli theorem.
- Loogle: `IsDeligneMumfordModuliStack, IsSmoothModuliStack, IsDenseOpenSubstack`.
  Zero hits; the first name is unknown to the Mathlib search service.
- Mathlib grep: `IsSmoothModuliStack|IsDenseOpenSubstack|StablePointedModuli|IsDeligneMumford`.
  Zero hits.
- LeanSearch: "Stable curves of genus at least two have a projective coarse moduli
  scheme". Eight hits on ordinary smooth/proper morphisms and elliptic Weierstrass
  models; none states the item.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for smooth/dense-open stack
  vocabulary returned no additional usable statement. A subsequent focused search
  for `unpointed_stable_coarse_projective|unpointed.*stable.*coarse|IsDeligneMumfordModuliStack`
  found only the existing moduli definition and the consumer's proof citation.
  The exact item-id search in `lean/WeilConjectures` found nothing.
- Read the DAG statements and Lean records of all five statement dependencies.
  Searching DAG statements for smooth atlas, smoothness of a stack, dense/open
  substack found the item and its surrounding supporting/consumer lemmas, not an
  existing definition node or theorem with a recorded declaration for this item.
- Searched `dag/lean_names_upstream.json` with the same declaration/name patterns:
  no duplicate declaration. Read Mathlib's `CostructuredArrow.mk`, `proj`,
  `BasedCategory.ofFunctor`, `BasedFunctor` and its `w_obj` API to verify the
  atlas-family evaluation, rather than assume a field of an abstract stack datum.

### Validation

`scompile.py Q20 lem-sfb-unpointed-stable-coarse-projective
<absolute sandbox path>/lean/Sheaf/AlgebraicGeometry/UnpointedStableCoarseProjective.lean`
passed both sandbox and library-module compilation, in 10.9 s and 10.4 s,
respectively. No errors or warnings were emitted. The file has explicit binders,
no local notation or instances, lines at most 100 characters, and one named
postponed theorem matching the item's DAG node.

## Second reading by Q20

This is a separate source-and-signature reread by the same worker. The dispatcher
explicitly forbids starting other agents; no independent second-worker reading
is claimed. Independent maintainer review is the delivery's next step.

Reread the node, all five dependency statements and interfaces, and the final Lean
signature together. The field and g≥2 assumptions are exactly the first four
binders, with no marking or characteristic restriction. The first conjunct uses
the recorded DM-stack predicate of the exact cartesian moduli category. The
second has the required actual coarse map, algebraic-space universal property,
geometric class bijection, finite-type conjunction and H-projectivity of its
specified structure map. The third characterizes the smooth-family full open
subcategory on every base change, including the empty base. The final conjunct
chooses a genuine representable étale surjective atlas, makes its structure map
smooth, and identifies its dense open by the actual atlas functor's pulled-back
family. Its density is neither a claim on the coarse scheme nor a condition on
all families. All seven proof steps are in the docstring; the four available
proof-only modules are imported without public visibility. No mismatch or
correction was found in this reread.
