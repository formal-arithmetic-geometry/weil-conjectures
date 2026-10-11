## Worker report

The module lean/Sheaf/CategoryTheory/DerivedCategory/PerfectScalarExtension.lean states
DerivedCategory.IsPerfect.scalarExtension with a single sorry, and defines no new notion.
The server compilation succeeded cleanly (2.2 seconds, exit 0).

Hypotheses and conclusion:
- The ring map A → B is `(f : A →+* B)` with `[CommRing A] [CommRing B]`.
  Stacks uses commutative rings throughout this chapter; no flatness, finiteness,
  Noetherian, field, or nonzero hypothesis is imposed.
- The complex K over A is `K : DerivedCategory (ModuleCat.{u} A)`.
- Perfectness of K is `hK : IsPerfect K`, using the upstream bounded finite-projective
  definition, not a new predicate or the scheme-level predicate.
- The conclusion is `IsPerfect` of the value at K of the chosen fixed-second-factor
  derived tensor functor. Its second argument is the regular B-module `ModuleCat.of B B`
  placed in degree zero by `HomologicalComplex.single`. The functor has target D(B),
  with B-action through the second factor, exactly K tensor_A^L B.
- Both HasDerivedCategory.{u} binders choose the existing derived categories. Rings
  and modules use a common arbitrary universe u, as the upstream perfect predicate does;
  any two small rings and a bounded finite-projective model fit a common universe.
  There is no quantification over a smaller universe of test objects.

Dependency declarations read and used:
- WeilConjectures.CategoryTheory.DerivedCategory.Perfect: DerivedCategory.IsPerfect
  (node def-pc-perfect-ring-complex), full definition and docstring read.
- Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor:
  DerivedCategory.exists_derivedTensor_second_factor_functor
  (node lem-pc-derived-tensor-second-factor-functor), full signature/docstring read.
  Classical.choose of its existential selects T; choose_spec supplies the left-derived
  property and K-flat comparison for stage 3. No arbitrary unconstrained functor is assumed.
- Original dependency Sheaf.AlgebraicGeometry.PerfectComplex:
  AlgebraicGeometry.Scheme.IsPerfect and IsStrictlyPerfect were read in full. These are
  scheme objects and cannot be applied directly to K in D(A); the node references are
  corrected below to the already existing ring-level node. No dependency module is needed.

Edge cases checked: K=0; zero rings including B=0; identity ring map; nonflat maps
such as Z → Z/2; arbitrary characteristic; complexes in any finite degree interval.
All are included. A perfect model is K-flat without requiring B flat. Finite projective
terms remain finite projective after any scalar extension, and zero terms remain zero.

Searches (2026-10-11):
- msearch.py leanfinder "Derived extension of scalars of a perfect complex over a ring is
  perfect": eight generic derived-category/linearity/Ext hits; no matching theorem.
- msearch.py loogle "DerivedCategory.IsPerfect": unknown identifier, zero hits
  (upstream project names are not in the Mathlib search index).
- msearch.py grep "IsPerfect|extensionOfScalars" CategoryTheory: zero Mathlib hits.
- rg in WeilConjectures/CategoryTheory/DerivedCategory for IsPerfect, extensionOfScalars
  and derived tensors: found the upstream ring-perfect definition, finite-field tensor
  cohomology under extra assumptions, and monoidal structures; no scalar-extension theorem.
- rg in lean/Sheaf for IsPerfect and derived tensors: found the shared mixed total tensor
  and fixed-second-factor derived tensor; reused these. The scheme perfect tensor-Hom
  theorem is about scheme objects, not this ring-level statement.
- rg for the exact proposed full name in Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json: no clash.
- rg for the item id in WeilConjectures: no match.
- DAG inspection found existing def-pc-perfect-ring-complex, so no new definition node.

The prescribed local Stacks .tex file is unavailable on this machine. Read the actual
source at https://stacks.math.columbia.edu/tag/066W, Lemma 15.76.9: arbitrary ring map,
perfect input, perfect derived scalar extension. The node's source.place numerical
15.68.3 is stale; its tag 066W identifies the correct lemma. Source field left untouched.
The docstring carries both DAG proof steps and their named dependencies.

## Statement corrected

Old statement (verbatim):

Let $A\to B$ be a ring map and let $K$ be a perfect complex [def-pc-perfect-complex] of $A$-modules. Then $K\otimes_A^{\mathbf L}B$ is a perfect complex [def-pc-perfect-complex] of $B$-modules.

The original references def-pc-perfect-complex, whose recorded declaration is on schemes
and cannot type an object of D(A). Replaced those two references by the existing
ring-perfect definition def-pc-perfect-ring-complex, made the standing commutativity
convention explicit, and identified the shared derived tensor functor. This is a
notation/typing correction, with the same assertion as Stacks Tag 066W (Lemma 15.76.9,
ring-perfect definition Tag 0656). The proof and proof_deps need no change: they already
argue with bounded finite-projective ring complexes and their affine interpretation.
The stmt_deps now name the ring-perfect definition and the shared derived tensor theorem.
No unit statement changes and no citer is edited.

All citers (found by recursive id search and filtering stmt_deps/proof_deps):
- lem-sc-perfect-finite-free-residue-model: holds true. Its first proof step applies
  the theorem to A → kappa(p), precisely the ring-level perfect scalar extension proved
  here; the corrected references do not alter that use.

No STATEMENT-DISPUTED flag: no mathematical counterexample or unresolved doubt.

## Second reading by Q1

Read independently against the corrected node, then the source, Lean module, and
recorded dependencies. The source check came first: Tag 066W states arbitrary
ring-map scalar extension of a perfect ring complex, with perfectness over the
codomain. I read the actual `more-algebra.tex` at
https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex,
labels `lemma-pull-perfect` and `definition-perfect`, as well as the chapter's
Introduction and Advice for the reader. Local literature contains no Stacks .tex.
The chapter concerns commutative algebra and uses unbounded derived categories;
no standing Noetherian, flatness, characteristic, or nonzero assumption applies.
The online tag is https://stacks.math.columbia.edu/tag/066W (currently 15.76.9).
The old numerical reference 15.68.3 is stale, but the stable tag and TeX label
identify the assertion unambiguously; source metadata was not edited.

Object/hypothesis/conclusion list, with the rendering and verdict for each:

- Objects A and B: `{A B : Type u} [CommRing A] [CommRing B]`. These are arbitrary
  commutative rings, including zero rings. Matches the source convention.
- Object and hypothesis A -> B: `(f : A →+* B)`. This is a unital ring homomorphism,
  with no flatness, finite type, Noetherian, field, or nontriviality restriction.
  Matches, including nonflat maps.
- Object K in D(A): `(K : DerivedCategory (ModuleCat.{u} A))`. This is an object of
  the unbounded derived category of A-modules, not a scheme complex. Matches.
- Hypothesis K perfect: `(hK : IsPerfect K)`. Opened the upstream definition at
  `WeilConjectures/CategoryTheory/DerivedCategory/Perfect.lean`: it existentially
  specifies a cochain complex P, integer bounds a,b, `IsStrictlyGE a`,
  `IsStrictlyLE b`, termwise `Module.Projective` and `Module.Finite`, and an
  isomorphism `K ≅ Q.obj P`. This is exactly the bounded finite-projective model
  required by `def-pc-perfect-ring-complex` and the source. No private predicate.
- Derived-category choices: the two `HasDerivedCategory.{u}` binders supply the
  categories used by the recorded upstream predicate. They do not impose an
  algebraic hypothesis on f or on its rings. A common arbitrary universe accommodates
  both rings; there are no smaller-universe test objects or independent indices.
- Object B in degree zero: `(HomologicalComplex.single (ModuleCat.{u} B)
  (ComplexShape.up ℤ) 0).obj (ModuleCat.of B B)`. This is the regular B-module,
  concentrated in degree zero. Matches the specified second tensor factor.
- Object K tensor_A^L B: apply `.obj` at that degree-zero complex to
  `Classical.choose (exists_derivedTensor_second_factor_functor f).2`, then apply
  its `.obj` to K. Read that theorem's entire signature and docstring: its second
  conjunct existentially supplies T and its comparison ε, the left-derived-functor
  property, and comparison isomorphisms on K-flat models. This chooses a constrained
  derived tensor functor, not an arbitrary functor or an extra hypothesis.
  Read `MixedTotalTensor.lean` too: `mixedTensor` uses `extendScalars f`, and the
  flip used here gives the B-action through the fixed second factor. Its output
  is in D(B), not D(A). Matches the node's named tensor construction.
- Conclusion: `IsPerfect (... .obj K)`, with the output module category over B.
  This asserts precisely perfectness of the derived scalar extension; no extra
  clause, weakened assertion, or changed quantifier order. Matches.

Dependency and correction checks:

- Opened both corrected `stmt_deps` node records and their recorded declarations:
  `def-pc-perfect-ring-complex` and
  `lem-pc-derived-tensor-second-factor-functor`. Both give the required notions.
- Opened the old `def-pc-perfect-complex` node and
  `lean/Sheaf/AlgebraicGeometry/PerfectComplex.lean`: `Scheme.IsPerfect` takes a
  scheme and an object of D(O_X), defined by local strictly perfect models.
  The worker's explicit correction to the existing ring-level node is justified;
  it preserves the mathematical source assertion and does not change a unit.
- Recomputed all citers by recursive node-id search. There is exactly one other
  node citing this item in `stmt_deps` or `proof_deps`, so a second distinct citer
  does not exist. Opened `lem-sc-perfect-finite-free-residue-model`, its statement,
  and every proof step: step 1 applies this item to A -> kappa(p), giving a perfect
  derived fibre. Its `holds: true` verdict remains correct. The recorded citer
  list is complete and no citer was edited.
- No new definition node or dependency module is delivered. The original proof
  steps use affine perfectness and termwise Tor-acyclic tensor; both steps are
  carried into the statement docstring, including the finite-free splitting
  argument. Their existing scheme/ring bridges remain stage-3 proof dependencies.

Edge cases: K=0, rank-zero terms, empty degree support, degree zero, arbitrary
positive or negative finite support bounds, identity maps, B=0, the possible maps
from A=0, nonflat maps such as Z -> Z/2, and every characteristic are admitted.
There is no assumption a <= b, so a zero model with empty support is admitted.
No index family or scheme is quantified over; empty index sets and empty schemes
are therefore not omitted cases of this ring-level assertion. The shared universe
u is arbitrary, as required by the upstream definition; no field specialization
or finite-dimensional cohomology replacement is made.

Independent searches (queries differ from the first reading):

- `msearch.py leanfinder "change of rings sends bounded complexes of finitely
  generated projective modules to perfect derived objects"`: eight K-projective
  and left-derived-functor results, including
  `CochainComplex.isKProjective_of_projective`; none states this theorem.
- `msearch.py loogle '"perfect", "tensor"'`: zero hits.
- `msearch.py grep 'perfect.*(scalar|base.change|tensor)|(scalar|base.change|tensor).*perfect'`:
  six hits concerning perfect fields and perfect pairings, not perfect complexes.
- `msearch.py leansearch "Derived change of rings preserves perfect complexes
  without flatness"`: service returned Internal Server Error; recorded as
  unavailable, not as a negative mathematical search result.
- The same conceptual regex over all upstream `WeilConjectures/` and project
  `lean/Sheaf/` found scheme perfect tensor statements and upstream
  `IsPerfect.tensor_homology`. Opened the latter: it assumes a Noetherian base
  and a field extension and states cohomology finiteness/vanishing; it is not
  this general D(B) perfect scalar-extension theorem. The upstream perfect
  predicate is reused, not duplicated.
- Exact-name/id search in Mathlib, upstream, project Lean, and
  `dag/lean_names_upstream.json` found no declaration clash or existing theorem.

Mismatches and changes: no mismatch in the delivered Lean signature or corrected
statement. The stale source number and original scheme-definition reference are
accounted for above; the worker already recorded the latter correction correctly.
Retained the Lean and node verbatim and appended this independent review only.
The existing dependency theorem uses local notation and lets internally; this
item introduces none, and no dependency rewrite is needed to use its signature.
There is no definition in the delivered module, hollow or otherwise, and its
single theorem has exactly one `sorry`. Imports are used, declaration and module
source docstrings carry the item id, proof steps are present, all variables and
universes are bound, and every Lean line is at most 100 characters.
The exact file signature equals `lean.statement` byte for byte.

Validation: prescribed `scompile.py Q1 lem-sc-perfect-pullback-perfect-residue`
on the delivered module returned exit 0 in 2.0 seconds, with no warnings or errors.
