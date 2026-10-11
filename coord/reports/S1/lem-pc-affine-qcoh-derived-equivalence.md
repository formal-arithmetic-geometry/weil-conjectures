## Worker report

The module `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence` states
`AlgebraicGeometry.exists_affineQCohDerivedEquivalence` with proof `sorry`.
It defines no new object, functor, category, or predicate. The node is unchanged
except for its `lean` record. No statement is disputed or corrected.

Hypothesis and clause correspondence:

- The ring `A` is `(A : Type u) [CommRing A]`. Commutativity is implicit in
  the source's `Spec(A)` (Stacks Tag 06Z0); there is no domain, field,
  Noetherian, nonzero-ring, or finiteness hypothesis.
- `Y = Spec(A)` is written as `Spec (.of A)` everywhere, so no unrelated
  scheme or choice of affine identification enters the statement.
- `D(A)` is `DerivedCategory (ModuleCat.{u} A)`. The two explicit
  `HasDerivedCategory.{wA}` and `HasDerivedCategory.{wY}` binders select the
  localization universes, as in def-weil-abstract-derived-category and
  def-pc-derived-category; they impose no algebraic restriction.
- `D_QCoh(O_Y)` is the dependency's `schemeDerivedQCohCategory`, with its
  exact dependency predicate `schemeDerivedQCohProperty` and full-subcategory
  inclusion `.ι`. The witness `e` is an equivalence between precisely these
  categories, not an equivalence with all of `D(O_Y)` or with bounded complexes.
- Termwise associated sheaf is Mathlib's `tilde.functor (.of A)` followed
  by `.mapHomologicalComplex (ComplexShape.up ℤ)`. The first natural-isomorphism
  clause identifies this on *all complexes and all complex morphisms* with
  `DerivedCategory.Q ⋙ e.functor ⋙ .ι`. Thus the equivalence is specifically
  induced by tilde, rather than being an unspecified abstract equivalence.
  The explicit `@id` types this existing functor in the canonical
  `SheafOfModules (moduleRings ...)` carrier of the dependency. The explicit
  zero-preservation record uses only the already proved `tilde.map_zero`;
  no new theorem is proved, no local instance or private bridge is introduced.
- The quasi-inverse clause is the natural isomorphism from `e.inverse` to
  `.ι ⋙ (RingedSpace.globalSectionsFunctor ... ⋙
  ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).rightDerivedFunctor`.
  Evaluation at the whole space gives Gamma valued in modules over
  `Γ(Y,O_Y)`. Restriction of scalars along the canonical inverse map
  `A → Γ(Y,O_Y)` gives exactly A-valued Gamma. The existing unbounded
  `Functor.rightDerivedFunctor` computes its derived functor by K-injectives.
  It is the construction used in def-pc-derived-direct-image, specialized
  to global sections, not a second implementation and not an arbitrary inverse.
  Stacks explicitly describes this as direct image to the one-point ringed
  space with ring A, rather than a morphism of schemes to `Spec(A)`.
- “Equivalence of triangulated categories” is expressed by the existence of
  a compatible `CommShift ℤ` structure on `e.functor ⋙ .ι` and the assertion
  that this same functor is `IsTriangulated`. The full-subcategory triangles
  are the ambient distinguished triangles, so this says exactly that the
  equivalence preserves the induced triangulated structure. No triangulated
  structure on the subcategory is assumed as a new hypothesis. An exact
  equivalence has an exact inverse.
- For every integer `k`, the last clause sends the image of `ModuleCat.of A A`
  under `DerivedCategory.singleFunctor ... 0`, shifted by `k`, to the image
  of `SheafOfModules.unit (moduleRings Y.toRingedSpace)` under the same
  degree-zero embedding, shifted by `k`, up to isomorphism. These are
  precisely `A[k]` and `O_Y[k]`; the Mathlib shift convention places the
  nonzero term in degree `-k`.

Dependencies and declaration signatures read:

- def-pc-scheme: `AlgebraicGeometry.Scheme` in
  `Mathlib.AlgebraicGeometry.Scheme`; its full locally affine structure and
  `Spec`, plus `Scheme.ΓSpecIso` (global sections of Spec isomorphic to A).
- def-pc-derived-category: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory` in
  `Sheaf.AlgebraicGeometry.DerivedCategory`, whose module and docstrings
  were read in full. All derived sheaves use that canonical carrier.
- def-pc-derived-direct-image: `schemeDerivedDirectImage` in
  `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage` and its underlying
  `RingedSpace.derivedModuleDirectImage` in
  `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage` were read in full.
  Both are aliases of the existing `Functor.rightDerivedFunctor`; this
  same construction is applied to Gamma in the theorem. A scheme-derived
  direct image is not Gamma to A-modules, so no scheme morphism or bogus
  identification with `Spec Z` is supplied. The underlying ringed-space
  module is imported for its `moduleGrothendieckAbelian` instance, which
  supplies the K-injective resolutions used by `rightDerivedFunctor`.
- Ordinary affine associated sheaf and adjunction: `tilde.functor`,
  `tilde.adjunction`, `tilde.map_zero` in
  `Mathlib.AlgebraicGeometry.Modules.Tilde` (recorded by
  lem-weil-pbc-affine-tilde-gamma-adjunction).
- Ordinary global sections: `RingedSpace.globalSectionsFunctor` and its
  additive instance in `Sheaf.Topology.RingedSpaceModuleCohomology`
  (def-sc-ringed-space-module-cohomology). These use evaluation on top,
  not the additive-group-valued sheaf-cohomology functor.
- `Functor.rightDerivedFunctor` in
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`
  was read with its full K-injective hypothesis and construction. This
  is imported transitively by RingedSpaceDerivedDirectImage.

Source checked: [Stacks Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0),
including the proof's one-point ringed space, affine vanishing, unbounded
truncation comparison, and unit/counit argument. Local
`literature/stacks-project/perfect.tex` is absent on this machine, so the
source was read from the official Stacks website. The declaration docstring
records all five node proof steps and their DAG inputs.

Edge cases: the zero ring and empty affine scheme are allowed. Their module
and sheaf categories are zero categories, and the shift assertion still
makes sense. The zero complex, negative shifts, `k = 0`, and unbounded
complexes are all included. The degree-zero embeddings and shift sign agree
with `A[k]` having A in degree `-k`. Universes `u`, `wA`, `wY` are independent
and explicit; the module size is the scheme/ring universe, and the two
localization sizes are independently chosen. There is no boundedness or
finite-generation condition on the equivalence or its factorization.

Searches made with the required remote search wrapper:

- LeanSearch: “On an affine scheme Spec A the derived category of A modules
  is equivalent to complexes of sheaves with quasi coherent cohomology”:
  service unavailable, Internal Server Error (recorded by msearch.py).
- LeanFinder: “Derived global sections and associated sheaf induce an
  equivalence D(A) D_QCoh(Spec A)”: eight hits, including the affine Zariski
  site sheaf equivalence, affine-scheme Gamma equivalence, and Gamma/Spec
  adjunction. None concerns the derived category of quasi-coherent modules.
- Loogle: `DerivedCategory, CategoryTheory.Equivalence`: zero hits.
- Mathlib grep: `derived.*(tilde|globalSections)|affine.*derived.*equiv`:
  zero hits.
- Project/source `rg`: affine/derived equivalences, tilde/derived, and
  derivedGlobalSections/globalSectionsDerived. Results concerned other
  étale functors, or docstring citations of this node; no existing affine
  quasi-coherent derived equivalence was found.
- Source `grep -rn` for `lem-pc-affine-qcoh-derived-equivalence`: no hits.
- `rg` for the proposed full theorem name in Mathlib, WeilConjectures,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collisions.

Validation: server single-file compilation passed without errors or warnings
(5.3 seconds). Earlier elaboration showed that Mathlib's `Scheme.Modules`
category instance must not be silently used as the canonical derived-sheaf
carrier; the explicit typed functor and existing zero-map theorem repair
that without a new definition. A temporary missing server olean for the
scheme alias was avoided by importing the underlying ringed-space module
that actually supplies the needed K-injective instance. No local builds,
source-checkout writes, or direct git commands were run.

## Second reading by S1

I independently opened the sandbox node and module, all three statement-dependency
records and their recorded source declarations. No mathematical mismatch was found;
the Lean and node signature are retained verbatim. This reading adds only this report.
There are no new definition nodes, dependency modules, or statement corrections to review.

Source: I read the Stacks source `perfect.tex`, both its Conventions and opening of
Section 36.3 and `lemma-affine-compare-bounded`, at
https://raw.githubusercontent.com/stacks/stacks-project/master/perfect.tex,
and checked https://stacks.math.columbia.edu/tag/06Z0. The section imposes no
Noetherian, separation, boundedness, or finiteness hypothesis. Its D_QCoh is the full
subcategory of complexes with quasi-coherent cohomology, not the derived category of
all sheaves or merely bounded complexes. The node extracts the tilde/RGamma equivalence
from the source's three-category diagram; the other arrow and the additional H^0
comparison are not extra clauses of this node. The normalization on A[k] follows from
termwise tilde as the node's fifth proof step says.

Object, hypothesis, and conclusion checklist, with verdicts:

1. An arbitrary ring A admitting Spec: `(A : Type u) [CommRing A]`.
   PASS: commutativity is inherent in the dependency's Spec of a commutative ring;
   no field, domain, nontriviality, or finiteness assumption is added.
2. Y is exactly Spec(A): every occurrence is `Spec (.of A)`.
   PASS: there is no unrelated scheme or extra choice of an identification.
3. D(A): `DerivedCategory (ModuleCat.{u} A)`.
   PASS: complexes are indexed by all integers and localized at quasi-isomorphisms.
   The binders `HasDerivedCategory.{wA}` and `HasDerivedCategory.{wY}` select chosen
   localization models, not boundedness or an algebraic hypothesis. I read Mathlib
   DerivedCategory/Basic: `HasDerivedCategory.standard` supplies the general model;
   the two localization universes are independent and explicit.
4. D_QCoh(O_Y): `schemeDerivedQCohCategory (Spec (.of A))`.
   PASS: I read DerivedCategory.lean: `schemeDerivedQCohProperty X` requires
   `((DerivedCategory.homologyFunctor ... n).obj K).IsQuasicoherent` for every
   `n : ℤ`, and the category is precisely its FullSubcategory. Its carrier is the
   shared `SheafOfModules.{u} (moduleRings X.toRingedSpace)`, with the canonical
   category structure, not the separate `X.Modules` category instance.
5. Termwise associated sheaf induces the equivalence: the witness
   `e : DerivedCategory (ModuleCat.{u} A) ≌ schemeDerivedQCohCategory ...`
   and first `Nonempty` natural-isomorphism clause identify
   `DerivedCategory.Q ⋙ e.functor ⋙ (schemeDerivedQCohProperty ...).ι`
   with tilde mapped to `ComplexShape.up ℤ` followed by `DerivedCategory.Q`.
   PASS: this specifies both the objects and morphisms of the inducing functor,
   rather than merely asserting an abstract equivalence. I opened Mathlib Tilde.lean:
   `tilde.functor` has `obj := tilde` and `map := tilde.map`.
   `@id` selects the shared sheaf-module carrier without changing these maps;
   the explicit zero-preservation record uses the existing `tilde.map_zero`.
6. Quasi-inverse is RGamma(Y,-): the second `Nonempty` clause identifies `e.inverse`
   with the inclusion followed by the unbounded right derived functor of
   `RingedSpace.globalSectionsFunctor ... ⋙ ModuleCat.restrictScalars
   (Scheme.ΓSpecIso (.of A)).inv.hom`.
   PASS: globalSectionsFunctor is evaluation at the whole space. I opened its
   definition and Mathlib's GammaSpec isomorphism: the latter is Gamma(Spec A) ≅ A,
   so its inverse gives exactly the scalar map A → Gamma(Spec A). I read the source
   RightDerivedFunctor/Defs.lean: rightDerivedFunctor is the unbounded K-injective
   derived functor. I also read SchemeDerivedDirectImage.lean and its underlying
   RingedSpaceDerivedDirectImage.lean. Those use this same construction; the scheme
   specialization is not itself a functor to A-modules. Applying the shared derived
   functor directly to Gamma is the source's one-point-ringed-space construction,
   not a duplicate derived-direct-image definition or a fictitious scheme morphism.
7. Equivalence of triangulated categories: the existential `CommShift ℤ` on
   `e.functor ⋙ ...ι` and `IsTriangulated` for that same functor.
   PASS: I opened Mathlib Triangulated/Functor.lean: this means preserving
   distinguished triangles with that shift comparison. Distinguished triangles in
   the full quasi-coherent subcategory are inherited from the ambient derived
   category. A fully faithful triangulated equivalence reflects these triangles,
   so its inverse is exact too; no additional structure hypothesis on D_QCoh is added.
8. Every integer shift: `∀ k : ℤ, Nonempty (... ≅ ...)`, using
   `singleFunctor (ModuleCat.{u} A) 0` on `ModuleCat.of A A`, and
   `singleFunctor (SheafOfModules ... ) 0` on `SheafOfModules.unit ...`,
   each shifted by k.
   PASS: these are A[k] and O_Y[k]; the one equivalence e precedes every k.

Edge cases: zero ring and its empty spectrum are admitted by CommRing and Spec;
there is no Nontrivial or Nonempty hypothesis. Zero modules/complexes and arbitrary
unbounded complexes are included. Every characteristic is included. Both negative
and positive shifts and k = 0 are explicitly covered; the cochain shift places A
in degree -k. No index set or n is introduced, so there is no empty-index or n = 0
restriction. Ring and module sizes are arbitrary u; wA and wY do not impose an
extra common localization universe. No variable or universe is unbound.

Independent searches using words differing from the worker's:

- LeanFinder via msearch: `unbounded complexes modules affine scheme sheafification
  equivalence with quasi-coherent cohomology`: eight hits, ordinary affine Zariski
  site sheaf equivalence, quasi-coherence predicates/data, abelian instances and
  sheaf cohomology; none states this derived equivalence.
- Loogle via msearch: `"tilde", "DerivedCategory"`: zero hits. An initial query
  without the comma produced a parse error and was corrected, not counted as evidence.
- LeanSearch via msearch: `Sheafification of complexes of modules over a commutative
  ring induces an equivalence onto the derived category of sheaves with quasi-coherent
  cohomology on its spectrum`: Internal Server Error, recorded as unavailable;
  this is not a no-match verdict.
- `rg` over all pinned Mathlib, all WeilConjectures, repository lean/Sheaf, and
  dag/lean_names_upstream.json for affine/derived/equivalence in both orders and
  tilde/derived in both orders: hits in lean/Sheaf are proof-docstring citations,
  not a declaration of this equivalence. Broader affine/equivalence searches find
  ordinary affine scheme/module or site equivalences, not this statement.
  The proposed full theorem name has no collision in those sources.

H5/H6/H8/H9: the delivery defines no data and proves nothing; the only theorem has
`by sorry`. The module and theorem docstrings name Tag 06Z0 and this blueprint id.
The proof docstring follows all five node steps, including the kernel input for
exactness, K-injective construction, affine vanishing with N = 1 and truncation,
unit/counit comparison, and the shift normalization. All source lines are at most
100 characters. Imports provide the shared derived carrier, unbounded derivation
and K-injective instances, Gamma, tilde, and triangulated-functor predicate.
I programmatically compared lean.statement to the file's signature: exactly equal.

Validation: the prescribed server single-file compilation passed in 5.3 seconds,
with no errors or warnings. My first compile invocation used a relative path from
the repository rather than the sandbox and failed to find the input file; rerunning
from the sandbox resolved this invocation error. No Lean repair was needed.
