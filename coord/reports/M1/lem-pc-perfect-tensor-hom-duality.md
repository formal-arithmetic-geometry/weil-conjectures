## Worker report

The module `Sheaf.AlgebraicGeometry.PerfectTensorHomDuality` states
`AlgebraicGeometry.perfect_tensor_hom_duality`, with proof `sorry`. The original
node statement is unchanged. The only added statement dependency is the new
`def-pc-scheme-derived-tensor-structure` needed to interpret its derived tensor
products as a fixed monoidal structure. All writes are confined to the sandbox.

Hypotheses and clauses, in the order of the node:

- “X a scheme”: `(X : Scheme.{u₁})`, Mathlib's `AlgebraicGeometry.Scheme`.
- “K in D_QCoh(O_X)”: `(K : schemeDerivedQCohCategory X)`. Its underlying
  ambient object is `K.obj`, and its membership proof is supplied by the full
  subcategory. No second module category or derived category is created.
- “K perfect”: `(hK : Scheme.IsPerfect X K.obj)`, with the recorded global and
  per-open `HasDerivedCategory` binders required to form that predicate. These
  are localization-size choices, not restrictions such as boundedness or flatness.
- The quasi-coherent complexes A and B range over `schemeDerivedQCohCategory X`.
  The natural Hom equivalences are encoded as tensor adjunctions: the
  `homEquiv A.obj B.obj` of the first adjunction is
  `Hom(K ⊗ A,B) ≃ Hom(A,Kdual ⊗ B)`; the inverse `homEquiv` of the second is
  `Hom(A,K ⊗ B) ≃ Hom(Kdual ⊗ A,B)`. An `Adjunction` includes naturality in
  both variables, not just an unrelated bijection for each pair.
- “there is a dual complex”: `∃ Kdual : schemeDerivedQCohCategory X`. Its
  quasi-coherent cohomology is part of its type.
- “evaluation and coevaluation”, and “dualizable”: `ExactPairing K.obj Kdual.obj`
  contains `evaluation' : Kdual ⊗ K → 𝟙` and
  `coevaluation' : 𝟙 → K ⊗ Kdual` and BOTH triangle identities, including the
  associators and unitors. The reverse exact pairing expresses the same duality
  with symmetry. Exact pairings give canonical tensor adjunctions via Mathlib's
  `tensorLeftAdjunction` and `tensorLeftHomEquiv`. Thus the existential adjunction
  clauses are redundant consequences of the exact-pairing data, not additional
  hypotheses. The data specify a dual with its maps; as usual such duals are
  uniquely isomorphic, rather than requiring a separately chosen name for RHom.
- “in D_QCoh”: explicit closure clauses
  `∀ A, schemeDerivedQCohProperty X (K.obj ⊗ A.obj) ∧ ... (Kdual.obj ⊗ A.obj)`
  keep the tensor objects in that full subcategory. Its morphisms are precisely
  the ambient morphisms used by the adjunctions. The ambient adjunctions entail
  the required restricted Hom equivalences; they already follow from duality.
- “every morphism g:X'→X”: `∀ (T : Scheme.{u₁}) (g : T ⟶ X)`, followed only by
  the same derived localization choices (global and per-open) on T. There is no
  flatness, quasi-compactness, separation, or other hypothesis on g.
- “Lg*K perfect”: `Scheme.IsPerfect T ((derivedPullback g).obj K.obj)`.
- “Lg*(Kdual) a dual of it”: the exact pairings use exactly
  `(derivedPullback g).obj K.obj` and `(derivedPullback g).obj Kdual.obj`.
  No fresh arbitrary dual is substituted. Both pulled objects explicitly satisfy
  `schemeDerivedQCohProperty T`.
- “both isomorphisms on X' for all quasi-coherent A,B”: the same two tensor
  adjunctions on T, with closure for all `A : schemeDerivedQCohCategory T`.
  Adjunction naturality quantifies over all morphisms and all target objects B.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `Scheme.IsPerfect`, with its actual
  per-open localized-site category and restriction functor.
- `Sheaf.AlgebraicGeometry.DerivedPullback`: `derivedPullback` and the defining
  `exists_derivedPullback` universal property and K-flat counit.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`: `SheafOfModules.tensorClosed`.
  Its existing first two conjuncts are used for additivity and closure; they
  were not restated as fresh sorry lemmas.
- Upstream `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`:
  `DerivedCategory.hasDerivedMonoidalCategory`; the generic `DerivedMonoidal`
  localization construction supplies the fixed tensor and all coherences.
- Upstream `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`:
  `SheafOfModules.isGrothendieckAbelian`.
- `Mathlib.CategoryTheory.Monoidal.Rigid.Basic`: `ExactPairing`,
  `tensorLeftHomEquiv`, `tensorLeftAdjunction`, with their full signatures and
  naturality read in source.

Edge cases checked mathematically before finalizing: K=0 is perfect and self-dual,
with zero evaluation/coevaluation and the identity of the zero object also zero.
A=0 or B=0 gives singleton Hom sets. The empty scheme has the zero module category
and causes no missing nonempty-cover hypothesis. No finite-dimensional, positive-rank,
bounded A/B, nonempty X, or characteristic restriction was introduced. Negative
shifts of K are included by the existing unbounded derived category. Derived pullback
is not restricted to flat g. Universe u₁ is the common scheme/module universe, and
w₁ is the shared Hom universe of the localizations; neither is auto-bound.

Searches: `msearch.py leanfinder` for “perfect complexes on a scheme are dualizable
in the quasi coherent derived category” returned eight generic derived-category and
K-projective declarations, no exact match. `msearch.py loogle` for
“ExactPairing, DerivedCategory” returned zero hits (unknown identifier ExactPairing).
`msearch.py grep` for “perfect.*dual|dual.*perfect|DerivedCategory.*monoidal” returned
14 hits about ordinary linear-algebra pairings, no scheme derived duality. `rg` in
WeilConjectures for the item id and both proposed full names returned no existing
statement. Broader `rg` for derived monoidal constructions found the upstream generic
construction, which is reused. Project search found TensorClosed, which is reused.
The new node records its separate three-kind searches, including the unavailable
LeanSearch service. `blueprint_refs.py search 'derived monoidal'` returned zero nodes.
No declaration says exactly the entire item, so it is not an existing attachment.

The local Stacks tex files are not installed here; the source places were read on
the official pages: https://stacks.math.columbia.edu/tag/08DQ (global perfect dual),
https://stacks.math.columbia.edu/tag/0FPC (exact dual pairing),
https://stacks.math.columbia.edu/tag/0GM7 (perfect internal-Hom pullback comparison),
and https://stacks.math.columbia.edu/tag/0A9T (the duality adjunction calculation).
The source does not impose flatness on g in the perfect case.

No statement correction or dispute. Proofs remain sorry. The combined server compile
passed with no errors or warnings. The dry run is the final mechanical check;
an independent second reading remains for the second worker, as instructed.

## Second reading by M1

I read the item node, its source place (duality.tex, Tag 0A9T), and both delivered
modules independently. The node introduces a scheme X, a perfect K in
`D_QCoh(O_X)`, arbitrary quasi-coherent A and B, a dual K^vee with evaluation and
coevaluation, two natural tensor-Hom isomorphisms, and then an arbitrary morphism
`g : X' ⟶ X` with the corresponding perfect pullback, pulled-back dual, and the
same two isomorphisms for all quasi-coherent A and B on X'.

The Lean rendering matches these items as follows. `X : Scheme.{u₁}` is the scheme;
`K : schemeDerivedQCohCategory X` is exactly an object of `D_QCoh(O_X)`; and
`hK : Scheme.IsPerfect X K.obj` is the perfectness hypothesis. The existential
`Kdual : schemeDerivedQCohCategory X` is the dual. `Nonempty (ExactPairing ... )`
in both orders supplies evaluation, coevaluation, and both triangle identities.
The two `Nonempty (tensorLeft ... ⊣ tensorLeft ...)` clauses supply the two
natural tensor-Hom equivalences. The two closure conjuncts state that every tensor
appearing for a quasi-coherent A remains in `D_QCoh`; since the full subcategory
has the ambient Hom types, the displayed ambient adjunctions render the node's
Hom sets. For `g`, the universal quantifier has exactly the node's arbitrary
`T` and `g : T ⟶ X`; it adds no flatness, separation, or finiteness hypothesis.
The following conjuncts give perfectness and quasi-coherence of `Lg^*K`,
quasi-coherence of `Lg^*(Kdual)`, exact pairings in both orders, both adjunctions,
and closure for every `A : schemeDerivedQCohCategory T`, exactly the pullback
clauses of the node. The local derived-category binders are the size data needed
by the recorded definitions and do not restrict the schemes or morphisms.

The additional definition node is read against its source before the item: its
`schemeDerivedTensorMonoidal` is the fixed K-flat derived tensor monoidal structure
on `schemeDerivedCategory X`, with the underived sheaf tensor, additive/closed
structure, and functorial flat resolution explicitly supplied. Its data are not
`sorry`; only the named flat-resolution theorem has a `sorry` proof. The item
module installs this structure locally for X, while the same construction is
available for each quantified T. Imports and declaration namespaces follow the
project conventions, and all variables and universes are explicit.

I checked the edge cases: empty X, the zero perfect complex, zero A or B, empty
index situations (there is no index binder), arbitrary characteristic, and shifts
of K are all admitted. No nonemptiness, positive-rank, boundedness, flatness of
g, or Noetherian assumption is present. The common universe `u₁` is retained for
schemes and module sheaves, with the independent localization universe `w₁` used
only where the dependency declarations require it.

For the one-definition check I searched Mathlib and the slopmaster2 source with
LeanFinder/Loogle and `rg` for perfect-complex dualizability, tensor-Hom duality,
and the full declaration name. The searches found only generic rigid-category and
module-derived declarations; no scheme-level statement matching this node exists.
The project search likewise found no existing `perfect_tensor_hom_duality`.
The derived-tensor search found only the generic upstream construction, so the
new specialization node is necessary and is the sole added dependency.

No mismatch was found between the node and the Lean signatures, so no statement
correction or weakening was made. The only repair in this second reading is this
record of the item-by-item comparison; both modules compiled together with the
server compiler and retain `sorry` only as statement-stage proofs.

## New nodes

`def-pc-scheme-derived-tensor-structure` supplies the missing fixed K-flat derived
monoidal structure on the existing shared schemeDerivedCategory. Its module
`Sheaf.AlgebraicGeometry.DerivedTensorStructure` specializes the upstream localization
construction, using the recorded underived tensor-closed theorem and Grothendieck
structure. The only new sorry is the named theorem
`schemeModule_hasFunctorialFlatResolution`: its docstring gives the functorial
sum-of-local-sections construction and stalkwise flatness argument. The definition's
data are the upstream construction, never sorry. The unit is the degree-zero structure
sheaf and the tensor is the total tensor of K-flat representatives, with descended
constraints. Source: Stacks 06Y7 and 06YH, and 03EO for the underived adjunction.

LeanSearch was unavailable (Internal Server Error). LeanFinder returned eight generic
Tor and condensed/sheaf monoidal declarations, no variable-ring O_X specialization.
Mathlib grep for SheafOfModules closed/additive tensor and functorial flat resolutions
returned zero hits. Upstream grep found the generic derived construction; project grep
found precisely TensorClosed's underived structure. DAG search returned zero derived
monoidal nodes. The general upstream construction needs the closed/additive and
functorial-flat-resolution structures installed for O_X-modules; it alone is not an
immediately usable specialization. This module fills that missing specialization,
while reusing its actual construction and all existing notions.
