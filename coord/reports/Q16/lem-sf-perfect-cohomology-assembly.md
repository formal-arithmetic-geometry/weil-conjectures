## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.PerfectCohomologyAssembly` states
`DerivedCategory.isPerfectRingComplex_of_perfect_cohomology`, with its whole proof `sorry`.
The node is unchanged outside `lean`. No new notions or dependency modules are needed.

Source read: Stacks Project, More on Algebra, Tag 066U, `lemma-cohomology-perfect`,
using the literature cache's `more-algebra.tex`, lines 18986–18996. It states that an
object of D^b(R) whose cohomology modules are perfect is perfect, and proves this by
finite induction with canonical truncations and the two-out-of-three lemma.
The node specializes the source's ring to a commutative ring, which is retained exactly.

Hypothesis and conclusion matching:

- A commutative ring A: `{A : Type u} [CommRing A]`.
- An object K in D(A): `[HasDerivedCategory.{w} (ModuleCat.{u} A)]` and
  `(K : DerivedCategory (ModuleCat.{u} A))`. The localization universe w is independent
  of the coefficient/module universe u, as in the recorded dependency interface.
- H^i(K) vanishes outside a finite integer interval: `hbounded` is
  `∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero ((homologyFunctor ... i).obj K)`.
  There is no requirement that K have bounded terms. A reversed interval simply forces
  all cohomology to vanish, which is also covered by any ordinary interval.
- Every integer i has perfect H^i(K) placed in degree zero: `hperfect` quantifies over
  all `i : ℤ` and applies `IsPerfectRingComplex` to
  `(singleFunctor (ModuleCat.{u} A) 0).obj ((homologyFunctor ... i).obj K)`.
  This requires a separate bounded finite-projective model for each module, with no
  uniform projective-resolution bound.
- K is perfect, meaning isomorphic to a bounded complex of finitely generated
  projective modules: the conclusion is `IsPerfectRingComplex K`, precisely the
  recorded definition (existential bounded model, finite/projective terms, derived iso).

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.singleFunctor` (degree-zero complex), with
  `DerivedCategory.Q` supplying the localization used by perfectness.
  Read their signatures and documentation, including the independent localization size.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor` and its documented factorization through Q.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`:
  `DerivedCategory.IsPerfectRingComplex`, read in full. This is the recorded declaration
  of `def-pc-perfect-ring-complex`, used for both the hypothesis and conclusion.
- Proof-only import `Sheaf.CategoryTheory.TruncationTriangle`:
  `DerivedCategory.truncation_triangle`, whose full signature and proof-plan source
  were read. The docstring carries the five steps of this item's DAG proof, including
  the fixed cohomology identifications, zero base case, shifts, finite extension
  induction, and final quasi-isomorphism.
- `lem-sf-perfect-ring-triangle-closure` has no recorded Lean declaration at the time
  of writing, so there is no recorded module to import. It is used only in the proof
  plan, not in this statement's interface. The upstream
  `DerivedCategory.isPerfect_obj₂_of_distTriang` was read as a related specialized
  theorem, not used as a replacement for this item.

Edge cases checked before writing: the zero ring; zero objects and entirely acyclic
complexes (empty cohomological support); cohomology in just degree zero or any other
single integer; gaps inside the support interval; negative bounds; arbitrarily large
individual finite projective resolutions. Neither Noetherianity, finite global
dimension, a field, nor finite generation alone is substituted for the stated
perfectness hypotheses. `IsZero` is used on an actual module-category object.
All universe and term variables are explicitly bound; no local notation, helper
instances, or additional hypotheses are introduced.

Searches performed with `msearch.py Q16 lem-sf-perfect-cohomology-assembly`:

- LeanFinder: `A bounded derived complex over a commutative ring is perfect if each
  cohomology module in degree zero is perfect`. Eight hits, including
  `CochainComplex.IsKProjective`, `DerivedCategory.isLE_iff`, `DerivedCategory.isGE_iff`,
  and bounded representative existence; none states perfectness from perfect cohomology.
- Loogle: `DerivedCategory, "Perfect"`. Zero hits (repeated with the same result).
- Mathlib grep: `IsPerfect|cohomology_perfect|perfect.*cohomology` in
  `Algebra/Homology`. Zero hits (repeated with the same result).
- LeanSearch: `Bounded cohomology with perfect cohomology modules implies a perfect
  complex over a ring`. Service unavailable: Internal Server Error; not a negative match.
- `rg` of the upstream `WeilConjectures/` and project `lean/Sheaf/` for
  `perfect.*[Cc]ohomology|[Cc]ohomology.*[Pp]erfect|isPerfect.*homology|IsPerfectRingComplex`:
  found the recorded definition and results about finite Tor amplitude, fields,
  geometric cohomology, and the opposite direction over coherent/Noetherian rings;
  no exact assembly theorem. Read the declaration list and relevant signatures in
  upstream `CategoryTheory/DerivedCategory/Perfect.lean`; its finite-Tor and field
  criteria have different hypotheses. The upstream node-id search returned no hits.
- `rg` of `dag/lean_names_upstream.json` for the corresponding name/concept patterns:
  found `DerivedCategory.isPerfect_of_flat_of_finite_homology`, a different criterion.
- Exact proposed declaration-name grep in upstream, Mathlib, and the project's Lean:
  no preexisting declaration with the chosen name.

No statement correction, disputed statement, or dependency-record fault was found.
The independent second reading is intentionally left to the dispatched second reader.

## Second reading by Q16

I independently opened the sandbox node and Lean file, both statement-dependency
nodes and their recorded declarations, and the source at
`/home/ubuntu/weil-launcher-nt/literature/stacks-project/more-algebra.tex`.
Tag 066U (`lemma-cohomology-perfect`, lines 18986–18996) assumes only a ring,
an object of D^b(R), and perfect cohomology modules. The surrounding definition
`definition-perfect` (lines 18870–18879) defines a perfect module by perfectness
of M[0], and a perfect derived object by a bounded finite-projective model.
There is no standing Noetherian, regularity, field, or characteristic assumption.
The commutative-ring specialization is explicit in the DAG node and is retained.

The full object/hypothesis/conclusion checklist is:

1. A commutative ring A is `{A : Type u} [CommRing A]`: exact. No nonzero-ring
   assumption is present.
2. K is an arbitrary object of D(A), rendered by
   `(K : DerivedCategory (ModuleCat.{u} A))` under
   `[HasDerivedCategory.{w} (ModuleCat.{u} A)]`: exact. I read the Mathlib
   `HasDerivedCategory`, `DerivedCategory`, and `Q` definitions in Basic.lean.
   This instance selects the localization in the node's chosen morphism universe;
   it adds no finiteness hypothesis. Both u and w are explicitly declared and
   independent. ModuleCat supplies its canonical abelian structure.
3. Cohomology vanishes outside some finite interval of integers: `hbounded`
   existentially quantifies a,b and requires `IsZero` of
   `((homologyFunctor (ModuleCat.{u} A) i).obj K)` when `i < a ∨ b < i`:
   exact. I read `homologyFunctor` and `homologyFunctorFactors` in
   HomologySequence.lean: these are the cohomology of the localized cochain
   complex, rather than its terms or a different cohomology theory.
4. For every integer i, H^i(K) in degree zero is perfect: `hperfect` has
   `∀ i : ℤ` outside `IsPerfectRingComplex`, applied to
   `(singleFunctor (ModuleCat.{u} A) 0).obj` of precisely that cohomology module:
   exact. Basic.lean's `singleFunctor` and `singleFunctorIsoCompQ` identify this
   object with the ordinary single complex localized by Q. Perfectness is a
   separate existential model for each i, so no uniform resolution bound is added.
5. K is isomorphic in D(A) to a bounded complex of finitely generated projective
   modules: the conclusion `IsPerfectRingComplex K` is exact. I opened the
   recorded PerfectRingComplexGeneral.lean, whose actual definition quantifies
   P,a,b, imposes `P.IsStrictlyGE a` and `P.IsStrictlyLE b`, requires both
   `Module.Projective` and `Module.Finite` in every degree, and contains
   `Nonempty (K ≅ Q.obj P)`. It has real predicate data, with no sorry or choice
   hidden in a definition. This same recorded predicate occurs in hypothesis 4.

Edge cases: the zero ring, the zero object, completely acyclic complexes, gaps
in the cohomology support, negative degrees, and support only in degree zero or
one other integer are included. There is no empty index-set binder or scheme in
this statement; empty cohomological support is allowed. Omitting `a ≤ b` in
`hbounded` is harmless: if a>b its condition forces every cohomology object to be
zero, which also satisfies the condition for a=b=0. Conversely any finite support
has ordered integer bounds. Arbitrarily long finite resolutions of individual
cohomology modules are allowed. No characteristic or universe equality is imposed.
The module universe can be chosen large enough for any given ring and complex.

Independent searches (using different wording from the first reader):

- LeanFinder, `finite number of nonzero homology groups admitting finite
  projective resolutions gives perfect derived object`: eight hits for
  K-projectivity, projective resolutions, Ext, and left-derived vanishing;
  none gives this theorem. A separate exact-name LeanFinder query returned
  perfect-ring/perfection results, also unrelated.
- Loogle, `DerivedCategory, "homology"`: found the canonical homology functor,
  its factorization through Q, shift and homology-sequence APIs; no perfectness
  assembly criterion.
- LeanSearch, `Finite extensions of shifted modules with finite projective
  resolutions are perfect objects of the derived category`: eight hits about
  projective resolutions, K-projective shifts, and Ext; no exact statement.
- `rg` across all Mathlib, upstream WeilConjectures, project lean/Sheaf, and
  dag/lean_names_upstream.json with cohomology/perfect and homology/perfect
  patterns and the proposed exact name found no duplicate. I opened upstream
  Perfect.lean's definitions and relevant signatures: `IsPerfect.finite_homology`
  is the opposite implication with Noetherianity; `isPerfect_of_finiteTorAmplitude`
  assumes Noetherianity, finite cohomology and Tor amplitude; `isPerfect_iff` is
  restricted to a field. None is the present all-commutative-rings criterion.

I also opened the proof-only dependency `DerivedCategory.truncation_triangle`
against its node. Its arbitrary-abelian-category signature supplies the canonical
truncations, the single cohomology object in degree q, and the distinguished
triangle required by this proof. The triangle-closure proof node has no Lean
record, so no corresponding import is missing at delivery time. No new node or
dependency module is included and no statement correction or citer audit is needed.
The statement docstring faithfully records all five DAG proof steps: fixed
representative and cohomology identifications, the acyclic base, shifted models,
finite truncation induction, and the final quasi-isomorphism. The only theorem
proof is `by sorry`; there are no added definitions, local instances, notation,
unbound universes, or auto-implicit variables. The source/blueprint docstrings,
topic, namespace, and line widths meet the conventions.

Verdict: no mathematical or interface mismatch found. I changed only this report
by adding the independent reading; the correct Lean and node signature are retained.

Validation: the prescribed `scompile.py` run finished successfully for the only
module, with no errors or warnings. A direct comparison confirmed that
`lean.statement` is verbatim the theorem signature, and every Lean line has at
most 100 characters.
