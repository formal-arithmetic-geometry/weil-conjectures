## Worker report

The module `lean/Sheaf/Paper/DoldKanHomology.lean` defines `ModuleComplex`, the
connective truncation, the inverse Dold--Kan functor, and the underlying simplicial-set
realization. `DgCategory` states graded composition, the Leibniz differential, closed
units, associativity, and both unit laws explicitly. `DgFunctor` records chain maps
preserving units and composition. `SimplicialDgCategory` records the simplicial
mapping-category data, the hom-complex comparisons, and its coherent nerve. The theorem
packages all clauses in `Statement` and leaves only its proof as `sorry`.

The theorem hypothesis is exactly a coefficient type `Λ : Type u` with `[CommRing Λ]`.
`ModuleComplex.{u,v} Λ` is a cochain complex in `ModuleCat.{v} Λ`. The `kan` field is
the Kan condition on every realization. `piZero` gives the component set and degree-zero
homology bijection. `piPositive` quantifies every `m : ℕ`, every vertex `z`, and
identifies the based group in dimension `m + 1` with homology in cochain degree
`-(m+1)`. `translation` carries the zero realization point to the chosen vertex.
`weakEquivalence` uses the enhanced weak-equivalence predicate and exactly the
isomorphism condition for every `r ≤ 0`. `dgRealization` quantifies every small
`DgCategory` and supplies its simplicial enrichment and coherent nerve.

The statement dependencies used are:

* `def-weil-size-convention`: a universe convention, rendered by explicit `u` and `v`.
* `def-weil-abstract-derived-category`: Mathlib's `CochainComplex` and homology.
* `def-cbc-enhanced-diagrams-cones`: `SSet.Enhanced.IsWeakHomotopyEquivalence`.
* `lem-coef-coherent-nerve-comparison`: `CoherentNerve.SCat` and
  `CoherentNerve.nerveFunctor`.

Edge cases checked include the zero coefficient ring, the zero complex, a one-term
complex in degree zero, a complex concentrated in degree `-m`, `m = 0`, an arbitrary
vertex rather than zero, and acyclic complexes. The truncation retains degree-zero
cycles, so the zeroth homology clause is not replaced by the degree-zero term. Empty
outer-horn correction loops are covered by the proof text in the node.

Searches made before writing the module:

* `msearch.py leanfinder`: “Dold Kan homotopy groups of simplicial modules and lax
  monoidal realization of differential graded categories”; normalization and Moore hits
  only, no complete match.
* `msearch.py loogle`: `CategoryTheory.Abelian.DoldKan.equivalence`; exact normalization
  equivalence only.
* `msearch.py grep`: `DGCategory|DgCategory|DoldKan|laxMonoidal`; no full match.
* `rg` over Mathlib, `WeilConjectures/`, and `lean/Sheaf/`: no declaration of this
  generic statement; the existing presheaf dg file is a different specialization.

The earlier draft's translation equation fixed the selected vertex. It was corrected to
require that translation carry the zero point to the selected vertex. No
`STATEMENT-DISPUTED` flag or node fault was found.

## Earlier second reading (a previous round; superseded)

I reopened the node and module and checked each binder against the node: `Λ`, both
explicit universes, every complex and vertex, all `r ≤ 0`, and every dg-category object,
hom complex, degree, composition, and identity. The translation equation has zero on the
left and the selected vertex on the right. The weak-equivalence field retains the
component and all positive based homotopy groups through the recorded enhanced predicate.
The dg structures have concrete data and equations; all declarations have source and
blueprint docstrings. The file compiles cleanly with `scompile.py`.


## Second reading by Q46

I read the DAG statement and its seven proof steps, Stacks `simplicial.tex`
`theorem-dold-kan` (019G) and `lemma-simplicial-group-kan` (08NZ), the actual
Mathlib normalization, inverse, counit, Moore projection, and truncation declarations,
and the recorded dependency interfaces. I also downloaded Higher Algebra (2017)
to `scratchpad/HA.pdf` and read Constructions the project server and the project server,
Example the project server, and Remarks the project server--14. Choudhury--Gallauer,
https://arxiv.org/pdf/1511.02828, §3.3, Fact 3.14(3)--(4), was read online.
Stacks 019G assumes an abelian category, with no field, finiteness, boundedness,
or characteristic hypothesis. Modules over the supplied commutative ring satisfy
that assumption. The additional homotopy and enrichment clauses are sourced to
HA and Choudhury--Gallauer, not attributed to 019G alone.

The object/hypothesis/conclusion checklist and verdicts are:

1. A commutative coefficient ring, without nonzero or field assumptions:
   `(Λ : Type u) [CommRing Λ]` in `doldKanHomology`; exact.
2. Arbitrary module complexes with independent coefficient/module bounds:
   `ModuleComplex.{u,v} Λ = CochainComplex (ModuleCat.{v} Λ) ℤ`;
   no connectivity, boundedness, Noetherian, or finite generation hypothesis; exact.
3. The good connective truncation with degree-zero cycles and terms E^(-m):
   `connectiveTruncation` uses `embeddingDownNat.truncLE'Functor`. I read
   `truncLE'XIso`, `truncLE'XIsoCycles`, the differential formulas, and the
   natural inclusion into restriction in `Embedding/TruncLE.lean`.
   Degree zero is cycles, not E^0 or its quotient by boundaries; exact.
4. Normalized chains and its inverse: `Abelian.DoldKan.equivalence`, `N`, `Γ`,
   and its counit, in Mathlib's `DoldKan/Equivalence.lean`. `simplicialModule`
   is truncation followed by this existing Γ. `simplicialRealization` forgets
   its module structure degree by degree. No second Dold--Kan equivalence; exact.
5. Kan condition including outer horns: `Statement.kan` uses `SSet.KanComplex`
   for every E. The proof docstring includes the two correction loops and their
   empty endpoint cases; exact.
6. Components naturally identified with H^0: `Statement.piZero` is a single
   family of equivalences; `piZero_natural` relates those very same equivalences
   for every cochain map. This repairs the per-map existential choices; exact.
7. Every positive based homotopy group: `piPositive E m z` uses `Fin (m+1)`
   and H^(-(m+1)), at every vertex, hence includes pi_1 when m=0. Its type is
   `≃* Multiplicative (...)`, so it preserves the group law rather than only
   identifying the underlying sets. `piPositive_natural` relates the same
   global family for every f, using the canonical equality of realization
   basepoints. `vertexPoint_natural` is the named postponed functoriality
   assertion needed for that transport; exact.
8. Translation at every vertex: `translation` is a simplicial isomorphism;
   `translation_formula` specifies addition by the constant degeneracy of z
   in every dimension. `translation_zero` specifies its action on zero;
   `translation_groups` requires the homology comparisons to agree with
   translation from zero. This repairs the arbitrary homeomorphism with the
   same effect on one point; exact.
9. Weak equivalences iff all cohomology maps in degrees r≤0 are isomorphisms:
   `weakEquivalence` uses exactly `SSet.Enhanced.IsWeakHomotopyEquivalence`.
   I read its definition: components and every positive based realization
   homotopy group at every realization point, not just at vertices; exact.
10. Small dg Λ-categories and dg functors: the draft's ad hoc `DgCategory` and
    `DgFunctor` are removed. The recorded landed `CategoryTheory.Dg.Cat`,
    `Dg.Fun`, `Dg.hom`, `Dg.mul`, and `Dg.unit` are used from
    `Sheaf.CategoryTheory.DgCategoryFreeCellCalculus`. I opened their signatures:
    `Cat` is Mathlib's `EnrichedCat` over cochain module complexes, so
    composition really is bilinear, associative, unital, and a chain map.
    Its category structure has dg functors as morphisms. The owning node
    `lem-coef-dgcat-free-cell-calculus` is added to stmt_deps; exact.
11. Size of the dg category: that existing interface requires its ring, modules,
    and object set to have a common bound. To avoid equating u and v or excluding
    categories larger than the original ring, `Statement.dgRealization` applies
    it to `ULift.{v} Λ`, at bound `max u v`. The real definitions
    `coefficientEquivalence` and `coefficientComplexEquivalence` explicitly
    transport by `ULift.ringEquiv.symm` using Mathlib's scalar-restriction
    equivalence, degree by degree. Restriction preserves underlying modules,
    differentials, and additive maps; bilinear composition and its identities
    transport along this ring isomorphism. The natural isomorphism
    `coefficient_realization` compares S over the lifted ring with S of the
    transported Λ-complex. `coefficient_realization_value` fixes that comparison
    on every normalized simplex generator, so it is the canonical coefficient
    transport, not an arbitrary isomorphism or an assumption on a chosen lift.
    Both the lift by zero and every larger v are included.
    This is the same coefficient ring
    up to the specified canonical isomorphism, with an arbitrary common size
    bound, not an extra equality of universes or a field assumption; exact.
12. Same objects and realized hom complexes: `DgRealization.objects_type`
    gives equality of the object types, `objects_eq` fixes the identification
    to its equality transport, and `homComparison` identifies each enriched
    hom with S of the original hom complex; exact.
13. Alexander--Whitney composition and original identity vertices:
    `simplexValue` is actual data obtained from face restriction, the Moore
    projection, the existing counit, and the truncation inclusion. `frontFace`
    and `backFace` are the actual monotone maps. `aw_composition` specifies
    on every p-simplex generator the sum over k=0,...,p of the front/back
    evaluations followed by `Dg.mul`, with the explicit integer degree cast.
    The order is b (front) then a (back), as in the node's m(b tensor a)D.
    `identity_vertex` specifies the original degree-zero unit. These formulas
    replace unrelated fields merely named `awComposition` and `awIdentity`;
    exact.
14. Naturality in dg functors and composition: `realization` is a functor on
    the existing category of dg categories; `objects_natural` and `hom_natural`
    identify its object and hom maps with the given dg functor. Composition
    is already fixed in every degree by `aw_composition`; exact.
15. Coherent nerve and the underlying infinity category: the nerve is exactly
    `CoherentNerve.nerveFunctor.obj (realization.obj B)`, using the recorded
    construction. `locally_kan`, `nerve_quasicategory`, and
    `mapping_weak_equivalence` state the actual local Kan, quasicategory,
    and mapping-space assertions. The `comparison` field is the existing
    `CoherentNerveComparisonStatement`, whose `CoherentMappingComparison`
    has its full simplex formula, vertex normalization, weak equivalence,
    and naturality in enriched functors; `composition_naturality` supplies
    its coherent composition 2-simplex. I read these fields in full.
    Together with (13)--(14), this gives the asserted mapping comparisons,
    original closed arrows, composition, and dg-functor naturality. The draft
    had only a freely chosen nerve and hom isomorphisms; repaired, exact.

Edge cases: the zero coefficient ring is allowed; no `[Nontrivial Λ]` occurs.
The zero complex and acyclic complexes give trivial homotopy groups. A complex
concentrated in degree zero uses H^0, not its full degree-zero term in general;
a complex concentrated in negative degree retains that homotopy group, including
m=0/pi_1. Positive cochain degrees have no effect after the good truncation.
All vertices, including zero, and all realization basepoints are retained.
An empty dg category is allowed by `EnrichedCat`; objects_type covers it.
The Alexander--Whitney sum for p=0 has one term, and its two faces are identities,
so closed degree-zero composition is retained. There is no characteristic
restriction. `u` and `v` remain independent; the larger dg bound uses the
explicit canonical coefficient equivalence above.

Independent searches used different queries from the first worker:

- `msearch.py leanfinder`: “homotopy groups simplicial abelian group normalized
  chains Alexander Whitney enriched category”; eight normalization/Moore hits,
  no theorem with all the node's clauses.
- `msearch.py loogle`: `CategoryTheory.Abelian.DoldKan.Γ`; found the existing
  inverse and equivalence_inverse, both opened and reused.
- `msearch.py leansearch`: “Dold Kan simplicial modules homotopy groups dg
  category realization”; eight Dold--Kan normalization/homotopy hits, no complete
  realization theorem.
- `msearch.py grep`: `DgCategory|DGCategory|AlexanderWhitney|MooreComplex`;
  normalization infrastructure, no complete theorem.
- Direct `rg` over Mathlib's AlgebraicTopology and Homology, all upstream
  WeilConjectures, project lean/Sheaf, and dag/lean_names_upstream.json:
  searched `dgCategory`, `differential graded categor`, `normalizedSimplex`,
  `Alexander.Whitney`, `shuffle`, and candidate declaration names. This found
  the overlooked existing Dg.Cat interface, which is now reused. The integral
  dg interface in SemiFreeDGModule has a different coefficient specialization.
  No full realization theorem or collision with the new helper names was found.

Other repairs: all declaration docstrings now carry their source and blueprint
id. The theorem docstring carries all seven proof steps and names the proof
inputs. Existing proof-dependency modules are imported; the three unstated
proof inputs have no module to import and are not restated as independent theorems.
No new definition node or dependency module is needed: the extra simplex maps,
coefficient transport, and basepoint transport belong to the construction stated
by this item. Every definition has concrete data; only `vertexPoint_natural`
and `doldKanHomology` have postponed proofs, both listed in lean.declarations
and covered by the node's functoriality/proof text. No natural-language statement
correction was needed, and no target statement or source file was modified.

Validation: `scompile.py Q46 lem-cbc-dold-kan-homology
lean/Sheaf/Paper/DoldKanHomology.lean` passed in both sandbox and module modes
with no errors and no warnings, including after the explicit coefficient-realization
comparison was added (2.9 s and 4.1 s). All universes and variables
are explicitly bound; no private definitions, local instances, or local notation
are used. The main lean.statement signature is unchanged and agrees verbatim
with the declaration. This section supersedes the earlier reading and its
claims that the draft's dg and naturality clauses were sufficient.
