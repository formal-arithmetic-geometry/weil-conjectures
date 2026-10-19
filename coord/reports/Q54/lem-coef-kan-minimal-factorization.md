## Worker report

The module `Sheaf.AlgebraicTopology.SimplicialSet.KanMinimalFactorization` states
`SSet.exists_subcomplex_retract_simplexwise_product`. It contains one theorem with
`sorry`, no new definition, and no auxiliary theorem. The docstring includes all
seventeen proof steps from the DAG node, including the moving-boundary correction,
the boundary lifting correction, and the transport/rigidity argument. The node is
unchanged except for its `lean` record.

Clause-by-clause comparison:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Small simplicial sets X and Y, with no Kan hypothesis on either | `{X Y : SSet.{u}}`, with arbitrary explicit `universe u` and no `KanComplex X` or `KanComplex Y` binder |
| Simplicial map p which lifts every positive-dimensional horn, including outer horns | `(p : X ⟶ Y) [Fibration p]` under `open SSet.modelCategoryQuillen`; the existing fibration structure is `J.rlp` with `J = ⨆ n, ofHoms (fun i : Fin (n + 2) ↦ Λ[n + 1, i].ι)` |
| A simplicial subset X′ of X | `∃ (A : X.Subcomplex)`; `A.toSSet` is its underlying simplicial set |
| Its inclusion s | The canonical inclusion `A.ι : A.toSSet ⟶ X`, rather than an arbitrary monomorphism |
| A retraction r with rs = 1 | `∃ (r : X ⟶ A.toSSet), A.ι ≫ r = 𝟙 A.toSSet` (Lean composition is left-to-right) |
| q = ps and p = qr | q is written directly as `A.ι ≫ p`, and the equation is `p = r ≫ (A.ι ≫ p)` |
| r lifts all boundary inclusions, including n = 0 | `∀ n : ℕ, HasLiftingProperty (boundary.{u} n).ι r`; no positivity restriction |
| Boundary is the union of the proper faces, with empty boundary in dimension zero | Existing `SSet.boundary`, with `boundary_eq_iSup` and `boundary_zero` in Mathlib |
| q is a Kan fibration | `Fibration (A.ι ≫ p)` |
| Every n ≥ 0 and every simplex y in Y | `∀ (n : ℕ) (y : (Δ[n] : SSet.{u}) ⟶ Y)` |
| A Kan complex F_y, possibly empty | `∃ (F : SSet.{u}), KanComplex F ∧ ...`, without an inhabitance/nonemptiness binder |
| Isomorphism Δⁿ ×_Y X′ ≅ Δⁿ × F_y | `∃ (e : pullback y (A.ι ≫ p) ≅ ((Δ[n] : SSet.{u}) ⊗ F))` |
| The isomorphism is over Δⁿ | `e.hom ≫ fst (Δ[n] : SSet.{u}) F = pullback.fst y (A.ι ≫ p)` |
| Products and pullbacks use the simplicial coordinate convention | The tensor is Mathlib's chosen degreewise product from `SSet.Monoidal`; the categorical pullback is the Mathlib pullback of simplicial sets (computed pointwise), and its canonical first projection is used |

Dependency interfaces read and used:

- `def-cbc-enhanced-diagrams-cones`: imported publicly as
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`. I read its module docstring and
  the recorded declaration `SSet.Enhanced.coneCategory` with its full signature
  and docstring. The statement needs the node's existing Mathlib simplicial
  primitives (`SSet`, `stdSimplex`, `KanComplex`, and the degreewise product),
  not its cone construction. No private copy of these notions was introduced.
- The public import
  `Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations` supplies the
  horn-defined `HomotopicalAlgebra.Fibration` scoped structure. I read `I`, `J`,
  `fibrations_eq`, and `fibration_iff`, as well as `KanComplex` and
  `KanComplex.hornFilling` in `SSet.KanComplex`.
- The proof dependency `lem-cbc-internal-hom-fibration-corner-map` is the Mathlib
  leaf `SSet.fibration_pullbackObjObjπ` in
  `Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct`,
  imported non-publicly. Its full signature allows arbitrary simplicial bases
  and uses only `[Mono i]` and `[Fibration p]`.
- The proof dependency `lem-weil-pbc-well-ordering-theorem` is the Mathlib leaf
  `exists_wellFoundedLT` in `Mathlib.SetTheory.Cardinal.Order`, imported
  non-publicly; its signature and source docstring were read.
- The proof dependency `lem-coef-infinity-monomorphism-boundary-cells` is the
  Mathlib leaf `SSet.relativeCellComplexOfMono` in
  `Mathlib.AlgebraicTopology.SimplicialSet.Skeleton` (publicly imported through
  `CategoryWithFibrations`). Its signature, docstring, and construction give
  precisely boundary cells indexed by the nondegenerate simplices outside X.

Edge cases checked before writing:

- For n = 0 the boundary quantifier is still present and `boundary_zero` identifies
  its source with the empty simplicial set; the theorem thus retains vertex
  surjectivity of r. The simplexwise product quantifier also includes n = 0.
- For an empty X one can have empty A and F; no `Nonempty` or vertex assumption
  rules this out. The empty simplicial set satisfies the positive horn condition.
- If Y is empty then X must be empty for a map p to exist; no hypothesis excludes
  this case. If a simplex pullback is empty, the fiber is allowed to be empty.
- The identity of a non-Kan simplicial set is a Kan fibration; the theorem imposes
  no Kan condition on X or Y and covers this case. Over a simplex the identity
  has the one-point product fiber.
- X and Y and the subcomplex/fibers use the same arbitrary universe u; no extra
  equality of distinct category universes or restriction to a concrete universe
  was imposed. The subset and fibers of a small simplicial set fit in this universe.
- The projection equation requires an isomorphism over the simplex, not just an
  unstructured isomorphism of total simplicial sets. No minimality conclusion was
  added: the node asserts its consequences but does not require a separate
  minimal-fibration predicate in the statement.

Searches (all run with the prescribed Q54/item wrapper where applicable):

- LeanFinder query: `Every Kan fibration retracts onto a subfibration with boundary
  lifting retraction and product trivializations over each simplex`. Eight hits:
  `SSet.modelCategoryQuillen.fibrations_eq`, `fibration_iff`, horn-lifting
  instances, and generic fibrant-object/retract interfaces. None asserts the
  required subcomplex, boundary-lifting retraction, and product trivializations.
- Loogle query: `"SSet", "minimal"`. Zero hits.
- LeanSearch query: `A Kan fibration factors through a retract subcomplex with
  right lifting against boundaries and a product over every standard simplex`.
  Eight hits: generic Brown factorization, stability under retracts, and horn
  lifting. Brown factorization assumes a model category (and its explicit
  construction assumes fibrant objects) and is not this minimal-subfibration
  existence theorem.
- Mathlib grep wrapper, subdirectory `AlgebraicTopology`, query
  `minimalFibration|minimal_fibration|minimal.*[Ff]ibration|[Ff]ibration.*minimal`:
  zero hits.
- Direct rg with the same terminology and the blueprint item ID across
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, shared `lean/Sheaf`, and
  Mathlib `AlgebraicTopology`: zero hits. The chosen declaration name was also
  searched in `dag/lean_names_upstream.json`, all Mathlib, the source repository,
  and shared `lean/Sheaf`: zero hits.

Source check: opened Hovey online at
https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hovey-model-cats.pdf
and read Theorem 3.5.9, Corollary 3.5.7, and Definition 3.5.1 (PDF pages 98,
101--104, printed pp. 88, 92--95). They give the retract/minimal factorization
and the isomorphisms over standard simplices. No statement correction, new node,
dependency repair, or statement dispute is needed.

Validation: `scompile.py Q54 lem-coef-kan-minimal-factorization` compiled this
single module, including its library-form copy, with no errors or warnings
(the only postponed proof is the required `sorry`). No global build was run.

## Earlier second reading (a previous round; superseded)

Pending: the dispatcher starts an independent second reader after this worker
returns. This paragraph records no second-reading verdict.

## Second reading by Q54

I independently opened the node, the complete Lean module, the statement-dependency
node and its recorded module, and the three proof-dependency declarations. There
is no repair note for this item, no `statement_change`, no new definition node,
and no dependency module in this delivery. Verdict: the Lean says exactly what
the node says. I found no mathematical or signature mismatch and changed no Lean
or DAG content; this section records the independent review and fresh validation.

The object/hypothesis/conclusion checklist I extracted from the node is below.
Every row passes.

| Node object, hypothesis, or conclusion | Lean rendering and verdict |
| --- | --- |
| Arbitrary small simplicial sets X and Y | `{X Y : SSet.{u}}`, with explicit arbitrary `universe u`; pass. |
| A simplicial map p | `(p : X ⟶ Y)`; pass. |
| p lifts all horns in positive dimensions, including the two outer horns | `[Fibration p]`, interpreted by `modelCategoryQuillen` as `J.rlp`; `J` ranges over every `n + 1` and every `i : Fin (n + 2)`; pass. |
| No Kan assumption on X or Y | Neither binder has a `KanComplex` assumption; pass. |
| A simplicial subset X′ of X | `∃ (A : X.Subcomplex)`; Mathlib defines this as `Subfunctor X`; pass. |
| Its inclusion s | `A.ι : A.toSSet ⟶ X`, the canonical subtype inclusion; pass. |
| A retraction r onto X′ | `(r : X ⟶ A.toSSet)` and `A.ι ≫ r = 𝟙 A.toSSet`; this is rs = 1 in mathematical composition order; pass. |
| q is p restricted to X′ | Every occurrence of q is the explicit composite `A.ι ≫ p`; no arbitrary replacement map; pass. |
| p factors through r and q | `p = r ≫ (A.ι ≫ p)`; pass. |
| r lifts every boundary inclusion, including dimension zero | `∀ n : ℕ, HasLiftingProperty (boundary.{u} n).ι r`; pass. |
| Boundary means the union of proper faces, empty at zero | Mathlib `boundary_eq_iSup` identifies this union and `boundary_zero` gives the empty subcomplex; pass. |
| q is a Kan fibration | `Fibration (A.ι ≫ p)` using the same scoped horn-lifting structure; pass. |
| For every nonnegative n and every simplex y of Y | `∀ (n : ℕ) (y : (Δ[n] : SSet.{u}) ⟶ Y)`; pass. |
| There exists a Kan fiber F_y, allowed to depend on n and y | `∃ (F : SSet.{u}), KanComplex F ∧ ...`, inside those universal quantifiers; pass. |
| F_y may be empty | No `Nonempty`, chosen vertex, or inhabitance instance occurs; pass. |
| The pullback is isomorphic to the product | `∃ (e : pullback y (A.ι ≫ p) ≅ ((Δ[n] : SSet.{u}) ⊗ F))`; pass. |
| This is an isomorphism over the simplex | `e.hom ≫ fst (Δ[n] : SSet.{u}) F = pullback.fst y (A.ι ≫ p)`; the inverse also commutes with projections by composing this equality with `e.inv`; pass. |
| Products and pullbacks are simplicial, computed degreewise | The tensor in `SSet.Monoidal` is the Cartesian degreewise product, not a tensor of coefficients; the presheaf category pullback and its projection give the indicated simplicial pullback up to its canonical isomorphism; pass. |

Source check: I independently read [Hovey, Model Categories,
Section 3.5](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hovey-model-cats.pdf),
especially Definition 3.5.1, Corollary 3.5.7, and Theorem 3.5.9
(PDF pages 98, 101--104). The theorem supplies the retract and boundary lifting;
the corollary supplies local triviality, with the precise over-simplex meaning
given by the definition. The section imposes no Kan condition on the total space
or base and no nonemptiness condition here. The nonempty-fiber assumptions in
Corollaries 3.5.2 and 3.5.10 belong to those separate results.

Dependency verification: `def-cbc-enhanced-diagrams-cones` explicitly uses
Mathlib's `SSet`, `stdSimplex`, `horn`, `KanComplex`, and Cartesian simplicial
product. I read its imports, module docstring, and `SSet.Enhanced.coneCategory`
signature and body; the cone construction is not needed in this statement and
none of its specialized hypotheses are imported as assumptions. I opened
`CategoryWithFibrations.lean` at `I`, `J`, the scoped instance, `fibrations_eq`,
and `fibration_iff`, and `KanComplex.lean` at the fibrant-object abbreviation
and horn-filling characterization. These definitions agree with the node.
I also read `Subcomplex.toSSet`, `Subcomplex.ι`, `boundary_eq_iSup`,
`boundary_zero`, and the coordinate formulas in `SSet.Monoidal`.

The proof dependencies are usable exactly as recorded: I opened
`SSet.fibration_pullbackObjObjπ` in `AnodyneExtensions/PushoutProduct.lean`
(arbitrary simplicial objects, `[Mono i]`, `[Fibration p]`),
`exists_wellFoundedLT` in `SetTheory/Cardinal/Order.lean` (an arbitrary type),
and `SSet.relativeCellComplexOfMono` in `SimplicialSet/Skeleton.lean`
(arbitrary simplicial monomorphism, boundary cells in every dimension).
The first two have direct non-public imports, and the last is imported publicly
through `CategoryWithFibrations`. No missing notion, private copy, or interface
repair is needed.

Edge cases: both universal dimension binders include zero. In the lifting clause
this gives the empty-boundary square, so vertex surjectivity is retained. Empty
X permits empty A and F; empty Y forces empty X whenever p exists. An empty
pullback may have empty Kan fiber. Identity maps of non-Kan simplicial sets are
covered because the theorem constrains only p. Over a point the product clause
is the fiber itself, and no minimality conclusion beyond the node's clauses is
added. There is no index set, coefficient ring, characteristic, scheme, or
additive zero object in this statement. Universes are explicitly bound: the
subset and fibers of `SSet.{u}` stay in `u`, and the same arbitrary `u` imposes
no finite-dimensional, countability, or inhabitance restriction.

Independent duplicate searches used different wording from the first worker:

- LeanFinder through `msearch.py`: `Simplicial horn lifting map admits a split
  subobject and becomes a Cartesian product after restriction to each
  representable simplex`. Eight hits, all horn constructions or horn-filling
  lemmas; none supplies the retract factorization and product trivializations.
- Loogle through `msearch.py`: `"SSet", "retract"`. Nine hits, about stability
  under retracts and presentations of anodyne extensions; none states this
  existence result. The relevant fibration-retract instance was read in
  `CategoryWithFibrations.lean` and only asserts closure under retracts.
- LeanSearch through `msearch.py`: `Every simplicial Kan fibration contains a
  retract subobject whose projection is isomorphic to a product on each
  representable simplex`. Eight hits: generic retract stability, horn lifting,
  and Brown factorizations between fibrant objects. None asserts this
  subcomplex factorization or its simplexwise product conclusion.
- Grep through `msearch.py`: `simplexwise|subcomplex.*retract|retract.*subcomplex|
  triviali[sz].*simplex|bundle.*simplex` (one query, no newline). Zero hits.
- Direct `rg`, on Mathlib's simplicial sets, upstream `WeilConjectures`, and
  shared `lean/Sheaf`, searched `simplexwise`, `subcomplex.retract`,
  `retract.*subcomplex`, `fibration.*product`, `product.*fibration`,
  `locally.trivial`, and `split.*fibration`. Relevant hits are the generic
  pushout-product APIs and the consumer `KanRealizationSerre`; none states
  this factorization. Other hits concern unrelated locally trivial sheaves.
- Exact-name and module-name `rg` over all Mathlib, upstream declarations,
  shared project Lean, and `dag/lean_names_upstream.json` found no duplicate.

H5--H9: the delivered module contains exactly one theorem and its proof is
`by sorry`; it has no definition, axiom, local instance, notation, or hidden
construction. I checked the entire docstring against all seventeen node proof
steps, including the moving-boundary transport in step 7, boundary-lifting
correction in steps 9--10, and rigidity in steps 14--17. Both source/blueprint
docstrings are present, imports follow the statement/proof distinction,
`autoImplicit` is false, `u` is bound, and every Lean line is at most 100
characters. The node differs from the shared node only in `lean`, and its
`lean.statement` is verbatim the theorem signature, checked mechanically.

Fresh validation: the required `scompile.py Q54
lem-coef-kan-minimal-factorization
lean/Sheaf/AlgebraicTopology/SimplicialSet/KanMinimalFactorization.lean` compiled
both the sandbox and library-form module successfully (1.2 s and 1.3 s), with
no errors or warnings. No proof was attempted and no global build was run.

Delivery dry run: `deliver2.py Q54 lem-coef-kan-minimal-factorization --no-push`
returned `OK`: server preflight and compilation passed (dry-run commit
`fee0d1831e`).
