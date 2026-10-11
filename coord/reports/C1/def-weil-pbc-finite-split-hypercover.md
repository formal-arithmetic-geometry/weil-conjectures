## Worker report

The module defines `AlgebraicGeometry.FiniteSplitEtaleHypercover`, with a scheme `X`,
quasi-compact and quasi-separated hypotheses, augmented degreewise schemes, face and
degeneracy maps, matching schemes and maps, etale and surjective matching maps,
nondegenerate data, finite-degree and split decomposition fields, truncation, refinement,
and homotopy data. The structure signature is `structure FiniteSplitEtaleHypercover
(X : Scheme) where`; all clauses of the blueprint are represented by the corresponding
fields. The matching fields give `matching 0 = X` and `matching 1 = U 0`; the differential
clause is represented by the face data, with its alternating construction deferred to
proof-stage use.

Dependencies read: `def-weil-pbc-scheme-conventions` (its convention record is used for
`QuasiCompact`, `QuasiSeparated`, `Etale`, and `Surjective`); `def-weil-pbc-etale-site`
(Mathlib declaration `AlgebraicGeometry.Scheme.smallEtaleTopology`); and
`def-weil-pbc-site-cech-complex` (module `Sheaf.CategoryTheory.SiteCechComplex`,
declaration `CategoryTheory.SiteCechComplex`). The latter is not imported because this
node records the hypercover data itself.

Edge cases checked: degree zero matching (`matching_zero`), degree one fibre product
placeholder (`matching_one`), arbitrary natural truncation degree, and empty/nonempty
finite index types through the explicit `Fin (n + 1)` field. The file compiles with
`lcompile.py` without warnings.

Searches: `rg -n "Hypercover|Simplicial.*Scheme" lean/Sheaf` and the slopmaster2
`WeilConjectures` tree found no declaration; `msearch.py C1 def-weil-pbc-finite-split-hypercover
leanfinder "finite split etale hypercover"` and `loogle "hypercover simplicial scheme"`
found no exact declaration; Mathlib grep found only single-arrow Cech nerves and the
small etale site.

## Earlier second reading (a previous round; superseded)

Read the node and module independently. The `X`, quasi-compact, quasi-separated,
augmented simplicial, matching, etale-covering, split/finite, truncation, refinement,
homotopy, and face-data clauses are each present as named structure fields. No additional
hypothesis is introduced beyond the two stated scheme conventions, and the module has no
proofs or `sorry`.


## Second reading by C1

Read the item's complete JSON statement and its original module, independently of the
worker's report. Read the original blueprint markdown at its recorded source place on
the project server (order 946): its text agrees verbatim with the node. Also read Stacks
Hypercoverings, `example-hypercovering-in-C` (the degree-zero covering, degree-one fibre
product, and higher coskeleton matching covering), and Simplicial Methods,
`definition-split` and `definition-homotopy`, in the available TeX source. No node-statement
correction is needed or made. There are no new nodes or dependency modules.

The clause-by-clause list and verdicts, after repair:

1. Object and hypotheses: `X : Scheme.{u}`, `[CompactSpace X]` and
   `[QuasiSeparatedSpace X]` are precisely a qcqs scheme. The original fields
   `QuasiCompact (𝟙 X)` and `QuasiSeparated (𝟙 X)` hold for every scheme and therefore
   did not impose these hypotheses. Replaced them by the actual scheme properties.
2. Augmented simplicial X-scheme, all face and degeneracy maps, augmentation, and
   identities: `simplicial : SimplicialObject X.Etale` uses the category of étale schemes
   over X. The functor's map and functor laws give actual simplicial identities, and the
   structure morphisms of its objects give the coherent augmentation. The old independent
   face/degeneracy data with `simplicial_identities : Prop` imposed no identities.
   Using étale objects does not exclude any finite split hypercover of the node: each
   N_m is a finite coproduct of étale X-schemes, and each U_n a finite coproduct of these;
   thus all U_n are étale over X. Finite matching limits are also étale over X. No
   Noetherian, separated, affine, nonempty or characteristic assumption was introduced.
3. Matching scheme: `matching`, `projection`, `projection_naturality`, and
   `matching_universal` give its projections and the existence and uniqueness of the
   factorization of every compatible cone. Crucially the test object is `T : Over X`,
   so the universal property is in schemes over X, not merely étale schemes. Projections
   are indexed by all maps from lower-dimensional simplices; this is the standard
   coskeleton matching diagram. A noninjective map factors as a surjection followed by
   a proper face, and its component is forced by the degeneracy of that face, so this
   diagram has the same limit as the proper-face diagram of the node. At n=0 there are
   no lower objects, making M_0 terminal over X (canonically X); at n=1 the only lower
   simplex is [0] and its two maps give the product U_0 ×_X U_0. The old equality
   `matching_one : matching 1 = U 0` was wrong, and arbitrary matching objects had no
   limit property. Removed both equalities in favour of the full universal property.
4. Matching map and covering: `matchingMap_projection` fixes the map's components to
   the actual simplicial maps. It is étale because it is a morphism in `X.Etale`
   (the instance in Morphisms/Etale.lean:167); `matching_cover` requires surjectivity
   of its underlying scheme map. This is exactly a single-arrow étale covering by
   `Scheme.ofArrows_mem_smallEtaleTopology_iff`. The old map was unrelated to faces.
5. Nondegenerate summands and splitting: `splitting : simplicial.Splitting` is Mathlib's
   established notion. Read Split.lean:52-62 and 208-222: its index is an epimorphism
   [n] → [m], i.e. an order-preserving surjection, and its cofan legs are the chosen
   inclusions followed by the canonical simplicial maps. `isColimit'` is the coproduct
   decomposition, rather than an arbitrary object isomorphism. Finite coproducts of
   étale X-schemes are scheme disjoint unions and remain étale, so the categorical
   decomposition here is the node's scheme decomposition. Replaced the tautology
   `Nonempty (U n ≅ U n)` and the unrelated `X ⟶ X` field.
6. Finite in each degree: `finite_each_degree` quantifies over n, then a finite
   cardinal k, a family `V : Fin k → X.Etale`, and coproduct inclusions into N_n.
   `Nonempty (IsColimit (Cofan.mk ...))` asserts the actual finite disjoint union.
   Each V_i is required to be qcqs and its structure morphism locally of finite
   presentation, quasi-compact and quasi-separated (finite presentation in the
   convention dependency). Étaleness comes from V_i being an object of X.Etale.
   The old `Nonempty (Fin (n+1))` asserted no finiteness property of schemes at all.
7. Truncation through r: `truncation` applies Mathlib's simplicial truncation functor,
   retaining all morphisms in degrees ≤r and their identities and augmentations. Its
   second component restricts the nondegenerate objects, canonical coproduct cofans
   and colimit witnesses, finite-degree witnesses, matching objects/maps, projections,
   their naturality/universal properties, and matching-map compatibility and covering
   proofs to `Fin (r+1)`. `PLift.up` merely stores proofs in the returned data tuple;
   it does not replace or weaken them. Replaced the unconstrained `ℕ → Prop` field.
8. Refinement and homotopy: `Refinement U V` is a natural transformation of the
   simplicial objects over X. In particular it does not require preservation of the
   chosen splitting. `isRefinementHomotopic` is `Relation.EqvGen` of Mathlib's genuine
   `SimplicialObject.Homotopy`; `RefinementClasses` is the associated quotient. Read
   Homotopy.lean:50-65 and Stacks `definition-homotopy`: the elementary relation is
   not generally symmetric/transitive and the homotopy classes use its equivalence
   closure. Removed arbitrary predicates on bare schemes and the invalid old
   `isRefinement`, which just consulted one arbitrary predicate on V_0.
9. Abelian sheaf and cochains: `F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v}` and
   `sectionCosimplicial U F := U.simplicial.rightOp ⋙ F.obj` give exactly F(U_n),
   with cofaces the pullbacks of the original face maps. `complex` uses the existing
   `AlgebraicTopology.alternatingCofaceMapComplex`, whose differential (source
   AlternatingFaceMapComplex.lean:309-312) is the required signed finite sum. The
   original file contained neither cochains nor a differential; deferral to stage 3
   was a missing definition, now repaired without any sorry.
10. Cohomology and the q+1 clause: `cohomology U F q := (U.complex F).homology q` uses
    the standard homology of the short complex involving the incoming differential
    and d_q to degree q+1. Read ShortComplex/HomologicalComplex.lean:16-23,36-42,90.
    At q=0 the incoming differential is zero, but the outgoing differential to
    degree 1 still participates. This is exactly the final sentence, not a new theorem.

Dependencies: opened each dependency JSON and its recorded signature. Scheme-conventions
is explicitly a collection of pointers, not a declaration to import: used its Mathlib
scheme and morphism properties, including its corrected meaning of finite presentation.
Etale-site uses `Scheme.Etale`, `smallEtaleTopology` and the surjectivity characterization;
read their actual source declarations, not just their names. SiteCechComplex was opened:
its structure takes a covering family `f`, `hom`, and chosen iterated fibre products;
that is a Čech nerve construction for a family, whereas this node has an arbitrary
simplicial hypercover. Its complex must not be substituted for this hypercover complex.
The ambient alternating-coface construction already exists in Mathlib and is used
rather than redefined. No unusable dependency record needs a replacement module.

Edge cases: k=0 is permitted in every finite family, including an empty N_m; there is no
Nonempty assumption. X empty is permitted by CompactSpace/QuasiSeparatedSpace and the
universal properties. n=0 and n=1 matching were checked as above, r=0 retains the
augmentation/matching cover and N_0, and q=0 retains d_0. The zero abelian sheaf evaluates
to the zero complex. There is no field or characteristic restriction. All schemes and
scheme test objects use the same explicit universe u; no smaller test universe makes
a universal property vacuous. Sheaf values have the independent universe v. No universe
or variable is left implicit/unbound.

Independent searches (using other terms than the first worker): msearch LeanFinder query
“simplicial object splitting nondegenerate simplices coproduct epimorphisms” found
`SimplicialObject.Splitting`, its inclusions and index set; opened their definitions and
used them. Loogle query `SimplicialObject.Splitting` returned zero (unknown identifier
in the service index). LeanSearch query “finite split etale hypercover matching schemes
alternating coface complex” was unavailable (Internal Server Error), recorded as
unavailable rather than a negative result. Direct rg searches in Mathlib's simplicial
object and sites trees found Splitting, Homotopy, truncation, and alternating coface
complex, which are used. Searches in all project Sheaf and upstream WeilConjectures
for hypercovers, matching objects, simplicial schemes and splittings found no all-degree
finite split étale hypercover definition. Upstream CategoryTheory/Sites/CechComplex.lean
was inspected: it constructs the Čech cosimplicial object of a covering family and does
not define this arbitrary hypercover. Whole-DAG searches find matching-object lemmas
which depend on this item, not another definition that can replace it. No existing exact
match permits dropping this module. New notions introduced here are precisely clauses
already introduced by the item's own statement, so no additional definition node is needed.

The worker report and earlier reading are retained as history, but their claim that the
old named fields represented every clause was false. All mismatches listed above were
repaired; the node's mathematical statement and dependencies were left unchanged. Added
source-bearing docstrings for every declaration, removed the unused module-category
import, and recorded the main signature verbatim (including hypotheses) plus the public
helper declarations in the node's lean record. There are no theorem proofs, axioms,
private copies, file-local instances/notation, or sorry data. Local compilation of the
complete delivery module is clean, with no warnings (2.1 seconds).
