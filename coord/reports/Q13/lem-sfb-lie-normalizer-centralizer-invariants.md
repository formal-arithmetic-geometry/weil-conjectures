## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.LieNormalizerCentralizerInvariants`
states `AlgebraicGeometry.lie_normalizer_centralizer_invariants`, with its sole proof
`sorry`. It adds no definitions, axioms, or extra theorem assumptions. The source
is Milne, Algebraic Groups (2017), Proposition 10.34, printed pp.197–198, read in
the local PDF, including the proof's distinction between all k-algebras and all
k[epsilon]-algebras. The full five-step accepted DAG proof is in the docstring.

The calculus structures have their own definition owner,
`def-sfb-affine-group-dual-number-data`, bound with `existing: true` to the landed
module's `dualMap`, `reduction`, `Kernel`, `Data`, and `Compatible`. The item cites
that definition node in `stmt_deps`. The existence theorem node
`lem-sfb-affine-group-dual-number-calculus` stays in `proof_deps` only.
The item also cites the landed definition nodes `def-wf-lie-algebra-derivation`
and `def-sc-general-linear-group`. The mathematical statement and Lean module
are unchanged. No dependency module or statement correction is needed.

Hypotheses and clauses, matched individually:

| Node text | Lean rendering |
| --- | --- |
| Algebraically closed field F | `(F : Type u) [Field F] [IsAlgClosed F]` |
| Affine F-group schemes G, K, H, C, N | Five `Grp (Over (Spec (.of F)))` objects, each with `[IsAffine …X.left]` |
| All five groups have finite type | Each has `[LocallyOfFiniteType …X.hom] [QuasiCompact …X.hom]`, the dependency's conjunction encoding |
| Closed inclusions K,H,C,N into G | Four maps in `Over`, with `[IsClosedSubgroupScheme iK]`, and similarly iH, iC, iN; these classes include `IsMonHom` |
| H is smooth | `[Smooth H.X.hom]`; neither G, K, C nor N is required to be smooth |
| Lie(J) is the identity tangent space, equivalently the dual-number kernel | Existing `GrpObj.Lie J.X`; `GrpObj.lieIdentityTangentEquiv` canonically identifies it with the dependency's `schemeTangentSpace` with scalars restricted by the structural residue map. The calculus `Data.E` identifies each scalar extension with the actual dual-number kernel and `Data.normalize` fixes it by `GrpObj.tangentPoint` |
| These Lie spaces are finite dimensional | `D.finite` for G and four explicit `Module.Finite F (GrpObj.Lie …X)` conclusions for K,H,C,N. Over a field this is finite dimension |
| The four closed inclusions have injective tangent maps | Four `Function.Injective (GrpObj.differential …)` conclusions |
| Conjugation induces the rational linear Ad action | Existential conclusion `D : AffineGroupDualNumberCalculus.Data G`: `D.Ad`, `D.conjugation` and `D.regular` specify this action. D is produced in the conclusion, not assumed |
| h is H-stable | For every R, h-point and scalar-extended vector in Lie(H), its image acted on by `D.Ad R (h ≫ iH)` lies in `LinearMap.range (LinearMap.baseChange R …)` |
| The induced quotient g/h and H-action | The quotient is `GrpObj.Lie G.X ⧸ LinearMap.range (GrpObj.differential iH).toLinearMap`. `Q R` is an H(R)-representation on its R-scalar extension, produced existentially. The following equation says `Q(h) q_R(v) = q_R(Ad(h)v)` for every scalar-extended v. Surjectivity of q_R determines Q uniquely; this is not an arbitrary action |
| The quotient action is rational | For every finite basis b, the `∃! ρ` clause realizes Q by an actual group-scheme morphism H→GL, with `IsMonHom ρ` and equality on every R-point. The index `ULift (Fin n)` includes n=0 |
| C represents the specified centralizer functor | `hC`: equality of the inclusion's image with the g satisfying commutation for every B and every `f : A →ₐ[F] B` and every K(B)-point |
| N represents the specified normalizer functor | `hN`: equality of the inclusion's image with the g whose conjugation carries the full image of H(B) onto itself, for every B and every `f : A →ₐ[F] B` |
| H lies in N, so h is contained in Lie(N) | Explicit `LinearMap.range (d iH).toLinearMap ≤ LinearMap.range (d iN).toLinearMap` conclusion |
| Lie(C)=g^K as subspaces of g | The penultimate equality identifies `Set.range (GrpObj.differential iC)` with all v for which every K(R)-point fixes `1 ⊗ₜ[F] v` under `D.Ad` |
| Lie(N)/h=(g/h)^H as subspaces of g/h | The last equality identifies the range of `mkQ.comp (GrpObj.differential iN).toLinearMap` with all z fixed by every H(R)-point under Q after scalar extension. With the explicit containment h≤Lie(N), this range is exactly the canonically embedded Lie(N)/h; its underlying-set equality is equality of the subspaces |
| Entire group functor invariants | Both fixed-vector clauses quantify `(R : Type u) [CommRing R] [Algebra F R]` and all points, not only F-points and not Lie-algebra actions |
| No characteristic, connectedness, reductivity, C/N smoothness assumptions | No such binders occur |

An arbitrary A-algebra B is rendered by its F-algebra structure and F-algebra map
`A →ₐ[F] B`, exactly the same extension data; no unnecessary `IsScalarTower`
assumption is needed. The common universe u is the existing scheme/point API's
size convention: F, groups, test algebras, dual numbers and scalar extensions
all live at that size, and u is arbitrary. There is no independent smaller test
universe that could make the conditions vacuous.

Dependencies read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs; its full declaration and docstring read.
- `def-weil-algebraic-closure`: its match explicitly gives `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic; this is the algebraically closed field clause, with no chosen closure needed.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` and bundled `Grp`, Mathlib.CategoryTheory.Monoidal.Grp. Group schemes over Spec F are the specialization documented in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType, and `QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact; full signatures and docstrings read.
- `def-sc-group-scheme-subgroup`: `AlgebraicGeometry.IsClosedSubgroupScheme`, WeilConjectures.AlgebraicGeometry.GroupScheme.Defs; its inherited IsSubgroupScheme, injectivity of points, group homomorphism and closed immersion fields were read.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth; full signature and docstring read.
- `def-sc-scheme-tangent-space`: `AlgebraicGeometry.schemeTangentSpace` and canonical module structure, WeilConjectures.AlgebraicGeometry.SchemeTangentSpace. Existing Lie and differential interfaces are from WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential, and the exact transport is `GrpObj.lieIdentityTangentEquiv` in WeilConjectures.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv. These source declarations were opened, including their docstrings.
- `def-sfb-affine-group-dual-number-data`: existing `AlgebraicGeometry.AffineGroupDualNumberCalculus.dualMap`, `.reduction`, `.Kernel`, `.Data`, `.Compatible` in Sheaf.AlgebraicGeometry.AffineGroupDualNumberCalculus. This new definition node owns the plain definitions; they are not chosen from a theorem. Their full signatures and docstrings were read. The Data package fixes E by normalization, naturality and scaling, and Ad by conjugation, and realizes Ad in every finite basis. No definitions are moved or copied.
- `lem-sfb-affine-group-dual-number-calculus` (proof dependency only): `.exists_compatible_calculus` in that same module supplies the existence and compatibility used in proof step 1. It is not a statement dependency.
- `def-wf-lie-algebra-derivation`: existing `GrpObj.Lie` and `lieEquivTangent` from WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Basic/Bracket, `GrpObj.tangentPoint` from Lie.Ring and `GrpObj.differential` from Lie.Differential. Full declarations were reread for the repair. The item now explicitly cites this owning definition node.
- `def-sc-general-linear-group`: Sheaf.AlgebraicGeometry.LinearGroupSchemes publicly imports the existing upstream `AlgebraicGeometry.GeneralLinearGroup` and `.homMulEquiv` from WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear. Their full signatures and docstrings were reread. The item now explicitly cites this definition owner for the GL rationality clauses. Its finite-index construction also permits rank zero as used here.

The public import of the calculus module exposes the definition-node structures
and also provides its theorem for the proof. The Lie/differential and GL owning
modules are already public imports of that module, so no import edit is needed.

Edge cases checked mathematically before drafting:

- K=1 gives C=G and all of g fixed; C need not be smooth.
- H=1 gives N=G and Q trivial, so both sides of the quotient identity are g.
- H=G gives N=G and the zero quotient, including the n=0 basis case.
- A finite étale H has h=0, so the second identity compares Lie(N) with the full H-fixed space in g; no connectedness is smuggled in.
- In characteristic p, K=mu_p inside G_m has nonzero Lie(K), although K(F) is trivial. Quantification over every algebra preserves the scheme-theoretic condition; in the commutative ambient group Ad is trivial and C=G, correctly.
- The zero test algebra is permitted by `[CommRing R]` without `[Nontrivial R]`; the scalar extension is zero and the point groups are trivial. Nonreduced algebras, including all dual numbers used in the proof, are permitted too.
- No geometric object or construction is chosen from a bare Nonempty hypothesis. D and Q occur as theorem conclusions, and Q is characterized on the surjective quotient map, so its value is determined.

Searches made:

1. `msearch.py … leanfinder "Lie algebra of scheme centralizer equals fixed vectors and Lie normalizer quotient equals group invariants"`: 8 hits, including LieSubmodule and LieSubalgebra normalizers and weight-space results. These are Lie-algebra invariants, not the whole affine group functor.
2. `msearch.py … loogle '"normalizer", "Lie"'`: 12 hits in Mathlib.Algebra.Lie.Normalizer; none states the scheme centralizer/normalizer identity.
3. `msearch.py … grep 'Lie.*centralizer|Lie.*normalizer|normalizer.*Lie|centralizer.*Lie' AlgebraicGeometry`: zero hits.
4. `msearch.py … leansearch "Lie algebra of scheme theoretic centralizer is the full group fixed subspace; normalizer Lie quotient is invariants"`: 8 hits on LieSubalgebra normalizers and ring invariants, no match.
5. `rg` of `Lie.*centralizer|Lie.*normalizer|normalizer.*Lie|centralizer.*Lie|adjointCalculus|fixed.*[Ss]ubspace` in both project Lean roots: comments in consumers and unrelated fixed subspaces, no statement matching this item. `rg` of the exact node id in WeilConjectures gave no hit; the only Sheaf hit was the Cartan-containing-normalizer consumer's proof docstring.
6. `rg` for the proposed full declaration/module names and item id in dag/lean_names_upstream.json and both Lean roots: no matching declaration. The existing dual-number calculus was reused rather than copied.

No STATEMENT-DISPUTED issue or mathematical node fault found. The original mathematical
statement is retained verbatim. Compilation of the delivered file via scompile.py
passed both sandbox and library module checks, with no unexpected warnings.


## Repair of returned delivery cd26fdfb9b7d

The return identifies one H2 dependency-ownership fault with three requested
repairs. All three are implemented:

1. Added `def-sfb-affine-group-dual-number-data` with `existing: true` on the
   already landed module, listing exactly its `dualMap`, `reduction`, `Kernel`,
   `Data`, `Compatible`. Replaced the theorem's entry in item `stmt_deps` by
   this definition node. The theorem remains in `proof_deps`, unchanged.
2. Added the landed `def-wf-lie-algebra-derivation` to item `stmt_deps` for
   `GrpObj.Lie`, its tangent point and differential interfaces.
3. Added the landed `def-sc-general-linear-group` to item `stmt_deps` for
   the upstream general linear scheme and its `homMulEquiv` point interface.

The sandbox's pre-repair node differed from current main only in `lean` and
`stmt_deps`; the repair started from the current main node and reapplied only
these two authorized fields. The immutable returned Lean file is byte-identical,
with SHA256 `484e85c8053b22356c45e6332909501a23d03fcd7406950b7654983f95f37047`
before and after this repair. The prior incorrect ownership explanation in this
report has been replaced. The maintainer accepted the mathematics clause by
clause; no mathematical statement or proof plan was altered.

## New nodes

`def-sfb-affine-group-dual-number-data` gives the definition of the existing
scalar-extended dual-number calculus datum and its compatibility predicate. It
records reduction and coefficient maps, the kernel functor, finite tangent
dimension, normalized natural E bijections preserving addition, zero, negation
and scaling, adjoint conjugation and rationality in every basis, and all three
compatibility clauses (differential naturality, closed subgroup intersection
with injectivity, and adjoint equivariance). The source is Milne 10.6, 10.11,
10.14, 10.18–10.21, printed pp.188–193. No existence theorem is smuggled into
this definition node. The `lean` record binds the five already landed definitions
in Sheaf.AlgebraicGeometry.AffineGroupDualNumberCalculus with `existing: true`;
there is no new Lean module, copy, move or choice. The inherited blueprint
ancestor is null (`blueprint_refs.py ancestor` reports None), with the full
inherited place and via path retained. This target-reachable node has
`import_flags: []` as required.

The definition-node `mathlib_searches` records the raw three new msearch results
as returned (LeanSearch, LeanFinder, and Mathlib grep), plus project/DAG grep and
blueprint searches. LeanSearch returned eight dual-number algebra facts;
LeanFinder returned eight dual-number/extension facts; Mathlib AlgebraicGeometry
grep found no datum. Project grep found the five exact existing definitions,
and DAG grep found only the theorem node recording them, with no definition
owner. `blueprint_refs.py search dual-number` found the Lie definition, which
does not define this calculus package. Thus this is ownership of an existing
notion, with no duplicated declaration.

New-node edge cases agree with its recorded structures: R=0 and nonreduced R
are permitted, the n=0 basis describes the trivial GL group, and compatibility
only demands injectivity of the differential when f is a closed inclusion. No
smoothness, characteristic, or finite-type hypothesis is inserted into the
plain structure definition: finiteness is one of the datum's fields, and the
separate theorem proves existence for the appropriate affine finite-type groups.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
