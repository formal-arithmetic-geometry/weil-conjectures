## Worker report

The module Sheaf.AlgebraicGeometry.ProjectiveCurveFiniteGroup states the corollary
as one theorem with proof `sorry`; it defines no new notion and proves nothing.
The original node statement and dependency lists are unchanged.

Clause-by-clause correspondence:

- A field: `(k : Type u) [Field k]`.
- Schemes over that same field: `(X S : Over (Spec (.of k)))`.
  The morphism `(f : X ⟶ S)` is a morphism over k, including the structural-map
  compatibility through the category Over; its underlying scheme map is `f.left`.
- Both schemes are of finite type over k: `[LocallyOfFiniteType X.hom]`
  and `[QuasiCompact X.hom]`, and the same two instances on `S.hom`.
  Mathlib's FiniteType module explicitly defines this phrase by those two properties;
  there is no `FiniteType` class in the pinned library.
- Projectivity: `[IsProjective f.left]`, exactly the blueprint's H-projective and
  quasi-compact convention, not properness or a weaker embedding condition.
- Geometric fibre dimensions at most one: `hdim` quantifies over every `s : S.left`.
  Its pullback is along `Spec.map` of the canonical inclusion of the residue field
  into its algebraic closure, followed by `S.left.fromSpecResidueField s`.
  `topologicalKrullDim ... ≤ 1` is the Krull dimension bound, including empty fibres.
- Finite abelian group: `(M : AddCommGrpCat.{u + 1}) [Finite M]`.
  AddCommGrpCat bundles precisely the abelian group structure.
- Its order invertible on S: `horder : IsUnit (Nat.card M : Γ(S.left, ⊤))`.
  The integer scalar section is invertible exactly when it is invertible in every
  stalk: local inverses agree on overlaps and glue to a global inverse.
- Every higher direct image: `(q : ℤ)` and `DerivedCategory.Plus.homologyFunctor ... q`
  applied to `Etale.rightDerivedLowerStarPlus ... f.left` of the constant sheaf in
  degree zero via `DerivedCategory.Plus.singleFunctor ... 0`.
  This includes degree zero and negative degrees, matching the node's direct-image
  convention and its explicit negative-degree boundary explanation.
- Constant coefficients: `(constantSheaf X.left.smallEtaleTopology
  AddCommGrpCat.{u + 1}).obj M`, the recorded sheafification of the constant presheaf.
- Constructible conclusion: `Scheme.IsConstructibleAbelianSheaf` on S's small etale
  site. This is the recorded global finite partition and finite local constancy
  definition, for abelian sheaves rather than a substitute module coefficient category.

Statement dependency declarations read and used:

- def-pc-projective-morphism: `AlgebraicGeometry.IsProjective`, recorded module
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`. The recorded path is
  absent in the local source snapshot; the identical full class and its docstring
  were read in `lean/Sheaf/AlgebraicGeometry/Morphisms/Projective.lean`. Server compile
  confirms that the canonical recorded upstream import and class are available.
- def-weil-pbc-direct-image: `AlgebraicGeometry.Etale.lowerStar`, module
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`. Its bounded-below derived
  declaration `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` is located in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`; its full
  signature/docstring were read in the group clone. Both modules are public imports.
- def-weil-pbc-constant-sheaf: `CategoryTheory.constantSheaf`, module
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`; read its definition and docstring.
- def-weil-pbc-constructible-abelian-sheaf:
  `AlgebraicGeometry.Scheme.IsConstructibleAbelianSheaf`, module
  `Sheaf.AlgebraicGeometry.ConstructibleAbelianSheaf`; read the full definition and
  docstring, including stratification, constructibility of strata, covers and models.
- def-weil-pbc-scheme-conventions is a convention record, with no declaration/module.
  Its constituent notions are Mathlib's Over, Spec, LocallyOfFiniteType, QuasiCompact,
  residue fields, algebraic closure and pullback. The geometric fibre is the expression
  specified by the existing def-weil-geometric-fibre record; no duplicate notion.

Every proof dependency with a recorded module is imported, using ordinary imports
when only the proof needs it. The Mathlib leaf
`lem-weil-pbc-sheafification-exact` has no lean record: its mathlib_match is the
finite-limit preservation instance for presheafToSheaf in
`Mathlib.CategoryTheory.Sites.Sheafification`, which is explicitly imported for the proof.
`thm-fin-projective-curve-constant` has no Lean record or Mathlib match yet, so it supplies
no import. The theorem docstring carries all seven steps of the node's proof,
including the scalar-conversion step, the degree-zero exact-sequence boundary, and
negative-degree vanishing. No import cycle was introduced.

Edge cases checked: empty X, empty S, and empty individual fibres have no Nonempty
hypothesis; the dimension is WithBot ℕ∞, so empty fibres satisfy the bound. The trivial
finite group has cardinality one, which is invertible over any base. No nontrivial-group
or prime-cardinality hypothesis is imposed. Groups of mixed prime order are included.
All field characteristics are allowed subject exactly to the stated invertibility.
Degree zero and all negative degrees are included. Universes are explicit, with scheme
and field universe u and sheaf values in u+1 as required for the small etale framework;
there is no independent small testing universe. No auto-bound implicit variables.

Searches for an existing statement (2026-10-15):

- msearch.py leanfinder: “higher direct images of finite constant abelian sheaves on
  projective families of curves are constructible”. Eight hits, on coherent-site
  projective objects, affine limits and condensed modules; none is this theorem.
- msearch.py loogle: `IsConstructibleAbelianSheaf, rightDerived`.
  Zero hits; reports unknown identifier IsConstructibleAbelianSheaf, which is a
  project-side declaration rather than Mathlib's.
- msearch.py leansearch: “higher direct images of finite constant abelian sheaves on
  projective curve families are constructible”. Service unavailable: Internal Server
  Error. Recorded as unavailable, without a negative search verdict.
- msearch.py grep: `constructible.*(direct.image|pushforward)|projective.*constructible`.
  Zero Mathlib hits.
- rg on upstream WeilConjectures and project lean/Sheaf:
  `IsConstructibleAbelianSheaf|projective.*[Cc]onstructible|constructible.*[Pp]rojective`.
  Only the abelian constructibility definition and an unrelated perfect-module comment.
- rg on upstream WeilConjectures for `cor-fin-projective-curve-finite-group`: no hits.
- rg on the upstream name index, Mathlib, upstream WeilConjectures and project lean/Sheaf
  for the proposed full theorem's final component: no hits.
- Additional fibre/dimension searches located Mathlib's `topologicalKrullDim`, and
  reading the existing geometric-fibre DAG record confirmed the canonical expression.

Validation: the module compiled cleanly on the server with scompile.py (nice 19,
two threads, 60-second per-file limit), including the published canonical projectivity
import and the side-only abelian-constructibility dependency. No local compiler used.
No statement dispute, correction, new node or dependency replacement was needed.

## Second reading by ND

Read the item's JSON, all five statement-dependency records, the blueprint source
corollary and its proof, and the delivered Lean theorem independently. The node's
object/hypothesis/conclusion list and its Lean rendering are:

1. A field k: `(k : Type u) [Field k]`. Exact; neither algebraic closedness nor a
   characteristic assumption is added.
2. Schemes X and S over the same k: `(X S : Over (Spec (.of k)))`. Exact; `f : X ⟶ S`
   is a morphism over that field, with underlying scheme morphism `f.left`.
3. X and S of finite type over k: the `LocallyOfFiniteType` and `QuasiCompact`
   instances on each structure map. Exact: the pinned Mathlib FiniteType module
   explicitly defines finite type as their conjunction. No separatedness is assumed.
4. Projective f: `[IsProjective f.left]`. Exact: read `IsHProjective` and
   `IsProjective` in the projectivity source; they require a closed embedding into
   finite-dimensional projective space over S and quasi-compactness, precisely the
   dependency node's convention. This is not a substitution of properness.
5. Every geometric fibre has dimension at most one: `hdim` quantifies over all
   `s : S.left` and bounds `topologicalKrullDim` of the pullback along the composite
   from the spectrum of the algebraic closure of its residue field. Exact: checked
   against def-weil-geometric-fibre and its recorded pullback expression; the
   projection and field embedding have the correct direction.
6. A finite abelian group M: `(M : AddCommGrpCat.{u + 1}) [Finite M]`. Exact;
   neither cyclicity nor prime order is imposed.
7. Its order invertible on S: `IsUnit (Nat.card M : Γ(S.left, ⊤))`. Exact: a scalar
   section is a unit globally iff it is a unit in all stalks. Local inverses exist
   near each point, agree by uniqueness, and glue, including on the empty scheme.
8. For every degree, constructibility of the higher direct image of the constant
   abelian sheaf: `(q : ℤ)` and `Scheme.IsConstructibleAbelianSheaf` of homology q
   of `Etale.rightDerivedLowerStarPlus` applied to the degree-zero
   `DerivedCategory.Plus.singleFunctor` of `(constantSheaf ...).obj M`. Exact.
   The direct-image node explicitly defines R^q this way for integer q.

Opened the canonical lowerStar definition and rightDerivedLowerStarPlus definition
in the group clone, including their variable sections: the former evaluates on
base change and the latter is its rightDerivedFunctorPlus. Their coefficient
requirements specialize to AddCommGrpCat; no additional assumptions on X or S are
hidden. Opened Mathlib's constantSheaf definition: it is constant presheaf followed
by sheafification. Opened the full IsConstructibleAbelianSheaf definition and its
LocallyClosedStratification dependency: one finite partition into constructible
locally closed strata, étale covers, finite abelian models, and abelian inverse-image
isomorphisms, exactly as the constructibility node states.

Source checks included Stacks etale-cohomology.tex, definition-finite-locally-constant
(03RU), definition-constructible (03RW), the preceding convention on locally closed
subschemes, lemma-constructible-quasi-compact-quasi-separated (095E), and
lemma-constructible-abelian (03RZ); also sites-modules.tex lemma-constant-exact (093J).
These require no omitted base hypothesis: the global finite-partition formulation
agrees with affine-local constructibility here because finite-type schemes over a
field are Noetherian, hence qcqs. Abelian constructibility needs no coefficient ring.
The theorem docstring follows all seven proof steps of the node, including
annihilation, scalar conversion, the q=0 boundary, and negative-degree vanishing.
All recorded proof-dependency modules are imported; the prime-coefficient theorem
has no recorded declaration yet. No new nodes or dependency modules are delivered.

Edge cases: X and S may be empty, as may any fibre; there is no Nonempty premise.
The empty fibre has dimension bottom and satisfies the bound. The trivial group
has cardinality one, so is allowed, and no finite abelian group has order zero.
Mixed-prime orders are included. In positive characteristic only the stated unit
condition restricts the group; for empty S even that condition is automatically
satisfied, correctly. Degree zero and every negative degree are included. Explicit
universe u for fields/schemes and u+1 for abelian coefficients is the site's standard
encoding, permits every finite group up to isomorphism, and introduces no small
universe of test algebras. Every binder/universe is bound by eye.

Independent duplicate searches, using different wording from the worker:

- msearch.py leanfinder: `proper pushforward torsion locally constant abelian sheaf
  constructibility relative dimension one`: eight hits, including constructible
  images of subsets and condensed locally constant functors, none this statement.
- msearch.py loogle: `"constructible", "constant"`: zero hits.
- msearch.py leansearch: `constructibility of etale cohomology sheaves of projective
  relative curves with finite constant coefficients`: service unavailable (Internal
  Server Error); this is an unavailable search, not evidence of absence.
- Direct rg on pinned Mathlib, upstream WeilConjectures, and project lean/Sheaf:
  `finite.*group.*constructib|constructib.*higher|curve.*direct.image|proper.*constructib`
  (case insensitive). Opened upstream Derived/Finiteness/DirectImage.lean: its
  general constructibility theorems concern module coefficients and bounded
  complexes, not this abelian-sheaf corollary. Project higher-direct-image hits
  define properties rather than state this theorem. No exact existing statement.
- The proposed theorem name is absent from dag/lean_names_upstream.json.

Verdict: no mismatch found; kept the theorem, imports, node statement, dependencies,
and recorded signature unchanged. The sole change from this second reading is this
review section. There is one named theorem with whole proof `sorry`, no new data
definition, no private notation/instance, and no proved auxiliary declaration.
The node's lean.statement is verbatim the theorem signature before `:= by`.
Validation: scompile.py compiled the delivered file cleanly on the server (1.7 s,
nice 19, two threads, 60 seconds per file), including its side-only dependency
overlays. No local compiler or library build was run.
