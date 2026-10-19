## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleModuleAffineBound` states
`AlgebraicGeometry.etaleModule_affine_cohomology_isZero`, with its sole proof `sorry`.
It preserves Q30's accepted six-step split. That acceptance was stage 1, not a Lean
statement delivery: the current node had no lean record. No previous delivery was
present in this sandbox. No statement correction, dependency repair, or new node.
The sole extra statement dependency is the already recorded, published
`lem-weil-pbc-etale-constant-ring-module-equivalence`, used to express ordinary module
inverse image by concrete canonical functors, without choosing a map or an action.

Clause-by-clause correspondence:

- The field is `{k : Type u} [Field k]`; finite or algebraically closed is
  `hk : Finite k ∨ IsAlgClosed k`.
- The prime is `(ℓ : ℕ) (hℓ : ℓ.Prime)`; invertibility in k is
  `hℓk : IsUnit (ℓ : k)`.
- The coefficient ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  The positive integer exponent is `(a : ℕ) (ha : 1 ≤ a)` and annihilation is
  `hA : (ℓ : A) ^ a = 0`. This is equivalent to ℓ^a A = 0: test on 1,
  and multiply the resulting scalar equality by any element. No nonzero-ring
  hypothesis is imposed.
- The finite-type k-scheme is `X : Scheme.{u}` with
  `[X.Over (Spec (.of k))]`, `[LocallyOfFiniteType (X ↘ Spec (.of k))]`, and
  `[QuasiCompact (X ↘ Spec (.of k))]`. No separatedness is imposed.
- The affine étale object is `(W : X.Etale) [IsAffine W.left]`; its structure
  morphism is `W.hom`, whose étaleness is part of the object. Affine here
  means the source scheme is affine, as in the node and its constant presentation.
- The larger universe is u+1 for coefficients and all module values, over
  Scheme.{u} and the corresponding small étale site. Every finite ring can be
  represented here. No equality of site object and morphism universes is imposed.
- `((topologicalKrullDim X).unbotD 0).toNat` is d_X. For the empty scheme,
  topologicalKrullDim is bottom and unbotD supplies 0. For nonempty finite-type
  schemes over a field the dimension is a finite natural number, and the
  expression retains it. This is also the exact dimension convention already
  used by ProEtale.HasClassicalUniformBounds. The bound in hq is 2*d_X+1.
- G is `ringedSiteModules.{u + 1} (Scheme.etaleConstantModuleRing X A)`,
  definitionally the ordinary SheafOfModules category over the constant ring
  sheaf `(constantSheaf X.smallEtaleTopology RingCat).obj (RingCat.of A)`.
  It is not an abelian sheaf with an unspecified action or condensed module.
- For inverse image, restrict G to its constant A-action by
  `Scheme.etaleConstantModuleRestrictionFunctor X A`; apply the dependency's
  `Etale.upperStar (ModuleCat A) W.hom`; extend scalars to the constant ring
  sheaf on W by `Scheme.etaleConstantModuleFunctor W.left A`. The two outer
  functors are the recorded canonical equivalence, both keeping the abelian
  presheaf unchanged. Applying inverse image to scalar operations is precisely
  constant-A module inverse image; this is the fixed-coefficient case explicitly
  included in def-weil-pbc-inverse-image. No additional inverse-image interface
  or arbitrary witness is postulated.
- Integer q is retained as `(q : ℤ)` with hq as the exact strict bound.
  Such q is positive. Its natural index q.toNat is therefore the same degree.
- I is an arbitrary `InjectiveResolution` of that module inverse image, using
  the recorded injective-resolution notion. Evaluating I.cocomplex by
  `SheafOfModules.evaluation` at `op (Scheme.Etale.mk (𝟙 W.left))` is evaluating
  at W, the terminal object of W's small étale site. Its `.homology q.toNat`
  is exactly the module-valued cohomology in the node, and `IsZero` asserts
  that this module is zero. Quantifying over I is independent of choices:
  these resolutions exist (enough injectives for small-site modules), and all
  compute the same right-derived sections. No extra property of I is assumed.
- G is entirely arbitrary. No constructibility, finite-generation, flatness,
  finiteness of its sections, or injectivity of its underlying abelian sheaf
  occurs in the statement.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact:
  AlgebraicGeometry.LocallyOfFiniteType and QuasiCompact.
- Mathlib.AlgebraicGeometry.Sites.Etale and Morphisms.Etale:
  Scheme.smallEtaleTopology, Scheme.Etale, Scheme.Etale.mk.
- Mathlib.Topology.KrullDimension: topologicalKrullDim.
- Mathlib.CategoryTheory.Sites.ConstantSheaf: CategoryTheory.constantSheaf,
  through the recorded constant-ring abbreviation.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules.
- Mathlib.CategoryTheory.Preadditive.Injective.Resolution:
  CategoryTheory.InjectiveResolution, its cocomplex and injective components.
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs:
  AlgebraicGeometry.Etale.upperStar, its full coefficient and universe signature.
- WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence:
  Scheme.etaleConstantModuleRing, etaleConstantModuleRestrictionFunctor,
  etaleConstantModuleFunctor, and their canonical unit/counit equivalence.
  Read the current server source using scompile.py --source, since the local
  Sheaf version is an older commutative specialization. The delivered import
  uses the recorded upstream module.
- def-weil-size-convention is a metatheoretic convention, rendered by explicit
  universe u, coefficient/module universe u+1, not an invented Lean object.

Proof dependencies with recorded modules are imported non-publicly, as required.
The proof-only lem-pe-constant-left-module-inverse-image has no Lean record yet,
so no nonexistent module is imported. It is not needed to type the statement:
the canonical equivalence and the existing fixed-coefficient upperStar give
its module inverse image explicitly. The docstring records all six DAG steps.

Edge cases checked before writing: X empty has d_X=0 and bound 1; then W is empty
and all evaluated cohomology is zero. Empty W over nonempty X is allowed. Zero A
is allowed by CommRing and the equivalence. Dimension-zero X has bound 1, including
finite fields with possible degree-one cohomology. q=1 or q=0 never satisfies hq;
negative q is also excluded by the node itself. q=2 with d_X=0 is represented
without a shift, since q.toNat=2. Nonconstructible G, infinitely generated section
modules, and nonflat A-modules are all admitted. No extra finiteness or affine
condition is imposed on X. Coefficients in the enlarged universe and the site's
unequal object/morphism universes remain intact.

Searches (msearch.py, group Q113, item lem-sfb-etale-module-affine-bound):

- leanfinder: "Uniform vanishing of etale cohomology of arbitrary finite torsion
  coefficient module sheaves above twice the dimension plus one". Eight hits:
  etaleLocus_eq_compl_support, derived/complex isZero_of_isGE/isLE, and formal
  étale/cotangent results; none asserts geometric cohomological dimension.
- loogle: "AlgebraicGeometry.Scheme.smallEtaleTopology, CategoryTheory.Sheaf".
  Six hits, affine-site sheaf equivalence and Grothendieck/abelian instances;
  none is the required cohomology bound.
- grep: "cohomologicalDimension|cohomological.dimension|etale.*cohomology".
  Zero Mathlib hits from the search service.
- leansearch: "Uniform vanishing bound for etale cohomology of arbitrary torsion
  module sheaves over finite type schemes over finite or algebraically closed
  fields". Eight hits concern affine sections, cotangent cohomology and étale
  loci; no match.
- rg of the upstream WeilConjectures and project lean/Sheaf trees for the exact
  item ID found no declaration. Further searches for etale/affine bounds found
  only ProEtaleClassicalBounds's abelian/pro-étale bounds; its full signature
  is not this module-sheaf statement. Searches for etaleConstantModule found
  the canonical equivalence above, which is reused rather than duplicated.

The source blueprint Fixed-degree truncation paragraph was read in full.
There is no STATEMENT-DISPUTED issue.

## Second reading by Q113

A separate rereading by the same dispatched worker matched the node with the
complete signature and checked each binder and conclusion using the mapping
above. The independent maintainer review remains the independent reading;
no other worker was started, as the dispatch forbids it. The rereading found
that the local Sheaf constant-ring equivalence was superseded by the recorded
upstream module; changed the import to that upstream module and read its current
source. Confirmed that the resolution is taken in ordinary constant-ring
modules on W, rather than in abelian sheaves or on X. Confirmed that q.toNat is
only used with positive q and that the empty-dimension convention is exact.
Confirmed no nonempty, nontrivial, constructible, flat, or separated binder.
