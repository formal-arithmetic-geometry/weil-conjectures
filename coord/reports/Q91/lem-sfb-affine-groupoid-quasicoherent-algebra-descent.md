## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.AffineGroupoidQuasiCoherentAlgebraDescent`,
`CategoryTheory.affineGroupoid_quasiCoherent_algebra_descent`. Its only theorem proof is
`sorry`; all definitions have actual data. The new definition module is
`Sheaf.AlgebraicGeometry.AffineGroupoidAlgebra`. Each file compiled separately through
scompile.py against the published live build, in dependency order, without errors or warnings.

Hypotheses and clauses, matched with the node:

- The field is `k : Type u` with `[Field k]`. The affine k-schemes are literally
  `Spec (.of E)` and `Spec (.of L)`, with `[CommRing E]`, `[CommRing L]`,
  `[Algebra k E]`, `[Algebra k L]`. The maps `sigma tau : E →ₐ[k] L` induce s and t by
  `Spec.map`, hence are k-morphisms. `e`, `i`, and `c` are precisely the scheme maps
  in the statement. `P.groupoid : Scheme.IsGroupoid ...` supplies every groupoid law.
  Source and target carry their exact `.IsFiniteLocallyFree` instances.
- `F`, `a`, and `P : SchemeGroupoidQuotientPresentation ... F a` describe the specified
  quotient stack with its atlas and original arrow composition. The recorded presentation
  predicate says exactly that objects lift fppf locally and its vertical arrows are the
  original arrows, with their composition. This is a presentation of the fppf
  stackification, not a quotient of isomorphism classes, and adds no algebraicity or
  smoothness assumption. It keeps the full two-isomorphism `P.arrows`.
- Algebras on the stack are the full subcategory `GroupoidQuasiCoherentAlgebras F P.stack.1`
  of the existing `ModuliAlgebraSheaf`, cut out by the existing
  `IsQuasicoherentModuliAlgebra`. These are commutative unital ring sheaves under the
  actual regular-functions sheaf. The quasi-coherence predicate is the existing general
  ringed-site predicate of local free presentations.
- The coordinate-algebra category is `Scheme.AffineGroupoidAlgebra`. Its `algebra` is an
  arbitrary commutative ring under the coordinate ring of U. `beta` is the source-to-target
  pushout isomorphism. `scalar` makes it an L-algebra isomorphism. By
  `CommRingCat.isPushout_tensorProduct` the pushouts are exactly A tensor_(E,s) L and
  A tensor_(E,t) L, and the left inclusions are a |-> a tensor 1. Coordinates are
  ULift of global functions. For Spec E, `Scheme.ΓSpecIso` followed by `ULift.ringEquiv`
  identifies them canonically with E. No independent replacement ring has been chosen.
- `unit` and `cocycle` say that identity transport is identity and that successive
  transports equal composition transport. They are tested on all rings in the ambient
  universe. The relation `groupoidAlgebraTransport ... r x y` says (y,r) beta = (x,r).
  The cocycle uses the second projection for the earlier arrow and the first for the
  later arrow, exactly c(a,b)=a after b. These equations are precisely the pullback
  identity and composition equations by Yoneda: testing rings includes the representing
  pushout itself, so does not lose scheme-theoretic or infinitesimal information.
- `Hom` is the subtype of all algebra maps preserving that relation. Testing the target
  pushout and its universal element gives the usual commutative square with beta;
  conversely that square preserves every transport relation. Thus the maps are exactly
  all equivariant algebra maps, with no additional condition. The forgetful functor
  retains those exact maps.
- `D : ... ≌ ...` states the category equivalence. It is normalized by the natural
  isomorphism `j` to the concrete functor `groupoidAtlasAlgebraEvaluation`, which
  literally evaluates the sheaf and its maps at the atlas object. The existential
  `theta` is uniquely determined by its `inl` and `inr` equations; it is not an arbitrary
  tensor comparison. It is an isomorphism and the third equation forces beta to be the
  forward transport induced by `P.arrows`. The inverse presentation arrow is used
  because ring sheaves are contravariant. Thus this states pullback identification,
  not merely the existence of some unrelated equivalence.
- `rho` is a ring equivalence from the existing `moduliGlobalSectionsRing` to the actual
  `RingHom.eqLocus` invariant subring. Its evaluation equation says the underlying
  invariant element restricts to the given global section on the atlas, through j.
  Therefore it is the pullback identification, and is natural in algebra maps by
  naturality of j and literal evaluation. The ring structure is not just a set bijection.
- For every `f : A ⟶ B`, the existing `IsSurjectiveModuliAlgebra f.hom` means locally
  surjective on the fppf site. The last conclusion is `Function.Surjective` of the
  actual underlying ring map of `D.functor.map f`. This map is already equivariant by
  membership in the category. No claim of surjectivity on global invariants is made.
- There is no finite type, presentation, module-finiteness, Noetherian, nonempty,
  reducedness, rank, characteristic, or algebraicity binder. The coefficient universe
  is the full `max (u+1) v w` used by the recorded stack algebra interface. Both v and w
  are arbitrary, and the new coordinate-algebra definition independently permits any
  ambient enlargement q. All ring-valued tests use the same ambient universe, which
  contains the pushouts they need; no vacuous smaller-universe testing is used.

Recorded dependencies read and used:

- Mathlib Field, AlgebraicGeometry.Scheme, Spec and Spec.map: field, schemes, spectra.
- `Sheaf.AlgebraicGeometry.SchemeGroupoidLaws`, `AlgebraicGeometry.Scheme.IsGroupoid`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`,
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`.
- Mathlib `AlgebraicGeometry.Scheme.fppfTopology` from Sites.Fpqc, through the recorded
  presentation and stack-algebra site; its slice is the big fppf site over Spec k.
- `Sheaf.AlgebraicGeometry.AdequateModuliSpace`,
  `CategoryTheory.IsAdequateModuliSpace` was read for the inherited conventions, not
  imposed as a hypothesis. Its imports supply the same stack and algebraic-space
  notions as the item's dependencies. The space convention is the existing
  `Sheaf.AlgebraicGeometry.AlgebraicSpace`, `AlgebraicGeometry.AlgebraicSpace`; it is
  not reconstructed or added as an extraneous parameter of this scheme-groupoid theorem.
- `Sheaf.AlgebraicGeometry.SchemeGroupoidQuotientPresentation`,
  `CategoryTheory.SchemeGroupoidQuotientPresentation` (added as a landed statement
  dependency): the exact fppf quotient presentation with composition.
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra` (added as an explicit statement
  dependency): `ModuliAlgebraSheaf`, `IsQuasicoherentModuliAlgebra`,
  `IsSurjectiveModuliAlgebra`, `moduliGlobalSectionsRing`, and the regular-functions
  presheaf. Their complete signatures and definitions were read.
- Mathlib `TensorProduct`, `Algebra.TensorProduct` and
  `CommRingCat.isPushout_tensorProduct`: the module tensor product with its algebra
  structure is used via its canonical ring-pushout representation.

Available proof-dependency imports are non-public:
`Mathlib.AlgebraicGeometry.Modules.Tilde` (`tilde.adjunction` and
`Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`),
`WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections`
(`Scheme.Modules.exists_tensorPullback_affine_sections`),
`WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections`
(`Scheme.Modules.quasiCoherent_tensor_product_affine_sections`), and
`WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
(`Scheme.Modules.quasiCoherent_cokernel_image`). Their source declarations and proof
plans were read. `lem-sfb-groupoid-module-descent-tensor-cokernel` has no recorded Lean
module in the current DAG, so no speculative import is made for that proof-only node;
its full statement remains the first step of this item's proof docstring. It is not
needed to type any definition or the statement in this delivery.

Edge cases checked mathematically: E=0 and the empty atlas give zero coordinate rings
and the unique zero algebra under them; L=0 is compatible with the groupoid identity
only in the empty case. The identity groupoid forces beta=identity and recovers all
E-algebras and their ordinary global sections. Infinitesimal arrows remain visible
because all ring tests, including nonreduced rings, are quantified. Arbitrary polynomial
algebras in infinitely many variables satisfy the type of objects; no finite-type
restriction occurs. Characteristic p is allowed. Local sheaf surjectivity is kept distinct
from surjectivity on invariant sections. Variable rank of the finite locally free maps
is allowed. The ambient universe contains every pushout used to test equations.

Searches: msearch.py LeanFinder query "Quasi coherent algebras on quotient stack of an
affine flat groupoid correspond to equivariant commutative algebras" returned the affine
scheme equivalence and general quasi-coherence presentations, not this result. Loogle
"CommAlgCat, TensorProduct, Groupoid" returned zero hits (Groupoid unrecognized by that
index). LeanSearch "A category of equivariant commutative algebras for an affine
groupoid" returned ordinary group actions and CommAlgCat isomorphisms. A second
LeanFinder query "Commutative algebras with flat scheme groupoid descent isomorphism
satisfying identity and cocycle laws" returned scheme flatness/descent and pseudofunctor
descent data, not the notion. msearch grep "GroupoidAlgebra|groupoid.*descent" in
AlgebraicGeometry and grep "AffineGroupoidAlgebra|groupoidAlgebraTransport|GroupoidAlgebra"
in Mathlib returned no hits. rg searches in lean/WeilConjectures and lean/Sheaf found
scheme-groupoid modules and algebra sheaves on stacks, but no coordinate-algebra descent
category or this theorem. Searching the item's id in WeilConjectures returned no match.
DAG and blueprint_refs.py searches likewise found no existing definition node for the
coordinate-algebra category. The raw search tool records are copied into the new node.

No statement correction or statement dispute is needed. Sources read: the full local
Stacks 06WT statement and construction, and Alper Proposition 8.2.1 at
https://arxiv.org/html/1005.2398v3 (first two proof paragraphs).

## New nodes

`def-sfb-affine-groupoid-algebra` defines the commutative coordinate-algebra descent
category, its actual morphisms and invariant subring. Source: Stacks 06WT applied to
commutative algebra objects and Alper Proposition 8.2.1. Its independent module has no
postponed theorem or hollow data. The searches above find no existing notion: the
landed scheme-groupoid module category does not include multiplication or unit, and the
stack-algebra category is on the other side of the desired equivalence. Ring pushouts
and global coordinate rings themselves are reused from Mathlib, not redefined.
The ancestor tool returns None, as on the item's inherited blueprint record; the new
node preserves this and gives its explicit current-blueprint anchor and full via path.

## Second reading by Q91

A second pass was performed in this worker session; no independent subagent was started,
as the dispatcher brief explicitly prohibits that. The maintainer performs the independent
review of the delivery. Re-read both modules against every clause of the node. Checked
especially the order of the composable arrows (snd earlier, fst later), inverse of the
presentation two-arrow for contravariant ring restriction, and the scalar equation making
beta an L-algebra map. The source relation x=(y,r) beta composes in precisely that order.
The natural atlas comparison alone would not determine transport; the three theta
equations supply the missing normalization. Global sections use the existing compatible
families and the equality is literal evaluation, so rho is canonical. The surjection
conclusion is on A->B, not on invariants. Both modules have explicit universe binders,
autoImplicit false, source/blueprint docstrings, and lines of at most 100 characters.
The first compile found wrong guessed import paths; they were replaced by the recorded
Tilde and ModulePullbackAffineSections paths. Later elaboration found required explicit
CostructuredArrow endpoint simplification and Under.mk_hom simplification; those were
supplied without changing the mathematical interface. Final scompile.py run was clean
for both files separately in sandbox and library module forms.
