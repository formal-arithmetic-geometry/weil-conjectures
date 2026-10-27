## Worker report

The module `Sheaf.RingTheory.TruncatedAlgebraMatchingFiniteType` states
`Algebra.truncatedMatchingAlgebra_finiteType`. Its sole theorem has proof `sorry`.
The four preceding helpers construct the matching algebra introduced by this very
node and express surjectivity of its canonical map. No new independent notion or
DAG node is needed. The original node is unchanged except for `lean`.

Sources read: `literature/stacks-project/cotangent.tex`, Tag 08PW,
`lemma-polynomial`, statement and entire proof (including its n=0 and n=1
calculations), and `more-algebra.tex`, Tag 08NI, `lemma-formal-consequence`.
The node's six proof steps are retained in the theorem docstring. No full
simplicial extension, polynomial structure, or trivial Kan fibration in dimensions
above n is imposed: the node is the finite-truncation consequence of that proof.

Hypothesis and clause correspondence:

- The commutative Noetherian base is `(A : Type u) [CommRing A]
  [IsNoetherianRing A]`. The augmentation target is `(B : CommAlgCat.{v} A)`
  and `_hB : RingHom.FiniteType (algebraMap A B)`.
- `n : ℕ` includes n=0. `P : SimplicialObject.Truncated
  (CommAlgCat.{v} A) n` is exactly a functor on the opposite of the full
  simplex subcategory in dimensions 0 through n; it includes every face,
  degeneracy, and functor identity. The natural transformation
  `ε : P ⟶ (Functor.const ...).obj B` is an A-algebra augmentation, compatible
  with all maps. This is equivalent to a truncated object in the category of
  A-algebras augmented to B, without extra assumptions on that category.
- `_hP` says `RingHom.FiniteType (algebraMap A (P.obj (op r)))` for every
  truncated simplex r. Objects of that full subcategory are precisely [k]
  for k≤n, so this is exactly the termwise finite-type assumption.
- `truncatedMatchingAmbient P B k` has a common b∈B and a coordinate x_θ
  in P_r for every r<k and θ:[r]→[k]. Its type consists of genuine products of
  the given rings. `truncatedMatchingEval` is the corresponding coordinate
  projection, composed from `Pi.evalAlgHom` and `AlgHom.snd`.
- `truncatedMatchingAlgebra` is the intersection of algebra equalizers
  `ε_r(x_θ)=b` and `x_(α≫θ)=P(α)(x_θ)`. Thus its ring operations and A-algebra
  structure are the inherited componentwise ones. This is exactly the node's
  equivalent compatible proper-face family presentation. Here “proper” means
  smaller dimension; all order-preserving θ, including degenerate simplices,
  occur, as in proof step 1 of the node.
- For k=0 there are no r<0. The ambient second factor is a singleton and all
  equations are empty, so the matching algebra is canonically B. For k=1
  the only smaller simplex is [0], and its two maps to [1] give precisely
  P₀×_B P₀, together with the uniquely determined common b. For 2≤k≤n+1,
  restriction to the k+1 facets gives (p₀,…,p_k). On their intersections the
  family compatibility is precisely d_i p_j=d_(j-1) p_i for i<j. Conversely
  these identities define all lower injective-face values independently of
  the chosen facet; surjection/injection factorization forces every degenerate
  coordinate. Functoriality then gives every displayed compatibility. Edges
  force the common augmentation, so retaining b does not add data. These are
  algebra isomorphisms preserving componentwise operations, exactly as the
  node's proof step 2 explains.
- `TruncatedMatchingSurjective P B ε k hk` quantifies every element x of
  that constructed matching algebra and asks for p∈P_k whose augmentation is
  x's common b and whose image under every proper θ is x_θ. This is the graph
  of the canonical map, not an arbitrary chosen map or an extra lifting
  condition. Naturality and the functor laws make these coordinates a matching
  family for every p. Restriction to facets identifies it with
  p↦(d₀p,…,d_kp). In degree zero only ε₀(p)=b remains. `_hμ` quantifies all
  k≤n, including zero, exactly as the node requires.
- The conclusion `RingHom.FiniteType (algebraMap A
  (truncatedMatchingAlgebra P B ε (n + 1)))` is finite type of M_(n+1) over A.
  The subalgebra coerces to its actual carrier ring. There is no surjectivity
  hypothesis in degree n+1, and no conclusion about a different degree.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`, together with its
  docstring and `isNoetherianRing_iff_ideal_fg`, renders exactly the dependency's
  finite-generation-of-ideals notion.
- `Mathlib.RingTheory.FiniteType`, `RingHom.FiniteType`, is the dependency's
  recorded declaration; its full definition is `Algebra.FiniteType` for the
  map's algebra structure. We use it on each structure map, including the
  conclusion. The underlying `Algebra.FiniteType` definition was also read.
- `Mathlib.AlgebraicTopology.SimplicialObject.Basic`,
  `CategoryTheory.SimplicialObject.Truncated`, is the needed clause of the
  coskeleton dependency's mathlib_match. The recorded truncation, coskeleton,
  coskeleton adjunction and right Kan extension declarations were also read;
  this statement needs a truncated object, and does not assume a chosen
  coskeleton or equality with a chosen coskeleton.
- The proof dependency `lem-sfb-finite-type-surjective-product-pullback` had
  no Lean record or Mathlib match at the time of writing, so there is no
  recorded proof module to import. Its exact statement was read and is cited
  in the proof docstring. It is not needed to type this statement.

Edge cases checked before and after writing: n=0 yields precisely finite type
of P₀×_B P₀ under surjective augmentation. Degree-zero matching surjectivity
really requires ε₀ onto and is not vacuous. In degree two the three pairwise
face equations are obtained, rather than a full product of P₁. The one-element
ring, zero algebra, and characteristics 0 and p are all allowed; there is no
nontriviality, field, or characteristic binder. Universes u for A and v for B
and all P_r are independent; no equality of universes and no quantification
over smaller-universe test algebras is imposed. A finite truncation can always
be represented in a single such v.

Searches performed (all on 2026-10-24):

- `msearch.py ... leanfinder` with query “The matching algebra of a truncated
  simplicial finite type algebra over a Noetherian ring is finite type if all
  lower boundary maps are surjective”: 8 hits, including submersive
  presentations, finite-type polynomial quotient descriptions,
  `Algebra.EssFiniteType.of_surjective`, and splitting-index finiteness.
  None states this theorem or defines the relative algebra matching family.
- `msearch.py ... loogle '"cosk", Algebra.FiniteType'`: 0 hits.
- `msearch.py ... grep
  '(matching|coskeleton|cosk).*(FiniteType|finite type)|FiniteType.*(matching|cosk)'`:
  0 hits in Mathlib.
- `msearch.py ... leansearch` with query “The next matching algebra of a
  truncated simplicial finite type algebra over a Noetherian ring is finite
  type if lower matching maps are surjective”: 8 hits, all generic
  finite-type/surjective-map results. No exact matching theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for matching/algebra terms,
  truncated matching, and all five proposed declaration names, plus search of
  `dag/lean_names_upstream.json`: no exact statement or conflicting name.
  `grep -rn` for the item id in `lean/WeilConjectures`: no hit. The existing
  `SimplicialObject.matchingBoundaryShape` and `matchingBoundaryIndex` were
  read: these give only a multicospan for a full simplicial object in
  dimensions n+1 and n, not this augmented truncated algebra construction.
  The finite polynomial resolution module cites this item in its proof but
  does not state it. The étale matching module concerns qcqs schemes and
  likewise is not the algebra construction here.

Validation: every compiler invocation used `scompile.py`. The final source
compiled against the current server sources in 8.1 seconds with no errors or
non-sorry warnings. A local wrapper attempt reported disk exhaustion and
successfully used its built-in server confirmation. No live file or launcher
script was edited. No statement correction or disputed statement is needed.

## Second reading by Q41

This is a second pass by the same dispatcher-started worker, with the node and
final module reopened; the brief prohibits starting other agents and assigns
independent review to the maintainer after delivery.

I checked A/Noetherian, B/finite type, n, the entire truncated functor,
augmentation naturality, and termwise finite type against the theorem binders.
I unfolded both equalizer intersections: the first keeps every face over the
same b; the second has the correct contravariant orientation
x_(α≫θ)=P(α)(x_θ). The subtype restricts exactly to dimensions below k; at the
conclusion k=n+1 it includes all dimensions available in P, and in the lower
hypotheses it includes only strict lower dimensions. The graph in `_hμ` uses
that same θ, not its reverse, and matches every coordinate and the augmentation.
The k=0 test leaves exactly augmentation surjectivity. The k=1 test leaves
two zero-simplex values with equal augmentation. For k≥2 I checked the
facet-intersection identification and that all lower degeneracies are forced;
there is no added compatibility condition. The conclusion uses the same
constructed matching algebra in degree n+1 and the recorded finite-type notion.
There are no changed hypotheses or missing clauses. The initial ambient
presentation indexed by proof arguments did not synthesize a ring structure;
it was replaced by a subtype of proper simplices before the clean compile.
The final coordinate projection spells out both product families to avoid
an elaboration metavariable. These fixes only change how the explicit
componentwise algebra is constructed.
