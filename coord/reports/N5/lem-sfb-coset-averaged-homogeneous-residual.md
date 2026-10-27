## Worker report

The module `Sheaf.RepresentationTheory.CosetAveragedHomogeneousResidual` states
`ContinuousCohomology.CosetResidual.coset_averaged_homogeneous_residual` with
`sorry`. It supplies real definitions of the tuple groups, deletion boundary,
diagonal translation, invariance predicate, additive evaluation, differential,
normalized average and evaluation of a chain operator. These are constructions
explicitly introduced by this node, not additional independent notions. Every
helper is recorded in `lean.declarations`. No definition contains postponed data
or proof, and the main theorem is the sole postponed theorem. The item's node
changes only in `lean`; there is no statement correction or dispute.

I read the current blueprint `literature/blueprint/latest/blueprint/`
`sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3). It gives the
application context, not this auxiliary statement. Accordingly the module
explicitly attributes the auxiliary argument to the agent-written expansion.
Its theorem docstring reproduces all nine proof steps in the node.

Hypothesis and clause correspondence:

- The node's topological group is `G` with `Group`, `TopologicalSpace` and
  `IsTopologicalGroup`. The subgroup is `H : Subgroup G`, with `H.FiniteIndex`.
  `D : Finset G` and `hD : Subgroup.IsComplement (H : Set G) (D : Set G)` say
  multiplication H times D is bijective: exactly one right-coset representative.
  The node's m is `D.card`, equal to H.index by the transversal bijection.
- The node's positive degree is `n + 1`, with the Lean binder `n : ℕ`.
  Tuple length k represents degree k-1. Thus the top tuples have length n+2,
  the primitive tuples length n+1, and the empty tuple has length zero.
  `E : Set (Fin (n + 2) → G)` is exactly the specified top-degree subset.
- `Chain G k := (Fin k → G) →₀ ℤ` is the canonical free integer tuple group.
  `Finsupp.single x 1` is its specified basis element. The definition uses
  `Finsupp.linearCombination` for the additive extension from this basis.
  The empty tuple is `Fin 0 → G`, a singleton type, not a zero chain group.
- `boundary G k` sends a length k+1 basis tuple to the signed sum of all
  its k+1 deletions. At k=0 it sends a singleton to the empty tuple.
  No boundary out of the empty tuple is needed by the truncated identities.
- `A` and `Q` are integer-linear homomorphisms, indexed by tuple length.
  They are padded outside the finite truncation with unused arbitrary maps;
  all requirements are restricted to lengths through n+2. Such padding adds
  no mathematical requirement: zero maps extend any truncated family.
- `hA0`, `hQ0` express A in degree -1 is identity and Q in degree -1 is zero.
  `hAe`, `hQe` express H-equivariance on every chain, including degree -1.
  `hchain` is boundary A = A boundary, through the node's degree n.
  `hhomotopy` is 1-A = boundary Q + Q boundary in all nonnegative degrees
  through that degree. No A one degree higher is assumed.
- `tA,tQ`, integer arrays `a,b`, continuous tuple maps `α,β`, and `hA,hQ`
  give exactly the input-independent finite expansions on every basis tuple
  in nonnegative degrees. They allow empty lists, zero coefficients and
  repetitions, and impose no test on the input values.
- `hE` says the support of A applied to every top basis tuple is contained
  in E. For the specified free basis this is exactly membership in the
  integer span of E. It does not require each term in a chosen unreduced
  expansion to lie in E, which would be an extra assumption.
- `l : ℕ` and `Fact l.Prime` give ℚ_[l] = Mathlib's Padic l. The subsequent
  quantification over `V : Type v` assumes exactly `AddCommGroup`, a
  `Module ℚ_[l]`, `TopologicalSpace`, `ContinuousAdd` and `ContinuousSMul`.
  In particular there is no Hausdorff, normed, complete or continuous-negation
  hypothesis. The trivial group action is expressed by diagonal invariance;
  no unrelated representation is supplied.
- `evaluate F` is the additive extension F-hat, `pull (Q (n+1)) F` is U F,
  and `pull (A (n+2)) F` is W F. `delta` is the displayed signed-deletion
  differential. `average (l := l) D` is the displayed normalized average,
  with denominator the cardinality of the given right transversal.
- The first coefficient-independent conjuncts give continuity of precisely
  the translated evaluation maps β_j(s*x) and α_j(s*x). Their formulas
  depend only on Q, A and D, all quantified before V.
- The first V-dependent conjunct states delta squared vanishes in every
  nonnegative homogeneous degree, for every function (hence for every
  continuous function) without invariance assumptions.
- The next three conjuncts say averaging preserves continuity and turns
  H-invariance into G-invariance, commutes with delta, and fixes invariant
  functions. `Invariant ⊤` means invariance under every group element.
  The algebraic commutation and fixed-function formulas apply to all
  functions; no continuity is needed for these finite-sum identities.
- The F conjunct assumes `Continuous F` and `Invariant ⊤ F`, and asserts
  continuity and H-invariance of both U F and W F. Under `delta F = 0`
  its four displayed conclusions are F=delta U F+W F, delta W F=0,
  the averaged decomposition, and delta of the averaged residual=0.
- The vanishing implication `(∀ x ∈ E, F x = 0)` gives W F=0 and
  its average=0. It lies outside the cocycle implication, so does not
  inadvertently assume F is a cocycle.
- The next two conjuncts explicitly display the finite sums over s in D
  and j in the given expansion arrays, with coefficients b_j/D.card and
  a_j/D.card, and maps β_j(s*x), α_j(s*x). These are valid for every F,
  with all integers and continuous maps fixed independently of V and F.
- The last two conjuncts express additivity and ℚ_[l]-homogeneity of
  M U and M W, respectively, on the full spaces of functions. These
  imply linearity on the continuous invariant functions in the node.
- There is no normality, prime-to-l, completeness, or cohomology quotient
  binder anywhere. Universes u for G and v for V are independent.

Dependency declarations read and used:

- `def-weil-pbc-free-module`: `Module.Free` in
  `Mathlib.LinearAlgebra.FreeModule.Basic`, whose class has a specified
  nonempty basis type. The concrete free object is Mathlib's Finsupp,
  with `Finsupp.single`, `Finsupp.linearCombination` and `Finsupp.lmapDomain`.
  I read the full signatures and docstrings of Free and linearCombination.
- `def-weil-l-adic-numbers`: its `mathlib_match` is `Padic` in
  `Mathlib.NumberTheory.Padics.PadicNumbers`; I read its definition as the
  Cauchy completion of ℚ with respect to the p-adic norm and the field
  instances derived there. The dependency has no Lean record and needs none.
- Right transversals use Mathlib's `Subgroup.IsComplement` and the documented
  `rightQuotientEquiv` from `Mathlib.GroupTheory.Complement`. I checked that
  the H-times-D order encodes right cosets H\G, not left cosets.
  All statement/proof dependency modules are publicly imported, since both
  proof dependencies are also statement dependencies.

Edge cases checked before and during writing: n=0 in Lean is node degree 1;
Q at tuple length 1 gives a degree-zero primitive; the augmentation uses the
unique empty tuple; H=G gives a one-element transversal, including a
representative other than identity; non-normal H still has right-coset
permutation by right multiplication; l dividing D.card still gives a
nonzero denominator in characteristic zero; V=0, E empty or universal,
and zero/empty finite expansions are allowed. D empty cannot satisfy hD
because a group contains the identity. No compactness is used to infer
continuity. Support containment permits cancellation in the chosen A list.

Searches made:

- `msearch.py ... leanfinder "Normalized finite right coset averaging of
  continuous homogeneous cochains and residual of a chain homotopy"`:
  eight hits, including ContinuousCohomology.homogeneousCochains and its
  recursive complex; none states the finite-coset residual result.
- `msearch.py ... leansearch "Normalized averaging over right cosets of a
  finite index subgroup commutes with the homogeneous cochain differential
  and evaluates a chain homotopy residual"`: eight hits on HomComplex,
  groupCohomology, inhomogeneous differentials, resolutions and homology;
  none matches this cochain-level statement.
- `msearch.py ... loogle '"IsRightTransversal"'`: no hits. Local source
  inspection instead found Subgroup.RightTransversal and IsComplement.
- `msearch.py ... grep '(averag|homogeneous|Transversal)'
  RepresentationTheory/Homological`: 25 hits on continuous homogeneous
  cochains and standard resolutions; no matching residual statement.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for coset averaging,
  homogeneous residuals, transversals and homogeneous cochains: found
  coordinate comparison modules, FiniteIndexRectanglePrimitiveOperator
  and BoundedFiniteEvaluationRectangleReplacement. Their statements were
  read: they construct a primitive in a geometric rectangle situation,
  rather than evaluate an arbitrary given chain homotopy and retain W F.
- `grep -rn 'lem-sfb-coset-averaged-homogeneous-residual'
  lean/WeilConjectures`: no declaration tagged with this node.
- Local Mathlib searches found Finsupp.linearCombination and lmapDomain
  and the right-coset API; those are used directly. I read
  TopRep.homogeneousCochains in ContCohomology/Basic: it is a recursively
  iterated continuous-map complex and does not provide these direct
  jointly continuous tuple evaluation maps or the asserted averaging theorem.
- DAG concept searches for tuple groups and alternating deletion found
  lem-sfb-ordered-join-coset-comparison (unstated, no recorded declaration)
  and the existing OrderedJoinPartialContraction module. The latter's
  colored, strictly increasing faces are different from all ordered tuples
  with repetitions. No independent definition node was needed for the
  concrete constructions expressly introduced by this item's statement.

Validation uses only scompile.py and deliver2.py. An initial support coercion
error was repaired by coercing the finite support to a Set; a line-width
warning was repaired by wrapping the scalar-linearity equality.

## Second reading by N5

The dispatcher brief prohibits starting another agent; this is a second
in-thread reading, not a claim of independent review. The maintainer's
independent review remains required. I reopened the node and read the
module's theorem clause by clause against it using the correspondence above.
In particular I checked the length/degree shift, the direction of the
transversal, that Q in the top degree is supplied, and that the vanishing
conclusion does not depend on the cocycle premise. I removed an initial
unnecessary universal quantifier over all chain operators from the U-linearity
clause, restricting it to the specified Q. The finite continuous formulas
are explicitly determined by the given input arrays, rather than being
arbitrary existential operators. No node correction or omitted clause was
found. The empty tuple and non-normal subgroup cases retain the node's scope.
