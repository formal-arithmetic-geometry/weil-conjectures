## Worker report

The module `Sheaf.AlgebraicTopology.SimplicialAbelianHornFilling` states
`CategoryTheory.SimplicialObject.exists_horn_filler`, with its sole proof `sorry`.
It adds no definition, assumption of the Kan property, or further node. The node is
unchanged except for `lean`. Its full seven-step proof is carried in the docstring.

Source read: `literature/stacks-project/simplicial.tex`, lines 5755–5803,
Tag 08NZ, `lemma-simplicial-group-kan`, including the compatible-face description
in the first paragraph and the two correction inductions. This is the additive
specialization of that statement, without a change to the source's hypotheses.

Hypothesis and clause correspondence (write N for the dimension in the node):

- A simplicial abelian group is `G : SimplicialObject AddCommGrpCat.{u}`.
  The universe `u` is arbitrary. Face and degeneracy homomorphisms are the existing
  `G.δ` and `G.σ`, rather than additional structure or assumptions.
- Every integer N ≥ 1 is represented uniquely as `n + 1`, with `n : ℕ`.
  No dimension covered by the node is omitted.
- The omitted face 0 ≤ k ≤ N is `k : Fin (n + 2)`, including both endpoints.
- The prescribed elements in degree N − 1 are
  `a : (i : Fin (n + 2)) → i ≠ k → G _⦋n⦌`.
  No value of the absent face is requested. The proof argument of `a` is irrelevant
  by Lean proof irrelevance, so this is precisely a family on indices other than k.
- Compatibility is `hcompat`. Its dependent match on `n, k, a` is `True` for
  `n = 0`, exactly the absence of compatibility conditions for N = 1. No face
  out of degree zero is used. For `n = m + 1`, any ordered pair p < q of indices
  in `Fin (m + 3)` is uniquely `p = i.castSucc`, `q = j.succ` for
  `i j : Fin (m + 2)` with `i ≤ j`. Conversely every such i,j gives p < q.
  The two nonmissing hypotheses are `hi : i.castSucc ≠ k` and `hj : j.succ ≠ k`.
  The equality `G.δ i (a j.succ hj) = G.δ j (a i.castSucc hi)` is exactly
  d_p a_q = d_(q−1) a_p. In particular `i = j` is included: it corresponds
  to adjacent distinct face indices, and must not be excluded.
- The conclusion `∃ u : G _⦋n + 1⦌, ∀ (i : Fin (n + 2)) (hi : i ≠ k),
  G.δ i u = a i hi` supplies the filler in degree N and all prescribed faces.
  It neither prescribes the missing face nor asserts uniqueness.

Dependency declarations read and used:

- `def-weil-pbc-simplicial-object`: its recorded module
  `Mathlib.AlgebraicTopology.SimplicialObject.Basic`; full signatures and docstrings
  of `CategoryTheory.SimplicialObject`, `.δ`, and `.σ` were read. The module is
  publicly imported, and `SimplicialObject` and `.δ` occur in the statement.
- Proof dependency `lem-weil-pbc-simplex-face-face-identity` is the Mathlib leaf
  `SimplexCategory.δ_comp_δ`, in `Mathlib.AlgebraicTopology.SimplexCategory.Basic`,
  lines 233–265 read. It is already publicly imported by the simplicial-object
  module. The functorial identity `SimplicialObject.δ_comp_δ` and the mixed
  identities were also read in that module. No additional import is needed.
- `Mathlib.Algebra.Category.Grp.Basic` supplies `AddCommGrpCat` and its actual
  homomorphisms. All imported modules serve the statement/dependency interface.

Edge cases checked before writing: dimension one has exactly one prescribed
vertex, filled by its zeroth degeneracy, for either missing endpoint. Dimensions
at least two use exactly the pairwise compatibility equations: in dimension two,
k = 1 leaves faces 0 and 2, with equation d_0 a_2 = d_1 a_0; k = 0 and k = 2
also retain their respective single compatibility equation. Adjacent indices
are represented by i = j. All endpoint faces are included by `Fin`; the lower
and descending inductions can have zero steps. In a constant simplicial group,
compatibility forces the prescribed elements to coincide once there are two;
the constant element fills the horn. The zero group has the unique zero filler.
No finiteness, nontriviality, characteristic or universe restriction is imposed.

Searches actually run with `msearch.py NV lem-trf-simplicial-abelian-horn-filling`:

- LeanFinder: `Every compatible horn in a simplicial abelian group admits a filler`.
  Eight hits including `SSet.KanComplex.hornFilling`, quasicategory horn filling,
  and `SSet.horn₃₂.exists_desc`/`horn₃₁.exists_desc`; none proves Kan for abelian groups.
- Loogle: `"SimplicialObject", "Kan"`. Eight hits about Kan extensions and
  Dold–Kan reflection of isomorphisms; no horn-filling theorem.
- LeanSearch: `Every simplicial abelian group is a Kan complex`. Eight hits,
  including `SSet.KanComplex`, Dold–Kan normalization, and `SSet.toTop`; no match.
- Grep in `AlgebraicTopology`:
  `hornFilling|exists_lift_of_kanComplex|AddCommGrpCat.*Kan|KanComplex.*AddCommGrpCat`.
  Ten hits on simplicial-set/quasicategory fillers, all requiring Kan/quasicategory
  assumptions. Read `KanComplex.lean` lines 30–62 to confirm the missing hypothesis.
- Local `rg` over `lean/Sheaf` and `lean/WeilConjectures` for horn filling and
  simplicial abelian groups found related surjective quasi-isomorphism and
  homotopy-equivalence statements, but no compatible-horn theorem. Also searched
  the node id in `lean/WeilConjectures` and `dag/lean_names_upstream.json`: no hit.
  `exists_horn_filler` has no declaration in Mathlib or either library root.

No statement correction, missing notion, unusable dependency or disputed claim.
The former worker's stale-dispatch concern is not an obstacle here: the current
live node has a stage-1 review by Q26 but no Lean declaration. This delivery is
stage 2 and preserves the reviewed statement and split.

Validation: the prescribed `scompile.py` compiled the module in sandbox and
library mode cleanly (1.1 s and 1.0 s). No diagnostic declarations remain.

## Second reading by NV

This is the author's second reading, under the dispatcher's instruction not to
start other agents; independent review is performed by the maintainer.

Re-read the live node, the complete new module, and Stacks 08NZ. The arbitrary
simplicial abelian group and universe match. Reindexing N = n + 1 covers every
positive dimension, and `Fin (n + 2)` includes both possible missing endpoint
faces. The dependent family has exactly the prescribed entries. In dimension
one the match reduces to `True`, so it adds no equation on vertices. In higher
dimension the reindexing of pairs is bijective: p < q gives i = p, j = q − 1,
with i ≤ j, and the two exclusions are precisely p,q ≠ k. Both sides of the
equation have degree N − 2. The conclusion quantifies exactly all nonmissing
faces and imposes neither an extra face nor uniqueness. The docstring follows
all seven proof steps and includes the boundary cases of both inductions.
The existing dependency interface is used directly. No mismatch was found and
no change to the node's mathematical statement was required.
