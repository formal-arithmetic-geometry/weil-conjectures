## Worker report

The module `Sheaf.CategoryTheory.MittagLefflerExactSequence` states
`CategoryTheory.ShortComplex.isMittagLeffler_iff_of_isEssentiallyConstant` with a single
`sorry`; no definitions or proofs are added. The node is unchanged except for `lean`.
All variables and the universe `u` are explicitly bound.

Source read: https://stacks.math.columbia.edu/tag/070D (Lemma 12.31.6), including the
proof. The local literature checkout is absent on this machine, so the official tag
was opened instead. The node agrees with the source. The declaration docstring follows
all nine proof steps of the DAG, including the tail argument and the omitted detail.

Clause-by-clause correspondence:

- Inverse systems of abelian groups indexed by positive integers: `S.X₁`, `S.X₂`,
  and `S.X₃` are objects of `ℕᵒᵖ ⥤ AddCommGrpCat.{u}`. Index `n` denotes the
  original index `n + 1`, a bijective order reindexing that loses no term.
- Morphisms of inverse systems: `S.f` and `S.g` are natural transformations.
  Naturality is exactly compatibility with all transition homomorphisms;
  equivalently, it is successor compatibility in the node.
- The displayed sequence has zero composite: bundled `ShortComplex.zero`.
  This is implied by pointwise exactness and adds no restriction.
- Exactness of `0 → A_i → B_i → C_i → 0` for every index: `hS` requires
  `(S.map ((evaluation ℕᵒᵖ AddCommGrpCat).obj n)).ShortExact` for every `n`.
  Evaluation takes the three groups and component maps at that index.
  `ShortExact.exact` is middle exactness, `mono_f` gives injectivity of the first
  homomorphism, and `epi_g` gives surjectivity of the second. In abelian groups
  these are exactly all three short-exactness requirements.
- Essentially constant quotient: `hC : S.X₃.IsEssentiallyConstant`, precisely the
  dependency's existential value, compatible cone, splitting, and eventual
  factorization condition. No eventual-isomorphism hypothesis is substituted.
- A is ML iff B is ML: the conclusion is the biconditional between
  `(S.X₁ ⋙ forget AddCommGrpCat).IsMittagLeffler` and the identical expression
  for `S.X₂`. Mathlib's condition is stabilization of transition-map ranges:
  ranges decrease with the index. An attained minimal range stays attained for
  every later index; conversely a stabilized range is contained in all ranges
  into the fixed term (factor through the larger of their indices). Equality
  of underlying ranges is equality of image subgroups.

Dependency declarations read and used:

- `def-weil-inverse-system`: Mathlib `CategoryTheory.Functor.ofOpSequence` and
  `CategoryTheory.NatTrans.ofOpSequence`, module
  `Mathlib.CategoryTheory.Functor.OfSequence`. We use their corresponding
  functor/natural-transformation form, as the node's match prescribes.
- `def-weil-pbc-essentially-constant-system`:
  `CategoryTheory.Functor.IsEssentiallyConstant` (and its underlying
  `IsEssentiallyConstantWithValue`) in
  `Sheaf.CategoryTheory.EssentiallyConstantSystem`, imported directly.
- `def-weil-pbc-mittag-leffler-system`:
  `CategoryTheory.Functor.IsMittagLeffler` in
  `Mathlib.CategoryTheory.CofilteredSystem`, applied after `forget` exactly as
  its mathlib_match prescribes.
- Structural Mathlib declarations: `CategoryTheory.ShortComplex`,
  `ShortComplex.map`, `ShortComplex.ShortExact`, and `evaluation` were read in
  `ShortComplex.Basic`, `ShortComplex.ShortExact`, and `Products.Basic`.
  The preadditive imports supply zero morphisms and evaluation's zero preservation.

Edge cases checked: arbitrary universe `u`; all groups zero; quotient zero;
A zero (then B is essentially constant); C constant; and essentially zero C
with nonzero terms (zero transition maps). None is excluded or forces the
transition maps to become isomorphisms. Index zero is the first positive index,
not an extra hypothesis on a term. The index set is fixed nonempty ℕ, as the
node requires, not a general index set with empty cases. No finiteness, countability
of groups, surjectivity of transition maps, or tail truncation is assumed.

Searches for reuse:

- `msearch.py ... leansearch`: query "Mittag Leffler kernel if and only if middle
  in a short exact sequence of inverse systems with essentially constant quotient".
  UNAVAILABLE: service returned Internal Server Error; no verdict inferred.
- `msearch.py ... leanfinder`: query "short exact sequence of inverse systems
  of abelian groups with essentially constant quotient kernel is Mittag Leffler
  if and only if middle is Mittag Leffler". Eight hits: unrelated direct-limit
  exactness, Profinite.NobelingProof exactness, adic completion exactness,
  Function.Exact.exact_mapQ_iff, Serre-class closure, and
  Functor.isMittagLeffler_iff_subset_range_comp. None states this lemma.
- `msearch.py ... loogle`: query
  `CategoryTheory.Functor.IsMittagLeffler, CategoryTheory.ShortComplex`.
  OK, zero hits.
- `msearch.py ... grep`: query `IsMittagLeffler|IsEssentiallyConstant` in
  `CategoryTheory`; only CofilteredSystem ML definitions/comments returned.
- `rg -n 'MittagLeffler|EssentiallyConstant|lem-weil-pbc-exact-sequence-ml'`
  in `WeilConjectures` and project `lean/Sheaf`: upstream has no hits; project
  has the recorded essentially-constant definition and unrelated derived-category
  essentially-constant diagram definitions. No exact-sequence ML statement.
- Full proposed declaration/module names searched in Mathlib, WeilConjectures,
  project `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision.

No statement dispute, node fault, new node, or dependency repair was found.
Server single-file compilation succeeded with no errors or warnings (1.1 seconds).

## Second reading by H1

Node statement checklist and verdicts:

- The three inverse systems are rendered by `S.X₁`, `S.X₂`, and `S.X₃` in
  `S : ShortComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{u})`; the index `n : ℕ` is represented by
  `n : ℕᵒᵖ` (with the positive index convention documented in the declaration). Verdict:
  same objects and indexing, with no universe restriction beyond the arbitrary `u`.
- The two morphisms of inverse systems are the short-complex arrows `S.f` and `S.g`,
  hence natural transformations and therefore compatible with every transition map.
  Verdict: present with exactly the required naturality.
- The zero composite is supplied by the `ShortComplex` structure. Verdict: present;
  pointwise short exactness implies this and the bundled zero-composite condition adds
  no extra mathematical hypothesis.
- Pointwise exactness is rendered by
  `hS : ∀ n : ℕᵒᵖ, (S.map ((evaluation ℕᵒᵖ AddCommGrpCat).obj n)).ShortExact`.
  `ShortExact` supplies exactness, monomorphism of the first map, and epimorphism of
  the second in `AddCommGrpCat`, exactly the three clauses of each short exact sequence.
  Verdict: same hypothesis, neither strengthened nor weakened.
- Essential constancy of the quotient is rendered by
  `hC : S.X₃.IsEssentiallyConstant`, using the project's declaration
  `CategoryTheory.Functor.IsEssentiallyConstant` for inverse systems of abelian groups.
  Verdict: same cone, splitting, and eventual factorization notion; no eventual-isomorphism
  condition is added.
- The conclusion is rendered as
  `(S.X₁ ⋙ forget AddCommGrpCat).IsMittagLeffler ↔
  (S.X₂ ⋙ forget AddCommGrpCat).IsMittagLeffler`.
  Verdict: this is precisely ML for the underlying inverse systems of abelian groups,
  equivalent to stabilization of transition-image subgroups in the node.

No mismatch was found. The Lean file and node `lean.statement` are verbatim aligned;
no repair was necessary. The declaration has no unbound variables, and its proof is only
`sorry` as required for a stage-2 statement.

Edge cases checked independently: arbitrary universe `u`; zero A, B, or C systems;
constant and essentially-zero quotients; zero transition maps; and the first positive
index represented by Lean's `0`. The node concerns the fixed nonempty positive-index
system, so no empty-index case is required. No characteristic, finiteness, Noetherian,
separation, or surjectivity assumptions occur in the source or Lean statement.

Reuse searches were rechecked against Mathlib, `WeilConjectures`, and `lean/Sheaf` using
`msearch.py` (LeanSearch, LeanFinder, and Loogle queries), `rg`, and declaration-name
searches. Only the generic `Functor.IsMittagLeffler` and the project's
`Functor.IsEssentiallyConstant` were found; neither states this exact-sequence theorem.
The full declaration name also has no collision. The recorded dependency declarations
therefore remain the correct ones, and no new or dependency module is needed.
