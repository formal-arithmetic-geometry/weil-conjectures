## Worker report

The module `Sheaf.RingTheory.RegularSequenceSwapTwo` states
`RingTheory.Sequence.IsRegular.swap_of_isSMulRegular`, with its proof left as `sorry`.
No definitions, extra nodes, dependency modules, or statement corrections are needed.

Hypothesis and conclusion correspondence:
- A commutative ring R is `{R : Type u} [CommRing R]`, for explicitly declared universe u.
- Elements a,b of R are `{a b : R}`.
- The hypothesis that a,b is a regular sequence in R is `(hab : IsRegular R [a, b])`.
  Here the module is R itself. Mathlib's `regular_mod_prev` expresses injectivity on each
  successive quotient; `top_ne_smul` expresses the nonzero final quotient R/(a,b).
- The extra hypothesis that b is a nonzerodivisor on R is `(hb : IsSMulRegular R b)`.
  The definition is injectivity of scalar multiplication on R, which is left multiplication.
- The conclusion that b,a is regular in R is `IsRegular R [b, a]`, retaining both
  successive injectivity and the nonzero final quotient, with precisely the reversed order.

Dependency used: `def-weil-pbc-regular-sequence` records
`RingTheory.Sequence.IsRegular` in `Mathlib.RingTheory.Regular.RegularSequence`.
Read the complete declaration and docstring, its parent `IsWeaklyRegular`, and
`isWeaklyRegular_iff_Fin`. The recorded Mathlib definition supplies exactly this specialization
M = R, so its import is used directly. Also read `IsSMulRegular` and its docstring in
`Mathlib.Algebra.Regular.SMul`; it is supplied transitively by the same import.
All variables and the universe are explicitly bound; auto-implicit variables are unnecessary.

Source check: the local `literature/stacks-project/algebra.tex` is absent on this machine.
Read the official source at https://stacks.math.columbia.edu/tag/07DW instead, specifically
Lemma 10.68.10's proof, case r = 2, which states exactly this implication. The declaration's
docstring contains both proof steps of the node: unwinding the definition and exchanging the
ideal generators, then the argument ax = by, y = az, x = bz. No additional assumptions appear.

Edge cases checked before writing:
- In the zero ring the hypothesis `IsRegular R [a,b]` fails since the final quotient is zero;
  no separate `Nontrivial R` restriction is imposed.
- If either element is a unit, the final quotient is zero and the regularity hypothesis fails.
- If a or b is zero in a nonzero ring, the requisite injectivity on R fails (for a from hab,
  for b from hb). If a = b, multiplication by b on R/(a) is zero, contradicting the nonzero
  final quotient. No distinctness or nonzero assumptions are added.
- Rings with zero divisors, nonlocal rings, non-Noetherian rings, and all characteristics
  remain allowed; the kernel argument uses no stronger ring assumption than commutativity.
- There is no empty-list case to exclude: the node specifically concerns two elements.

Searches (actual outputs logged in searches.jsonl by msearch.py):
- leansearch query: "If a b is a regular sequence in a commutative ring and b is a
  nonzerodivisor then b a is a regular sequence". Service unavailable: Internal Server Error.
- leanfinder query: "Swapping a regular sequence of length two when the second element is
  a nonzerodivisor on the ring". Eight results include IsRegular.cons, cons',
  isRegular_cons_iff, IsLocalRing.isRegular_of_perm and IsWeaklyRegular.prototype_perm;
  no exact statement. Local permutation needs local/Noetherian hypotheses; prototype_perm
  has subquotient torsion conditions and concludes only weak regularity.
- loogle query: "RingTheory.Sequence.IsRegular, List.Perm". Two results:
  IsLocalRing.isRegular_of_perm and IsRegular.of_perm_of_subset_jacobson_annihilator;
  both require unavailable extra assumptions.
- grep query: "swap|prototype_perm|isRegular_of_perm", subdirectory RingTheory/Regular.
  Read the private IsWeaklyRegular.swap (line 576) and public prototype_perm (line 594).
  The private statement is not externally usable, concludes only weak regularity, and uses
  a torsion condition rather than the node's nonzerodivisor hypothesis.
- rg over WeilConjectures and lean/Sheaf for regular/swap and IsRegular with lists:
  no exact statement; the existing regular-local-ring and regular-system-of-parameters
  material concerns other statements. grep for the item id in WeilConjectures: no hits.
- rg for `IsRegular.swap_of_isSMulRegular|swap_of_isSMulRegular` in Mathlib,
  WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json: no name collision.

No statement dispute or node fault was found. Validation: server single-file compile and
`deliver2.py E1 lem-weil-pbc-regular-sequence-swap-two --no-push`; the second reader supplies
its independent reading and delivery after this worker finishes.

## Second reading by E1

Independent object/hypothesis/conclusion inventory, matched with the actual signature:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Arbitrary commutative ring R | `{R : Type u} [CommRing R]`, with `universe u` | Exact; no field, domain, locality, Noetherianity, or nontriviality instance. |
| Two elements a,b of that ring | `{a b : R}` | Exact; both universally quantified before the hypotheses. |
| a,b is a regular sequence in R | `(hab : IsRegular R [a, b])` | Exact specialization of the dependency's recorded definition to the self-module R. |
| b is a nonzerodivisor on R | `(hb : IsSMulRegular R b)` | Exact: the definition is `Function.Injective ((b • ·) : R → R)`; the self-module action is multiplication. |
| b,a is a regular sequence in R | `IsRegular R [b, a]` | Exact; includes injectivity of b on R, injectivity of a on R/(b), and nonzero R/(b,a), in this order. |

Opened `def-weil-pbc-regular-sequence.json`, including its statement and recorded Mathlib
signature, and read Mathlib `RegularSequence.lean` lines 129–147 and `SMul.lean` lines
35–46. `IsWeaklyRegular.regular_mod_prev` tests every index against the quotient by
`Ideal.ofList (rs.take i) • ⊤`. For `[a,b]` these are R/(0) and R/(a); for `[b,a]`
they are R/(0) and R/(b). These submodule quotients are precisely the underlying
R-modules of the ideal quotients in the node. `IsRegular.top_ne_smul` says the full
quotient is nonzero, rather than just weak regularity. Mathlib's use of
`Quotient.nontrivial_iff` at line 201 confirms this interpretation. The definition's
optional phrase “in an ideal” is not invoked by this item; no ideal membership
hypothesis is missing. The only dependency record is usable, and its module is
imported directly. No additional notion, new node, or dependency module is needed.

Source read independently: because the repository's Stacks checkout is absent,
opened https://stacks.math.columbia.edu/tag/07DW and /tag/00LF and fetched the official
`stacks/stacks-project/master/algebra.tex` into this item's scratchpad. Read its
Conventions (lines 32–43), regular-sequence definition (16594–16609), and the named
polynomial-ring lemma and proof (16797–16830). Rings are commutative with identity,
including the zero ring. The r=2 proof states this precise implication. The surrounding
lemma's non-unit-ideal condition is already implied by hab's nonzero final quotient;
no extra independent hypothesis is required. The regular-sequence section imposes
no ambient Noetherian or local assumption.

Edge cases: the zero ring is admitted by `[CommRing R]`, but hab is impossible since
its final quotient is zero. A unit among a,b likewise makes hab impossible. Zero a
contradicts its initial injectivity on the nonzero ring implied by hab; zero b
contradicts hb. Equal a,b cannot satisfy the hypotheses: b then acts as zero on the
nonzero intermediate quotient. All characteristics, rings with zero divisors,
non-Noetherian and nonlocal rings remain in scope. Universe u is arbitrary, with no
unbound universe or variable. There is no index family, scheme, or n parameter;
empty-index, empty-scheme and n=0 cases are inapplicable to this fixed two-term node.

Independent searches, with different queries (logged in searches.jsonl):
- LeanSearch: “Exchange two successive regular elements assuming each acts injectively
  on the original ring”; service unavailable (Internal Server Error), recorded without
  claiming a negative mathematical result.
- LeanFinder: “IsRegular R [x,y] and injective multiplication by y imply IsRegular R [y,x]”;
  results concern regular elements/products and scalar multiplication, not this sequence theorem.
- Loogle: `IsSMulRegular, RingTheory.Sequence.IsRegular`; eight results, including
  `IsRegular.cons`, `cons'`, the cons iff statements, and induction principles; no exact match.
- Logged grep: `IsRegular.*(swap|comm|pair)|IsWeaklyRegular.*(swap|comm|pair)|isRegular.*(pair|two|comm)`
  over Mathlib RingTheory. Read the private `IsWeaklyRegular.swap` at 576,
  `prototype_perm` at 594, and public permutation statements at 627–670.
  The private lemma is not reusable as a public declaration and gives only weak
  regularity. Public permutation results require extra Noetherian/local/Jacobson or
  torsion conditions, so cannot be recorded as an exact existing match.
- Independently ran rg over the whole source `WeilConjectures` and repository
  `lean/Sheaf` for regular-sequence predicates, two-element list statements and swap
  vocabulary. Opened the source extension
  `WeilConjectures/Mathlib/RingTheory/Regular/RegularSequence.lean` in full: it states
  flat transport, concatenation along a surjection, and polynomial-variable weak
  regularity, not the present swap. No exact statement was found in the project.
  Name/id searches over these roots and `dag/lean_names_upstream.json` found no collision.

No mismatch was found. Left the correct Lean module and node record unchanged;
only appended this independent review and search evidence. No statement correction
or citer-verdict check is applicable. The module and theorem docstrings name 07DW and
the blueprint id. The theorem docstring carries both node proof steps: transfer
nonvanishing by equality of the generated ideals, then ax=by, y=az, cancellation of a
and x=bz. There are no definitions and exactly one named theorem with proof `sorry`;
no theorem is proved. Header, namespace, import and line widths conform. Checked
`lean.statement` against the theorem signature verbatim, including its line break.

Validation: `scompile.py E1 lem-weil-pbc-regular-sequence-swap-two` on the delivered
module completed with exit code 0 in 1.3 seconds, with no warnings or errors.
