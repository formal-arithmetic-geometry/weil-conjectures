## Worker report

The module `Sheaf.AlgebraicGeometry.AmpleSeparated` states
`AlgebraicGeometry.isSeparated_of_isAmple`: for a scheme `X`, an invertible
module `L` with `L.IsAmple` implies `X.IsSeparated`.

The node's hypotheses and conclusion render as follows. The scheme hypothesis
is `(X : Scheme.{u})`; the invertible module is `(L : X.Modules)` together with
the typeclass hypothesis `[L.IsInvertible]`; ampleness is the explicit
proposition `(hL : L.IsAmple)`. The conclusion that the structure morphism is
separated is represented by Mathlib's scheme-level proposition `X.IsSeparated`,
which is separatedness over the terminal scheme (the terminal scheme is
`Spec ℤ`). The theorem proof is intentionally `sorry` at stage 2.

The dependency declarations consulted were `AlgebraicGeometry.Scheme` and
`AlgebraicGeometry.Scheme.Hom` (Mathlib, for `Scheme`),
`AlgebraicGeometry.Scheme.Modules.IsAmple` from
`Sheaf.AlgebraicGeometry.Ample` (for the ample invertible module), and
Mathlib's `AlgebraicGeometry.IsProper` record for the proper-morphism node.
The latter records the broader proper notion; the separated conclusion itself
uses Mathlib's `AlgebraicGeometry.Scheme.IsSeparated`.

Edge cases checked: the universe `u` is explicit and unrestricted; no
quasi-compactness hypothesis is added to the theorem (the node's general
covering formulation says it is unused); no positivity or nonemptiness
assumption beyond `IsAmple` is introduced; affine and empty schemes are covered
by the scheme-level proposition.

Searches for an existing statement or duplicate included:

* `msearch.py C1 lem-weil-pbc-ample-scheme-separated leanfinder "scheme with
  an ample invertible module is separated"`: no project declaration found.
* `msearch.py C1 lem-weil-pbc-ample-scheme-separated loogle
  "IsAmple, IsSeparated"`: Mathlib's `Scheme.IsSeparated` and the project's
  `Scheme.Modules.IsAmple` found, but no implication theorem.
* `msearch.py C1 lem-weil-pbc-ample-scheme-separated grep "ample|IsSeparated"
  Mathlib/AlgebraicGeometry`: no ample-to-separated theorem.
* `rg -n "IsAmple|isSeparated_of_isAmple|ample.*separated" lean/Sheaf
  WeilConjectures`: only the `IsAmple` definition and unrelated separatedness
  uses; no duplicate theorem.

No statement fault or `STATEMENT-DISPUTED` applies.

## Earlier second reading (a previous round; superseded)

Reading the node and module side by side, the binders match exactly: `X` is a
scheme, `L` is an `X.Modules`, `[L.IsInvertible]` supplies invertibility, and
`hL : L.IsAmple` supplies ampleness. The conclusion `X.IsSeparated` is the
scheme-level separatedness predicate corresponding to the structure morphism
to `Spec ℤ`. No hypothesis or clause is omitted, strengthened, or specialized;
therefore no changes were needed.


## Second reading by C1

Independent reading against the sandbox node and module, the three dependency
nodes, their declarations, and Stacks `properties.tex` (local source copy
`/home/ubuntu/c1-stacks-review/properties.tex`, labels `definition-ample`,
`lemma-affine-s-opens-cover-quasi-separated`, `lemma-ample-separated`).
The section assumes only a scheme and an invertible module, with no fixed
field, characteristic, Noetherian condition, or separatedness hypothesis.

Object/hypothesis/conclusion checklist (node statement, in order):

1. A scheme X [def-pc-scheme]: `(X : Scheme.{u})` in both theorems.
   Verdict: exactly Mathlib's `AlgebraicGeometry.Scheme`; its locally ringed
   space has an affine cover. The dependency's Mathlib match records this
   type and its morphisms, not a restricted class of schemes.
2. An invertible O_X-module L: `(L : X.Modules) [L.IsInvertible]`.
   Verdict: exact. Opened `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
   `Scheme.Modules.IsInvertible` asks for local isomorphisms to the structure
   module on neighbourhoods of every point. It is the scheme-module notion
   required by the contract, with no additional instance assumption.
3. Ampleness [def-weil-pbc-ample-invertible-module]: `(hL : L.IsAmple)`.
   Verdict: exact for the first theorem. Opened the recorded module
   `Sheaf.AlgebraicGeometry.Ample`: `IsAmple` is `CompactSpace X` AND the
   affine nonvanishing-locus covering condition. Compactness here is
   quasi-compactness, with no Hausdorff condition. The locus uses the germ
   outside the maximal ideal times the stalk, as Definition 01PS and the
   node require. This is not upstream's `AlgebraicGeometry.IsAmple`, whose
   source module `Modules/Ample.lean` restricts to projective field-schemes.
4. X is separated, meaning its structure morphism to Spec Z is separated
   [def-weil-proper-morphism]: `X.IsSeparated` in both theorems.
   Verdict: exact. Read `Mathlib.AlgebraicGeometry.Morphisms.Separated`:
   `Scheme.IsSeparated` means `IsSeparated (terminal.from X)`;
   `AlgebraicGeometry.IsSeparated` means the diagonal is a closed immersion.
   Read `Mathlib.AlgebraicGeometry.Limits`: Spec Z is terminal (the
   universe-polymorphic construction uses Spec of ULift Z). These are the
   separatedness notions explicitly defined in the proper-morphism node;
   its match `IsProper` is not imposed as a hypothesis. No properness or
   finite-type assumption has been smuggled in.
5. More generally every point lies in an affine X_s for a positive-degree
   section, without quasi-compactness: the new theorem
   `isSeparated_of_affine_nonvanishing_cover` has
   `hcover : ∀ x : X, ∃ n : ℕ, 0 < n ∧ ∃ s :
   (L.tensorPow n).val.presheaf.obj (Opposite.op ⊤), ∃ U : X.Opens,
   x ∈ U ∧ IsAffineOpen U ∧ (U : Set X) =
   nonvanishingLocus (L.tensorPow n) s`, concluding `X.IsSeparated`.
   Verdict: exact, now present. The existential open U is exactly X_s,
   not merely an affine subopen of X_s. The existing dependency's
   `nonvanishingLocus` is reused; no private notion is introduced. Read
   `tensorPow`: degree zero is the tensor unit and successors tensor with L.
   The global section is the sheaf evaluated at the top open. Quantifiers
   follow the point, degree, section order of the node and Stacks 01PY.

Edge cases: both theorems quantify over arbitrary `Scheme.{u}` with an
explicit unrestricted universe. Neither requires a base field or restricts
characteristic. The empty scheme is included; the general pointwise cover
condition is vacuous there. No nonempty index set or finite covering is
assumed. The zero module is eligible precisely when the invertibility
hypothesis holds (in particular on the empty scheme); no nonzero hypothesis
was added. Degree n = 0 is correctly excluded by `0 < n`, as in the node,
while the underlying tensor-power definition includes it. The general
statement allows non-quasi-compact schemes and arbitrary covering size.

Independent searches used different terms from the first worker:

- `msearch.py ... leansearch "a line bundle whose affine nonvanishing loci
  cover a scheme implies separatedness"`: service unavailable (Internal
  Server Error); this is not evidence of absence.
- `msearch.py ... loogle "IsSeparated, Scheme"`: no hits, unknown identifier
  in that service's index; this is not evidence of absence.
- `msearch.py ... leanfinder "An invertible sheaf with affine section nonzero
  loci covering X forces the diagonal of X to be a closed immersion"`:
  eight hits for separated diagonal and affine-cover machinery, including
  `isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange` and
  `Scheme.isSeparated_iff_isClosedImmersion_prod_lift`; none states this
  implication for invertible modules.
- `msearch.py ... grep
  "isSeparated.*[Aa]mple|[Aa]mple.*[Ss]eparated|nonvanishingLocus"
  AlgebraicGeometry`: no Mathlib hits.
- `rg` for `isSeparated_of_isAmple`, ampleness/separatedness in either order,
  and `nonvanishingLocus` across upstream `WeilConjectures`, project
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: only existing locus
  definitions and uses, comments mentioning the result, and unrelated
  relative projective ampleness; no existing theorem for this node.
  Opened upstream `Modules/Ample.lean` to verify the different notion.

Mismatches repaired: H3, the parenthetical general conclusion was absent;
added the second theorem without changing the correct ample theorem or the
node's mathematical statement. H8, the docstring only summarized the proof;
expanded both theorem docstrings to all six node steps and their dependency
ids (cover, common degree, transition functions, localization, tensor-map
surjectivity, affine-cover criterion). H9, added the conventional copyright
header. Recorded both declarations in the node's `lean.declarations`; the
main `lean.statement` still agrees verbatim with its unchanged signature.
Both theorem proofs are `sorry`; there are no definitions or proved claims
in the delivered module. No new nodes, dependency modules, or statement
correction is needed.

Validation: `scompile.py C1 lem-weil-pbc-ample-scheme-separated` compiled
this complete module on the server in 1.8 seconds with no errors or warnings.
Checked all binders and universe `u` by eye, checked the main signature
against `lean.statement` byte for byte, and checked every line is at most
100 characters. `deliver2.py ... --no-push` printed OK: preflight and
server compile both passed.
