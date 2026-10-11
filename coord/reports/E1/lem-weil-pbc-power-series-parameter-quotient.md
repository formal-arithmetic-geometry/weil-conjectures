## Worker report

The module `lean/Sheaf/RingTheory/PowerSeriesParameterQuotient.lean` states the field and
Cohen cases separately, with sorry proofs only. No definition is introduced and no node
statement is changed. Source checked directly at https://stacks.math.columbia.edu/tag/07NM,
clauses (2), (4), with the proofs of (1), (3). The literature TeX is not present on this
machine, so the official Stacks page supplied the source text.

Hypothesis and clause matching:

- Field coefficients K: `(K : Type u) [Field K]`; n variables: `MvPowerSeries (Fin n) K`.
- Cohen coefficients: `(Λ : Type u) [CommRing Λ]`, `(p : ℕ)`, `hΛ : IsCohenRing p Λ`.
  The explicit `IsLocalRing Λ` and `IsNoetherianRing Λ` instances expose structures already
  entailed by hΛ (a DVR is a local PID, hence Noetherian); they impose no additional
  mathematical condition. They supply the existing power-series local and Noetherian
  instances needed to type the parameter-system predicate.
- The partial system z and chosen complementary parameters y are finite ordered lists.
  Giving both lists explicitly states the result for every chosen completion of z,
  exactly as the node's final variable-identification clause requires. An existential
  completion can immediately be used as a witness to these binders.
- In the field case `IsLocalRing.IsRegularSystemOfParameters (z ++ y)` says their ideal
  span is the maximal ideal and their number is the Krull dimension. In the Cohen case
  the list is `C (p : Λ) :: (z ++ y)`: p is present apart from z. This predicate on a
  Noetherian local ring entails regularity, as explained by its definition node and
  Mathlib `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`. No extra regularity
  hypothesis is imposed on the power-series ring.
- r is `z.length`; the count is `z.length ≤ n` and `y.length = n - z.length`.
  Thus `Fin y.length` is precisely the remaining n-r variables. In particular natural
  subtraction never conceals an overlong parameter list.
- The quotient is `MvPowerSeries (Fin n) K ⧸ Ideal.span {a | a ∈ z}`, respectively Λ.
- The isomorphism is an existential algebra equivalence from the remaining power-series
  ring to this quotient. An algebra equivalence fixes coefficients, as the substitution
  maps in the source do. `IsLocalHom e.toRingHom` explicitly records locality.
- For every remaining index i, `e (X i) = Ideal.Quotient.mk _ (y.get i)` identifies the
  variable with the image of the chosen other parameter, not an arbitrary quotient
  isomorphism. The Cohen case additionally records
  `e (C (p : Λ)) = Ideal.Quotient.mk _ (C (p : Λ))`.

Dependencies used:

- def-weil-pbc-cohen-ring: `Sheaf.RingTheory.CohenRing`, `IsCohenRing`; full definition
  read: prime p, existential domain and DVR structures, maximal ideal span p, and
  adic completeness. The recorded declaration is usable without any dependency repair.
- def-weil-pbc-multivariate-power-series: `Mathlib.RingTheory.MvPowerSeries.Basic`,
  `MvPowerSeries`; full definition and operations read. Equiv supplies finite-variable
  Noetherianity, Inverse supplies the local-ring instance, and the C algebra structure
  and X variables are the standard ones.
- def-weil-regular-scheme: `Mathlib.RingTheory.RegularLocalRing.Defs`,
  `IsRegularLocalRing`, used through the existing parameter predicate's import. Only
  its regular-local-ring clause is relevant; no scheme notion is used.
- Existing additional project definition: `Sheaf.RingTheory.IsRegularSystemOfParameters`,
  `IsLocalRing.IsRegularSystemOfParameters` (def-weil-pbc-regular-system-of-parameters).
  Full signature and docstring read, together with that node's statement and lean record.
  Reusing this definition avoids a private parameter-system predicate. The item's node
  remains unchanged outside lean: no new notion or dependency module is needed.

Edge cases checked: n=0 allows empty lists in the field case and just p in the Cohen
case; r=0 gives the zero ideal; r=n gives a zero-variable power-series ring, which is
isomorphic to the original coefficient ring. No nonempty variable type or positive
n/r binder appears. Positive and zero characteristic fields are both allowed; Cohen
prime characteristic is specified by hΛ, and p itself is never among the killed
parameters of a regular system retaining it. Universes are explicitly bound; coefficients
range over arbitrary Type u. Lists allow all finite ordered parameter systems, and
neither a repetition nor a unit can satisfy the full minimal-generator predicate.

Searches for existing statements:

- msearch leanfinder: `quotient of formal power series ring by part of a regular system
  of parameters`: eight one-variable Weierstrass results; no exact match.
- msearch loogle: `MvPowerSeries, AlgEquiv`: rename, empty-variable, and iterated-variable
  equivalences; no parameter quotient.
- msearch grep in RingTheory: `regular system of parameters|quotient.*power.series|parameter.*quotient`:
  no hits.
- msearch leansearch: `quotient of multivariate power series ring by regular parameters`:
  service unavailable (Internal Server Error); no conclusion drawn.
- rg of the item id and parameter/quotient descriptions in WeilConjectures: no statement
  match. rg in lean/Sheaf found uses in formal-smoothness proof docstrings and the
  parameter-system definition, but no quotient declaration.
- rg of both proposed declaration names in Mathlib, WeilConjectures, and
  dag/lean_names_upstream.json: no collisions.

Server compile via scompile.py: exit code 0, 1.7 seconds, no warnings.
No statement dispute or node fault was found. The natural-language proof docstrings
cover all four supplied proof steps, divided between the two declarations.

## Second reading by E1

The node introduces a field `K`, a natural number `n`, a multivariate power-series
ring `K[[X_1, ..., X_n]]`, a finite partial parameter list `z`, and a chosen
completion `y` to a regular system of parameters.  The field conclusion is the
parameter count, `z.length ≤ n` and `y.length = n - z.length`, followed by a local
`K`-algebra equivalence from the power-series ring on `y.length` variables to the
quotient by the ideal generated by `z`, carrying every `X i` to the class of `y.get i`.
These items are rendered by
`MvPowerSeries.exists_algEquiv_quotient_parameters_field` exactly in that order;
`IsRegularSystemOfParameters (z ++ y)` is the stated completion hypothesis.

The Cohen case introduces a commutative Cohen ring `Λ` with prime `p`, the same
`n,z,y`, and the completion `C p :: (z ++ y)`, so that `p` is retained among the
parameters.  Its conclusion has the same count and quotient equivalence over `Λ`,
the variable-image equalities, and the additional equality fixing `C p`.  These are
rendered by `MvPowerSeries.exists_algEquiv_quotient_parameters_cohen`.  The explicit
`IsLocalRing` and `IsNoetherianRing` instance binders are the canonical structures
entailed by the Cohen-ring DVR hypothesis and are needed to elaborate the recorded
regular-parameter predicate; they do not restrict the mathematical Cohen-ring cases.

The source is Stacks, More on Algebra, Tag 07NM, clauses (2) and (4), with clauses
(1) and (3) supplying the full-parameter substitution argument.  The four proof
steps in the node are represented in the declaration docstrings: invertible linear
part and completeness, quotienting the first variables, and the corresponding Cohen
argument with `p` fixed.  The declarations use the existing `IsCohenRing`,
`MvPowerSeries`, and `IsLocalRing.IsRegularSystemOfParameters` notions; no private
copy or new dependency was introduced.  Searches (LeanSearch, LeanFinder/Loogle,
and repository/Mathlib grep) found no existing parameter-quotient theorem.

Edge cases were checked: `n = 0`, empty `z` or `y`, `r = 0`, `r = n`, zero-variable
power series, arbitrary field characteristic, and Cohen residue characteristic are
all admitted.  Universes are explicitly bound.  No mismatch was found and no source
or Lean file required repair.
