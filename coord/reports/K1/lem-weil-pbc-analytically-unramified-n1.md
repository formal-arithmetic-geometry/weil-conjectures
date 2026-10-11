## Worker report

The module `Sheaf.RingTheory.IsN1OfIsAnalyticallyUnramified` states
`isN1_of_isAnalyticallyUnramified`, with `sorry` as its entire proof. It adds no definitions.
The declaration docstring gives the node's six proof steps and the dependencies used in each.

Hypotheses and clauses, matched individually:

- The commutative ring `A` is `(R : Type u) [CommRing R]`.
- Integral domain is `[IsDomain R]`; in particular, the zero ring is excluded by the node itself.
- Local ring `(A, m)` is `[IsLocalRing R]`. Its unique maximal ideal is
  `IsLocalRing.maximalIdeal R`, used by the recorded analytic unramifiedness definition;
  there is no additional choice of maximal ideal.
- Noetherian is `[IsNoetherianRing R]`.
- Reduced maximal-ideal-adic completion, equivalently analytic unramifiedness, is
  `(h : IsAnalyticallyUnramified R)`. Unfolding the dependency definition gives exactly
  `IsReduced (AdicCompletion (IsLocalRing.maximalIdeal R) R)`.
- Its fraction field is `(K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]`.
  This introduces the fraction field mentioned in the conclusion, without restricting which
  fraction field represents it or requiring it to have the same universe as `R`.
- The integral closure being a finite `R`-module, and hence `R` being N-1, is the conclusion
  `IsN1 R K`. The recorded definition unfolds to `Module.Finite R (integralClosure R K)`.
  Thus the finite-module clause and the “i.e. N-1” clause are the same proposition, not
  independent conclusions requiring a redundant conjunction.

Dependency declarations read and used:

- `Sheaf.RingTheory.AnalyticallyUnramified`: `IsAnalyticallyUnramified`, including its
  docstring and full reduced-completion definition.
- `Sheaf.RingTheory.JapaneseDomain`: `IsN1`, including its docstring and full definition.
  The recorded main declaration `IsN2` and the module's other declarations were also read;
  N-2 is not a hypothesis of this theorem.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, the Noetherian self-module
  condition, with its docstring and ideal-finiteness equivalence.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`, the subalgebra with
  carrier `IsIntegral R`; the recorded `IsIntegral` and `IsIntegrallyClosedIn` signatures
  and docstrings were read in their defining files.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, defined by finite generation of the
  top submodule, with its docstring. These Mathlib declarations are supplied transitively
  by the two imports; neither dependency receives a private replacement.

Edge cases checked: fields (maximal ideal zero, completion reduced, integral closure itself)
are included; nonnormal domains are included (no integrally closed hypothesis); every
characteristic is included; the zero ring is correctly excluded by integral-domain/local-ring
assumptions. No dimension, perfection, separability or completeness assumption is added.
Universes `u v` are independently and explicitly bound. All variables are explicitly bound.

Source check: the local Stacks checkout is absent on this machine. Read the full statement
and proof online at https://stacks.math.columbia.edu/tag/032Y instead. Clause (5) is exactly
this statement, and proof (4) specializes to fraction fields in the domain case. No statement
correction, disputed statement, missing notion or unusable dependency was found.

Searches made with `msearch.py K1 lem-weil-pbc-analytically-unramified-n1`:

- `leanfinder`: “A Noetherian local integral domain whose maximal ideal adic completion is
  reduced has finite integral closure in its fraction field”. Eight hits, including
  `completeIntegralClosure_eq_integralClosure`, Dedekind-domain characterizations and
  Noetherian integral-closure theorems, but none has this reduced-completion hypothesis.
- `loogle`: `IsN1, IsAnalyticallyUnramified`. Zero hits; unknown identifier `IsN1`.
- `leansearch`: “Noetherian local analytically unramified domain is N-1”. Service unavailable
  (Internal Server Error), recorded as unavailable; no mathematical verdict from that tool.
- `grep` over Mathlib `RingTheory`: `AnalyticallyUnramified|analytically unramified|isN1_of|IsN1`.
  Zero hits.
- `rg` over upstream `WeilConjectures`, project `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the same names and the item's id. Only the project dependency definitions and
  `isN1_of_isN2` appear; no theorem with the analytic hypothesis. The proposed full name is
  absent from the source and existing project modules.

Validation: the single module is compiled on the server using `scompile.py`; the required
`deliver2.py --no-push` dry run checks the record and delivery. The second reader supplies
its independent reading and performs delivery; this worker does not push.

## Second reading by K1

I independently compared the node statement with the Lean declaration and the source at
Stacks Project, Algebra, Lemma 10.162.10 (tag 032Y), clause (5), whose statement says that a
Noetherian local analytically unramified domain is N-1. The objects and clauses match as follows:

- The node's Noetherian local integral domain `(A, m)` is rendered by `(R : Type u)` with
  `[CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]`; `IsLocalRing` supplies the
  unique maximal ideal used by `IsAnalyticallyUnramified`.
- The hypothesis that the maximal-ideal-adic completion is reduced is exactly
  `(h : IsAnalyticallyUnramified R)`, whose dependency unfolds to reducedness of
  `AdicCompletion (IsLocalRing.maximalIdeal R) R`.
- The fraction field is represented by `(K : Type v)` with `[Field K] [Algebra R K]
  [IsFractionRing R K]`, allowing arbitrary universes as in the mathematical statement.
- The conclusion that the integral closure is a finite `R`-module is exactly
  `IsN1 R K`; the dependency definition unfolds to
  `Module.Finite R (integralClosure R K)`, matching the node's final “i.e. N-1” clause.

No hypothesis is added or strengthened, and no conclusion is weakened. The zero ring is excluded
by `IsDomain`; fields and all characteristics remain included. Empty-index issues do not arise in
this single-ring statement, and `u` and `v` are independently explicit. The declaration has no
unbound variables or universes.

I searched Mathlib, the source `WeilConjectures` tree, and project `lean/Sheaf` by the analytic
unramified and N-1 notions, and repeated LeanFinder, Loogle, and LeanSearch searches recorded in
`searches.jsonl`; no existing declaration states this theorem. The Lean module compiled cleanly
with `scompile.py`. I found no mismatch and made no code or node-statement changes.
