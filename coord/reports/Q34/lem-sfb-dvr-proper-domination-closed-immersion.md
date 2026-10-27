## Worker report

The module `Sheaf.AlgebraicGeometry.DvrProperDominationClosedImmersion` states the
proper-domination closed-immersion theorem from Stacks Project `limits.tex`, Tag 0208
(lemma-Noetherian-dvr-valuative), equation-solid and the final contradiction.  The
Lean declaration is
`AlgebraicGeometry.isClosedImmersion_of_proper_domination_of_dvr_lifts`.

The binders render the node as follows.  `X Y P S : Scheme.{u}` and
`f : X ⟶ S`, `π : Y ⟶ X`, `i : Y ⟶ P`, `q : P ⟶ S` are the four schemes and
morphisms.  `comm : i ≫ q = π ≫ f` is exactly `qi = fπ`.  `[IsProper π]` renders
properness of π, and `[IsSeparated q]` separatedness of q.  `[IsImmersion i]`
is the specified immersion.  `[CompactSpace Y]` is quasi-compactness of Y and
`[IsLocallyNoetherian P]` together with `[CompactSpace P]` is the stated locally
Noetherian and quasi-compact (Noetherian) hypothesis on P.  The `hDVR` binder
quantifies over a commutative domain DVR A, its fraction field K with the explicit
algebra and fraction-ring instances, and maps `a : Spec K ⟶ X` and
`b : Spec A ⟶ S`; its equation is `a ≫ f = Spec.map(algebraMap A K) ≫ b`, and its
conclusion supplies `h : Spec A ⟶ X` with `h ≫ f = b` and
`Spec.map(algebraMap A K) ≫ h = a`.  The conclusion is `IsClosedImmersion i`.
All variables and universes are explicit; no additional hypotheses such as
surjectivity or separatedness of f or uniqueness of DVR lifts are present.

The proof docstring records the five Stacks steps: finite type of the immersion,
a boundary DVR, application of the assumed lift, proper valuative existence, separated
comparison, and the closed-image characterization of a closed immersion.  The proof
itself is intentionally `sorry` at stage 2.

Statement dependencies and declarations used are: schemes and scheme morphisms,
`AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom` (Mathlib); proper,
`AlgebraicGeometry.IsProper` (Mathlib); closed immersion and immersion,
`AlgebraicGeometry.IsClosedImmersion` and `AlgebraicGeometry.IsImmersion` (Mathlib);
locally Noetherian schemes, `AlgebraicGeometry.IsLocallyNoetherian` (Mathlib);
DVRs, `IsDiscreteValuationRing` (Mathlib); and spectra, `AlgebraicGeometry.Spec`
and `AlgebraicGeometry.Spec.map` (Mathlib).  Proof imports use the recorded
`AlgebraicGeometry.exists_dvr_of_mem_closure_range_not_mem_range`,
`AlgebraicGeometry.UniversallyClosed.eq_valuativeCriterion`, and
`AlgebraicGeometry.IsSeparated.valuativeCriterion` interfaces, along with the
Mathlib finite-type, quasi-compact, quasi-separated, and valuative-criterion APIs.

Edge cases checked were empty Y (the compactness and immersion hypotheses remain
well-formed and the conclusion is vacuous in the expected way), an already closed
immersion, and the standard open immersion `G_m → A^1` (which fails the DVR existence
hypothesis).  The DVR type is not restricted to a chosen characteristic, and A, K,
and all scheme objects share the explicit universe `u` required by the boundary-DVR
interface.

Searches for an existing declaration were made with `msearch.py`: LeanFinder query
“An immersion into a Noetherian separated ambient scheme is a closed immersion if its
source is proper over a scheme satisfying existence of lifts from discrete valuation
rings” (hits only generic Mathlib immersion/closed-immersion APIs; no match), LeanSearch
query “An immersion into a Noetherian scheme is closed if proper domination and the
existence part of the valuative criterion for discrete valuation rings hold” (hits
only generic `IsClosedImmersion` declarations; no match), and Loogle query
`AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.IsImmersion` (generic hits,
no theorem with this statement).  The required grep over `AlgebraicGeometry` found no
proper-domination or DVR closed-immersion theorem.  The existing DAG node was also
searched by id; it has no Lean declaration.  Therefore this delivery adds one module
and records it as a new statement.

No `STATEMENT-DISPUTED` issue or node fault was found.

## Second reading by Q34

I independently opened the node JSON, Stacks Tag 0208, and the complete Lean file.
The four scheme objects and four morphisms occur with the same directions as the node;
`comm` has the correct categorical composition order.  Properness, separatedness,
immersion, quasi-compactness of Y, and both parts of Noetherianity of P are all
present.  The DVR hypothesis quantifies over every explicit A/K and every compatible
pair of maps and states existence only, with no uniqueness or extra properties.  Its
fraction-field map is `Spec.map (CommRingCat.ofHom (algebraMap A K))`, exactly the map
used by the boundary-DVR interface.  The conclusion is precisely
`IsClosedImmersion i`.  The declaration compiles cleanly with `scompile.py`; no
mismatch was found and no change was required.
