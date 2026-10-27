## Worker report

Module: `Sheaf.AlgebraicGeometry.CoefficientOrderHilbertEquality`.
Main declaration: `AlgebraicGeometry.HilbertCoefficient.coefficient_order_hilbert_equality`.
Its only theorem proof is `sorry`, with the six accepted proof steps in its docstring.
`coefficientDerivativeIdeal` constructs the regular coefficient derivative ideal introduced
by this node, as an actual ideal span. It is a helper of this notion, not an independent
existence assumption. Every generator index has bounded total degree, so there are finitely
many generators although its comprehensible span is written with an existential set.
The H2 repair adds a definition node bound to the existing Taylor constructions.
It delivers no replacement dependency module and no duplicate definitions.

The item statement is unchanged. Its added statement dependencies are now
`def-trf-regular-hilbert-coefficient-datum`, `def-trf-formal-initial-diagram`, and
`def-trf-taylor-rank-minor-ideals`. The two comparison theorems are proof dependencies only.
The stronger `RegularHilbertCoefficientDatum` is not a hypothesis: it requires conditions
on the entire order locus and a Hilbert bound which this item does not assume.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Characteristic-zero field k | `{k : Type u} [Field k] [CharZero k]` |
| Smooth affine finite-type U/k | `U`, `[IsAffine U]`, `p`, `[Smooth p]`, `[LocallyOfFiniteType p]`, `[QuasiCompact p]` |
| Closed X in U with coherent ideal | `i`, `[IsClosedImmersion i]`, `hcoherent : RingedSpace.IsCoherent U.toRingedSpace i.ker.toModules` |
| a in X | `a : X`; the ambient distinguished point is `i a` |
| Smooth closed N through a | `N`, `j`, `[IsClosedImmersion j]`, `[Smooth (j ≫ p)]`, `b₀`, `hb₀` |
| Ambient regular coordinates and etale w on N | `coord`, `hetale`, `hover`, `w`, `hw`, `hetaleW`; the coordinate maps are explicitly `U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom coord)` and its N analogue; the structure map uses `coord.comp MvPolynomial.C` |
| Coordinate partial derivatives | `der`, `hderk`, `hderx`, and `derW`, `hderWk`, `hderWw` specify the coordinate derivations uniquely, rather than arbitrary maps |
| Regular defining equations with invertible transverse Jacobian | `equations`, `hequations`, `hjacobian`, with evaluation at every `b : N` |
| Ordinary centered Taylor variables on all of U | `TU`, `hTU : isTaylorMap ...`; all `Fin m ⊕ Fin n` variables remain at nonclosed points |
| Taylor expansion on N | `TN`, `hTN`; its coefficients lie in the actual `N.residueField b` |
| Straightened centered (W,Z) | `straight`, `hres`, `hk`, `hW`, `hZ`; the last formula is z restricted to N, expanded in W, plus the new Z variable |
| K_b, Taylor ideal of X | `taylorIdeal (RingHom.ker i.appTop.hom) (straight b)`; for ordinary ambient points use `TU y` |
| Regular coefficients on one common N | `coeff : Fin s → (Fin n →₀ ℕ) → Γ(N, ⊤)` |
| f_i,b has exactly the displayed expansion | `f` and `hexpansion`, split into W and Z exponents by `Finsupp.comapDomain.addMonoidHom` |
| f_i,b belongs to K_b | `hmember`, at every b, with no equality/generation assumption away from the center |
| Monotone orthant diagram D with ordered minimal vertices (0,alpha_i) | `D`, `hmonotone`, `hvertices`; `fullVertex` inserts zero W coordinates and `finSumFinEquiv` merely numbers W followed by Z |
| Transverse variables exactly the essential variables | `hessential`; conversely all vertices already have zero W exponents by `fullVertex` |
| d_i and orders at a | `d_i` is the degree `(α l).degree`; `horder` specifies precisely this order |
| Unique supported homogeneous division for every degree prefix | `hdivision : homogeneousDivision α (f b₀)` uses the landed prefix definition |
| Supported generation of K_a | `hgeneration`, including every quotient support `inDelta` |
| Initial diagram of K_a is D | `hinitial`; renaming W,Z to `Fin (m+n)` allows reuse of the existing `initialDiagram` |
| Q at least max d_i-1 | `Q`, `hQ`; Nat subtraction covers the empty/degree-zero bounds without an invented maximum of the empty list |
| Each degree block and its accumulated essential variables | `hblocks` and `hlater` quantify degrees occurring among the vertices; `essential α d` is exactly the accumulated variable set |
| Chosen vertex derivatives for every b | `hblocks` quantifies b before its existential `pick`, `β`; choices may depend on the point and block |
| alpha_i=beta+e_j and prefix membership | The first two conjuncts in `hblocks`; the choice is among vertices of that prefix |
| g_j in (Z^ell), invertible Jacobian | Third conjunct in `hblocks`, followed by `IsUnit (Matrix.det ...)` with constant coefficients after formal differentiation |
| Later derivatives in the prefix variable ideal | `hlater`: strictly larger vertex degree, restricted-variable support, prefix diagram membership and `δ.degree ≤ Q`, concluding membership in `transverseIdeal α d` |
| S by the stated local coefficient orders | The existential-b predicate in the first conclusion: each coefficient germ belongs to `maximalIdeal ^ (d_i - γ.degree)` when `γ.degree < d_i` |
| a in S | `hcenter`, on `b₀` |
| Neighbourhood V in U containing a | `∃ V : U.Opens, i a ∈ V ∧ ...` |
| S intersect V equals extended Hilbert equality locus | The first conclusion, pointwise for all y in V, identifies existence of b in S mapping to y with equality to `hilbertCount D` in every degree |
| H_D(t) counts exponents outside D through degree t | `MonomialDiagram.hilbertCount D t`, coerced to `ℕ∞` to compare with the existing finite-length Taylor quotient |
| H_X/k uses the ordinary ambient Taylor quotient outside N | `extendedHilbert (taylorIdeal ... (TU y)) t`, whose definition is precisely the quotient by K plus the (t+1)-st power of all variables |
| Sufficiently large finite q >= max d_i-1 | `∃ q₀`, its bound for each vertex, then `∀ q, q₀ ≤ q → ...` |
| Any regular generating list of the ideal of X | `∀ r generators`, with `Ideal.span (Set.range generators) = RingHom.ker i.appTop.hom`; the cutoff is independent of that choice |
| Cumulative Taylor-rank minors through q | `⨆ t ∈ Finset.range (q+1), regularJetMinorIdeal coord der generators (U.Γevaluation (i a)).hom t` |
| Coefficient derivative ideal on N | `coefficientDerivativeIdeal α coeff derW` has exactly indices `γ.degree < d_i` and `δ.degree < d_i - γ.degree` |
| Adjoin the equations of N to inverse images | `Ideal.comap j.appTop.hom` of the coefficient ideal: since j is closed in affine U, this is exactly its inverse-image ideal, including the full kernel of j |
| Equality of coherent ideals on a common neighbourhood | Equality of `Scheme.IdealSheafData.ofIdealTop ...` after `.comap V.ι`, not equality of radicals or only their supports |
| Taylor extension at a is E | `Ideal.map (straight b₀)` of the cumulative minors equals `lowDerivativeIdeal α (f b₀)` |
| E=(Z, partial_W^δ T_a(c_iγ)) | Final equality: supremum of the span of all transverse variables and the span of exactly those formal coefficient derivatives, with `MvPowerSeries.rename Sum.inl` embedding W-series |
| Empty lists allowed | `m n s : ℕ` have no positivity assumption; no closedness, reducedness or rationality assumption on any point is imposed |

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly exposes the exact
  `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `WeilConjectures.AlgebraicGeometry.Coherent`; its finite-type conjunction alone is not used
  as a substitute for coherence.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and `Scheme.Γevaluation`.
- `Mathlib.RingTheory.MvPowerSeries.Basic` and `.Derivative`: `MvPowerSeries`,
  `MvPowerSeries.pderiv`; the derivative node is a Mathlib leaf, not an unstated dependency.
- `Sheaf.RingTheory.SupportedHomogeneousDivision`:
  `MonomialDiagram.IsMonotone`, `MonomialDiagram.IsOrderedVertexFamily`.
- `Sheaf.LinearAlgebra.Matrix.MinorIdeal`: `Matrix.minorIdeal`, via the existing
  `finiteMinorIdeal`/`regularJetMinorIdeal` definitions, including oversized minors.
- `Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum`: `fullVertex`, `inDiagram`,
  `inDelta`, `essential`, `supported`, `transverseIdeal`, `iteratedPartial`,
  `homogeneousDivision`, `isTaylorMap`, `taylorIdeal`, `extendedHilbert`.
- `Sheaf.RingTheory.FormalInitialDiagram`: `MonomialDiagram.initialDiagram`,
  `MonomialDiagram.hilbertCount`.
- `Sheaf.AlgebraicGeometry.FormalHilbertStratumMinors`: `regularIteratedPartial`,
  `regularJetMinorIdeal`, `lowDerivativeIdeal`; the entire signatures and docstrings of
  the formal equality, generator independence, Taylor compatibility and equality-germ
  theorems were read. The item reuses the existing constructions directly, recorded
  separately by the definition node with `existing: true`.
- `Sheaf.AlgebraicGeometry.ImplicitTaylorCoordinateCalculus`:
  proof dependency only. Its coordinate and structure morphism bodies are written directly
  in `hetale`, `hover` and `hetaleW`, so its theorem is not a statement dependency.
- Proof imports: `Sheaf.AlgebraicGeometry.JetDiagramHilbertControl` and
  `Sheaf.RingTheory.PresentationFittingIdeal`; read their recorded signatures. The
  implicit calculus is an ordinary proof import. FormalHilbertStratumMinors is publicly
  imported for its existing constructions, recorded on the new definition node, and
  supplies a proof theorem already listed in proof_deps.
  `lem-trf-etale-coordinate-derivations-jacobian` and `lem-trf-taylor-normal-cone-splitting`
  have no recorded Lean declaration in the read clone; their statements were read and
  the proof docstring names them, but there is no module to import for them.

Edge cases checked before the final statement:

- Empty vertices: essentiality forces n=0. The equations list is empty and its kernel
  is zero, so closed N in affine U is U. Supported generation forces the central Taylor
  ideal to vanish. The coefficient and formal derivative spans are empty and zero;
  the rank minors of a zero ideal are oversized and vanish locally. No nonempty index
  instance or maximum of an empty list is used.
- m=n=0: power series are the coefficient field, Taylor matrices still include the
  constant monomial, and empty Jacobians have determinant 1.
- Zero coefficients have germs in every maximal-ideal power, so their orders are infinite
  as required. Strict degree bounds give no derivative of weight zero.
- A degree-zero vertex would contradict membership of f in the proper Taylor ideal at
  the given point of X; it is not silently removed by a positivity assumption.
- Nonclosed points use every relative Taylor variable and actual residue fields. At the
  generic point of a smooth affine curve, a nonzero regular function is a unit in the
  local field, and its nonzero Taylor constant detects failure of any positive order
  bound. No closed-point or residue-field-equals-k hypothesis appears.
- For z^d, the low derivative ideal is (z) and there are no nonzero coefficient tests;
  the equality locus is N. For z^2+w^3, E=(z,w^2), and the coefficient derivative ideal
  is (w^2) near zero, checking the strict derivative cutoffs and scheme multiplicities.
- Rank-zero matrices use 1-minors; zero fibre quotient dimensions use oversized minors.

Searches actually run with `msearch.py Q52 lem-trf-coefficient-order-hilbert-equality`:

1. `leanfinder`: "Coefficient order locus equals the extended Hilbert equality germ via
   Taylor rank minors and coefficient derivative ideals". Eight univariate Weierstrass
   preparation/division results; none states this multivariate scheme germ or ideal equality.
2. `loogle`: `MvPowerSeries, Matrix.det`. Zero results.
3. `grep`, subdirectory `RingTheory`: `HilbertSamuel|coefficientIdeal|Hilbert.*[Ss]trat`.
   Zero results.
4. `leansearch`: "Coefficient order locus equals extended Hilbert Samuel equality germ and
   Taylor minor ideal equals coefficient derivative ideal". Eight results, including
   polynomial Taylor coefficients, orders of series and unrelated analytic Taylor series;
   none is an exact match.
5. `rg` in `lean/Sheaf` and `lean/WeilConjectures` for
   `coefficient.order|CoefficientOrder|hilbertEquality|HilbertEquality` found the regular
   datum, formal transform criterion and common-power marking. Opened those interfaces:
   `coefficient_equality_germ` requires the stronger regular datum and lacks the coherent
   ideal assertion. Thus it is not this node's statement. The minor constructions and
   implicit calculus are reused, rather than copied.
6. `rg` in those two source trees and `dag/lean_names_upstream.json` for
   `coefficient_order_hilbert_equality|coefficientDerivativeIdeal|CoefficientOrderHilbertEquality`
   found no existing declaration. The exact item-id search in `lean/WeilConjectures`
   also found no declaration.

Source checked: the latest blueprint ancestor `lem-trf-local-term-locality.md` is about
local terms and is not this node's statement; the accepted historical lower-branch source
is BM 1997. Read BM Theorem 7.14 references, Remarks 9.1 and 9.5 on printed pp.275--277,
and the completion of Theorem 9.6 on printed p.282 online:
https://mahalex.net/seminars/gabber/Bierstone-Milman%20Canonical%20desingularization%20in%20characteristic%20zero.pdf
In particular Remark 9.5 uses strict derivative weights, not the apparent <= typo in the
closing paragraph on p.282. The delivered statement follows the accepted node's strict
weights. No statement correction and no STATEMENT-DISPUTED flag is needed.

Validation: final module compiled cleanly via the prescribed `scompile.py` in both sandbox
and library-name mode; no errors or unexpected warnings. `autoImplicit` is false, every
universe and parameter is explicit, and all lines have at most 100 characters.

## Second reading by Q52

A separate pass through the written node and the completed signature checked the table
above. No independent agent was started, as the dispatcher brief explicitly prohibits it;
the maintainer's independent delivery review remains separate.

This pass removed a first-exponent hypothesis from the initial draft: the node explicitly
assumes orders, homogeneous division, supported generation and the initial ideal diagram;
it does not separately require each supplied f to be the standard basis element with that
first exponent. The final signature has no such added hypothesis. Checked that `hmember`
is at every point, while orders/division/generation are only at b₀, and that block choices
are made after quantifying b and the block. Checked that the regular ideal equality uses
the same V as the set equality, keeps the nonradical ideal, and takes every sufficiently
large q and every regular generating list. Checked that the formal equality includes
both W and Z derivatives below the orders, and that all coefficient derivatives have the
strict bound |δ|<d_i-|γ|. Empty lists and nonclosed points remain included. The only helper defined in the item module
is the actual regular coefficient derivative span belonging to this node. No data is
postponed by sorry; only the main named theorem is postponed.

## Returned deliveries repaired

The first return, H2 at e1dc7ac6725e, required definition ownership for plain helpers,
rather than theorem-node statement dependencies. The second return at 607b225f1955
reported eleven duplicate declarations in the extracted TaylorRankMinorIdeals module
and required import and reuse of the existing declarations. This packet repairs both:

- Retains `def-trf-taylor-rank-minor-ideals`, but binds it to the eleven exact existing
  definitions in `Sheaf.AlgebraicGeometry.FormalHilbertStratumMinors` with `existing: true`.
  This is definition ownership in the DAG without moving or redeclaring Lean definitions.
- Removes the delivered TaylorRankMinorIdeals module and the replacement
  FormalHilbertStratumMinors module and node record. Neither is part of this packet.
  The live theorem module is reused directly and retains its original declarations.
- The item publicly imports FormalHilbertStratumMinors and uses its existing names.
  Its statement dependencies cite the new definition node, not the theorem node.
  Both comparison theorem nodes remain in the original proof_deps only.
- The coordinate morphisms stay expanded as `toSpecΓ` followed by `Spec.map`, including
  `coord.comp MvPolynomial.C` for the structure map, as authorized by the first return.
  No dependency on the implicit-calculus theorem is needed to state these maps.
- Rebased the item metadata on the current main node. Read the current server source
  with `scompile.py --source Sheaf.AlgebraicGeometry.FormalHilbertStratumMinors`:
  all eleven original constructions are still declared there. No rename, alias,
  alternative construction, theorem hypothesis or theorem conclusion is introduced.

The second return's complete collision list is resolved by existing bindings:
`finiteMinorIdeal`, `formalJetMatrix`, `formalJetMinorIdeal`, `formalJetRank`,
`formalStratumIdeal`, `jetExponents`, `lowDerivativeIdeal`, `multiFactorial`,
`regularIteratedPartial`, `regularJetMatrix`, `regularJetMinorIdeal`.
Each is declared only by the original FormalHilbertStratumMinors module.

## New nodes

`def-trf-taylor-rank-minor-ideals` records the eleven existing definitions in
`Sheaf.AlgebraicGeometry.FormalHilbertStratumMinors`, with main declaration
`AlgebraicGeometry.HilbertCoefficient.regularJetMinorIdeal`. It delivers no Lean module.
Its source is BM 1997 Definitions 7.9, 7.12--7.13 and Remarks 9.1, 9.5, already read for
the accepted construction. No existing definition node owned these notions; the existing
record was the comparison theorem node. The new node records the constructions alone.

Hypotheses and clauses of the new node correspond to its existing declarations:

| Definition-node clause | Existing Lean declaration or binder |
| --- | --- |
| finite variable type, independent universe | `{σ : Type v} [Fintype σ]` |
| E_t of degree at most t | `jetExponents σ t` |
| factorial in coefficient ring | `multiFactorial R δ` |
| finite matrix reindexing and minors | `finiteMinorIdeal B r` via `Matrix.minorIdeal` |
| formal Taylor matrix, zero for η not ≤ δ | `formalJetMatrix f t`, its conditional entry |
| constant-coefficient rank | `formalJetRank f t` |
| next-sized minor ideal | `formalJetMinorIdeal f t` |
| cumulative sum through q | `formalStratumIdeal f q` |
| low formal derivatives with strict degree bound | `lowDerivativeIdeal α f` |
| regular derivative iteration in fixed finite order | `regularIteratedPartial D δ h` |
| regular Taylor matrix and scalar inverse factorials | `regularJetMatrix c D h t` |
| residue map to any field, frozen fibre rank | `regularJetMinorIdeal c D h ev t` |

All are actual finite matrices, folds and ideal spans, with no existence assumptions or
sorry data. No characteristic hypothesis is added to these definitions. Their binders,
signatures, bodies and docstrings were read in the current published server source.
The node's main signature is exactly the existing declaration's signature.

The project search `rg -l 'regularJetMinorIdeal|lowDerivativeIdeal|formalJetMatrix'`
over `dag/nodes`, `lean/WeilConjectures` and `lean/Sheaf` finds the existing
FormalHilbertStratumMinors construction and its theorem node. The new definition node
uses `existing: true` precisely to reuse those definitions. The earlier extraction
attempt is superseded. `blueprint_refs.py search 'Taylor rank minors'` and
`blueprint_refs.py search 'low derivative ideal'` found zero blueprint matches;
`ancestor` gives `lem-trf-local-term-locality`. The historical source route is retained.
Three actual logged searches are retained verbatim in mathlib_searches: LeanSearch for
finite regular/formal Taylor matrices and frozen fibre rank ideals gave 8 analytic
Taylor/Sylvester results; LeanFinder for truncated Taylor matrices and rank minor ideals
gave 8 presentation Jacobian results; Mathlib RingTheory grep for the construction
names and Taylor matrices gave zero results. None gives an exact Mathlib match.

Edge cases: t=0 includes the constant monomial; empty sigma still has one row; an empty
generator family has no columns and rank zero; oversized next-rank minors vanish;
full rank is covered by oversized minors. The variable universe is independent of the
coefficient universe. For specified noncommuting regular derivations, the finite
iteration order is explicitly part of the definition. These checks require no change
to the existing definitions.

## Repair second reading by Q52

Compared the saved signature from 607b225f1955 with the revised item module: the theorem
signature and body are byte-identical; only its imports change. Thus all at-a versus
every-b quantifiers, block/later conditions, strict weights, the common V, actual
ideal-sheaf equality and the formal E identity are retained. The current server source
contains each of the eleven constructions once. The new node references those exact
names in that existing module; no delivered module redeclares them. The comparison
theorem node is absent from stmt_deps and remains in proof_deps. Every existing binding
will be #checked by deliver2.py, in addition to the item's required scompile.py check.
The original hypothesis table and edge-case checks apply unchanged.

Validation of the duplicate repair: the prescribed scompile.py completed successfully
for the remaining item module in sandbox and library-name modes, with no error or
unexpected warning. Textual checks confirm the main theorem signature is unchanged,
the node signature matches it verbatim, all eleven existing definitions are present in
the original module, and no delivered file redeclares any collision name. The new
existing record's signature also matches the original declaration verbatim.
