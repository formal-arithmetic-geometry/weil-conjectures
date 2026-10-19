## Worker report

The module `Sheaf.Paper.FlagLocalComparison` states
`WeilConjectures.PurityFiniteSetting.flag_local_comparison`. All theorem bodies are
`sorry`; definitions and instances have real constructions. Its helpers give the
coordinate tower and its two classes, with their unique geometric/recursion
normalizations. No independent mathematical notion or new DAG node is introduced.

Hypothesis and clause correspondence:

- Finite setting: `P : PurityFiniteSetting.{u}` retains its fixed finite field,
  coefficient extension and arbitrary positive coefficient level. No divisibility
  condition on that level, no trivialization of the Tate line, and no new
  exceptional-adjoint datum is assumed.
- Separated finite-type k-scheme S: `aS : S ⟶ Spec (.of P.field.k)` with
  `[IsSeparated aS] [LocallyOfFiniteType aS] [QuasiCompact aS]`.
- Every r >= 0: `∀ r : ℕ` in the first conclusion. `flagCoordinateSpace S r` is
  exactly Mathlib `AffineSpace (ULift.{u} (Fin r)) S`. The lift retains universe u.
- Coordinates: `flagCoordinates S r j = AffineSpace.coord S (ULift.up j)`.
  `flagCoordinateInclusion S j` copies the first j coordinates and appends zero.
  Thus the tower is E_j = A^j_S, canonically the coordinate subspaces in E_r,
  and `flagCoordinateZero` is z_j. `flagCoordinateGeometry` records closedness,
  Cartier regularity and z_j followed by a_j = z_(j+1).
- Theta: `flagCoordinateThetaEtale` is selected from a UNIQUE recursively normalized
  family. `FlagCoordinateThetaNormalization` starts with the published
  `localizedFlagInitialModel` and uses exactly the published
  `localizedFlagCompose`, including its specified Cartier arrow, direct image,
  inverse projection, twist multiplication and shifts. It is not an arbitrary map.
  `flagCoordinateTheta` applies `functorialCupCompare` to this same family.
- The corrected equality `Theta = ((-1 : ℤ)^r) • Cup` is the first conjunct, in the
  exact supported-Hom model of `supported_cohomology_hom`. The source is z_* A_S
  in degree zero and the target A_E(r)[2r].
- Ordered cup product in full E_r: `flagCoordinateCup` uses the existing
  `frameBoundaryProduct` on `flagCoordinateSpace S r`, with the whole tuple
  `flagCoordinates S r`. Its factors are therefore `frameBoundary` for each
  individual divisor V(x_j) in E_r. It uses `frameCupNext`, hence `supportedCup`,
  in the published left-associated order. The only source transport is
  `frameClosedCoefficientIso` for `flagCoordinateSupportIso`: the unique
  quotient-normalized isomorphism V(x_1,...,x_r) ≅ S over E_r. Neither side is
  defined by the comparison equality being asserted.
- Frame interpretation: the unsigned cup class is literally the definition's
  `frameBoundaryProduct`; `flagCoordinateSmoothPair` states smooth relative rank r,
  smoothness of S over itself, and the full pointwise Krull-codimension formula.
  This uses the unrestricted body of `frameClass`, rather than its interface's
  accidental binding of smooth rank to `P.level`. Neither rank nor coefficient
  level is restricted, and the definition `frameClass` itself is not duplicated.
  The coordinate support isomorphism supplies the generating condition for the
  identity etale chart. No assertion about arbitrary zero schemes is present.
- Every base morphism: the second conjunct quantifies over arbitrary finite-type
  separated T/k and f:T→S with `f ≫ aS = aT`. The ambient map is the actual
  `AffineSpace.map (ULift (Fin r)) f`. `flagCoordinateBaseChange` is the canonical
  chosen Cartesian square of zero sections. Both equalities use the published
  `functorialCupPullback true`, with its fixed source, twist, shift comparisons.
  Thus both classes, and consequently their equality, commute with restriction.
- Rank zero: the final two HEq clauses identify both classes with
  `localizedFlagInitialModel` for the pro-etale constant restriction, whose
  invertibility is `flagCoordinateEmptyProRestriction`. This map is inverse
  restriction followed by the zero-shift comparison, i.e. identity after A^0_S=S
  and z_0=id. HEq only transports endpoint presentations; it does not assert
  equality after a possibly nonfaithful restriction.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, its `Coefficient`,
  constant sheaves and finite field/coefficient data.
- `Sheaf.Paper.LocalizedFlagProduct`: `LocalizedFlagH`,
  `localizedFlagCompose`, its explicit `LocalizedFlagComposeNormalization`,
  `localizedFlagInitialModel`, `localizedFlagRestriction`. The full nested
  construction (not merely its support-forgetting conclusion) is reused.
- `Sheaf.Paper.SupportedCohomologyHom`: `supported_cohomology_hom`, which fixes
  the underived closed direct-image source and cochain shift convention.
- `Sheaf.Paper.SupportedCup`: `cupSingle`, `cupCoefficientRestriction`,
  `supportedCup` through the published frame product.
- `Sheaf.Paper.PurityFrameClass`: `frameBoundaryProduct`, `frameCupNext`,
  `frameClosedCoefficientIso`; read `frameClass` and its full signature too.
- Mathlib `AlgebraicGeometry.AffineSpace`: `AffineSpace`, `coord`, `homOfVector`,
  `map`, `isPullback_map` and its rank-zero projection isomorphism.
- `Sheaf.Paper.SupportedCupFunctoriality`: `FunctorialCupH`,
  `functorialCupCompare`, `functorialCupPullback` and their canonical normalizations.

All recorded proof modules are imported, directly or through the exact owners
already imported by LocalizedFlagProduct. The finite-coefficient pro-etale
TensorResolution module is deliberately not imported separately: its declarations
collide with the legacy upstream tensor owner already used by SupportedCup.
The supported cup's published tensor and interchange construction is retained.

Edge cases: r=0 uses the actual affine-zero-space isomorphism and supported unit;
r=1 uses the same Cartier composition and single boundary without changing
normalizations. Empty S is allowed throughout, and there is no Nonempty binder.
Polynomial variables remain nonzerodivisors over nonreduced bases. Every positive
coefficient level is permitted, independently of r and including ramified levels.
The corrected integer scalar is `((-1 : ℤ) ^ r)`, acting on the additive Hom group;
this needs neither a choice of Tate generator nor an additional coefficient hypothesis.
Identity and arbitrary, nonflat base morphisms are included. No affineness or
regularity of S is imposed. The coordinate quotient normalization removes any
possible ambiguity of the supported source.

Searches performed:

- msearch leanfinder: “Nested coordinate Cartier Gysin composition equals ordered
  supported cup product of Kummer boundaries”; eight unrelated Proj and
  Kaehler/Jacobi-Zariski hits, no match.
- msearch loogle: `"Gysin", "Kummer"`; zero hits.
- msearch grep: `flag_local_comparison|coordinate.*[Cc]up|[Gg]ysin`; three unrelated
  canonical-topology hits, no match.
- msearch leansearch: “composition of coordinate Gysin maps equals supported
  Kummer cup product”; eight unrelated support-function/group-cohomology hits.
- rg in lean/WeilConjectures and lean/Sheaf: `flag.local.comparison`,
  `flagLocalComparison`, `coordinate.*Gysin`, `coordinate.*Kummer`; found the
  existing rank-one Kummer constructions and the citation in LocalizedTopChern,
  but no statement of this nested-versus-cup equality. Search for the item id
  in upstream WeilConjectures returned no result.
- Read the blueprint localized-top-Chern proof Step 3 and the entire DAG proof;
  the latter supplies the corrected coordinate-zero-section argument and all
  projection normalization steps, included in the theorem docstring.

## Statement corrected

The old statement, verbatim:

> In the finite setting [def-pur-conventions], let $S$ be a separated finite-type $k$-scheme and $r\geq0$. In $E_r=\mathbf A^r_S$ with coordinates $x_1,\ldots,x_r$, put $E_j=\{x_{j+1}=\cdots=x_r=0\}$, so $E_0=S$ and $a_j:E_{j-1}\hookrightarrow E_j$ has equation $x_j=0$. Form $\Theta_r:(z_r)_*A_S\to A_{E_r}(r)[2r]$ by composing the Cartier supported morphisms along this chain exactly as in [lem-pur-flag-localized-product]. In the supported-Hom identification [lem-pur-supported-hom],
> $$\Theta_r=\partial\kappa(x_1)\cup\cdots\cup\partial\kappa(x_r)\in H^{2r}_{E_0}(E_r,A(r)).$$
> Here the $j$th factor on the right is the Kummer boundary for the divisor $\{x_j=0\}$ in the full ambient $E_r$, and the cup product is [def-pur-supported-cup]. Equivalently, when the frame construction [def-pur-frame-class] is read with its rank parameter instantiated by $r$ (independently of the coefficient index), this is the ordered coordinate frame class for the smooth pair $E_r\to S$, $E_0\to S$. For every morphism $S'\to S$ of separated finite-type $k$-schemes, the equality commutes with restriction to $S'$. For $r=0$ both maps are the identity. There is no assertion here about applying the smooth-pair frame definition to an arbitrary zero scheme.

The old statement asserted an unsigned equality. The corrected live `lem-pur-divisor-class`
uses the Yoneda supported Cartier convention `-∂κ(f)` (its `DivisorLocalEquations`
explicitly pins the negative frame boundary). For odd `r`, the r-fold composition therefore
has factor `(-1)^r`; over `A = F_3`, `S = Spec(k)`, and `r = 1`, the boundary generator is
not equal to its negative. The source is `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/thm-pur-localized-top-chern.proof.md`,
Step 3, read with that corrected divisor convention.

Citer audit: `thm-pur-localized-top-chern` holds:false. Its proof Step 9 identifies
Theta with the positive coordinate product and the local value of u; that use requires
the factor `(-1)^r` in odd rank. This is the sole node whose statement or proof
dependencies name the item. It was read but not edited. The occurrence in the
statement_change audit of `lem-pur-divisor-class` is not a dependency edge.

The theorem's first conjunct now states
`P.flagCoordinateTheta aS r = ((-1 : ℤ) ^ r) • P.flagCoordinateCup aS r`.
Step 1 now defines beta as `-∂κ`, whose representative is `c_D` (or `d_j`).
The existing induction then applies to the signed products Q. Steps 6 and 7
extract `(-1)^r` by bilinearity and identify the unsigned frame class. The base-change and rank-zero clauses are unchanged.

No new node or dependency replacement. 
Historical validation of the returned version: the first complete compile passed both sandbox and library contexts without
warnings (18.2 and 23.1 seconds). After the full import list was made explicit, an asynchronous elaboration run
timed out. Setting `Elab.async false` resolved it with no change to the statement
or constructions: the final scompile passed in 51.6 s (sandbox) and 15.1 s
(library). The timeout limit remains 60 s. Delivery preflight follows.

## Second reading by NP

Final in-process rereading of the node, signatures and definitions (the dispatch
forbids starting another agent; independent review is the maintainer's).
Checked every hypothesis and clause against the correspondence above. In
particular the RHS uses full ambient coordinates, not successive restricted
boundaries; the corrected divisor convention contributes one minus sign per factor, so the first conjunct has `(-1)^r`; Theta uses the dependency's actual normalized composition, not its
support-forgetting image; base change asserts equality of both classes under
the specified map; and both zero-rank maps are explicitly normalized identities.
The geometric rank is an independent natural number throughout. Definitions
choose data only from unique normalizations or concrete Mathlib constructions.
No theorem supplies the desired main equality as a construction premise.
Added explicit rank-zero and smooth-pair clauses during this check, and retained
all proof dependencies through their existing module owners.

Repair self-check (2026-10-19): rank zero has scalar 1, rank one is minus the
positive boundary, rank two has scalar 1. Over F_3 the rank-one sign is nontrivial;
over residue characteristic two the integer scalar action still gives the correct
formula. Arbitrary base change preserves signs because pullback is additive.
The retained geometric helpers and canonical normalizations are unchanged.
