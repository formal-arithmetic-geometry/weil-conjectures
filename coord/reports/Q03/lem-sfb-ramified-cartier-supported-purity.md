## Worker report

Delivery: lean/Sheaf/Paper/RamifiedCartierSupportedPurity.lean and the item's node copy.
The main theorem is AlgebraicGeometry.Etale.ramifiedCartierSupportedPurity; its single
proof is sorry. RamifiedCartierPurityAssertion is a transparent Prop-valued helper
spelling out this same node's clauses, with real terms throughout its definition.
No new nodes, dependency repairs, statement correction or extra axioms.

Routing: I read the current repair note and both 2026-10-24 maintenance records
before interpreting the historical NU return. The saved NU sandbox named there
is absent on this machine. More importantly, the live item is now split in seven
steps with a passing independent NU review accepting those exact steps and ten
tool uses, and coord/queue.tsv selects stage 2. The note has state resolved.
Therefore the older instruction to resume an unsplit stage-1 candidate has been
completed by a different worker; this packet preserves that accepted live split
and supplies its missing Lean statement. It does not run deliver.py to resplit an
already accepted node. The historical H1/H2 missing-module defect is addressed by
this actual compiled module and lean record. No dropped input is revived: the two
finite-coefficient regular-pair statements remain unsplit inputs authorized by
the route decision, imported only when they have actual modules.

Hypotheses, clause by clause:

- Prime ell and s >= 1: `(hℓ : ℓ.Prime)` and `(hs : 1 ≤ s)`.
- A = Z/(ell^s): the assertion uses precisely `ULift.{u+1} (ZMod (ℓ ^ s))`.
  ULift is the site coefficient-size convention, with the original ring operations.
  hA is the actual cast-zero proof from ZMod.natCast_self; no coefficient datum is
  assumed and no arbitrary annihilated ring is substituted.
- X and X' Noetherian regular affine: both IsAffine and IsNoetherian instances,
  and hX/hX' using the recorded IsRegularScheme.
- ell invertible: hℓX and hℓX' are IsUnit in global section rings.
- f and g global sections and nonzerodivisors: the explicit Γ binders and hf/hg
  membership in nonZeroDivisors. These allow units and the zero ring convention.
- D = V(f), D' = V(g), their regularity: actual zeroLocusSubscheme singleton
  terms in hD/hD'. The assertion uses their canonical zeroLocusSubschemeι maps.
- h and exponent: `(h : X' ⟶ X)`, `(e : ℕ)`, he : 1 ≤ e and the exact equation
  h.appTop.hom f = g ^ e. No flatness, smoothness, equal characteristic or
  invertibility of e is imposed.
- Effective Cartier ideals: hI/hI' are CONCLUSIONS, using the recorded
  Scheme.IdealSheafData.IsInvertible. They are not extra hypotheses.
- Ordinary small etale D(-,A): recorded DerivedCategoryModule and upperStar on
  ModuleCat.{u+1} A. No pro-etale category, completion or constructibility appears.
- Negative Tate line: recorded closedDual from CartierDualKummerNormalization
  uses finiteEtaleTateSheaf at -1, the internal dual of finiteEtaleTateLine.
- K_D and K_D': the published sectionsWithSupport kernel, right-derived and
  evaluated on ordinaryFiniteUnit. q/q' are the right-derived kernel inclusions,
  followed by the canonical identification of the derived identity with identity.
  The assertion includes distinguished triangles with EXACTLY the actual
  mapDerivedUpperStarLowerStarAdjunction units; hence these are the stated fibres.
- Supported Kummer factorization and isomorphisms: P/P' are isomorphisms
  closedDual ≅ K[2]. Applying [-2] gives precisely i_* A(-1)[-2] ≅ K.
  KummerNormalized fixes their forget-support arrows by the unique positive
  SupportedKummerBoundary and actual tensor evaluation; it is not a supplied
  orientation or arbitrary purity axiom. Each following universal clause says
  every arrow with that forget-support composite equals P.hom/P'.hom.
- h_D and reduction: E is literally V(g^e), kept separate from D'. Witness d
  makes the E/D square Cartesian, and r ≫ k = i' makes r the actual closed
  reduction. Monicity fixes r; Cartesianity fixes d. sqD uses h_D = r ≫ d.
  There is no assertion that the reduced D'/D square is Cartesian.
- rho: the EXISTING closedExchange applied to sqD, with normalized negative
  Tate pullback. Its commuting-square mate equals Cartesian exchange to E
  followed by the specified reduction, as the recorded definition states.
- theta and its actual unit normalization: the source is H.obj K, target K'.
  theta's forget-support square uses the actual canonical constant identification
  a.hom. A universal clause makes this supported arrow unique. The full boundary
  square uses beta, explicitly exactDerivedBaseChangeMap for the Cartesian open
  square, exactDerivedSquareUpperStarIso, and a.hom. Thus the map is the actual
  unit mate, not a freely selected scalar normalization.
- Main equality: H.map P.hom, H.commShiftIso 2 and theta[2] equal
  `(e • ρ) ≫ P'.hom`. This is exactly the common shift-by-two form of
  theta ∘ h^* P_D = P_D' ∘ (e rho)[-2]. Lean composition ≫ runs left to right.
- Degree-two concentration: for every z != 2, IsZero of H^z K and H^z K'.
  The last equation applies H^0 to the displayed shifted equality, so its target
  is H^0(K'[2]) = H^2(K'); it is the explicit degree-two consequence, including
  the same closed exchange and multiplier. No independent per-degree purity
  model replaces the derived assertion.
- Empty divisors and e=1: no Nonempty or nonzero section/ideal assumption occurs;
  IsZero allows the empty supported object. The phrase 'sole nonzero' means
  'only possibly nonzero', as already resolved in the accepted split step 7.

Dependency declarations read and used:

- Sheaf.AlgebraicGeometry.IsRegularScheme: AlgebraicGeometry.IsRegularScheme
  = IsLocallyNoetherian X ∧ IsRegular X.
- WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible:
  AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible (locally regular principal).
- WeilConjectures.AlgebraicGeometry.DerivedCategories and its Coefficients import:
  AlgebraicGeometry.Etale.DerivedCategoryModule; Mathlib homologyFunctor.
- Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist:
  Scheme.finiteEtaleTateLine and finiteEtaleTateTwist, including their full source.
- Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer:
  ordinary_supported_kummer and ordinary_supported_kummer_uniqueBoundary, with
  full signatures/docstrings read; their published SupportedKummerBoundary and
  ordinaryFiniteUnit are used through the existing normalization definition.
- Sheaf.Paper.CartierDualKummerNormalization:
  RamifiedRoot.closedDual, KummerNormalized, closedExchange, closedEvaluation,
  twistPullback. Its definition node is added to stmt_deps because the statement
  explicitly uses these existing notions; no private duplicate was written.
- Sheaf.AlgebraicGeometry.ExactUnboundedExchange:
  exactDerivedBaseChangeMap and exactDerivedSquareUpperStarIso (the canonical
  adjunction mate). Its existing definition node is added to stmt_deps.
- WeilConjectures.SixFunctors.OpenClosed.SupportedSections and its public
  ClosedImmersionUpperShriek import: ordinary sectionsWithSupport and inclusion.
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp:
  canonical derived-identity comparison, used to type the inclusion.
- WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme:
  Scheme.zeroLocusSubscheme and zeroLocusSubschemeι (existing closed subschemes).

All recorded proof dependencies that have published modules are imported without
public, except ordinary_supported_kummer which is already a statement import.
The bounded-below adjunction and Hom-triangle facts have no own recorded modules;
the two authorized finite-coefficient regular-pair purity/class-calculus inputs
also have no modules. No replacement statement or new assumption was invented
for any of these proof inputs.

Sources: read the actual ILO XVI PDF, supported Chern construction and Definition
2.1.1, Section 2.3 and Theorem 3.1.1 (PDF pp. 234-249, printed pp. 228-243).
ILO uses a convention involving the Cartier ideal; this node and its approved
split choose the published positive O(D) Kummer boundary. The actual multiplier
formula is unchanged by that common orientation convention. Read latest blueprint
sk-thm-sf-ctf-stability/_section.md. The module proof docstring carries all seven
accepted assembly steps; no assertion of smooth purity for a general regular pair.

Edge checks: empty X; f or g a unit; D' empty while D nonempty; identity h/e=1;
the map t↦t^e on affine lines; ell^s dividing e (the comparison is zero, not an
isomorphism); the mixed-characteristic Spec Z[1/ell], V(p) case. All are retained.
E need not be regular or reduced. The shift orientation was checked against
closedDual ≅ K[2] in the already landed root-limit consumer. Natural number e
matches exactly the positive integers in the node.

Searches: msearch.py leanfinder with the query 'Ramified pullback of the supported
Kummer purity isomorphism for a regular Cartier divisor multiplies by its
ramification index' returned eight Dedekind ramification-index lemmas, not this
statement. Loogle '"Etale", "Kummer"' returned zero. Mathlib grep
'(ramification|ramified).*(purity|Gysin|support)|(purity|Gysin|support).*(ramification|ramified)'
returned five lines in RingTheory/Unramified/Locus.lean about Kahler support.
LeanSearch 'Ramified pullback of ordinary etale cohomology with support for a
regular Cartier divisor is multiplication by the parameter exponent' returned
ramification indices, formal etaleness, additive module pullback, and Scheme.Etale.
None has this statement. Logs are searches.jsonl (recorded directly by msearch).
rg on lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
ramifiedCartierSupportedPurity, RamifiedCartierPurityAssertion and the item id
found only the downstream root-limit theorem's docstring citation. Reading that
consumer found the exact existing dual-normalization definition; it is reused.
No existing theorem states the arbitrary regular-pair ramification square.

Validation: scompile.py compiled the actual file in both sandbox and library
module modes cleanly (21.5s/19.1s), with no diagnostics. No direct Lean, Lake,
global build, git mutation or write to the read-only repository was performed.

## Second reading by Q03

A separate source/signature audit in this session checked the compiled file
against every hypothesis and clause above. This is a self-audit, not a claim
that an independent agent was run (the dispatcher forbids starting agents).
The maintainer's independent delivery review remains required. No mathematical
statement change was found necessary. Checked explicitly: all existence of
Cartier/unit/transport data is concluded, not assumed; the two triangles use
actual units; E is not incorrectly made regular; the derived equation has e,
not its inverse; and the H^0 shifted equation is precisely the H^2 transition.
Only the item's lean attachment and two added existing definition dependencies
are changed; all accepted stage-1 proof, source and statement fields are kept.
