## Worker report

The module `Sheaf.Paper.SupportedCupFunctoriality` states
`WeilConjectures.PurityFiniteSetting.supportedCupFunctoriality`. It packages the
algebra, localization, and comparison clauses as three explicit proposition structures.
Every theorem has `sorry`; all definitions have actual data. The auxiliary declarations
specialize the existing notions or expose their canonical maps; they belong to the
supported-cup construction and are listed in `lean.declarations`.

Clause audit:

- The datum `P : PurityFiniteSetting.{u}` is the recorded finite datum, including
  `P.level_pos`. The exponent is the existing `P.diagonalExponent = ell^n`, with
  `P.diagonalExponent_annihilates`. No assumption that the ramification index divides
  the level is used.
- `functorialCupTwist` uses `Scheme.finiteEtaleTateSheaf` for every `r : ℤ`, and its
  canonical comparison inverse image. Positive twists are the exact `frameTwist`
  sheaves already used by `frameKummer`. Negative twists are their published sheaf
  duals. Products and pullbacks retain the normalized signed-root dependency's maps.
  `FunctorialCupTwistProducts` retains one entire product family together with its
  left/right unit, positive-power, evaluation, associativity and symmetry equations;
  it does not choose unrelated isomorphisms at individual pairs of indices.
- `pro : Bool` selects the actual small etale site (`false`) or actual small
  pro-etale site (`true`); their object and morphism universes are unchanged.
- Ambient schemes are arbitrary `Scheme.{u}`. A structure morphism
  `aX : X ⟶ Spec (.of P.field.k)` is explicit wherever the k-scheme hypothesis is
  needed. Pullback morphisms `v : Y ⟶ X` have no finiteness or separatedness instance.
- Closed supports are precisely `[IsClosedImmersion i]`. The arbitrary chosen
  Cartesian square represents `C' = Y times_X C`, including any presentation of
  that fiber product. `functorialCupExchange` is uniquely determined by its equation
  on restriction of constants, so it is ordinary coefficient exchange, not purity
  or exceptional base change.
- `FunctorialCupH` is the existing supported-Hom model, with the underived closed
  direct image of the actual constant module in degree zero and integer cohomology
  degree. `functorialCupPullback` is exactly inverse source exchange, exact inverse
  image on the morphism, canonical shift comparison, then normalized twist pullback.
  The supported-Hom proof in the node identifies it with pullback on support kernels.
- `FunctorialCupAlgebraLaws.identity` and `.composition` state the identity and
  arbitrary two-step composition equations, using any chosen presentations of the
  three Cartesian squares. No special pullback object is silently equated with an
  iterated pullback.
- `.kummer_add` is `kappa(u*w)=kappa(u)+kappa(w)` for both sites. The definitions
  use exactly `P.frameKummerEtale` and `P.frameKummer`, not abstract classes satisfying
  the desired laws. `.kummer_pullback` uses the actual function pullback
  `Units.map v.appTop.hom.toMonoidHom`.
- `functorialCup` is the inverse supported-coefficient tensor comparison, tensor
  of the two representatives, `cupTensorShiftIso`, and the canonical twist product.
  On the pro-etale side its first composite is exactly the construction of
  `ProEtale.supportedCup`, specialized to degree-zero twist sheaves. On the etale
  side it uses `closedConstantTensorMap`, giving precisely the analogue prescribed
  by the node. It does not assume a cup product from an arbitrary pairing.
- `.add_left`, `.add_right`, `.smul_left`, `.smul_right` state bilinearity over A.
  `.associativity` includes both degree/twist reindexings and the closed-support
  reassociation. A map between the displayed triple intersections over X is
  necessarily the canonical one because closed immersions are monic.
- `.pullback` states the cup pullback equality, with the Cartesian square for the
  intersection support explicitly supplied. `.symmetry` includes the support swap
  and the coefficient symmetry through the normalized twist products. Its scalar
  `(-1 : ℤ) ^ (a*b).natAbs` is the sign `(-1)^(ab)` for arbitrary integer degrees:
  an integer and its absolute value have the same parity.
- `FunctorialCupOrdinaryH` is ordinary cohomology as Hom from the actual unit.
  `functorialCupForget` is precomposition by restriction of constants to C.
  `FunctorialCupLocalizationLaws.full_support` says this identification is bijective
  for C=X. Together with `.forget_support`, this says that pullback for full support
  is ordinary pullback, including its specified normalization.
- The open-complement group is represented by
  `Hom_X(j!A_U[0], A(r)[a])`, using the existing exact extension-by-zero adjunction.
  This is `H^a(U,A(r)|_U)`, canonically identified with the specified twist on U by
  its normalized pullback. `functorialCupOpenRestriction` is precomposition with
  the actual counit. `functorialCupSequence` is the actual open-closed coefficient
  sequence, and `functorialCupBoundary` is composition with its actual `singleδ`.
  This is the same boundary convention as the existing frame-principal boundary
  and the support long exact sequence: applying Hom into an injective representative
  gives the kernel-of-restriction exact sequence, with the same connecting arrow.
  `.open_restriction` and `.boundary` state the two naturality squares.
- `FunctorialCupComparisonLaws` uses exact comparison inverse image, whose maps on
  the closed sources and open sources are uniquely fixed by restriction of constants
  and by the counit, respectively. Its fields state the comparison bijections and
  compatibility with geometric pullback, cup, the concrete Kummer class, forgetting
  supports, restriction to the open complement, and the actual boundary.
- The theorem quantifies both Boolean values and asserts all three structures.
  It has no Cartier, regularity, constructibility, purity-invertibility, exceptional
  base-change-invertibility, Noetherian, quasi-compactness, or finite-type hypothesis.

Recorded statement dependencies used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `Coefficient`, `constantEtale`, `constant`, and the existing coefficient data.
- `Sheaf.Paper.PurityFrameClass` (and its published Kummer/principal-boundary
  imports): `frameKummerEtale`, `frameKummer`, `frameConstantPullback`, and the
  established degree-zero supported cup convention.
- `Sheaf.AlgebraicGeometry.SupportLongExact`:
  `AlgebraicGeometry.exists_support_longExact`, the kernel and localization convention.
- `Sheaf.Paper.SupportedCup`: `cupIntersection`, `cupCoefficientRestriction`,
  `cupCoefficientMap`, `cupDerivedCoefficientMap`, `cupSingleTensorMap`,
  `cupTensorShiftIso`, `cupComposite`, `supportedCup`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- Added already-landed statement dependency `def-weil-pbc-cartesian-square`, module
  `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`, declaration
  `AlgebraicGeometry.ChosenCartesianSquare`, makes the arbitrary Cartesian
  presentations in the laws explicit. No dependency record is changed.

Additional published interfaces include the etale closed-constant tensor lemma,
`Scheme.etaleFiniteTwistPullback`, the exact inverse-image functors and their single
and shift comparisons, and `ShortComplex.ShortExact.singleδ`. The modules of the
recorded, already-stated proof dependencies are imported non-publicly.

Edge cases checked mathematically before writing: empty ambient scheme; empty support;
full support; disjoint supports; identical supports; nonreduced supports; arbitrary
inverse images that fail to be Cartier; zero and negative degrees; degree zero;
negative twists and evaluation against positive twists; n=1 and arbitrary ramified
positive levels; odd/odd degrees giving the minus sign; even degrees giving plus;
coefficient characteristic two; identities and arbitrary composites; and open
complements that are not quasi-compact. The source and open exchange normalizations
remain unique in the empty and zero-object cases.

Searches for an exact existing statement:

- `msearch.py ... leanfinder "pullback and graded commutativity of cup products in
  cohomology with closed support"`: eight unrelated group-cohomology functoriality
  hits; no supported-scheme statement.
- `msearch.py ... loogle "CategoryTheory.Sheaf.H, cup"`: no hits; `cup` unknown.
- `msearch.py ... grep "supportedCup|supported_cup|cup.*commut"`: no Mathlib hits.
- `msearch.py ... leansearch "cohomology with supports cup product functorial graded
  commutative"`: eight hits on group cohomology and graded-object totalization;
  no match.
- `rg` in upstream `WeilConjectures` for supported cup and functoriality patterns:
  coordinate purity and Kummer-specific declarations, not the full statement.
  `grep -rn` for this node id: no upstream match.
- `rg` in `lean/Sheaf` finds the prescribed `SupportedCup`, downstream textual
  citations, Kummer first-Chern and Cech/module-cup work, and the separate shifted
  tensor calculus. None states all clauses of this node on both small sites.
- `rg` for the new names in upstream and `dag/lean_names_upstream.json`: no collision.

Sources read: the complete node and its eight-step proof, every statement dependency
and its recorded interface, Stacks `sites-cohomology.tex` at the associative and
commutative cup lemmas, and the main-20261015 frame-independence proof at unit
multiples, permutations, and the shear family. No statement correction or dispute.

Validation: prescribed `scompile.py` passed for the complete module on 2026-10-18,
in both sandbox and library modes, with no errors and no warnings. All 67 explicit
declarations are listed in the node record; every universe and variable is bound.

## Second reading by Q67

The dispatcher explicitly forbids starting another agent and assigns independent
review to the maintainer who receives this delivery. No independent worker review
is claimed here. The worker's final clause audit is the detailed mapping above;
the maintainer's independent delivery review remains required. In that audit I
checked the actual node against the file, in particular the arbitrary positive
coefficient index, signed degrees/twists, both sites, the exact support and counit
normalizations, the integer Koszul sign, all localization arrows, and the absence
of Cartier or exceptional-base-change assumptions.
