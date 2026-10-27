## Worker report

The module `Sheaf.Paper.FiniteTwistRootTrivialization` states
`WeilConjectures.FiniteTwistRootTrivialization.finite_twist_root_trivialization`.
Its only theorem has proof `sorry`. The helper abbreviation and two structures
have real data: the structures package precisely the isomorphisms and equations
asserted in the node. They are conclusion data, never assumptions on the input.
The repair adds two definition ownership nodes for already published declarations.
There are no new Lean modules, dependency-interface repairs, or statement corrections.

### Hypotheses and clause correspondence

* The input `P : PurityFiniteSetting.{u}` is the published finite datum of
  `def-pur-conventions`: its `field` is the fixed algebraic closure of the finite
  field, `coefficients.l` is prime and differs from the characteristic,
  `extension` is a finite subextension of the fixed coefficient closure, and
  `level_pos` asserts `1 ≤ level`. `P.Ring` is literally the existing
  `Padic.coefficientExtensionRing ... P.level`, not a new coefficient ring.
* The first three conjuncts are `Finite P.Ring`,
  `((P.coefficients.l ^ P.level : ℕ) : P.Ring) = 0`, and
  `∃ b : ℕ, Nat.card P.Ring = P.coefficients.l ^ b`.
  The cast equation also says multiplication by that integer kills the entire
  ring and its additive group, by multiplying the equation by each element.
* `Nonempty (CompatibleBases P.field.k P.coefficients.l)` packages one family
  for every scheme and coefficient level, so the naturality assertions concern
  the same bases. The scheme binder is the whole category
  `Over (Spec (CommRingCat.of k))`; a morphism in it is exactly a k-morphism.
  There is no finite-type, separated, reduced, connected, or nonempty hypothesis.
* A finite quotient level is indexed as `n+1` in the published APIs
  `finiteTateCoefficient`, `finiteCoefficientTwist`, and `purTwistFiniteOne`.
  The root exponent is separately `l^(r+1)`. This distinguishes the coefficient
  level from a possibly larger common annihilator. All positive integers occur;
  there is no ramification-index divisibility assumption.
* `CompatibleBases.root_quotient` is the canonical quotient
  `cokernel (l^(r+1) • 𝟙 M) ≅ μ_(l^(r+1))`, with
  `cokernel.π ≫ q.hom = limit.π`. Thus it is the quotient in sheaves, with the
  actual projection from the actual root limit. Additive sheaves are equivalently
  Z-module sheaves; this is the module quotient by mM. It does not assert a
  sectionwise quotient, which would be the wrong construction on a general site.
* `SignedBasis.presentation` is
  `finiteRootProTensor A m hm hA T ≅ proSigned l E n T 1`.
  The source is the published sheafification of the balanced scalar extension
  of the actual pro-etale root sheaf. The A factor is first, as in the recorded
  etale API; this is the usual symmetric presentation of `μ_m ⊗_(Z/m) A`.
  `presentation_projection` fixes its inverse on every local pure tensor by
  the coordinate `limit.π ... (op r)` of the original root tower.
* `CompatibleBases.root` is the pro-etale cyclic-module basis.
  `root_formula` states on EVERY weakly etale test object that j maps to the
  pullback of `ζ ^ j.val`. The etale basis is the existing
  `constantZModIsoRootsOfUnitySheaf ... T.hom hζ`, whose definition is the
  constant-root power map. `root_site` fixes the comparison with this actual
  etale basis using `ProEtale.cartierRootsIso`, the inverse-image unit and
  restriction along every arrow from a pro-etale test to an etale test.
  Its `hT` is a proof parameter for that existing comparison, not an extra input
  to the theorem. `SignedBasis.invertible` supplies that property as a conclusion.
* `SignedBasis.pro` trivializes the ACTUAL signed detailed pro-etale twists,
  as modules over their constant coefficient ring sheaf. `pro_one` sends 1 to
  `ζ ⊗ 1` through the normalized tensor presentation. `pro_signed` is the
  existing `IsPurPointSignedCoordinates`, which is a predicate on an arbitrary
  scheme despite its historical name: zero is the coefficient identity,
  successive positive generators are pure tensors, and the inverse in every
  negative degree is evaluation on the positive generator. Its quantifiers
  range over every localized test, not merely global sections.
* `SignedBasis.etale` trivializes the existing signed `finiteEtaleTateSheaf`.
  `etale_zero` is the identity, `etale_one` specifies every constant coefficient
  times the primitive root, `etale_positive` specifies tensor powers, and
  `etale_dual` is precisely the evaluation/dual-basis normalization.
* `SignedBasis.comparison` identifies the inverse image of the signed etale
  realization with the detailed pro-etale line. At nonnegative degrees,
  `comparison_positive` is the published `IsFiniteTateSiteComparison`, normalized
  on all local root tensors and their projections. `comparison_basis` fixes the
  same comparison in every signed degree by its normalized bases. In particular
  the negative comparison is evaluation on the pulled-back positive basis,
  rather than an unspecified isomorphism to a constant sheaf.
* `CompatibleBases.etale_pullback` uses the recorded, canonical
  `finiteEtaleTwistPullbackData.c` and states its basis square for every k-morphism
  and every signed exponent. `pro_pullback` supplies the corresponding signed
  isomorphisms, fixes their square on the same bases, requires the published
  `IsFiniteTateProPullback` on all nonnegative degrees (including zero), and
  states the full scheme-pullback/site-comparison square in every signed degree.
* `root_power` is compatibility with reduction of labels and root power maps at
  ANY two ordered exponents, with primitive roots related by the appropriate
  power. `exponent_basis` says the resulting detailed pro-etale signed bases are
  literally equal. On the etale side their conjugate identifies the two
  presentations and takes every root tensor to its specified power-transition
  tensor. The signed tensor and evaluation clauses determine all other degrees.
* `CompatibleBases.coefficient` quantifies over TWO arbitrary finite extension
  rings and positive quotient levels, an arbitrary ring homomorphism `φ` between
  their lifted quotients, and ONE common exponent `l^(r+1)` annihilating both.
  There is no flatness or injectivity assumption. It supplies isomorphisms after
  the existing ordinary scalar-extension functors on both sites. The first two
  clauses normalize their degree-zero adjuncts by the literal map `a ↦ φ a`.
  The next two clauses are the signed basis squares, the next is compatibility
  with the canonical scalar/site comparison, and the last two fix the first
  line's adjuncts on every root tensor and root-limit tensor. Together with the
  signed evaluation clauses these specify the actual coefficient comparison,
  including its duals; no arbitrary map has replaced a canonical construction.
  In particular maps `A_(E,n') → A_(E,n)` of nonreduced quotients are included.

The normalizations also entail identity and composition: in degree zero the
canonical maps fix all constant sections, and in each signed degree the square
fixes the image of its generating basis. Two composites with the same scalar
map therefore agree locally on generators, hence as sheaf morphisms. This
uniqueness is why the family is packaged with its equations rather than as an
unconstrained `Nonempty` choice of isomorphisms.

### Recorded declarations used

All seven original statement dependency records were read, including the source
signatures and docstrings. Their modules are imported publicly:

* `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, its `Ring` and field
  and coefficient data; the older `exponent` requiring ramification divisibility
  is deliberately not used.
* `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: reexports
  `finiteCoefficientTwist`, `coefficientTwistLine` and the original root limit
  and finite tensor construction. `proSigned` only applies the existing
  `finiteTateConstantRestriction` to this exact signed object.
* `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`:
  `finiteEtaleTateSheaf`, `finiteEtaleTwistPullbackData.c`, the signed powers and
  canonical pullback maps.
* `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: the recorded comparison
  adjunction, via `ProEtale.comparisonUpperStar` and `comparisonAdjunction`.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the existing
  monoidal structure on module sheaves with independent site universes.
* `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology.

The statement uses the definition owner
`def-amb-finite-tate-site-comparison-data` for `finiteTateCoefficient`,
`finiteTateConstantRestriction`, `finiteTateProGenerator`, `finiteTateLimitRootValue`,
and `IsFiniteTateSiteComparison`/`IsFiniteTateProPullback`. It uses the two new
existing-definition owners below for `finiteRootProModule/Tensor/Generator` and
`purPointConstant`/`IsPurPointSignedCoordinates`. The point-named definitions are
already generic in the scheme, as their full signatures show. None is a choice
from a theorem. The theorem nodes `lem-amb-finite-root-site-comparison` and
`lem-amb-finite-tate-site-descent` remain in the original `proof_deps`; the point
coordinate theorem is not used (the node's direct tensor/evaluation proof is retained).
The exact existing etale root
basis is imported from `WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity`;
ordinary scalar extension is the recorded
`WeilConjectures.SixFunctors.ProEtale.ScalarExtension`.

Stated proof dependency modules are imported as well: extension integers DVR,
finite-root site comparison, finite Tate site descent, sheaf tensor bilinear
universality, inverse limits, and internal Hom. The nodes
`lem-weil-valued-dvr-finite-quotients`,
`lem-pur-affine-line-finite-group-devissage`, and
`lem-pur-primitive-root-etale-basis` have no recorded module to import; they
remain explicit proof steps in the theorem docstring. No independent dependency
was silently assumed as a new hypothesis.

### Sources, searches and edge cases

Read the current `literature/blueprint/latest/.../sk-prop-a1-kummer.proof.md`,
Coefficients and Reduction to a geometric fibre, and the local Stacks source
`literature/stacks-project/etale-cohomology.tex`, section-kummer (03PK).
The complete eight-step DAG proof is carried in the theorem docstring.

Searches used `msearch.py Q135 lem-pur-finite-twist-root-trivialization`:

* LeanFinder: "Finite signed Tate twists are trivialized by compatible primitive
  roots naturally in schemes and coefficient maps". Eight hits, including
  `modularCyclotomicCharacter.spec`, `cyclotomicCharacter.spec` and related
  cyclotomic-character formulas; none states this geometric sheaf assertion.
* Loogle: `"rootsOfUnity", "Sheaf"`. No hits.
* LeanSearch: "A finite signed Tate sheaf has a primitive root basis compatible
  with pullback and arbitrary change of coefficients". Eight hits on algebraic
  basis change and sheaf pullback, including `IsBaseChange.basis_repr_comp` and
  `SheafOfModules.pullbackObjFreeIso`; no complete match.
* Mathlib grep: `Tate.*trivial|twist.*constant|rootsOfUnity.*[Ii]so`.
  Sixteen unrelated hits (roots of unity, finite abelian duality, FLT, topology,
  and ordering); no finite signed sheaf statement.
* `rg` across `lean/WeilConjectures` and `lean/Sheaf` for
  `finite.*[Tt]wist.*[Rr]oot|root.*[Tt]rivial|[Tt]wist.*[Bb]asis|finiteTwistRoot`
  found the cited finite Tate/site APIs, point root coordinates, root local
  models and curve root trivializations. Each relevant interface was opened;
  none states the full arbitrary-scheme and arbitrary-coefficient assertion.
* The required node-id `grep -rn` in `lean/WeilConjectures` returned no match.

Checked edge cases before writing: empty schemes and empty test objects (all
formulae remain sheaf/section equations, with no choice of a point); disconnected
and nonreduced schemes; `l=2`; coefficient level one; zero, positive and negative
signed exponents; the identity scheme morphism and arbitrary compositions;
ramified coefficient extensions with level not divisible by ramification index;
two different levels sharing a larger annihilator; nonflat quotient coefficient
maps; and arbitrary field extensions of the common coefficient prime. The signed
base recursions use the actual tensor unit at zero and internal Hom at negative
integers. Sites keep object universe `u+1` and morphism universe `u`; coefficients
are the standard `ULift` to `u+1`, with no equality imposed on those site universes.

Validation uses only the prescribed `scompile.py`, in module mode, under the
unchanged 60-second per-file limit. All explicit universes and variables are
bound, and `autoImplicit` is false. No live source or shared build was modified.

No `STATEMENT-DISPUTED` issue was found.


## New nodes

`def-pur-finite-root-pro-tensor` owns only the unchanged
`AlgebraicGeometry.Scheme.finiteRootProModule`, `finiteRootProTensor`, and
`finiteRootProGenerator` from `Sheaf.AlgebraicGeometry.FiniteRootSiteComparison`.
The statement follows the published restriction to constant scalars, restriction
along the lift isomorphism, sectionwise scalar extension and sheafification unit.
Sources: Stacks 03PK, 03EK and 03EL. In particular it assumes neither finiteness
of A nor invertibility of m on T, and permits m=1 and zero rings. Its existing:true
record has the exact tensor signature, including u+1 coefficients and u schemes.

`def-pur-signed-root-coordinate-data` owns only the unchanged
`WeilConjectures.purPointConstant` and `IsPurPointSignedCoordinates` from
`Sheaf.Paper.PointTateRootCoordinates`. Its statement records the constant-label
unit and all six predicate clauses: zero, recursive positive tensor, scalar
linearity, positive inverse, negative inverse by evaluation, and the dual
normalization. Sources: Deligne (2.2), (2.13). The signed predicate has arbitrary
scheme S, coefficient sheaf R and line L; it assumes no primitive root, finite
field, or existence theorem. The independent u,v sizes of constant labels and
the u+1 coefficient size of signed coordinates are preserved. Empty tests and
zero rings are included. The existing:true signature is copied verbatim.

For both nodes, actual new searches on 2026-10-24 were logged by msearch.py:
LeanSearch query "Pro etale roots of unity module scalar extension tensor pure
generator and signed Tate line coordinate normalization" returned eight unrelated
algebra-generator, cyclotomic-character, etale-algebra and root-system hits;
Loogle queries `"finiteRootProTensor"` and `"IsPurPointSignedCoordinates"`
returned zero hits; Mathlib grep
`finiteRootPro(Module|Tensor|Generator)|purPointConstant|IsPurPointSignedCoordinates`
returned zero hits. The same rg query in WeilConjectures returned no match,
while Sheaf has the existing definitions named above. DAG rg found only their
theorem records and consumers, no definition owner. The similarly named
`def-pur-finite-root-tensor-presentation` was opened: it owns a different shifted
purity-reduction comparison, not these three root-tensor definitions.
`blueprint_refs.py search 'root tensor'` and `search 'signed coordinates'`
returned zero blueprint nodes. Thus these add ownership records, with no duplicate
construction, module or proof. The ancestor tool reports `lem-pur-frame-independence`.

## Repair of return L at a04626abeb58

H2: removed all three theorem-node additions from stmt_deps and cited the
existing finite-Tate definition owner plus the two new existing:true definition
owners above. The root-comparison and Tate-descent theorems remain proof_deps
as in the accepted split. No statement consumes their `.choose` or conclusion.
The point-coordinate theorem is unused; only its plain generic definitions occur.
The Lean file and theorem signature are unchanged from the returned packet.

Advisory addressed: stmt_deps now also cites `def-asd-finite-etale-tate-sheaf`
(finiteEtaleTateSheaf and finiteEtaleTateOneGenerator),
`def-sc-mu-trivialization` (constantZModIsoRootsOfUnitySheaf),
`def-sfb-cartier-reduction-data` (ProEtale.cartierRootsIso),
`def-pur-roots-of-unity-sheaf` (actual roots, sections, transitions and tower),
`def-pur-twist-sheaves` (purTwistZlOne, purTwistRootsModule and purTwistFiniteOne),
`def-sfb-site-derived-constant-module-functor` (realizationRingUnit), and
`def-sf-etale-sheaf-scalar-extension` (ordinary etale extension and its adjunction).
Their existing declaration records were read; no record is rewritten.

## Self-check by Q135

This is the author's repair self-check, not an independent second reading.
The independent maintainer H3 reading in the return found no substance fault.
Reopened the saved node, complete Lean file, generic root-module and signed-coordinate
signatures/docstrings, current owner records and current blueprint Coefficients
paragraph. The clause correspondence in Worker report remains accurate: finite
ring and ell-power order; actual cokernel projection; root tensor presentation;
root power bases on both sites; positive tensor and negative evaluation coordinates;
site and scheme pullback squares; arbitrary coefficient maps with a common
annihilator and no flatness assumption. No mathematical declaration changed.
The only saved/current item differences before repair were lean and the three
added stmt_deps; the repaired item still changes only lean and stmt_deps.
New ownership statements neither assert theorem conclusions nor choose witnesses.

Validation repair: the current server preflight requires `import_flags: []` on
both new definition nodes, beyond the listed brief schema; those fields are
included following its concrete diagnostic. Tensor and Hom citations are
written separately for its citation parser. The direct scompile.py check of
the unchanged main module passed in sandbox and library modes (36.4s, 34.2s).

## Second reading by Q135

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
