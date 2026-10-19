## Worker report

The module `Sheaf.Paper.PurityFrameClass` defines the concrete finite-level class
`WeilConjectures.PurityFiniteSetting.frameClass`. It reuses the upstream
`Scheme.Hom.EtaleFrame`, rather than introducing a second frame structure. It
constructs actual Kummer classes, takes each individual closed-open boundary,
and folds the published supported cup operation in tuple order. No frame
independence, existence theorem, or purity isomorphism is asserted.

### Hypotheses and clauses

* The finite field, coefficient extension, prime and positive coefficient level
  are the fields of `P : PurityFiniteSetting`. `P.Coefficient` is the existing
  size lift of the actual quotient O_E/(varpi_E^n), not an arbitrary torsion ring.
* `b : B ⟶ Spec (.of P.field.k)` and `v : V ⟶ B` specify the k-scheme diagram.
  All remaining structure maps are their composites. The exact relative
  dimension in the node is `[SmoothOfRelativeDimension P.level v]`.
* The closed subfamily is `i : Z ⟶ V` with `[IsClosedImmersion i]` and
  `[Smooth (i ≫ v)]`. `c : ℕ` includes zero. `_hcodim` is the pointwise equation
  of `ringKrullDim` of the two local rings, valued in `WithBot ℕ∞`. No finiteness
  of dimension or noetherian condition is imposed.
* `F : i.EtaleFrame c` contains `F.U`, `F.e`, its etaleness proof, and the ordered
  tuple `F.f : Fin c → Γ(F.U, ⊤)`. Its `toZ` and `isPullback` identify the actual
  common zero subscheme with Z times_V U. This is equivalent to the ideal
  generation condition, including scheme structure. No open-immersion
  assumption is made on `F.e`.
* For any function f, `X.zeroLocusSubschemeι {f}` is the principal closed
  subscheme D and `(X.basicOpen f).ι` is its complementary open W. The actual
  unit is `X.basicOpenUnit f`, constructed by localization.
* `P.diagonalExponent` is ell^n. The published
  `diagonalExponent_annihilates` and `diagonalExponent_isUnit` give mA=0 and
  invertibility on every k-scheme, without e dividing n.
* `frameTwistEtale` is the existing `Scheme.finiteEtaleTateSheaf` at m, and
  `frameTwist` is its exact comparison inverse image. This is the published
  finite root-line tensor presentation of A(d). The node explicitly identifies
  the completed-root reduction and this presentation by theta, characterized
  by z tensor a mapping to pi_n(z) tensor a. Consequently using this presentation
  transports sigma to the scalar-extension unit v mapping to v tensor 1_A.
  The published extension-of-scalars implementation writes A tensor mu, so its
  generator is 1_A tensor v; the ordinary degree-zero tensor symmetry identifies
  this with v tensor 1_A in the node. We do not choose a generator, orientation,
  or trivialization of the line.
* `frameKummerEtale` first applies the actual `Scheme.kummerδ₀` to the unit,
  then `Sheaf.H.map` of `Etale.ordinaryFiniteRootMap`. This is scalar extension
  on the roots sheaf, never on G_m as an R-module. The inverse of
  `moduleClassToAbelian_bijective` represents that same class as module Ext.
* `frameKummer` uses `Ext.mapExactFunctor comparisonUpperStar`, the canonical
  etale-to-pro-etale cohomology comparison. Naturality and exact inverse image
  give precisely comp followed by H1(sigma rho) in the root-tensor presentation.
  The root comparison is induced by identical root sections; no arbitrary
  cohomology isomorphism is substituted.
* `frameEtalePullback` uses the published finite-twist pullback theorem with
  its kernel-inclusion and local pure-tensor normalization. `frameTwistPullback`
  applies the canonical comparison-composition isomorphism. Thus the open
  restriction of A(1) is identified through roots and tensors as required.
* `frameOpenInclusion` and `cupCoefficientRestriction` are the actual coefficient
  maps j_!A_W → A_X → i_*A_D. The two named proof obligations state zero composite
  and short exactness. `frameBoundary` composes its Yoneda extension class with
  the exact j_! image of the Kummer class and the twist adjunction counit.
  This is the closed-open connecting morphism in the supported-Hom model:
  applying Hom(-, an injective resolution) to this coefficient sequence gives
  the kernel-of-restriction complex defining supported sections. The usual Ext
  connecting convention fixes its sign. Each factor uses its own D=V(f), not
  the final common support.
* `cupSupportedHom` is the recorded supported cohomology Hom convention, with
  the shared `cupHasDerivedCategory` and `cupSingle`. The target of the boundary
  has degree 2 and coefficient `frameTwist X 1`.
* `frameIntersection_existsUnique` is the canonical identification of the full
  zero subscheme with the pullback of the prefix support and the last principal
  support. Its over-X equation makes it unique. Its proof docstring explains
  the sum-of-ideals calculation and gluing. `frameClosedCoefficientIso` is built
  from existing pushforward-composition and constant-pullback isomorphisms.
* `frameCupNext` calls the recorded `supportedCup` through `frameCupSheaves`.
  This helper uses `DerivedCategory.Plus.singleFunctor` in degree zero for both
  sheaves; its ambient objects are definitionally the recorded `cupSingle`
  objects. The over-base instance comes from the displayed structure morphism.
  Thus the published coefficient comparison and right-shift-first convention
  are reused directly. `frameCupTransport` composes the source identification,
  this cup, the tensor coefficient map and the degree conversion. No second cup
  product or tensor structure is introduced.
* `frameEtaleTensorNext` uses the defining left-associated finite line powers
  (the left unitor at degree zero). `frameSheafTensorNext` transports by the
  strong monoidal comparison. `frameTensorNext` is the published K-flat
  degree-zero tensor comparison followed by that sheaf tensor map. The local
  freeness clause in the dependency identifies ordinary and derived tensors.
* `frameBoundaryProduct` recursively appends the last factor to the prefix:
  this is the ordered, left-associated product of alpha_1 through alpha_c.
  `frameDegreeNext` performs only the integer degree conversion 2d+2=2(d+1).
  The target is degree 2c, coefficient A(c), and the full common zero support.
* At c=0, `frameEmptyRestriction_isIso` records that the zero ideal gives all of
  X. `frameEmptyClass` is the inverse coefficient restriction in degree zero,
  followed by the canonical zero-shift isomorphism: the supported unit 1.
  The recursion begins at this unit. For c=1 the unit cup alpha_1 is alpha_1
  under the same canonical unit comparisons.

### Dependency declarations used

The principal recorded interfaces are `PurityFiniteSetting` and its constants,
module/abelian comparison (`Sheaf.Paper.PurityFiniteSetting`);
`Scheme.ProEt` and its topology (Mathlib); `SmoothOfRelativeDimension`, `Smooth`,
`IsClosedImmersion`, `Etale`, `IsOpenImmersion` (Mathlib);
`Limits.pullback` for the scheme-base-change convention;
`supportSections`/`supportHypercohomology` (`Sheaf.AlgebraicGeometry.SupportCohomology`);
`cupSupportedHom`, `cupSingle`, `cupHasDerivedCategory`, `cupMonoidal`,
`cupCoefficientRestriction`, `cupCoefficientMap`, `cupDerivedCoefficientMap`,
`cupDerivedCoefficientMap_isIso`, `cupSingleTensorMap`, `cupComposite` and
`cupIntersection` (`Sheaf.Paper.SupportedCup`).

The coefficient dependency publicly reexports
`Sheaf.Paper.FixedFinitePositiveCoefficientTwist`, whose `diagonalExponent`,
`diagonalExponent_annihilates` and `diagonalExponent_isUnit` are used.
`Scheme.finiteEtaleTateSheaf` is the positive finite twist presentation;
`Scheme.pur_twist_sheaf_locally_free` in
`Sheaf.Paper.PurTwistSheafLocallyFree` supplies its completed-root reduction and
flatness interpretation. The ordinary tensor and derived tensor structures are
the existing ones used by the recorded supported cup; no private tensor or
cohomology functor is defined here.

The actual Kummer sequence and boundary are `Scheme.kummerSequence_shortExact`
and `Scheme.kummerδ₀` in `WeilConjectures.AlgebraicGeometry.Sites.Kummer`.
The units sheaf is the existing `Scheme.gmSheaf`. Cohomology is the existing
`Sheaf.H`, with the recorded right-derived universal delta convention.
The comparison used is `ProEtale.comparisonUpperStar` and its canonical
cohomology map, in the recorded etale/pro-etale geometric morphism and abelian
cohomology comparison. Its pro-etale root is the recorded
`Scheme.proEtaleRootsOfUnitySheaf`.

The concrete affine-line dependency's `kummerEtale`/`kummer` has a ramification
index divisibility argument. The formula here uses the same root map and
Kummer connecting construction with the published universal annihilator ell^n,
as the item's expanded statement expressly requires for all positive levels.
`Etale.ordinaryFiniteRootMap` in
`Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer` provides the already published
scalar-extension unit, and its owning landed node is cited by the new Kummer node.
`Scheme.etaleFiniteTwistPullback` supplies the normalized root and finite tensor
restriction. The existing compact wrapper `Etale.p1DecompositionSheafPullback`
in `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition` exposes those same
normalized maps without requiring noetherianity or any projective-line data.
Both owning landed nodes are cited. Only this normalized helper is used; the
projective-line decomposition theorem is not used.
The open lower-shriek, its adjunction, and comparison monoidality are the
published pro-etale framework, imported under their WeilConjectures paths.
`Scheme.Hom.EtaleFrame` is reused from
`WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion`.

### Edge cases

Checked c=0 (zero ideal, full support, unit), c=1 (single boundary), an empty
scheme (all section maps and coefficient comparisons still defined), a unit
function (empty individual support), a zero function (empty complementary open),
ramified levels with e not dividing n (m=ell^n remains valid), and non-open etale
frames (no use of an open embedding for F.e). Infinite Krull dimension is retained
in WithBot N-infinity; no subtraction of infinite dimensions occurs. Neither a
trivialization of roots nor a choice of primitive roots is assumed. The tuple is
ordered and no permutation invariance is asserted.

### Searches for an existing declaration

* msearch leanfinder, query describing the class of an etale frame as supported
  Kummer boundaries: hits on etale and smooth algebra loci, no cohomological class.
* msearch loogle, `frameClass, kummer`: unknown identifier `frameClass`.
* msearch grep, `frameClass|[Kk]ummer.*[Cc]lass|[Cc]lass.*[Ff]rame`: field-theoretic
  Kummer extensions and lattice frames, no exact class.
* msearch leansearch, `etale frame class supported Kummer boundary cup product`:
  commutative-algebra formal-etaleness results, no exact class.
* rg/grep over the named Mathlib, WeilConjectures and shared Sheaf trees, including
  the item id: upstream has the exact frame structure and an abstract
  `Etale.frameClass`. The latter assumes `HasKummerClass`/`HasTateTwist`, is on the
  etale site, and does not specify the concrete finite-coefficient boundary.
  Therefore it is not an exact attachment for this node. The existing frame
  structure itself is reused.
* Searches for frameEtalePullback/frameBoundary/PurityFrameClass in shared and
  upstream sources found no conflicting existing concrete construction. The
  root scalar map and normalized finite-twist pullback were found and reused.

No statement correction, disputed statement, or dependency replacement is needed.
The separate all-level Kummer notion is recorded below. All postponed proofs are named theorems with complete
natural-language proofs in their docstrings, and all data are actual constructions
or objects specified uniquely by their stated characterization.

## Second reading by NZ

The section delivered here was a short self-check, not a clause-by-clause
reading (delivery-errors H11). The maintainer's second reader replaced it with
this reading of node, source place and the three modules at 7be9f89c8299. No
Lean file and no node record was changed.

Source place: blueprint main-20261015
sec-six-functors-basics/sk-prop-a1-kummer/def-pur-frame-class.md (identical in
content to master sec-smooth-purity, order 1942).

Clauses of the node and their Lean (verdict for each):

1. Finite-field and coefficient datum, n >= 1, A = O_E/varpi^n, Lambda = A:
   `P : PurityFiniteSetting.{u}`, coefficients `ModuleCat.{u+1} P.Coefficient`
   (the size lift of the actual quotient). Correct.
2. k-schemes and V -> B smooth of relative dimension n: `b : B ⟶ Spec k`,
   `v : V ⟶ B`, `[SmoothOfRelativeDimension P.level v]`. The node and the source
   both use the same letter n for the level and the relative dimension; the Lean
   follows the node verbatim. The hypothesis is not used by the construction.
   Correct (see observation O1).
3. i : Z -> V closed immersion, Z -> B smooth: `[IsClosedImmersion i]`,
   `[Smooth (i ≫ v)]`. Correct.
4. Pure codimension c >= 0, dim O_{V,z} = dim O_{Z,z} + c with Krull dimension
   as supremum: `c : ℕ`, `_hcodim` with `ringKrullDim` in `WithBot ℕ∞` at
   `i z` and `z`. Infinite dimension allowed, no noetherian hypothesis. Correct.
5. Frame: etale e : U -> V, ordered f_1..f_c in Γ(U,O) generating the ideal of
   Z ×_V U: upstream `Scheme.Hom.EtaleFrame c i` (U, e, etale, `f : Fin c →
   Γ(U, ⊤)`, `toZ`, `isPullback` of the zero subscheme of `Set.range f` with i
   along e). The pullback square is exactly "the f_j generate the ideal sheaf
   of Z_U", scheme structure included; e is not an open immersion. Correct,
   and it reuses the existing frame structure (H4).
6. D_j = V(f_j), W_j = U \ D_j, f_j a unit on W_j via 1/f_j:
   `zeroLocusSubschemeι {f}`, `(basicOpen f).ι`, `basicOpenUnit f`
   (localization unit). Correct.
7. m = l^n, mA = 0, m invertible on W, without e | n: `diagonalExponent`,
   `diagonalExponent_annihilates`, `diagonalExponent_isUnit`. Correct.
8. A(1)_W ≅ mu_m ⊗_R A via theta, sigma(v) = theta^{-1}(v ⊗ 1): `frameTwist` is
   the comparison inverse image of `finiteEtaleTateSheaf A (l^n) W 1`, the same
   published root-line tensor model as the recorded finite interface
   (`diagonalTwistEtale`, `affineLinearBaseCoefficient`); sigma is
   `Etale.ordinaryFiniteRootMap` (z ↦ 1 ⊗ z). Correct; no generator chosen.
9. Kummer boundary delta_W of the actual Kummer sequence with G_m:
   `Scheme.kummerδ₀` (H^0 at the terminal object, then `Sheaf.H.δ` of
   `kummerSequence_shortExact`). Correct.
10. kappa_W(u) = H^1(sigma rho)(comp delta_W(u)) in H^1(W_proet, A(1)):
    `frameKummer` = exact `comparisonUpperStar` image of the module Ext class of
    H^1(sigma)(delta(u)). Since A(1)_proet is modelled as nu^{-1}A(1)_et, this is
    comp followed by H^1(sigma rho) by naturality. Correct.
11. alpha_j = boundary of the pair (U, D_j) applied to kappa_{W_j}(f_j|W_j), in
    H^2_{D_j}(U, A(1)): `frameBoundary` = Yoneda composite of the extension
    class of 0 → j_!A_W → A_U → i_*A_D → 0 with j_! of the Kummer class and the
    counit through the normalized twist pullback. Supported Hom from i_*A_D is
    the recorded supported-cohomology model; the Yoneda composite is the
    connecting map of Hom(-, I) applied to that sequence, i.e. of
    0 → Γ_D(I) → Γ(I) → Γ(W, I) → 0. Each factor has its own support. Correct
    (see observation O2 on the sign).
12. cl(f) = alpha_1 ∪ ... ∪ alpha_c, ordered and left-associated, in
    H^{2c}_{Z_U}(U, A(c)): `frameBoundaryProduct` recursion appends the last
    factor via the recorded `supportedCup`, transported along the unique
    intersection isomorphism V(f_1..f_d) ×_U V(f_{d+1}) ≅ V(f_1..f_{d+1}) over U,
    the K-flat-to-ordinary tensor map and the monoidal comparison of
    nu^{-1}, then 2d+2 = 2(d+1). Target support is the zero subscheme of the
    full tuple, which is Z_U through `F.isPullback`. Correct.
13. c = 0: empty tuple, Z_U = U, unit 1 in H^0_U(U, A): `frameEmptyClass` is the
    inverse of the (isomorphic) restriction A_U → i_*A_U in degree zero;
    `frameTwist U 0` is definitionally the constant sheaf. Correct.
14. Tensor of locally free lines agrees with derived tensor: the published
    `cupSingleTensorMap` is used. Correct.
15. No independence, existence or purity claim: none stated. Correct.

Edge cases: c = 0 (unit), c = 1 (unit cup alpha_1), empty U, f_j a unit
(empty D_j, alpha_j = 0 class), f_j = 0 (empty W_j), ramified levels with e ∤ n,
non-open etale e, infinite Krull dimension, repeated f_j (Set.range only enters
the support, the product uses the ordered tuple). All covered.

Universes: schemes in `u`, coefficient modules in `u+1`, the standard small
pro-etale site; no extra universe equation.

Postponed obligations (sorry, with proof docstrings): the unique intersection
isomorphism, its over-X equation, invertibility of restriction for the empty
tuple, 2d+2 = 2(d+1), the zero composite and short exactness of the coefficient
sequence. All are true; data are actual constructions or uniquely
characterized isomorphisms.

Searches: reran grep for `frameClass|kummerδ₀|supportedCup|EtaleFrame` over
the side and upstream trees: the only other frameClass is the abstract upstream
`Etale.frameClass` (HasKummerClass, etale site), not this concrete class.

New nodes `def-pur-frame-kummer-class` and `def-pur-frame-principal-boundary`
were read against the source paragraph: both genuinely absent elsewhere,
correctly stated, real data, cited dependency nodes exist and own the
declarations used (`ordinaryFiniteRootMap`, `p1DecompositionSheafPullback`).

Observations (no change): O1, the source reuses n for relative dimension and
coefficient level, the node keeps that, the Lean follows the node. O2, the sign
of the support boundary is the Yoneda/Ext connecting convention; the dependency
theorem is existential and fixes no sign.

Compile: `nt_compile.py --json` of the three modules, rc 0, no error or
warning (32.6 s, 23.8 s, 43.5 s).

## New nodes

`def-pur-frame-kummer-class`, module `Sheaf.Paper.PurityFrameKummer`, records
the concrete arbitrary-unit Kummer class at every positive finite level. The
existing affine-line datum assumes e divides n and the imported pur9 Kummer
class uses its admissible-level constant-root convention. Neither supplies this
node's all-level finite-field root-tensor prescription. The new definition
reuses the actual Kummer delta, the published scalar-extension root map, the
unique module/abelian comparison, exact pro-etale comparison, and normalized
finite-twist pullback. It adds no assumption or arbitrary map. Its statement
introduces all its objects and cites the existing owning nodes. The additional
normalized pullback wrapper was checked for dependency cycles: no path leads
back to the frame node. The main frame
class cites it and uses its `frameKummer` and normalized restriction helpers.
The item cites this independently specified arbitrary-unit construction and
uses its class on each complementary open.

The new-node searches were run with msearch LeanSearch, Loogle and Mathlib grep,
plus upstream and shared rg and blueprint_refs.py search. Their queries and
results are preserved in the new node's mathlib_searches. In particular no
Mathlib declaration gives this site/coefficient-specific class. The new module
has real data throughout and introduces no postponed theorem. The signature of
`frameKummer` binds P, W, the structure morphism, and the unit explicitly;
`frameTwistEtale`/`frameTwist` reuse existing finite tensor sheaves and their
canonical inverse image, with the universe fixed to the published u+1 module
size. The normalized pullbacks add no assumption on the morphism beyond being
a morphism over the finite field via the displayed structure composite.

`def-pur-frame-principal-boundary`, module
`Sheaf.Paper.PurityFramePrincipalBoundary`, separately records the individual
alpha_X(f) construction specified before the source's ordered product. The
recorded support long exact theorem provides its convention; this module exposes
the actual canonical map in the recorded supported-Hom presentation using the
coefficient extension, exact open extension by zero, and the counit. This is a
construction for every principal function, without a Cartier assumption. Existing
OrdinarySupportedKummerBoundary supplies a Cartier-normalization predicate and
Chern class, not this arbitrary-function construction. The new node lists all
seven helpers, including its two named proof obligations with full proof
docstrings. All prior clause and edge-case checks for frameBoundary apply here.
The searches and raw search-service results are recorded in this node. Its source
is precisely the individual-pair paragraph of the owning frame definition.

The final files separate the all-level Kummer class, one individual supported
boundary, and the ordered tuple product. Both new definitions are read together
with the main node in this self-check; the owning frame statement is unchanged.

## Saved-packet repair and validation

The resumed dry run found unowned `PurityFrameTest*.lean` scratch modules under
`lean/`. Retained these experiments as text files in `scratchpad/`, outside the
delivery module tree. Re-read the current blueprint frame definition, the three
modules and node records, finite coefficients, normalized root scalar and
pullback interfaces, supported cup and support exactness conventions. The
signature clauses and edge cases remain as matched above.

The full compile identified a kernel-checking timeout in the concrete
`frameCupNext` composite. The imports-only check passed in 3.6 seconds. The final
implementation calls the recorded `supportedCup` directly on degree-zero
sheaves via `frameCupSheaves`; `frameCupTransport` performs ordinary composition,
shift and degree conversion with abstract category objects. Both helpers are
listed in the owning node's lean.declarations and have source docstrings.
The maps, public frameClass signature, assumptions and conventions are unchanged.

The isolated direct specialization passed with a diagnostic bound of 20000
heartbeats (18.4 s and 15.3 s). All diagnostic commands and diagnostic limits are
outside delivered modules. The final packet is checked through deliver2.py with
the prescribed standard per-file limits.

All three final modules compiled cleanly in the full dry run. Its preflight
required `blueprint.from.via: []` for both new nodes, since the owning item is
itself a blueprint node; corrected that provenance metadata. Removed redundant
direct added dependency edges from the item: the new Kummer node already cites
the root-scalar and normalized-pullback owners. The original statement dependencies
are all retained, and the item directly cites both new definitions.
