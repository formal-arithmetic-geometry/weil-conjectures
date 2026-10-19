## Worker report

The module `Sheaf.Paper.PotentialRegularBaseChange` states all clauses of
`lem-per-potential-regular-base-change` in five named theorems, each with whole proof
`sorry` and the corresponding natural-language proof in its docstring. No mathematical
statement is corrected. The H2 repair adds two existing-declaration definition nodes;
no dependency module is needed.
`Coefficients` and `pull` are transparent abbreviations for the specified lifted
prime-power ring and the existing left-derived inverse image; they introduce no new
choice or operation.

Hypothesis and clause correspondence:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`; `(r : ℕ) (hr : 1 ≤ r)` gives the exponent.
  `Coefficients ℓ r = ULift (ZMod (ℓ ^ r))` is Z/ℓ^rZ at the small-etale coefficient
  universe u+1. This is a coefficient-size lift, not a field assumption; r>1 is included.
- X and Y are `Scheme.{u}`, with `[IsNoetherian X] [IsNoetherian Y]`.
  Excellence is exactly `∀ U : X.affineOpens, IsExcellent Γ(X,U)`, and likewise for Y,
  using the recorded `IsExcellent` definition. Invertibility of ℓ is
  `IsUnit (ℓ : Γ(X,⊤))` and its Y analogue. A global section is a unit precisely when
  its germ is a unit everywhere, so these are the stated Z[1/ℓ]-schemes.
- Regularity of `(p : Y ⟶ X)` is `[Flat p]` and `hreg`: every canonical scheme fibre
  after every finite extension k' of κ(x) is `IsRegularScheme`. The identity extension
  is included. This is the same finite-extension test used by the recorded
  `isIso_derivedBaseChangeMapPlus_of_regular`; it is geometric regularity over a field,
  without imposing finite type or smoothness of p.
- L lies in the ordinary ambient derived category of small-etale constant-coefficient
  module sheaves, with `DerivedCategory.isBoundedConstructible ... L`. Q and K are
  `DerivedCategory.Plus` objects, and `.obj` takes their underlying ambient objects.
  There is no upper bound or constructibility assumption on Q or K.
- `regular_internalHom` asserts `IsIso (etaleInternalHomPullbackComparison ... p L Q.obj)`.
  This existing map is literally the tensor-Hom transpose of pulled-back evaluation
  after the inverse of `leftDerivedUpperStarTensorIso`. Consequently its evaluation
  compatibility is part of the named map, rather than an arbitrary isomorphism of its
  endpoints. This renders the first map and evaluation clause of the node.
- For the biduality clause, `CoefficientChangeDualizing.dual R X K` is the recorded
  `derivedHom` with target K. `CoefficientChangeDualizing.biduality` is exactly the
  transpose of evaluation after the canonical signed symmetry. `regular_biduality`
  assumes constructibility of L and its K-dual, and asserts isomorphisms b and c whose
  homs are the two actual canonical comparisons. Its equation is
  `p*.map eta_L ≫ c.hom ≫ D_(p*K).map b.inv.op = eta_(p*L)`.
  Thus c followed by dual of b inverse gives the stated double-dual identification
  and identifies the arrows. K is not assumed dualizing and has no pinnings.
- `pullback_exact_constructible` asserts finite-limit and finite-colimit preservation
  for `upperStar` (exactness in these abelian categories), and preservation of the
  recorded bounded-constructible object property by `pull`. The latter is the
  left-derived functor of that exact inverse image, canonically identified with its
  termwise map by `leftDerivedUpperStarIsoMapDerivedCategory`. As Step 1 of the node
  explicitly observes, this clause holds for every scheme map and needs no regularity.
- `strict_localization_geometry` uses the dependency's actual
  `Scheme.strictHenselizationScheme s` and its canonical structural morphism. It states
  flatness, Noetherianity, excellence on every affine open, and finite topological and
  ring Krull dimension using the two recorded dimension notions. Its final universal
  fibre condition is precisely the same geometric regularity test as hreg.
- `isIso_of_strict_localizations` quantifies over every algebraically closed Ω and
  geometric point s and asks for invertibility of the actual pullback of a morphism a.
  It concludes `IsIso a`, for arbitrary ambient etale derived objects M and N; neither
  boundedness nor constructibility is added.

Dependency interfaces read and used:

- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent` and its catenary/G-ring/J-2 data.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`, finite-value constructible cohomology
  and a bounded cohomological interval in `DerivedCategoryModule`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`: the generic ringed-site
  localization and its public ordinary-etale `Etale.derivedHom` and
  `Etale.derivedTensorHomAdjunction` specialization.
- `Sheaf.AlgebraicGeometry.StrictHenselization`: `Scheme.strictHenselizationRing`,
  `strictHenselizationScheme`, and the small affine pointed-neighbourhood colimit.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`; and
  `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- Existing landed nodes added to stmt_deps for the exact helpers consumed:
  `def-weil-pbc-strict-henselization-structural-map`, using the recorded upstream
  `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap` declaration;
  `def-per-etale-hom-pullback-comparison`, using
  `Sheaf.SixFunctors.EtaleGenericHomTriangle.etaleInternalHomPullbackComparison`
  (the declaration namespace is `AlgebraicGeometry.Etale`);
  `def-per-etale-relative-biduality`, using the existing `dual` and `biduality`
  definitions from `Sheaf.Paper.CoefficientChangeDualizing`; and
  `def-weil-regular-scheme`, using `AlgebraicGeometry.IsRegularScheme`.
  These add no hypothesis from the larger theorems owning those helpers.

Every available recorded proof-dependency module is imported without `public`.
The already-public constructibility and dimension modules are not imported twice.
The two not-yet-stated nodes `lem-per-etale-internal-hom-localization` and
`lem-per-regular-supported-base-change` have no recorded module to import; their
proof roles are retained explicitly in the docstrings. No theorem from them is
assumed as an extra hypothesis.

Sources read: the node and every stmt_dep statement and record; the exact declarations
and docstrings listed above, including `scompile.py --source` for the current upstream
strict-local structural map; ILO XVII printed pp. 281--282 (Proposition 4.2.2 and
its constant/lisse/open-closed devissage), p. 296 (Proposition the project server and the formal
bidual comparison), and the opening strict-local reduction of §6.5. The full node
proof is distributed as Steps 1--7, 8, 1, 9--10, and 11 among the five theorem docstrings.

Edge cases checked before writing: empty X or Y (zero sheaf/derived category; strict
local testing is vacuous only on empty X), zero L/Q/K, r=1 and r>1, nonperfect finite
modules over Z/ℓ² (no finite-projective-dimension assumption), p the identity, finite
residue extensions including the identity, arbitrary lower bounds on Q and K,
unbounded M and N in the conservativity clause, and nonreduced schemes. All site
object/Hom universes remain u+1/u; coefficient modules are in u+1, geometric fields
and schemes are in u. No independent smaller test-field universe is used.

Searches (actual wrapper results are retained in searches.jsonl):

- LeanFinder: "Regular pullback commutes with derived internal Hom of constructible
  etale complexes and biduality; strict localizations detect isomorphisms" returned
  eight generic module-pullback comparison results, none this statement.
- Loogle: "AlgebraicGeometry.Etale.derivedHom, AlgebraicGeometry.Etale.pullback"
  returned no hits (the remote index does not know the project-specific derivedHom).
- LeanSearch: "regular morphism etale derived internal Hom constructible base change"
  returned eight generic etale/base-change results, none this statement.
- msearch grep: `regular.*[Hh]om|[Hh]om.*regular`, Mathlib AlgebraicGeometry, no hits.
- rg of upstream WeilConjectures and lean/Sheaf for regular/Hom, pullback/biduality,
  canonical comparison, and strictHenselization; upstream blueprint-id grep returned
  no exact target match. The project search found the exact canonical helper
  `etaleInternalHomPullbackComparison`, and the existing `dual`/`biduality` definitions,
  so those are imported, not copied. The regular direct-image theorem is not the
  internal-Hom assertion. Upstream perfect/dualizable pullback is a different special
  case and does not cover all bounded constructible L over prime-power coefficients.
- `dag/lean_names_upstream.json` was searched for the item's id; no attachment found.

No STATEMENT-DISPUTED issue was found.

## Second reading by Q114

Author's separate second reading, with the node and final source open; the dispatched
brief prohibits starting another agent, so the maintainer supplies independent review.
Checked every hypothesis and conclusion against the correspondence above. In particular
both constructibility hypotheses are present only where needed for biduality; K is
bounded below but arbitrary; the comparison homs are fixed to the existing evaluation
transpose, and the final equation has the contravariant inverse b in the right direction.
The strict-local clause includes finite dimension as well as flat and geometrically
regular fibres. The testing morphism is arbitrary in the unbounded category. The
coefficient ring is lifted Z/ℓ^r, not a field; the primality fact is an instance so Lean
can infer finiteness, with exactly the same mathematical hypothesis. Replaced the older
library-side structural-map import by the node's recorded upstream import to avoid
having two versions of the same declaration. No node statement was changed.


## New nodes

`def-per-etale-hom-pullback-comparison` owns the existing concrete definition
`AlgebraicGeometry.Etale.etaleInternalHomPullbackComparison` in
`Sheaf.SixFunctors.EtaleGenericHomTriangle`, recorded with `existing: true`.
Its statement defines the canonical comparison as the actual transpose of inverse
canonical tensor comparison followed by pulled-back evaluation (ILO XVII 4.2.2,
pp. 281--282). It requires only a finite commutative coefficient ring and arbitrary
scheme morphism and derived objects. The declaration has exactly these binders:
`A : Type (u+1)`, `[CommRing A] [Finite A]`, schemes in u, `g`, `K`, `M`.
The finite-ring condition permits every lifted Z/ell^r ring in the item.
The source and exact signature/body were read. Three fresh search kinds (LeanSearch,
LeanFinder, Mathlib grep), project/DAG search, and blueprint search are recorded
verbatim in its `mathlib_searches`. The existing shifted-Hom-set pullback definition
`def-per-derived-hom-pullback` is a different object. No definition node currently
owns this ordinary-etale internal-Hom comparison. No new Lean module is written.

`def-per-etale-relative-biduality` owns the existing `dual` abbreviation and
`biduality` construction in `Sheaf.Paper.CoefficientChangeDualizing`, recorded with
`existing: true`. Its source is ILO XVII the project server (p. 296), the canonical relative-dual
and biduality identification. It quantifies over every commutative R in u+1,
scheme X in u and arbitrary K,M. `dual` is the flip of derivedHom with target K;
`biduality` is homEquiv of signed symmetry followed by the evaluation counit.
The transpose uses tensoring on the left by D_K M, so its pairing has source
D_K M tensor M, swaps to M tensor D_K M, then evaluates. This is precisely the
existing Lean body and has no dualizing or boundedness assumption. Three fresh
search kinds, project/DAG and blueprint searches are recorded in its node.
I checked `etaleEvaluationBiduality` in
`Sheaf.Paper.DualizingLocallyClosedInheritance` (the alternate already-existing
arrow identified by the return): its body agrees after unfolding dual, and no
definition-node record owns it. The landed `def-per-ringed-site-bidual-transpose`
is for an explicitly supplied generic normalized ringed-site model and its
naturality, rather than the fixed ordinary-etale derivedModule presentation and
adjunction consumed here. This new node records the already-existing specialization;
it creates no duplicate construction. Its dependencies record the canonical
signed symmetry (`lem-kun-tensor-sym` exposes the actual natural iso, not just
existence), the tensor, Hom/adjunction and ordinary-etale derived category.

## Repair of returned head acbf27a5e59d

The initial saved-packet dry run passed (commit e4764db8e5), confirming the preserved
Lean module still compiles, but the packet still had the H2 ownership defect in the
return. Replaced `lem-sf-etale-generic-hom-triangle` and
`lem-per-coefficient-change-dualizing` in stmt_deps by the two definition nodes
above. Neither theorem supplies data by choice, and neither theorem is assumed
by the statement. Kept all mathematical statements, proof steps and proof_deps
unchanged; the five theorem signatures and the Lean module are unchanged.
The current shared item has the same mathematical statement and proof as the
saved packet, with no landed Lean record; new records are based on that current DAG.

Second reading of this repair by Q114, performed directly because the dispatcher
forbids sub-agents: read both new statements and the exact declaration bodies.
Verified the tensor comparison is inverted before evaluation, both Hom variables
have the correct variance, the dual functor has the exact arbitrary target K,
and the biduality transpose uses the same signed symmetry and adjunction counit.
No data, theorem assumption, universe restriction or clause was added to the item.
The earlier clause-by-clause second reading remains applicable to the byte-identical
Lean module. The maintainer's independent review supplies the independent reading.
