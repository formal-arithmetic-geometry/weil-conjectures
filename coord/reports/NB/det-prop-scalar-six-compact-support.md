## Worker report

The module `Sheaf.SixFunctors.ScalarSixCompactSupport` states
`AlgebraicGeometry.ProEtale.CondensedRing.scalarSixCompactSupport`, with proof `sorry`.
The three construction helpers have real data and introduce no independently chosen
comparison. No theorem is proved in this delivery. The mathematical statement is unchanged.

Hypothesis and clause correspondence:

- The prime ell is `(ell : ℕ) [Fact ell.Prime]`. The standing field is `(k : Type u)
  [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]`. Primality of its
  characteristic gives exactly positive characteristic different from ell.
- Standing schemes X and Y are objects of `Over (Spec (.of k))`, with
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on each structure map.
  Finite type is locally finite type plus quasi-compactness. The arrow `f : X ⟶ Y`
  is a k-morphism. There is no extra properness hypothesis on f.
- The coefficient rings are `ScalarSixRing.{u}` and their map is `a : Λ ⟶ Λ'` with
  `ListedCoefficientMap ell a`, the exact predicate used by the recorded direct-image
  dependency. It includes nonflat finite maps, continuous integral-to-finite maps,
  localization, finite field/integer extensions, the finite-subextension algebraic
  closure, identities and finite composites. No extra flatness is assumed.
- Every compactification is quantified as `c : Compactification f.left`. Its fields
  `c.i`, `c.g`, the open/proper instances and `c.comm` encode f = p j. The ambient
  object is exactly `rightDerivedLowerShriekOfCompactification Λ.X c` = D(j!) then Rp*.
- `K : ConstantModelConstructibleFiniteTor Λ.X X.left` is exactly the recorded Dctf,
  using finite constant local models, boundedness, and finite Tor amplitude.
- `scalarCompactSupportMap a c.i c.g` is the displayed composite. Its first factor
  is `scalarDirectImageMate a c.g` at D(j!)K; its second is Rp* of
  `derivedOpenImmersionShriekIso a.hom.hom c.i`. Associators only align parentheses.
- The first conjunction asserts `IsIso` of this specified component, together with
  `constantModelBoundedConstructible` and `DerivedCategory.finiteTorAmplitude` for
  BOTH endpoints over Λ'. Since Dctf is full, this is exactly an isomorphism in Dctf.
- Independence is the second conjunction: for every boundary compactification c,
  every dense compactification d and every boundary-preserving refinement `h : d.obj ⟶ c`,
  `T(ρ_h) ≫ C_d = C_c ≫ ρ'_h`. The morphisms ρ are precisely the existing
  `compactificationRefinementComponent`, not independently chosen isomorphisms.
  The source's common-refinement construction and `compactification_coherence_cocycle`
  identify the canonical comparison c1 to c2 with ρ1 followed by inverse ρ2.
  Pasting these two equations and cancelling ρ2 is exactly the full independence square.
  Arbitrary nondense c are included; schematic-closure normalization gives the same square.
  All compactifications in the first clause have quasi-compact open immersion in this
  setting, so packaging them as boundary objects loses none.
- Composition is the final conjunction, for every standing S, k-arrow g, models cf and
  cg, and dense boundary compactification cr of cf.g followed by cg.i. The displayed
  arrows m and m' are required to satisfy the published
  `compositionInterchangeIsNormalized` equations at j!K and j!TK. This is the actual
  identity-on-restriction condition, not an unconstrained map or an isomorphism assumption.
  `properOpenInterchange` supplies existence and uniqueness of these maps; quantifying
  over their normalized representatives therefore states the equation for the canonical
  arrows, without choosing from a mere existence assertion.
- `scalarCompactSupportModelComp` applies Rq* to m, the inverse
  `RootCoordinateFace.lowerComp`, and proper image of the canonical exact open compositor.
  `scalarCompactSupportOpenComp` is explicitly `Adjunction.leftAdjointUniq` for the
  actual open adjunctions and the actual derived pullback compositor. Thus this is the
  source's model compositor alpha, not an arbitrary endpoint isomorphism.
  The last equality is `T(alpha) ≫ C_gf = C_g ≫ H'_g(C_f) ≫ alpha'`.
  Independence from the second conjunction transports the model equation to every chosen
  model of gf and identifies it with compatibility with R(gf)! ≅ Rg! Rf!.

Dependency declarations read and used:

- `Sheaf.Paper.ExceptionalInverseImageExistence`:
  `AlgebraicGeometry.ProEtale.CondensedRing.exceptionalInverseImage_exists`; imported
  publicly as prescribed. It gives compactification lower shriek and Dctf preservation.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`:
  `coefficientMap`, `coefficientMap_id`, `coefficientMap_comp`, the coefficient compatibility
  equations, and `CondensedRing.derivedOpenImmersionShriekIso`. Scalar change is the
  existing ordinary derived extension, accessed by `scalarSixChange`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField`, `ProEtale.BoundedConstructible` and the
  compactification over-base interfaces. All geometry is explicitly bound as in this record.
- `Sheaf.Paper.FiniteConstantRingedLocalModel`, through
  `Sheaf.Paper.CondensedConstantConstructibility`: `constantModelBoundedConstructible`,
  `ConstantModelConstructibleFiniteTor`, and their finite constant local-model definitions.
- `Sheaf.SixFunctors.ScalarSixDirectImage`: `scalarSixDirectImage`, using its published
  `ScalarDirectImageMateCoherence.scalarDirectImageMate` construction (actual declaration
  `AlgebraicGeometry.ProEtale.CondensedRing.scalarDirectImageMate`).
- `Sheaf.SixFunctors.ScalarSixPullback`: `scalarSixPullback`; its ordinary open comparison
  is the upstream `derivedOpenImmersionShriekIso` cited above. A local wrapper
  `scalarSixOpenScalarIso` seen in the read checkout was unavailable in the server interface;
  using the recorded upstream declaration directly compiled cleanly. No duplicate was made.
- `Sheaf.Paper.CompactificationCoherenceCocycle`:
  `compactificationRefinementComponent` is the statement-level definition, now owned
  by `def-sfb-compactification-refinement-component`. The theorem
  `compactification_coherence_cocycle` supplies proof-level context only;
  `Sheaf.Compactification.BoundaryRefinement`: `BoundaryCompactification`,
  `DenseBoundaryCompactification` (quasi-compact opens, boundary-preserving morphisms).
- `Sheaf.Paper.ProEtaleProperOpenInterchange`:
  `compositionInterchangePullback`, `compositionInterchangeRestriction`, and
  `compositionInterchangeIsNormalized`, now owned by the new normalization definition
  node. The theorem `properOpenInterchange` supplies proof-level context only.
- `Sheaf.Paper.RootTowerCoordinateFace`: `RootCoordinateFace.lower`, `lowerComp`,
  normalized by the exact inverse-image adjunction; `lower` is the same ambient Rp*.

The additional statement dependencies are `sk-def-nagata-sketch-data`, the landed
`def-sfb-compactification-refinement-component`, and the new
`def-sfb-proper-open-interchange-normalization`. They supply precisely the
compactification data, refinement components, and normalization predicate used in
the Lean signature. The two theorem nodes formerly listed here have been removed
from `stmt_deps`; their conclusions are not hypotheses of the statement.

Proof imports: the stated direct-image, pullback, cocycle, compactification-localizing,
scalar-ctf, proper-open-section, and cofiltered-compactification modules are imported.
The three newly split coefficient-square proof nodes have no recorded modules yet, so
cannot be imported. The proof dependency `sk-lem-nagata-density-normalization` records
`Sheaf.Compactification.NagataDensityNormalization`, but its own `lean.note` says this
unreached module was deleted on 2026-10-20; it is omitted, not recreated. It supplies no
object needed to type this statement. Finite-type Noetherianity is Mathlib material.

Edge cases checked before and after writing:

- Empty schemes and zero K remain permitted by all binders; the comparison is between
  zero images. No nonempty scheme or nonzero coefficient hypothesis occurs.
- Zero finite rings and nonflat finite ring homomorphisms remain allowed by the existing
  `ListedCoefficientMap`. No preservation-of-finite-limits assumption on scalar extension
  or K-flat representative is added.
- Nondense compactifications are permitted, and refinement independence quantifies over
  a dense source to an arbitrary target model, as required by schematic closure.
- Identity geometric maps and identity open immersions remain allowed; open composition
  uses their same adjunctions. Identity coefficient maps remain allowed by the predicate.
- Composition g is arbitrary in the standing setting. The auxiliary cr is dense because
  that is the source's construction of the canonical proper/open compositor, not a
  restriction on f, g or their chosen compactifications. All such cr and all normalized
  arrows are quantified, so no auxiliary choice is frozen.
- All site/coefficient universes are the existing small-pro-etale internal-module universe
  u with Ab.{u+1}. No extra equality of unrelated universes is imposed.

Searches (fresh searches are recorded in sandbox searches.jsonl):

- `msearch.py leanfinder`: “Derived extension of scalars commutes with compactly supported
  direct image independently of compactification and compatibly with composition”:
  8 hits, ordinary ModuleCat extension-of-scalars coherence and compactly supported
  continuous maps; none states this theorem.
- `msearch.py loogle`: `CategoryTheory.mateEquiv`: 12 abstract mates/pasting hits;
  these construct the comparisons but do not assert this compact-support theorem.
- `msearch.py leansearch`: “Derived coefficient extension commutes with compactly supported
  sheaf cohomology”: 8 hits, generic sheaf cohomology, ordinary module pullback/sheafification,
  and unrelated topology; no match.
- `msearch.py grep`: `compactification|lowerShriek|coefficient.*comparison`, scoped to
  `Mathlib/AlgebraicGeometry`: 0 hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `scalar.*(compact|shriek)|compact.*scalar|coefficient.*(compact|shriek)` found the
  existing finite-coefficient comparisons, ordinary module-object scalar maps, and
  separate integral/rational realization theorems. These do not cover all listed
  condensed coefficient maps with this canonical mate and all three conclusions.
- `rg` in those two trees and `dag/lean_names_upstream.json` for
  `scalarSixCompactSupport|scalarCompactSupportComparison|ScalarSixCompact` found no
  declaration collision. Search for this node id in `lean/WeilConjectures` found none.

Sources: the latest blueprint item, latest unit coefficient list and latest proof were
read. The resolved repair note is stage 1 only; the accepted split is retained. There is
no mathematical statement correction and no STATEMENT-DISPUTED flag.

Validation: the repair reran scompile.py against the live server build and checked
both sandbox and library module modes cleanly (55.4 s and 29.1 s). The only postponed proof in this
module is the named theorem. All variables and universes are explicitly bound, and
all lines have at most 100 characters.

## Second reading by NB

The dispatcher expressly forbids starting another agent; this is a separate self-audit,
not a claim of independent review. The maintainer's independent review remains required.
I reopened the node, the latest source, and the entire file and checked the hypothesis
and clause correspondence above. In particular I checked orientations: the refinement
square is Tρ then C_d versus C_c then ρ', and the composition square is Talpha then C_gf
versus C_g then H'_g C_f then alpha'. Both match the source in diagrammatic order.
The open compositor uses the actual pullback comparison and left-adjoint uniqueness,
and m/m' satisfy the actual identity-on-restriction equation. These normalizations avoid
weakening either clause to unrelated isomorphisms. Source and target Dctf memberships
are both present. There are no extra flatness, properness-of-f, density-of-c, nonempty,
or bounded-representative assumptions. No statement mismatch was found in this reading.


## Repair of return 705fd9c15ed4

H2 is repaired at the definition level. In the item's `stmt_deps`,
`det-sf-comp-coherence-cocycle` is replaced by the already landed
`def-sfb-compactification-refinement-component`, and
`det-sf-comp-composition-interchange` is replaced by the new
`def-sfb-proper-open-interchange-normalization`. The new node has an `existing: true`
record for the three plain definitions in `Sheaf.Paper.ProEtaleProperOpenInterchange`.
The file and its Lean signature are unchanged, as requested by the return. In
particular no cocycle natural isomorphism is a statement parameter, and the
interchange arrows remain universally quantified subject to the actual normalization
equation; they are not selected from the theorem's unique-existence conclusion.
The node copy was refreshed from the current read-only base before reapplying the
reviewed Lean record and these repaired statement dependencies. The mathematical
statement, proof, proof dependencies, and maintainer-owned fields are preserved.

## New nodes

`def-sfb-proper-open-interchange-normalization` records the normalization equation
from the latest blueprint's composition-interchange proof, paragraph (2), used by
the compact-support proof's Composition paragraph. It introduces a commutative
condensed ring, arbitrary scheme morphism p, open immersion i, and boundary
compactification c of p followed by i, exactly the section parameters of the
existing declarations. `compositionInterchangePullback` is the canonical derived
pullback comparison from composition and the compactification equality;
`compositionInterchangeRestriction` is its adjoint mate followed by the counit.
For A and m of the stated source and target,
`compositionInterchangeIsNormalized` says precisely that the open-adjunction
adjunct of m followed by that restriction map equals Rp* of the j-open adjunction
unit. This is the normalization equation in the node, clause for clause. All three
existing definitions have real construction data, so no module or duplicate
construction is added. The primary signature is copied verbatim into the record.
The definition applies also to empty schemes, zero A, identity maps, nonproper p,
and nondense c; it asserts no existence, uniqueness, cartesianness, or invertibility.
The existing universe u and Ab.{u+1} are retained.

Fresh searches for this node are recorded verbatim as tool result summaries in
its `mathlib_searches`: LeanSearch for normalization by the open unit and canonical
restriction mate returned eight unrelated topology/adjunction results; LeanFinder
for the canonical derived proper/open restriction map returned eight ordinary
restriction results; Mathlib grep for
`compositionInterchange(IsNormalized|Pullback|Restriction)|properOpenInterchange`
returned zero hits. Project rg found exactly the three definitions in
`Sheaf/Paper/ProEtaleProperOpenInterchange.lean` (lines 73, 88, 107), no declarations
in WeilConjectures, and only consumers elsewhere. DAG searches found the theorem
record and a consumer, but no definition node owning these notions;
`blueprint_refs.py search` for both "interchange normalization" and
"compositionInterchangeIsNormalized" returned zero matches. Therefore the correct
reuse is a new DAG definition node pointing to the existing declarations, as the
maintainer requested.

Repair self-audit: reopened the new node and all three source definitions, checked
the mate and unit orientations, their section parameters, and the existing refinement
definition record. The repaired `stmt_deps` contain exactly the plain notions the
signature uses, and neither of the returned theorem dependencies remains in that
list. There is no statement correction and no disputed mathematical assertion.
