## Worker report

The module `Sheaf.Paper.IdentityOpenUnderivedSquareNormalization` states
`AlgebraicGeometry.ProEtale.CondensedRing.identity_open_underived_square_normalization`.
Its proof is `sorry`. Three helper definitions have real data: the conjunction
`IdentityOpenUnderivedNormalization`, and the two natural-isomorphism paths
`identityOpenSquareLeft` and `identityOpenSquareRight`. No mathematical statement
was corrected. The H2 repair adds two definition nodes with existing:true records; no
new module or dependency module is needed.

Hypotheses, clause by clause:

- The prime is `ℓ : ℕ` with `[Fact ℓ.Prime]`. The field is `k : Type u` with
  `[Field k] [CharP k p]`, `hp : 0 < p` and `hpℓ : p ≠ ℓ`.
- The admissible commutative condensed coefficient is the section variable
  `Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1}` with
  `[MonObj Λ] [IsCommMonObj Λ]` and `hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ`.
- All six schemes use `Scheme.{u}`, their structure morphisms to `Spec (.of k)`,
  and `LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated` instances. Every
  named arrow has `IsOver (Spec (.of k))`. Thus the small-site object/morphism
  universes remain u+1/u, and coefficients lie in u+1.
- The unprimed arrows are `h`, `j`, `i`; `j` is open and quasi-compact,
  `i` is open, and `hi : i ≫ h = j`. The specified identity-open identification
  is `hU : IsPullback i (𝟙 U) h j`. This is exactly the square identifying
  D ×_Z U with U, with its specified two projections, rather than a mere
  equality of underlying point sets. No properness or density is assumed.
- The base change is `sq : ChosenCartesianSquare w h' h v`; the open base
  change is `sqU : ChosenCartesianSquare vU j' j v`. These give both chosen
  fibre-product identifications and commutativity. `hi'` and `hw` express
  h'i'=j' and wi'=ivU. The resulting inclusions i',j' are explicitly open;
  the first conclusion states their identity-open pullback square. Their
  quasi-compactness follows from base change and need not be added as a
  hypothesis.

Conclusions, clause by clause:

- `IdentityOpenUnderivedNormalization Λ j i h hi` first asserts invertibility
  of the existing canonical `identityOpenRestriction` (the specified c_h),
  and of `identityOpenSectionArrow`. The canonical open-slice section
  coprojections are bijective. The next clause says that c_h sends a
  section to its restriction along the inverse fibre-product identification.
  This is the sectionwise identity under D ×_Z T ≅ T. Both sides are maps
  of the existing internal modules, so their ring actions are the specified
  restricted actions; no fresh scalar action is introduced.
- The a_h in every equation is the existing
  `identityOpenPullbackComparison Λ j i h hi`. Its body is
  `(upperStarComp Λ i h).symm ≪≫ upperStarCongr Λ hi`. Consequently this
  is precisely the inverse composition comparison with equality transport,
  with the recorded conjugate/composite-adjunction normalization.
- The sixth conjunct of the predicate is
  `j*.map (adj.unit.app M) ≫ c.app (h*.obj M) = a.inv.app M`.
- Its seventh conjunct expands the adjunct exactly as
  `adj.unit.app M ≫ h_*.map t` and states
  `j*.map (...) ≫ c.app N = a.inv.app M ≫ i*.map t`.
  Lean composition is diagrammatic, so these are the two printed equations.
- Its last conjunct states the tensor-unit normalization on every section:
  apply the actual h-adjunction unit at jV, restrict along the identity-open
  section arrow, take the i-slice coprojection, and apply a_h. The result is
  the j-slice coprojection of the original s. These are precisely the
  localized tensor generator 1 ⊗ s and s. Bijectivity of both slice
  coprojections ensures this is a normalization on all localized sections.
- The same predicate at `(j',i',h',hi')` gives every preceding clause,
  including both adjunct equations, on the primed configuration.
- `openCoherencePullbackSquare Λ sq.toCommSq` is theta;
  `openCoherencePullbackSquare Λ sqU.toCommSq` is s;
  `openCoherencePullbackSquare Λ (CommSq.mk hw)` is t0.
  The left helper is a_h' inverse, whiskered theta, then whiskered t0.
  The right helper is s followed by the vU-whiskered a_h inverse.
  The only extra arrows are canonical functor associators. Its component
  equality at every A is exactly the displayed square, naturally in A.
- `NatIso.mapHomologicalComplex` of those exact two paths gives the equality
  of chain maps on every unbounded cochain complex P. Finally
  `Functor.mapDerivedCategoryNatIso` of the same paths gives equality on
  every object of the ordinary unbounded derived category. Applying the
  canonical derived-composite factorization identifies this with the
  displayed square of termwise derived pullbacks, with precisely the same
  comparisons. There is no termwise descent of a nonexact direct image,
  completeness condition, boundedness restriction or choice of another map.

Dependency declarations used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `lowerStar`, `upperStar`, `upperStarLowerStarAdjunction`, `lowerStarComp`,
  `upperStarComp`; all in `AlgebraicGeometry.ProEtale.CondensedRing`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence`:
  `upperStarCongr`, `upperStarId`, and the conjugate/associativity normalization.
- `Sheaf.Paper.IdentityOpenDerivedRestriction`: `identityOpenRestriction`,
  `identityOpenSectionArrow`. `Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization`:
  `identityOpenPullbackComparison`. The added statement dependencies name
  the definition nodes `def-sfb-identity-open-restriction-arrows` and
  `def-sfb-identity-open-pullback-comparison`. The stronger theorems in those
  modules are not statement dependencies: all three constructions are plain
  definitions, not choices from a theorem. The new nodes depend only on
  existing definition nodes, so there is no DAG cycle.
- `def-sfb-open-square-restriction-mates` exports the existing
  `Sheaf.Paper.DerivedDirectImageOpenCoherence` constructions
  `openCoherencePullbackSquare`, `openCoherenceSectionCoprojection`,
  `derivedOpenCoherencePullbackSquare`. This landed node is added to stmt_deps.
- `Sheaf.Paper.LocalizingAdmissibleCoefficients`:
  `AlgebraicGeometry.ProEtale.IsLocalizingAdmissibleCoefficient`.
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare` and its `toCommSq`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`, `Morphisms.FiniteType` and
  `Morphisms.QuasiCompact`: `IsOpenImmersion`, `LocallyOfFiniteType`, `QuasiCompact`.
- `Mathlib.CategoryTheory.Adjunction.Basic`, `Mates` and `CompositionIso`:
  `Adjunction.comp`, `Adjunction.id`, `conjugateEquiv`, `conjugateIsoEquiv`,
  `Adjunction.leftAdjointCompIso`. The recorded general compositor is usable
  exactly as stated; the published `upperStarComp` is its specialization.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `moduleObjectDerivedPullback` is the total left derived upperStar. Its
  exact-functor identification justifies the termwise presentation used here.
  `NatIso.mapHomologicalComplex` is in Mathlib.Algebra.Homology.Additive;
  `Functor.mapDerivedCategoryNatIso` is the existing exact localization API.
- The recorded proof modules are imported without public: weakly-etale
  localization, section-module equivalence, general ringed-site localization,
  coefficient Cartesian comparison, universe-general pullback localization,
  exact condensed pullback and quasi-isomorphic K-injective derived resolutions.
  Their canonical comparisons and the proof steps are described in the
  theorem docstring; no new theorem is asserted for any of those dependencies.

Edge cases checked: U and U' may be empty; every quantifier still has its
correct meaning. The case h=identity and identity/arbitrary base change v
uses the same compositors and equality transports. Zero modules and the zero
coefficient ring require no exclusions. No density, properness, boundedness,
nonempty-site, finite-coefficient-only or site-universe-equality hypothesis
was introduced. The coefficient list is the already recorded admissibility
predicate, including its published algebraic-closure compatibility clauses.

Sources read: Stacks sites-modules.tex labels
lemma-localize-morphism-ringed-sites (04J0),
lemma-push-pull-composition-modules (03D8); sites-cohomology.tex
remark-base-change (07A7); the current main-20261015 blueprint
sk-thm-sf-comp-composition/det-sf-comp-composition-base-change.proof.md (3).
The exact module functors, adjunction, compositors, congruences, identity-open
maps and their docstrings were read before writing.

Searches actually made with msearch.py NR and this item:

- leanfinder: "restriction of module sheaf direct image to identity open locus
  adjunction unit and pullback composition square" returned eight hits,
  including Scheme.Modules.restrictAdjunction_unit_app_app and
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit.
  These concern different module realizations and do not state this theorem.
- loogle: "SheafOfModules.pullbackComp, CategoryTheory.Adjunction.leftAdjointCompIso"
  returned zero hits.
- grep: "identityOpen|identity_open|pullback_assoc" in
  Algebra/Category/ModuleCat/Sheaf returned pullback_assoc at line 193 of
  PullbackContinuous.lean, not the condensed-module specialization.
- leansearch: "sheaves of modules localization identity morphism canonical
  pullback comparison unit and base change associativity" returned eight
  results, including SheafOfModules.pullback_assoc and pullback unit laws;
  none is the full statement.
- rg in both lean/WeilConjectures and lean/Sheaf found the existing
  IdentityOpenDerivedRestriction, IdentityOpenDerivedAdjunctionNormalization
  and DerivedDirectImageOpenCoherence modules. They supply the canonical
  constructions but no theorem with this underived unit and square conclusion.
  Searching the item id in lean/WeilConjectures returned no match; searching
  all source roots and dag/lean_names_upstream.json for the proposed new
  declaration names returned no match.

Validation: all compilation uses scompile.py. Initially spelling every composite
inline made elaboration exceed the per-file limit. The two path definitions
remove that elaboration cost without changing any map; compilation then took
4.8 seconds in the sandbox and 4.3 seconds at its library module path, with no
errors or warnings. No limit was increased. All helpers are real constructions
and only the item's theorem is postponed. No STATEMENT-DISPUTED fault was found.

## Second reading by NR

The dispatcher prohibits starting another agent. This section records a separate
self-audit, not a claim of an independent second reader; the maintainer performs
the independent delivery review. I reopened the node and the finished file and
checked all six schemes and nine maps, the two Cartesian identifications, both
adjunct formulas, the sectionwise coefficient normalization and the orientations
of a_h, theta, s and t0. The audit changed the fully expanded square to two
named paths to share elaboration; expanding the definitions gives exactly the
same three-arrow left path and two-arrow right path. The complex and derived
clauses now apply those exact paths. Removed the unused j argument of the
left path and the unscoped heartbeat option. No statement discrepancy remains.

## New nodes

`def-sfb-identity-open-restriction-arrows` records the existing plain definitions
`identityOpenRestriction` and `identityOpenSectionArrow` in
`Sheaf.Paper.IdentityOpenDerivedRestriction`, without editing that module. Its
statement specifies the common-open base-change mate followed by the identity
direct-image comparison, and the site arrow with projections identity and i v.
The former uses arbitrary arrows with hi=j; the latter assumes precisely that
i and j are open. Neither claims invertibility. Source: Stacks 0D6G and the
identity-open parenthesis in blueprint composition base-change proof (3).
LeanSearch for canonical condensed-module restriction returned eight generic
restriction results, including Scheme.Modules.restrictFunctor; LeanFinder for
the common-open mate returned eight scheme-restriction results, beginning with
morphismRestrictRestrict. Neither gives these condensed-module constructions.
The exact-name Mathlib grep returned zero hits. Searches in WeilConjectures
returned none, while Sheaf found these exact definitions at lines 53 and 77.
A scan of all DAG definition-node lean records found no owner. Thus the new
node reuses the existing constructions through existing:true rather than
copying them or depending on the stronger derived-restriction theorem.

`def-sfb-identity-open-pullback-comparison` records the existing plain definition
`identityOpenPullbackComparison` in
`Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization`, without editing that
module. It is exactly the inverse upperStar compositor followed by transport
along hi=j, for arbitrary arrows. Source: the specified composition convention,
Stacks 09T5, and blueprint composition base-change proof (3). LeanSearch for
the inverse module-pullback compositor returned eight general results, including
SheafOfModules.conjugateEquiv_pullbackComp_inv and Scheme.Modules.pullbackComp.
LeanFinder for the comparison returned eight categorical pullback-object
results, beginning with Limits.map_lift_pullbackComparison. Exact-name grep
found no Mathlib or WeilConjectures definition; Sheaf found the existing plain
definition at line 50. No definition-node lean record owns it. This node uses
that exact existing construction, with no choice from the derived theorem.

Both nodes retain the arbitrary commutative condensed coefficient and scheme
universe u, with AddCommGrpCat in u+1. Blueprint searches for identity-open and
inverse composition comparison returned respectively one unrelated imported
node (cor-cbc-proper-coincidence) and zero nodes; the ancestor tool identifies
det-sf-comp-composition-base-change. Their statement dependencies are exactly
the definition nodes named in their self-contained TeX statements.

## Repair of return L at 89f8904b3961

H2 is repaired by replacing only the two delivery-added theorem statement
dependencies with the two new definition nodes above. The item still cites
def-sfb-open-square-restriction-mates for the other plain constructions. Its
Lean module, theorem signature, mathematical statement, proof and original
statement dependencies are unchanged. No assertion of either removed theorem
is used by the item statement. The unchanged modules remain imported because
they contain the three recorded plain definitions.

The separate NR self-reading was repeated on both new nodes and their full
source declarations/docstrings. The restriction has exactly the type
h_* ⋙ j^* → i^*; its data are the canonical mate, lowerStarId and right unitor.
The section arrow has precisely the object types in the node and is built
from pullback.lift, with the two stated projections. The comparison has type
h^* ⋙ i^* ≅ j^* and data (upperStarComp Λ i h).symm ≪≫ upperStarCongr Λ w.
In applicative mathematical order this is i^* h^* ≅ j^*. The unchanged item
uses these three constructions in its predicate and square paths. Empty
opens, identity h and arbitrary base change remain covered. There are no new
Lean declarations, proofs or assumptions.

Repair validation: scompile.py compiled the unchanged module cleanly in 4.8 seconds
in its sandbox namespace and 4.3 seconds at its library module path. The item
signature matches lean.statement verbatim. Comparing with current main shows
only lean and stmt_deps changed; every original statement dependency is retained,
and the added dependencies are definition nodes. Both new existing:true records
match their source signatures exactly and have no lean.file.
