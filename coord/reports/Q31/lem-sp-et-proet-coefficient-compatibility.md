## Worker report

The repaired delivery states `lem-sp-et-proet-coefficient-compatibility` in
`Sheaf.Paper.EtaleProEtaleCoefficientCompatibility`. The node is represented by six
named theorems, all with `sorry` proofs, and the canonical-map definitions with real
data. The repair defines the pro-etale arrow by transporting the actual recorded
`reductionDirectImageComparison` through the normalized coefficient realization.
The transport has its own definition node and source/blueprint docstrings.
The main theorem, refinement, composition, sum normalization, counit transport and
naturality declarations are all listed in `lean.declarations`. The original statement,
proof, and proof dependencies are unchanged. The recorded `def-sp-reduction-direct-image-comparison` node is now explicitly in
`stmt_deps`, alongside the fixed-coefficient and unbounded interfaces used here.

Source reading: Stacks `more-etale.tex`, remark-Rf-lower-shriek-change-of-rings (0GL6),
lemma-shriek-composition (0F7J), and refinement 0F7I; the current main-20261015
`sk-lem-sp-reduction-exceptional.proof.md`, Charts and Locality paragraphs. The node
expands the normalized coherence needed by those paragraphs; no claim is replaced by
an arbitrary morphism or an existentially chosen isomorphism.

Hypotheses, one by one:

- The field is `(k : Type u) [Field k] [CharP k p]`, with `0 < p`. The prime is
  `(ell : ℕ) [Fact ell.Prime]` and `p ≠ ell`. Positive characteristic of a field
  already forces that characteristic to be prime.
- Finite commutative rings in the site/coefficient, refinement, composition and
  counit theorems are `{A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]`.
  Their fixed-module presentations use `ULift.{u + 1, u} A`, `ULift.{u + 1, u} B`
  and the canonical lifted ring map `uliftRingHom φ`. The sum and naturality
  assertions retain arbitrary finite rings in `Type (u + 1)` because they use only
  the etale presentation. Every finite ring has a small representative, so this
  explicit presentation convention excludes no coefficient ring or morphism. The two explicit existential annihilation hypotheses are
  `∃ n : ℕ, ∀ x, (ell ^ n) • x = 0`. The map is exactly `(φ : A →+* B)`.
  There is no flatness, injectivity, surjectivity, nontriviality, or projective-dimension
  hypothesis on this map.
- Schemes have `[X.Over (Spec (.of k))]` and similarly for Y and, in composition, Z.
  Each structure map has `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated`.
  Morphisms have `IsOver (Spec (.of k))`, `IsSeparated`, `LocallyOfFiniteType`, and
  `QuasiCompact`, as the node's separated finite-type maps require. Compactifications
  are actual `Compactification f` objects, with their existing open/proper factors.
- The small sites are the existing `X.smallEtaleTopology` and
  `Scheme.ProEt.topology X`. Modules are ordinary `ModuleCat.{u + 1} (ULift.{u + 1, u} A)`-valued sheaves,
  the fixed-coefficient presentation of modules over the constant ring sheaf. The
  site objects remain in universe u+1 and site morphisms in u; they are never equated.
  Finite coefficient rings may be lifted into u+1, so this size convention excludes
  no finite coefficient ring.
- Bounded constructible finite-Tor input is exactly
  `AdjunctionTransfer.etaleProperty (ULift.{u + 1, u} A) X L.obj`, the conjunction of the existing
  `Etale.DerivedCategory.isBoundedConstructible` and `DerivedCategory.finiteTorAmplitude`.
  The `Plus` object retains its actual ambient derived complex. The witness `hLB`
  asserts a lower bound on the actual scalar extension of L; it neither supplies a
  replacement complex nor assumes a Tor-dimension bound for B over A. The sum and
  naturality assertions allow ambient objects directly with this same property.

Conclusions and named constructions, clause by clause:

1. The functors F are the existing
   `Etale.rightDerivedLowerShriekOfCompactification` and
   `ProEtale.rightDerivedLowerShriekOfCompactification`, applied to the supplied c.
   They are Rr_*j_!, rather than a separately postulated compact-support functor.
2. `etaleCoefficientMap` is the actual composite of `Etale.scalarMate φ c.g` and
   `Etale.properOpenCoefficientOpenIso φ c.i`. The first is the normalized proper
   counit mate, and the second is the unit-normalized open tensor identification.
   `proEtaleCoefficientMap φ c` is definitionally
   `transportedRecordedReductionDirectImageComparison φ c
   (reductionDirectImageComparison φ c.i c.g)`. Its definition applies the fully
   faithful inverse of postcomposition with `(sfIntrinsicDerivedEquivalence Y B).functor`
   to the intrinsic b, conjugated by `scalarPresentation` and `supportPresentation`.
   The intrinsic b occurs as a morphism in the composite. There is no independent
   fixed composite and no structure storing unrelated intrinsic and fixed arrows.
   Both IsIso and all pro-etale squares use this definition directly.
3. Scalar extension is `pbcFixedScalarExtension` (on the etale site its existing
   abbreviation `Etale.scalarExtension`), the published left adjoint to actual
   `Sheaf.derivedRestrictScalars`. The existing K-flat normalization identifies this
   with derived tensor extension. The site tensor iso delta is the existing
   `pbcComparisonReduction`, oriented by `.hom` from T_pro nu to nu T_et.
4. The site comparison c in the node is precisely
   `(compactSupportSiteComparison A c).inv`: that existing ambient iso is stored in
   the opposite direction. Its definition uses `fixedComparisonDirectImageMatePlus`
   and the open extension comparison, with Plus/ambient compatibility inserted.
   Consequently the requested site maps are isomorphisms by their type, rather than
   by an unrelated isomorphism-existence assumption.
5. `etaleProEtaleCoefficientCompatibility` states both `IsIso` assertions for beta
   and b and the exact scalar/site square. Reading Lean composition left-to-right,
   the first side is T_pro(c_A), then b(nu L), then F_pro,B(delta_X). The other side is
   delta_Y(F_et,A L), then nu(beta L), then c_B(L_B). This is the node's displayed
   equality with its actual named arrows and orientations.
6. `siteRefinement` is c_A^{-1}, nu(phi), c_A in the orientation from pro F_c nu L
   to pro F_d nu L; phi is the existing canonical etale compactification comparison.
   The `_refinement` theorem states the etale square for arbitrary c,d, and its
   pro-etale counterpart with the same named b. The terminal delta factors identify
   the actual scalar extension of nu L with the retained etale origin nu(L_B).
   This is the node's permitted etale-origin transport. Since c,d are unrestricted
   and phi has the existing cocycle, this includes comparison through any common
   refinement, with neither a map of compactifications nor a cartesian-refinement
   hypothesis added.
7. `etaleCompositor` uses the existing canonical changes from each supplied
   compactification to the chosen compactification, followed by
   `unboundedEtaleLowerShriekCompIso`, then change back to the supplied e.
   `compositionSiteBoundary` inserts the actual c_f,c_g and ambient/Plus
   compatibilities. `siteCompositor` conjugates the preceding etale compositor by
   this boundary and c_gf. Thus c intertwines these specific composition maps by
   construction, exactly as the node defines the etale-origin counterparts.
   The `_composition` theorem states both displayed coefficient equations for
   arbitrary composable f,g and arbitrary compactifications c,d,e. Its pro-etale
   side includes F_g,B(b_f) and b_g(F_f,A nu L), with the final delta identification.
   Identities are included among these morphisms; associativity and identity
   normalizations are those of the existing canonical compositor and its
   `unboundedEtaleLowerShriekCompIso_assoc` / `_units` laws, preserved under the
   specified conjugation. No alternate compositor is assumed.
8. `normalizedSumComparison` evaluates the recorded
   `Etale.EtaleCompactSupportNormalization.comparison`. Its Noetherian and compact
   hypotheses are supplied from finite type and quasi-compactness over the field,
   not added to the node. The theorem `_sum` quantifies over normalization structures
   satisfying that dependency's full graph/summand normalization, which the
   dependency supplies for all finite A and B. Thus it applies to the canonical
   normalized identification, without choosing a bare endpoint isomorphism.
   `sumCoefficientIso` is the exact sum/pullback adjunction conjugate of the existing
   scalar-restriction pullback comparison. Its right-hand comparison is identity on
   the underlying sheets, so its left-hand mate is the summandwise tensor map,
   computed termwise on a K-flat representative. The `_sum` equality is beta then
   c_e,B = T(c_e,A) then sigma, with the exact sum functor's derived category map.
9. The `_counit` theorem makes the node's conditional transport assertion explicit:
   `adjA` and `adjB` are actual adjunctions for the supplied etale F_c, and `_hCounit`
   is their coefficient-counit identity. The conclusion substitutes the actual b,
   delta, and compactSupportSiteComparison into the transported identity. Its last
   delta inverse lands in the scalar extension of nu N. The `etaleToPlus` origins
   come from the actual constructible finite-Tor objects HA(N), HB(TN). This is the
   counit formula used by `det-sp-et-proet-adjunction-transfer`, not a hypothesis
   asserting the desired pro-etale equality.
10. The `_naturality` theorem gives the objectwise beta naturality equation for every
    morphism between the stated input complexes. All other comparisons are existing
    NatTrans/NatIso or their objectwise canonical composites, hence retain their
    naturality. No choices of origins other than lower-bound proofs enter a map.

Dependency declarations used (their full signatures and source docstrings were read):

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField`, for the geometric setting; the theorem
  retains the explicit finite-type/separated-over-field data.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: finite coefficient realization;
  `WeilConjectures.AlgebraicGeometry.DerivedCategories`: ordinary derived categories;
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`: constructibility;
  `Sheaf.Paper.ProEtaleConstructibleSheaf` and
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`: intrinsic comparison predicates.
- `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`: `scalarExtensionFunctor` and its
  K-flat normalization and finite-Tor preservation;
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
- `Sheaf.Paper.WitnessCompatibility`: `pbcFixedScalarExtension`,
  `pbcRestriction_isRightAdjoint`, `pbcComparisonReduction`;
  `Sheaf.Paper.PurEtaleScalarMateProjection`: `Etale.scalarMate`, `scalarPullbackIso`;
  `Sheaf.Paper.ProperOpenCoefficientRefinement`: `properOpenCoefficientOpenIso`.
- `Sheaf.SecSmoothPurity.ReductionDirectImage`: `reductionDirectImage_isIso`;
  `Sheaf.SecSmoothPurity.ReductionDirectImageComparison`:
  `reductionDirectImageComparison`; `Sheaf.Paper.EtaleProEtaleCoefficientTransport`:
  `transportedRecordedReductionDirectImageComparison`, `scalarPresentation`,
  `supportPresentation` and `directImagePresentation`.
- `Sheaf.Paper.ComparisonPullbackExact`: `comparisonPullbackExact`;
  `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `fixedComparisonDirectImageMatePlus` and its counit normalization;
  `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`:
  `openImmersionLowerShriekComparisonUpperStarIso`;
  `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `compactSupportSiteComparison`, `compactSupportSiteComparisonPlus`.
- `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer`: `AdjunctionTransfer.etaleProperty`,
  `etaleToPlus`, the ambient normalized counit transfer.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: the compactification F and
  Plus compatibility; `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`:
  canonical refinement comparisons;
  `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`:
  `Etale.unboundedEtaleLowerShriekCompIso` and its agreement/coherence laws.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`: exact
  `Etale.etaleLowerShriek` and its upper-star adjunction;
  `Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization`:
  `Etale.EtaleCompactSupportNormalization`,
  `Etale.nonempty_etaleCompactSupportNormalization`.
- All recorded proof-dependency modules are imported (ordinary imports where only
  used by the proof plan). The theorem docstrings give the node's Steps 1--11 across
  the six conclusions: flat model, proper/open mate pasting, refinement and tower
  pasting, reflection of invertibility, sum normalization, and naturality.

Edge cases checked against the signatures and constructions: the zero complex; the
empty scheme and empty sheet sum; the zero coefficient ring (no `Nontrivial` is
imposed); exponent n=0 (which permits precisely the zero ring); identity coefficient
map; identity/open/proper morphisms and their identity compactifications; arbitrary
compactifications and common refinements; composable triples and the transported
canonical associativity law; nonflat coefficient maps such as ℤ/ell² → ℤ/ell. None
requires finite projective dimension. The sum adjunction preserves labels, including
zero summands; a zero input is admitted by the existing bounded-constructible and
Tor predicates. All variables and universes are explicit, with autoImplicit false.

Searches made before writing:

- `msearch.py ... leanfinder "Finite coefficient compact support etale proetale
  comparison commutes with scalar extension compactification refinement composition"`:
  eight unrelated finite-type/StandardEtale hits; no statement match.
- `msearch.py ... loogle "Functor, Adjunction, NatTrans"`: zero hits (the unqualified
  Adjunction name was not resolved). Corrected to
  `"CategoryTheory.mateEquiv, CategoryTheory.Adjunction"`: twelve hits, namely the
  Mathlib mates equivalence and its unit/counit/pasting lemmas. These supply the
  generic canonical construction, not this geometric compatibility theorem.
- `msearch.py ... grep "compactSupport.*[Cc]oefficient|coefficient.*[Rr]efinement"
  CategoryTheory`: no Mathlib match.
- `rg` in the slopmaster2 WeilConjectures source and shared `lean/Sheaf` for coefficient,
  compact-support, site-comparison, refinement and scalar-mate names located the
  dependency interfaces above. No single declaration states the requested square
  together with its refinement, composition, sum and counit normalizations.
- `grep -rn "lem-sp-et-proet-coefficient-compatibility"` in the slopmaster2 source:
  no match. The shared DAG and Lean were checked for exact duplicate names/notions;
  no new independent notion is needed.

No STATEMENT-DISPUTED issue or mathematical statement correction is proposed.
Only the Lean presentation of finite coefficients changes: the underlying finite
rings are small and their ordinary fixed-module sheaves use their canonical ULifts.
Site object and morphism universes are still u+1 and u respectively.

## Repairs of the return

R1: removed `RecordedReductionTransport`, the tautological intrinsic projection
lemma, the unused intrinsic alias and its duplicate IsIso theorem. Removed the
independent fixed direct-image/open composite. The replacement transport genuinely
conjugates the supplied b and takes its fully faithful preimage. The item definition
supplies the recorded `reductionDirectImageComparison`; every site square, refinement,
composition and counit statement evaluates that definition. No identification theorem
or arbitrary presentation isomorphism is assumed.

R3: the definition node now cites every construction it uses, and each citation is
in its stmt_deps. Its data are explicit composites, adjoint uniqueness maps and the
fully faithful preimage. Its only choices are from existing existence-and-uniqueness
theorems with complete section/unit or K-injective normalizations. `uliftRingHom`
is the existing RingHom.ulift specialized to the exact coefficient universes and has
a source docstring. The former summary search records are replaced by
actual tool results.

R2: this report removes all claims about the nonexistent
a transport equality theorem that was absent from the files; the final implementation
constructs the transported map directly and needs no such theorem.

R4: the dependency on `fixedScalarRestrictionOpenMap` is dropped entirely. The old
`CompactSupportRestrictionOfScalars` module is no longer imported. The scalar
presentation comparison uses the uniquely section-normalized theorem
`sfRealizationRestriction_existsUnique` via .exists.choose, not a plain mate definition
from a theorem node. The proper model change uses .exists.choose from
`openSquarePullbackModel_existsUnique` and right-adjoint uniqueness. The resulting
natural isomorphism is derived and followed by the recorded, K-injective-normalized
`sfIntrinsicDerivedDirectImageComparison`. Thus the two intrinsic direct-image models
are explicitly identified; they are not assumed definitionally equal.

## New nodes

`def-sp-et-proet-coefficient-transport` defines the genuine transport of an intrinsic
coefficient arrow through the canonical constant-coefficient realization. Its source
is Stacks 00YV/03D3/06YY/07A5 and the Charts paragraph of the current blueprint.
It assembles existing normalization interfaces into scalar and support presentation
isomorphisms and takes the fully faithful preimage of their conjugation of b.
The DAG and blueprint searches find no node for this assembled transport. Mathlib
provides generic fully faithful whiskering and preimages, not this geometric
construction. The source and side project provide the constituent comparisons.

## Second reading by Q31

I reopened the node, both final modules, the Stacks coefficient and composition
passages, and the blueprint Charts and Locality paragraphs. This is an in-session
second pass, with no other agent launched, as the dispatcher requires.

The geometric hypotheses remain precisely the field, prime, characteristic,
finite-type and separated hypotheses enumerated above. The coefficient hypotheses
remain finite commutative rings, arbitrary unital map, and power-of-ell annihilation.
The ULift is an explicit coefficient presentation, with the actual scalar action;
it imposes no flatness or projective-dimension bound. The input predicate is still
the existing bounded-constructible and finite-Tor conjunction.

The b clause now follows the supplied intrinsic arrow through the actual definition:
postcompose the fixed source with realization; undo its scalar presentation; undo
its support presentation; apply b at the realized input; apply the target scalar and
support presentations; take the inverse of the fully faithful postcomposition map.
Changing b therefore changes that composite. The boundary isomorphisms use canonical
section/unit and representative normalizations. There is no b-independent fixed
field. The main theorem's IsIso and square, both pro-etale refinement arrows, all
three composition arrows, and the pro-etale counit arrow use this same map.

The c and delta orientations match the node: c is the inverse of the recorded
compact-support site comparison, delta is the hom of pbcComparisonReduction.
Refinement still quantifies over arbitrary c,d; composition over arbitrary c,d,e;
their pro-etale counterparts are the stated etale-origin transports. The sum and
naturality assertions retain their existing etale maps and exact hypotheses. The
conditional counit assertion uses actual etale adjunctions and the coefficient
identity as its premise, and concludes the transported identity using the actual b.
All six postponed proofs still have their complete proof docstrings and the item
as their DAG node. The transport module itself postpones no theorem or data.

Edge cases checked again: zero rings, zero complexes, empty schemes/sums, identity
coefficient and scheme maps, nonflat finite ring maps, arbitrary refinements, and
the identity/associativity composition laws. The realization and adjunction units
used for transport exist in all these cases. Every variable/universe is explicit.

Validation: the final two modules compiled cleanly with scompile.py, separately
and in dependency order (transport 4.0 seconds, item 11.3 seconds; no diagnostics).
The first repaired-packet dry run also compiled both files and identified only a
combined citation bracket in the new definition statement; that bracket was split
into the exact individual dependency citations required by the preflight. The
metadata signatures and declaration lists were checked against both final files.
