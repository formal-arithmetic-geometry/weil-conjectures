## Worker report

Stage 2, Q147. The former worker's unchanged-item refusal was for stage 1. The live
item is stage-1 split/reviewed by Q80, has no Lean record, and is in the stage-2 queue.
No repair note or open return reopens its split. This delivery preserves the complete
accepted mathematical statement, proof, dependencies and metadata; it adds the Lean
record and the new definition dependencies needed to state it. No stage-1 delivery is
being repeated, and no library or launcher source was edited.

The main module is Sheaf.AlgebraicGeometry.RegularSpaceDivisorLineDictionary. Its
regularSpaceDivisorLineDictionary states all clauses with sorry. The three prerequisite
modules construct total fractions, Cartier and Weil divisors, rational generators,
associated lines and the local-equation/tensor normalization of flat pullback. Definition
data are explicit; only the named naturality/functor laws and flat preservation proof
obligations are sorry. Each has a source/proof docstring and is listed in the lean record
of its owning definition node, whose statement includes these construction laws.

Hypothesis and clause correspondence:

- X is AlgebraicSpace over Spec (ULift Z), the terminal scheme in the given universe.
  This is the absolute interpretation of algebraic spaces; no morphism to a specified
  extra base or chosen atlas is added. IsRegularNoetherianSeparated is compactness of
  the existing point topology, regularity including local Noetherianity of every etale
  scheme chart, and the existing IsSeparatedPresheafMap of the structure map to the
  terminal presheaf. Separatedness gives quasi-separatedness, so this is exactly the
  node's regular Noetherian separated hypothesis, including its absolute diagonal.
- Prime divisors are SpacePrimeDivisor: point classes having stalk Krull dimension one
  in an etale chart. On a regular Noetherian space reduced closures of these points
  are precisely the integral closed codimension-one subspaces; no closed-point or
  dimension-one-space hypothesis is substituted. SpaceWeilDivisor is their Finsupp Z.
- SpaceCartierDivisor is global sections of the sheafification of local K-units modulo
  the IMAGE of O-units. Sheafification is of the underlying Type-valued quotient;
  this is the underlying set of the quotient sheaf of abelian groups, without choosing
  an extra group structure. Cartier divisors need not have a global equation.
- The existential equivalence c is normalized by HasWeilDivisor on EVERY local equation
  and every chart codimension-one point. divisorChartOrder is the difference of the
  actual lengths of local numerator and denominator quotients, Ring.ord.toNat; at
  regular codimension-one stalks these are finite and are the normalized DVR order.
  The chosen localization sec supplies the actual numerator/denominator; no arbitrary
  valuation or meromorphic function map is assumed.
- Nonzero rational sections are SpaceRationalSection, isomorphisms from localized O
  to localized L. This is precisely a generator at all generic components. The second
  conjunct gives one for every IsLineModule. The function d has HasCartierDivisor:
  locally the divisor equation is the coefficient in a regular frame. Thus c(d L s)
  is exactly div(s), with the specified normalized orders.
- For every Cartier D (hence every Weil divisor by c), line D and sec D give a line
  and nonzero rational section. IsAssociated records an actual mono into K and local
  frames e sent to g inverse, with s=g e. Thus the subsheaf is g inverse times O,
  and s maps to 1. The identity d(line D)(sec D)=D gives the stated divisor D.
- The unique iso L ≅ line(d L s), with Preserves, is precisely the specified unique
  iso of rationally trivialized lines. Its direction agrees with the node.
- IsRegularGenerator is existence of an actual regular isomorphism O≅L whose canonical
  scalar extension equals THIS rational section. The iff with c(d L s)=0 therefore
  tests the given section, not just triviality of L.
- Dense-open uniqueness quantifies an open dense subset W of the existing point space.
  Equality is required on all affine etale basis charts whose images lie in W. This
  is the restriction of the two given maps to W. The conclusion is f=g.
- The scheme clause is IsLineModule L iff every schemeRestriction X T of L is the
  existing Scheme.Modules.IsInvertible. In particular the identity chart gives the
  usual scheme line module. It does not replace scheme modules by arbitrary sheaves.
- The final conjunct quantifies every regular Noetherian separated X' and every flat
  q:X'→X, with MapIsFlat from the existing chartwise scheme Flat predicate. pullD is
  normalized by IsFlatPullback: EVERY local fraction equation pulls back by the actual
  localization homomorphism of the flat coordinate-ring map. pullS is normalized by
  s=g e ↦ q(g)(1 tensor e), where divisorPullbackRegularSection uses the existing
  moduleTensorSection and fixed adjunction unit. It gives nonzero rational generators.
- The equation d'(q*L)(pullS L s)=pullD(d L s), transported by c and c', is the asserted
  div(q*s)=q*div(s). The unique iso q*(line D)≅line'(pullD D), with Preserves, is the
  required section-preserving comparison. Open restrictions and etale pullbacks are
  included since these maps are flat; their maps on equations are actual restriction,
  and the same local inverse-equation normalization gives the same comparisons. No
  relative dimension assumption, dominance, surjectivity or connectedness was added.

Dependency declarations read and reused:

- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicSpace, EtaleSite, etaleForget,
  structureSheaf, Modules, IsLineModule. Read the full declarations and documentation.
- Sheaf.AlgebraicGeometry.IsRegularScheme: IsRegularScheme = IsLocallyNoetherian ∧
  IsRegular. Mathlib.AlgebraicGeometry.Noetherian: IsLocallyNoetherian. The scheme
  Flat and its stalk criterion were read in Mathlib.AlgebraicGeometry.Morphisms.Flat.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible: Scheme.Modules.IsInvertible.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel: SmallEtaleModel,
  smallEtaleInclusion, smallStructureSheaf/Rings, smallModuleRestriction and equivalence.
  The small basis is in u; the full site's object universe remains u+1.
- Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology: Point, schemePointMap, the final
  point topology; Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal:
  IsSeparatedPresheafMap and diagonalPresheafMap, as the existing absolute diagonal test.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties: MapIsFlat and MapIsLocally.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: moduleTensorPullback,
  moduleTensorAdjunction and moduleTensorSection, with their complete normalized
  section-limit/adjunction definitions; no arbitrary functor or map is introduced.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction: schemeRestriction.
  The existing scheme/etale invertible-comparison, enlarged-site model, invertible
  descent and regular-local UFD modules are proof imports, not restated prerequisites.
  Proof dependencies without a usable current Lean attachment are not imported.

Sources and edge cases: read the current blueprint direct-images proof, clause (3),
which retains this supporting Picard branch through the proper-direct-image input.
Read spaces-divisors.tex at 0DMM, 0EN6/0EN7, 0EN9, 0ENA and 0EPQ, and the item proof.
The generic-section basis tuple includes disconnected components. Empty X gives empty
point type, zero Weil group and unique generator of the zero-on-empty module; empty
charts have zero coordinate ring, whose localization and unit group are still valid.
For a DVR with parameter t and D=n[closed], including n negative, g=t^n and the frame
is t^(-n), so the coefficient of 1 is t^n, giving n and the correct sign. A field has
no prime divisors and its rational generators are regular generators. A regular surface
V(x) is allowed; there is no curve-only local dimension hypothesis. A flat generic-field
map has no source prime divisor and still pulls back every equation. A ramified flat
map of traits sends t to u times pi^e; the length order multiplies by e. No assertion
of invariant orders for arbitrary flat maps was made; invariance is only the etale case.
The theorem takes no size equality between full-site objects and coefficient carriers.

Searches were run through the prescribed msearch.py; searches.jsonl preserves their
actual responses. LeanFinder queried the whole dictionary, total fractions/generators,
and inverse-equation/flat-pullback notions. LeanSearch queried total quotient sheaves
and Cartier/Weil divisors: its closest hit, totalQuotientPresheaf, is topological-space
presheaves, not this algebraic-space etale basis. Loogle AlgebraicGeometry.Scheme.Divisor
reported unknown identifier, not an established match; IsLocalization.map, Units.map
returned zero hits. Mathlib grep CartierDivisor|WeilDivisor|meromorphic in
AlgebraicGeometry and grep SpaceCartier|SpaceWeil|SpaceRationalSection|chartTotalFractionRing
returned zero hits. Read-only rg of both WeilConjectures and Sheaf found scheme
MeromorphicModule and smooth-connected-curve RationalSectionDivisor; their full
signatures were read and their stronger hypotheses do not represent this statement.
DAG definition searches and blueprint_refs search Cartier Weil / meromorphic algebraic
found no existing definition node for these algebraic-space notions. Existing small-site,
module, point and morphism-property definitions were reused. No statement correction
or STATEMENT-DISPUTED finding is needed.

## New nodes

- def-sfb-space-total-fractions owns SpaceTotalFractions. It defines the literal affine
  fraction presheaf and canonical sheafification, scalar extension, generator,
  regular-extension predicate and section-preserving morphism predicate. Stacks 0EN6,
  0EN7, 0ENA and 0EPQ supply the definitions. The actual searches described above found
  scheme constructions but no algebraic-space construction. Its helper theorems state
  exactly the preservation/naturality/identity/composition laws included in its node.
- def-sfb-space-divisors owns SpaceDivisorDefinitions. It defines regular Noetherian
  separated spaces using existing predicates, codimension-one cycles, the true sheaf
  quotient of units, local equations and rational coefficients. Sources: 0BE2, 0BE3,
  0B8Z, 0AGA and Spaces Divisors. The logged searches found no such existing interface.
  No data are chosen from a mere existence theorem; quotient maps and sheafification
  are actual constructions. Its helper laws are part of this node's statement.
- def-sfb-space-divisor-operations owns SpaceDivisorPullback. It defines the length
  orders, equation-normalized divisor relation, inverse-equation associated subsheaf
  predicate, flat fraction pullback and actual tensor normalization of rational
  pullback. Sources: 02MD, 0BE3, 0AGA, 0EN7 and 0EN9. The searches are recorded verbatim
  in each new node. The one supporting theorem is preservation of non-zero-divisors
  by the flat chart map, explicitly included in this definition node's statement.

## Second reading by Q147

This is the dispatched author's self-check, not a claim of independent review; the
maintainer's separate reader reviews the delivery. I reread the node and all four
modules together. The initial scratch theorem was replaced before delivery: absolute
separatedness uses the structure-map diagonal, quasi-compactness uses the existing
point topology, prime orders quantify every codimension-one chart point, generator
extension compares the given localized section, and dense-open equality evaluates
maps on the actual included etale basis objects. The final statement includes the
scheme interpretation and the full section-preserving flat comparison. The final
interfaces use no hollow hypothesis, no arbitrary valuation, no choice of unnormalized
comparison, and no private notation or auto-bound variable. The sign and empty cases
above were checked against each definition. The three new-node statements record all
the named construction proof obligations. The item's accepted split remains intact.
