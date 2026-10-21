## Worker report

The module Sheaf.Paper.WeilTateTwistFrobenius states
`WeilConjectures.wfTateTwist_closedFrobenius`, with its sole proof `sorry`.
It repairs the old module's reference to the no-longer-declared
`wfTateTwistLocalModel`. The helper now has real data: it specializes the existing
`FrobeniusCoefficientTwists.rationalWeilLine` to the finite coefficient stage.
No target or natural-language node statement changes. The only other node field
change is adding the already-landed `def-weil-frobenius-coefficient-twists` to
stmt_deps, because its exact canonical signed-line declaration is used directly.
No dependency node is changed and no new notion is defined.

Clause-by-clause correspondence:

- `D : FiniteFieldDatum.{u}` supplies p prime, a >= 1, q = p^a, a base field
  of cardinality q and its chosen algebraic closure. These are the actual fields
  D.k₀ and D.k, not independently chosen fields with an extra relation.
- `c : D.CoefficientDatum` supplies the prime ell, c.different : ell != p,
  and the chosen algebraic closure c.Qbar of Q_ell.
- `E : Padic.FiniteCoefficientFields c.l c.Qbar` supplies every finite
  intermediate extension. `pbcFiniteField.{u} c.l c.Qbar E` is the recorded
  Shrink coefficient model, algebra-isomorphic to E, and is also the coefficient
  field used by the recorded PBC twist. No coefficient extension is assumed
  unramified or equal to Q_ell.
- `X₀ : Over (Spec (.of D.k₀))` and the three instances IsSeparated,
  LocallyOfFiniteType and QuasiCompact on X₀.hom mean separated finite type.
  D.geometricFiber X₀ is exactly X₀ base-changed to D.k.
- `m : ℤ` includes all positive and negative twists and zero.
- The helper's `rationalWeilLine ... m` is the integral signed root lattice
  in degree zero followed by raw rationalization, with the prescribed root,
  tensor-unit, positive tensor and negative evaluation-dual structure maps.
  It is not a scalar-character substitute for the root construction.
- `x : {x : X₀.left // x ∈ closedPoints X₀.left}` ranges over all closed points.
  `ι` is a residue-field embedding into D.k and `hι` expresses k₀-linearity.
  Both are universally quantified, so no geometric lift is preferred or omitted.
- `localClosedFrobeniusCohomology ... x ι hι 0` is precisely the existing local
  geometric Frobenius on H^0 of the derived fibre. The integral line is in degree
  zero; its stalk in the node is this H^0. This operator uses the residue degree,
  the iterated Weil map and the semilinear geometric-point return.
- `Nat.card (X₀.left.residueField x.val)` is the actual Q_x, cast into the same
  coefficient model; `^ (-m) • 𝟙 _` states equality of endomorphisms with
  Q_x^{-m} times the identity, not just equality of traces or eigenvalues.

Exact relationship between the two coefficient presentations (source declarations
read in full): WfTateTwist.line unfolds to pbcTateLineSheaf, which is restriction
of `coefficientTwistLine ... (purTwistIntegralModule ...) m` along
`(purCoefficientIso ...).hom`. The framework's `integralTwistLine` is that same
coefficientTwistLine before coefficient restriction; sfIntegralTwistingObject
places it in degree zero. WfTateTwist.lineMap_exists fixes its map by HEq on every
adjunction-unit section to the very `FrobeniusCoefficientTwists.signedLineMaps`
used by rationalWeilLine. In the framework the completed pullback is compared to
ordinary transport by `completedToOrdinary`; rationalDerivedLineMap then
rationalizes this same map. Thus the helper gives the framework presentation of
the specified PBC line, retaining its root maps and lattice. The published
`rationalCoefficientCategoryComparison` identifies these presentations through
identity on integral representatives and localized maps and its finite-reduction
pullback comparison. It is imported for proof step 7; no arbitrary comparison
system or Nonempty equivalence is chosen in the helper.

Statement dependencies read and reused:

- Sheaf.Paper.WfTateTwist: WfTateTwist.line, lineMap_exists, integralLine,
  rationalLine, rationalLineMap, weilLine and functor. The node's recorded main
  functor is tensor with precisely these lines.
- Sheaf.Paper.WeilTensorProduct: wfTensorFrobenius, the completed tensor
  comparison followed by tensor of the given Weil maps.
- Sheaf.Paper.WeilInternalHom: wfInternalHomFrobenius, using the inverse first
  Weil map contravariantly, with the canonical derived Hom comparison.
- Sheaf.Paper.LocalFrobeniusTrace: localClosedPoint, localClosedPointDegree,
  localClosedFrobenius and localClosedFrobeniusCohomology, along with the recorded
  localFrobeniusTrace. Its chosen embedding/compatibility binders are retained.
- Sheaf.Paper.FrobeniusCoefficientTwistsCanonical:
  FrobeniusCoefficientTwists.rationalWeilLine, signedLineMaps,
  integralDerivedLineMap and rationalDerivedLineMap. These are existing data,
  not new copies of any line, root tower or tensor/Hom operation.

Every recorded proof dependency with a declaration is imported, including
WfTateTwistCompatibility and RationalCoefficientCategoryComparison (missing
from the old item's imports), primitive-root existence, roots inverse image,
ClosedPointField, point transport, its naturality and FiniteCoefficientPoint.
The theorem docstring carries all eight DAG proof steps.

Edge cases checked mathematically: m=0 gives the coefficient unit and scalar 1;
m=1 gives inverse cardinality; m=-1 gives cardinality through contravariant duality;
all larger positive and negative m retain their ordered tensors/duals. For a
closed point of degree d>1 the operator iterates d times, producing q^{-md},
not merely q^{-m}. The residue cardinality is finite and nonzero because x is
closed on a finite-type scheme over a finite field. Hence negative powers are
legitimate in characteristic-zero E. Ell=2 and ramified E impose no extra
condition. The empty scheme has no such x. There is no rational-point-only or
geometrically-connected restriction. Universes are explicitly bound by u and
`set_option autoImplicit false` is set.

Searches (2026-10-21, via prescribed msearch.py unless noted):

- LeanFinder, query "Geometric Frobenius on the stalk of an integer Tate twist
  E(m) over a finite field acts by the residue field cardinality to the power
  minus m": eight hits on Witt isocrystals and arithmetic Frobenius at primes;
  none states the finite-E pro-etale signed-line stalk theorem.
- Loogle, query `cyclotomicCharacter`: four hits defining the character and its
  value on roots/reductions; none states the sheaf stalk theorem.
- Mathlib grep, query `TateTwist|tateTwist|cyclotomicCharacter_frobenius`:
  zero hits.
- LeanSearch, query "Geometric Frobenius acts on the stalk of an l adic Tate
  twist by the residue cardinality to the negative twist power": eight hits,
  finite-field Frobenius formulas and Witt isocrystals; no matching theorem.
- rg in lean/WeilConjectures and lean/Sheaf, query
  `wfTateTwist|WfTateTwist|lem-wf-tate-twist-frobenius`: the old item module
  and its stale helper reference; current WfTateTwist and Compatibility;
  upstream WeilSheaf/StalkTateTwist.lean. Read upstream
  `stalk_frobenius_tateTwistSheaf` and its signature/docstring: it is the Qbar
  constant-twist WeilSheaf model, not this finite-E root-line/local-operator
  statement, so cannot be an existing:true attachment for the item.
- Direct signature searches through CoefficientTwistsDetailed,
  IntrinsicCoefficientTwistsUnrestricted, PbcCoefficientTwists and
  FrobeniusCoefficientTwistsCanonical found the exact existing integral signed
  lines and their canonical framework Weil structure used by the helper.

No statement dispute, new node, dependency-module replacement, or statement
correction is required. The stale helper reference was an interface fault in
the previous Lean module, repaired in this item module.

Validation: prescribed scompile.py compiled the module successfully in module
mode against the live published library; no errors or non-sorry warnings.

## Second reading by NL

This dispatcher brief forbids starting other agents and assigns independent
review to the maintainer. This section records the writing worker's second
pass, not an assertion of an independent worker review. I reopened the item,
its four original dependency records and their source declarations, then the
new helper and theorem. All finite-field and coefficient data, separated
finite-type hypotheses, all integer exponents, all closed points and all
geometric lifts appear in the binders above. The conclusion is the actual
local operator equal to Q_x^{-m} times identity on the degree-zero stalk.
The fault found in the old module was an undefined wfTateTwistLocalModel;
the repaired helper uses the existing signed-line lattice and canonical maps.
The old Qbar upstream stalk theorem is not substituted. Added the canonical
signed-line node to stmt_deps and its public import, and restored the two
missing proof imports. No further mismatch was found in this pass. The
maintainer's independent mathematical review remains the next review step.
