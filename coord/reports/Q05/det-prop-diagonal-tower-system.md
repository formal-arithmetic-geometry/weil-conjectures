## Worker report

The delivery states `AlgebraicGeometry.ProEtale.exists_diagonalTowerSystem` in
`Sheaf.Paper.DiagonalTowerSystem`. Every theorem is postponed with `sorry`.
Definitions contain real data or universal-property specifications; no construction
is selected from a bare existence assertion.

Earlier main-module compilation repair: the two global instances `diagonalModuleSheafAbelian` and
`diagonalAbSheafAbelian` name the existing Mathlib abelian structures by
`inferInstance`, once for module-valued sheaves and once for abelian sheaves.
Their values are actual canonical structures; no choice, new category, size
restriction or hypothesis is introduced. Every original declaration, equation,
and all six `sorry` proofs remain byte-for-byte unchanged. Sharing these data
prevents nested-proof abstraction from repeatedly rebuilding sheafification
witnesses in the Ext expressions. This follows the implementation explanation in
upstream `WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`, lines
119–151. The earlier scratch experiments are absent from the delivery.

Hypotheses and objects:

- `Y : Scheme.{u}` is arbitrary. `Fact ℓ.Prime` supplies precisely primality, and
  `hY : IsUnit (ℓ : Γ(Y, ⊤))` is invertibility on Y.
- `diagonalSurface Y` is the existing scheme pullback of the two projective-line
  projections. `diagonalImmersion Y` is `pullback.diagonal`.
- `DiagonalAb W` is the abelian sheaf category on `Scheme.ProEt.topology W`.
  `diagonalComparisonUnits Y` is exactly `comparisonUpperStar` of the etale
  `gmSheaf`; it is not the sheaf of all pro-etale units.
- `DiagonalMod ℓ W` uses sheaves with values in modules over a universe lift of
  `PadicInt ℓ`. This is the standard fixed-scalar presentation of modules over the
  *constant* ring sheaf, not the pulled-back continuous-function ring.
  `DiagonalSystems ℓ W` is the genuine functor category `ℕᵒᵖ ⥤ DiagonalMod ℓ W`.
  The index n always denotes exponent n+1; exponent zero is never substituted.
- The `HasDerivedCategory` and `HasExt` instances only choose the common size of
  the localizations and Ext, as in the recorded abstract-derived-category interface.
  The site retains object universe u+1, morphism universe u, and values u+1.

Clause 1:
`diagonalIntegralSource` is closed direct image of the actual constant integer
sheaf. `diagonalIntegralBoundary` transports the already recorded relative Cartier
pole-extension class through exact comparison inverse image and the canonical
supported-constant comparison. Its minus sign makes its derived Hom the *positive*
projection roof required by this node: Mathlib's extension class uses the negative
cone projection. The existing pole specification fixes the complementary splitting,
the frame torsor of O(Delta), and t inverse mapping to +1; it retains all integral
powers, not just a simple pole. Thus the boundary is not an arbitrary supported
Ext class. `diagonalImmersion_cartier` states the regular local equations used by
this construction, with the complete chart argument in its docstring.

Clause 2:
`diagonalScalarExtension` is ordinary tensor from integer modules to Z_l-modules,
followed by sheafification, using Mathlib's integer-module equivalence and scalar
extension. `diagonalScalarAdjunction` is the actual insertion-of-one adjunction.
`DiagonalReductionPresentation` fixes E(M) at level n as the cokernel of
ℓ^(n+1) on that scalar extension, naturally in M. This is its tensor with
Z_l/ℓ^(n+1)=Z/ℓ^(n+1). `transition` requires the *quotient* transitions through the
same cokernel projections. This specifies the simultaneous ordinary tensor,
including its scalar actions and maps, by its universal property.
`DiagonalDerivedReduction` supplies a pointwise everywhere-defined left derived
functor T of this entire E, its universal counit, and its triangulated exactness.
Its target is D(strict systems), not systems in D.
`DiagonalCompletionSpec` specifies total right derived inverse limits RF (Z_l)
and RZ (integral) by their universal derived comparisons. An independently
specified integral simultaneous reduction I is the left derived functor of the
cokernels on the *identity* functor. Hence `I.T ⋙ RZ` is exactly
Rlim_n(K tensor^L Z/ℓ^(n+1)), the derived ℓ-completion formula of Tag 099M.
The natural isomorphism says forgetting scalars from `D.T ⋙ RF` gives the
integral formula, retaining its Z_l enhancement. Repair R2 adds two independent
requirements: each output C(K) receives only zero maps from every P for which
`IsIso (ℓ • 𝟙 P)`, and the natural `unit : 𝟭 _ ⟶ C` induces a bijection
`Hom(C(K),N) → Hom(K,N)` for every N with this same orthogonality property.
These are intrinsic derived ℓ-completeness and the universal completion-unit
property. All shifts are tested because P ranges over the whole unbounded
category, including its shifts. This is the principal nonzerodivisor criterion
for (ℓ) in Z, not an assumption on the input K and not ordinary completeness of
cohomology. It is the criterion spelled out in the published upstream
`Derived.DerivedCategory.derivedComplete_iff_rightOrthogonal` in
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Principal` (lines 290–298),
whose docstring cites Stacks 091Q/0999. We write the Hom criterion directly in
this existing abelian-group presentation; no universe transport to the
one-universe ringed-site `ConstantCompletion.IsComplete` is imposed.

Clause 3:
`a` in `DiagonalCycleSystemSpec` identifies T of the supported integral constant
with the degree-zero strict system `D.ordinary.E.obj (diagonalIntegralSource Y)`.
The equation for `a.hom` fixes it as `diagonalDerivedSingleCounit`, using the
universal counit and the standard single-complex comparisons. The level
isomorphisms s identify it with the *closed direct image* of the residue
constant, restricted through `diagonalResidueProjection`; their normalization
says the quotient unit is exactly `cartierProIntegralGenerator`.
`H` is a strict system of Z_l-module sheaves. The natural isomorphism `roots`
identifies its whole underlying diagram with the recorded
`Scheme.proEtaleRootsOfUnityTower`, including the power-ℓ transitions.
`b` identifies T(G_m[1]) with this system placed in degree -2. The finite t maps
preserve the actual root inclusions via `cartierProRootMap`, with no arbitrary
choice of a Tate-line automorphism.

Clause 4:
`c : Ext (D.ordinary.E.obj F) H 2` presents one actual morphism
`single F_system ⟶ (single H)[2]` via `Ext.homEquiv`. The equation for `c.hom`
is exactly `a.inv ≫ D.T.map partial ≫ b.hom`.
The final equality evaluates this Ext class by the exact evaluation functor,
transports it with the source and target identifications s and t, and equates it
in *Z_l-module Ext* with the existing `cartierResidueReducedPro` restricted from
Z/ℓ^(n+1). The latter is the full relative-normalized class of `sk-lem-geo-cartier`,
not merely a map with the right first-Chern composite. It is not an equality only
after forgetting coefficients. The proof docstring explains the uniform negative
Kummer identification compensating the positive roof projection.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`:
  `Scheme.proEtaleRootsOfUnityTower`, with its actual root kernels and transitions.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the recorded
  sheaf tensor framework, imported together with the scalar-tensor constructions.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, Q, and `singleFunctor`.
- `Mathlib.CategoryTheory.Functor.OfSequence`: the strict natural-number tower
  convention used by the recorded roots tower.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: its `lowerStar` direct-image
  presentation, compatible with `Scheme.proEtaleSheafDirectImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `comparisonUpperStar`, the
  coefficient version of the recorded geometric comparison adjunction.
- `Sheaf.CategoryTheory.RingedSiteModules`: the standard category interpreted by
  the fixed-scalar module-sheaf presentation; no replacement category is defined.
- `Sheaf.Paper.ProEtaleTateTwists`: the roots/finite-Tate convention, with its
  general nonfinite twists kept separate from this constant Z_l tower.
- `Sheaf.AlgebraicGeometry.GeoCartierCycleClass`: `geoCartierConstant`,
  `geoCartierLine`, and the full supported Cartier class interface.
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer` and `Sites.Gm`:
  `Scheme.gmSheaf`, `rootsOfUnitySheaf`, `kummerSequence` and exact Kummer.
- Definition dependency `def-sfb-cartier-reduction-data` records the already
  published definitions in `Sheaf.AlgebraicGeometry.CartierReductionSiteComparison`;
  `def-sp-cartier-pole-boundary` (`Sheaf.AlgebraicGeometry.CartierPoleBoundary`)
  supplies its relative boundary specification:
  `Etale.cartierPoleBoundary`, `cartierIntegralSourceIso`, `cartierResidue_cast`,
  `cartierResidueReducedPro`, `cartierProIntegralGenerator`, `cartierProRootMap`.
  These provide the canonical boundary and normalized finite comparisons.
  R1 replaces the unused comparison-theorem dependency with a definition-node
  record of these exact existing declarations. No declaration is copied.

Edge cases checked: arbitrary nonreduced bases are covered by the explicit
regularity arguments for b-a and 1-ab. Y may be empty; the zero global-section ring
still makes every relevant natural scalar a unit, and the constructions are zero
sheaves. Index 0 is exponent 1, so there is no incorrect μ_1 level. ℓ=2 is allowed.
The residue rings are nonzero for every prime and positive exponent. No countable
product exactness, boundedness, noetherianness, or choice of primitive roots is
assumed. The ℓ-adic coefficient ring here is discrete constant; no unjustified
identification of comparison units with all pro-etale units occurs.

Searches (2026-10-18):

- `msearch.py ... leanfinder "torsion diagonal cycle classes form one morphism of
  inverse systems derived ell completion"`: eight unrelated inverse-system and
  local-cohomology hits, no statement match.
- `msearch.py ... loogle "Functor.ofOpSequence, DerivedCategory, PadicInt"`:
  no hits, with Loogle reporting unknown `Functor.ofOpSequence`; the actual
  Mathlib declaration was checked directly in its recorded source.
- `msearch.py ... grep "diagonal.*(tower|system)|[Cc]artier.*[Ee]xtension"`:
  two unrelated root-system Cartan-matrix hits, no sheaf/tower statement.
- `rg` of the upstream WeilConjectures tree and side lean/Sheaf for the item id,
  diagonalTower, diagonal_tower, CartierExtension/cartierExtension and divisible
  extension: found the existing divisible-extension reduction and Cartier
  comparison interfaces, reused above; no existing statement of this node.
- `rg` of `dag/lean_names_upstream.json` and both source trees for the item id and
  proposed declaration names: no collision or exact existing match.

No statement correction and no STATEMENT-DISPUTED flag are needed. The existing
sign convention in the node's proof explains the signed boundary above.

Consumer-specialization justifications (R4, moved here by F1):

- `def-weil-sheaf-of-modules-category` remains NH's `ringedSiteModules`, with
  its original note and owning `RingedSiteModules.lean`. `DiagonalMod` uses
  Mathlib's fixed-scalar `Sheaf J (ModuleCat (ULift Z_l))` presentation of modules
  over the constant ring sheaf: constant scalar actions extend uniquely by local
  gluing; conversely one restricts the ring-sheaf action to constant sections.
  These inverse presentations preserve linear morphisms, sectionwise kernels
  and sheafified cokernels. This is a consumer presentation of the same notion.
- `def-pur-sheaf-tensor-product` remains Q46's record and owning
  `CochainTensorUniverses.lean`. `diagonalScalarExtension` implements the same
  balanced tensor by `ModuleCat.extendScalars` followed by sheafification, with
  the insertion-of-one adjunction. `DiagonalReductionPresentation` specifies
  tensor with each finite coefficient quotient by the cokernel universal
  property and quotient transitions. No additional tensor bifunctor is defined.
- `sk-def-sp-tate-twist` remains N4's record and owning
  `ProEtaleTateTwistsOfUniverses.lean`. Its finite first-twist specialization here
  is the actual `proEtaleRootsOfUnityTower` (power-ell transitions) and
  `geoCartierLine` at each finite residue ring. `cartierProRootMap` fixes the
  tensor generator and scalar action. The general nonfinite condensed-coefficient
  twist does not replace this discrete constant Z_l tower.

Repair F1 restores all three dependency-node files byte-identically to the
current newtargets-dag and removes the Dependency modules section. Thus the
delivery changes none of those landed records, their authorship, their module
ownership or their original §1(B) notes. The item lean.note contains these same
R4 justifications. All Lean declarations and the new definition node are retained.

## Second reading by Q05

I reopened the returned node, its source blueprint, the complete module, the new
definition record, and all three dependency records. The clause-by-clause reading
found the following matches and repairs.

- Hypotheses: “Y a scheme” is `Y : Scheme.{u}` with arbitrary u; primality is
  `[Fact ℓ.Prime]`; invertibility is exactly `hY : IsUnit (ℓ : Γ(Y, ⊤))`.
  The HasDerivedCategory/HasExt instances fix localization sizes only. W and
  Delta are the actual projective-line pullback and `pullback.diagonal`.
  No regularity, noetherianness, boundedness or nonempty-base hypothesis was added.
- Category convention: `DiagonalAb` is abelian sheaves on the actual small
  pro-etale site, `DiagonalMod` presents modules over the discrete constant
  Z_l sheaf, and `DiagonalSystems` is the strict functor category before taking
  its derived category. This retains the node's D(W^N), including its morphisms.
  The first index 0 means exponent 1. The coefficient ring is not the sheaf of
  continuous Z_l-valued functions.
- Clause 1: `diagonalIntegralSource` is Delta_* of the actual constant integers,
  and `diagonalComparisonUnits` is comparison inverse image of etale G_m.
  `diagonalIntegralBoundary` is minus the uniquely normalized relative pole Ext
  class transported by the canonical supported-source mate. The minus sign is
  required because the node specifies the positive roof projection whereas the
  imported Ext convention uses the negative projection. The underlying
  two-term complex is in degrees -1,0; the pole specification retains all
  integral powers, sends t inverse to +1 and fixes the complementary splitting.
  The new definition node reuses these exact maps; no comparison theorem is
  substituted for a definition (R1).
- Clause 2, tensor and exactness: the ordinary simultaneous reduction is fixed
  by the scalar-extension cokernels and quotient transitions. `T`, `ε`,
  `universal`, `pointwise` and `triangulated` state the everywhere-defined total
  left derived functor of this strict diagram functor and its exactness.
  `RF` and `RZ` are total right derived inverse limits. The returned file stopped
  at the natural isomorphism with the integral naive formula: that was a missing
  conclusion. It now also requires every C(K) to be intrinsically derived
  ℓ-complete, using right orthogonality to all ℓ-invertible complexes, and gives
  a natural unit universal for maps into every such complete N (R2). This is a
  reflector onto complete objects; the input K is unrestricted. In particular,
  the added assertion is meaningful for noncomplete K, unlike a hollow
  assertion that a displayed formula is isomorphic to itself.
- Clause 3, source: `a` is an isomorphism onto the degree-zero strict finite
  source system and its hom is the universal derived single-complex counit.
  The level maps `s` identify the levels with closed direct image of finite
  constant coefficients, and `DiagonalSourceNormalization` sends the quotient
  of integral 1 to the specified supported coefficient unit. Thus the source
  comparisons cannot independently rescale the finite cycles.
- Clause 3, target: `roots` identifies the whole underlying strict H diagram
  with `Scheme.proEtaleRootsOfUnityTower`, including zeta-to-zeta^ell transitions.
  `b` identifies T(G_m[1]) with H[2]; each `t` has the fixed roots-to-finite-Tate
  map after forgetting coefficients. The finite twist needed here is the roots
  tensor line, not the nonfinite condensed-coefficient twist. The dependency
  item note and Worker report state that specialization explicitly (R4/F1).
- Clause 4: `c.hom = a.inv ≫ D.T.map (diagonalIntegralBoundary Y).hom ≫ b.hom`
  is exactly the image of the integral arrow under the two identifications.
  Evaluation is exact; the final Ext equality conjugates its level by s and t
  and compares it with `cartierResidueReducedPro` after restriction from the
  residue coefficient ring to Z_l. This equality is in module Ext, with its
  positive Kummer normalization, and tests the entire supported arrow.
- New node: `def-sfb-cartier-reduction-data` names the already published
  pole boundary, supported-source mate, coefficient units, roots-to-line maps,
  residue ring and normalized reduced arrow. I read their full source
  signatures/docstrings and the blueprint's (G1) and derived reduction
  paragraphs. The data is fixed by constructions or unique Ext conditions.
  `existing: true` prevents duplicate definitions and leaves the published
  module intact. The comparison theorem is absent from the new node's list.
- Dependency records (F1): the module-category, sheaf-tensor and Tate-twist
  records are restored byte-identically to newtargets-dag. Their existing
  interfaces are usable; this delivery supplies no dependency module and makes
  no §1(B) rebind. NH, Q46 and N4 retain authorship, their owning files and their
  original notes. The consumer-specialization justifications below are in the
  item's lean.note and Worker report (R4).
- Edge cases: empty Y gives zero sheaves and is not excluded; the local diagonal
  equations remain regular over nonreduced bases; ℓ=2 is allowed. All levels
  have positive exponent. The completeness predicate tests all shifts and all
  unbounded P,N, and the universal unit is tested on every complete target,
  including zero and already-complete inputs. No exactness of ordinary
  countable products is assumed.

- Compilation repair: I compared the final module to the retained reviewed
  source. Removing the two new canonical-instance declarations recovers that
  source exactly. The instances use `inferInstance` before their own registration,
  hence reuse Mathlib's real structures. The theorem signature, universe binders,
  pole sign, completion reflector, strict-system identifications and normalized
  module-Ext equality are unchanged. No scratch helper, new assumption, profiler
  option or singleton wrapper remains.

R3 is repaired by this explicit hypothesis and clause matching. The changes above
address R1–R4; no source statement or target statement was corrected.

## New nodes

`def-sfb-cartier-reduction-data` records the canonical boundary and finite Cartier
reduction data used in clauses 1, 3 and 4. Its source is the blueprint Cartier
proof's (G1), opening comparison paragraph and derived reduction paragraphs.
The LeanSearch and LeanFinder queries recorded verbatim in `mathlib_searches`
returned eight unrelated hits each; Mathlib grep returned zero. Searching the
upstream tree returned no declaration, while side-source grep found all the
exact definitions in `Sheaf.AlgebraicGeometry.CartierReductionSiteComparison`.
The only DAG record listing them was the theorem node returned in R1;
`blueprint_refs.py search "Cartier pole"` found zero blueprint nodes.
Consequently the new definition node uses `existing: true`, with that module and
all seven declaration names requested by the return. It owns their definition
attribution without copying or moving a published declaration. The item cites
this node instead of the unused comparison theorem, as R1 explicitly directs.

## Validation

Repair F1 (2026-10-18): restored sk-def-sp-tate-twist,
def-pur-sheaf-tensor-product and def-weil-sheaf-of-modules-category byte-identically
to current newtargets-dag, preserving N4, Q46 and NH's owning files and notes.
The item lean.note and Worker report now carry the R4 specialization
justifications; the obsolete Dependency modules section is removed.

In the main module, the only Lean delta from the retained reviewed source is the two canonical
abelian-structure names described above. The main signature still matches
`lean.statement` verbatim; the original hypotheses, clauses, normalizations,
six postponed proofs and existing-definition node remain unchanged.
The first required saved-packet dry run failed at the 60-second per-file limit.
After diagnosing nested-proof abstraction in the sheaf abelian structures, the
minimal two-instance candidate passed both wrapper checks with no warning or
error; its library check reported 53.6 seconds. The fixed 60-second limit,
two-thread execution and prescribed `scompile.py` wrapper were retained.
The canonical delivery path and the complete packet are now checked again by
`scompile.py` and `deliver2.py --no-push` before pushing.


## Return L correction

R1: removed the spurious `lem-sp-cartier-reduction-site-comparison` statement
prerequisite. The diagonal module uses the canonical definitions recorded by
`def-sfb-cartier-reduction-data` and the pole-boundary definition node; it never
uses the comparison theorem. Those definition dependencies remain unchanged.

R2: restored `CartierReductionSiteComparison.lean` and its owning theorem node
byte-identically to the current published base. This removes all nineteen
irreducibility attributes and preserves Q54's original Lean record and ownership.
The verified identical dependency copies are omitted from the packet; the delivery
therefore retains their published base versions. Removed the corresponding repair
paragraph from the item's `lean.note` and the obsolete dependency-repair report
sections. The item module and new definition
node are unchanged from the retained packet, as requested by the return.

Self-check: reopened the item statement, the complete 478-line diagonal module,
and the new definition record. The hypotheses, four clauses, positive roof sign,
completion reflector, strict-system maps and normalized finite Ext equality still
match the clause-by-clause reading above. The theorem dependency withdrawal does
not change any Lean declaration or mathematical statement. Compilation and the
required dry run are repeated below before delivery.

Final correction validation (2026-10-18): the prescribed `scompile.py` invocation
passed with exit code 0 and no warnings or errors, using the unchanged published
Cartier import. The diagonal module took 41.3 seconds in the sandbox check and
40.7 seconds at its library path. The standard 60-second per-file limit and two
threads were retained. Exact-signature, six-sorry, permitted-field and preserved
source-hash checks passed before the dry run.
