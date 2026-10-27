## Worker report

The module `Sheaf.Paper.ProperFiniteNormalization` states all clauses of
`lem-weil-proper-finite-normalization`, using the existing canonical maps. It has
three postponed theorems, each a clause of this DAG node, and three concrete recipe
definitions. There is no new notion, dependency repair, or statement correction.

Source read: `literature/blueprint/latest/blueprint/sec-zeta-weil/sk-input-weights/
prop-weil-proper-compact-coincidence.proof.md`, first paragraph. This explicitly
uses the identity compactification and the compactification-independent finite
comparison. The node's five proof steps give its more explicit normalization,
refinement, and quotient compatibility requirements; these are retained.

Hypothesis-by-hypothesis correspondence:

- `P : WeilConjectures.PurityFiniteSetting.{u}` has `field : FiniteFieldDatum`,
  including p, a >= 1, q = p^a, the finite field k0 and its algebraic closure k.
  `P.coefficients : P.field.CoefficientDatum` supplies the prime l, l != p, and
  the fixed algebraic closure Omega of Padic l. `P.extension` is literally an
  intermediate field of Omega finite-dimensional over Padic l. Thus it is the
  specified E subset Omega, rather than an unrelated field extension.
- `P.Ring` is definitionally `Padic.coefficientExtensionRing
  P.coefficients.l P.extension P.level`. Its integer ring, uniformizer, ideal
  and quotient are the already recorded Padic constructions. `P.level_pos`
  retains n >= 1. `properNextLevel` changes just the exponent to n+1, so its
  ring is A_(n+1), with the same E and uniformizer; twice gives A_(n+2).
  Quantification over all P covers every positive level, prime, and finite
  subextension. The setting carries no Kummer divisibility assumption.
- `X Y : Scheme.{u}` are arbitrary schemes in the same unrestricted universe.
  In each theorem, `aX`, `aY` are their structure maps to Spec P.field.k.
  `IsSeparated aX`, `LocallyOfFiniteType aX`, `QuasiCompact aX`, and the three
  analogous instances for aY mean separated finite-type k-schemes.
  The explicit structure maps support the two maps over the same base and
  their compatibility `_hf : f ≫ aY = aX`.
- `f : X ⟶ Y` with `[IsProper f]` is the proper k-morphism, not an assumed
  proper structure map. Properness supplies separatedness and finite type
  of f; it does not impose properness over k on X or Y.

Clause-by-clause correspondence:

- The identity compactification is exactly `Compactification.ofIsProper f`;
  its i is identity, its g is f. The sheaf identification a_n is the existing
  `sfIntrinsicOpenId P.Ring X`, uniquely normalized by the open adjunction and
  identity restriction. `sfIntrinsicDerivedOpenId` applies its maps termwise
  and descends to D; `properFiniteIdentityNormalization P.Ring f` then whiskers it
  by ordinary `proEtaleConstantDerivedDirectImage f P.Ring` and the unitor.
  The identity-open construction is reused from its defining module;
  properFiniteIdentityNormalization is the explicit whiskering recipe in this item.
  They give alpha^0 on the whole unbounded category.
- `properFiniteComparison f c` is, by its actual body, the existing
  `P.clopenSupportCanonicalComparison c (Compactification.ofIsProper f)`
  followed by `properFiniteIdentityNormalization`, restricted along the full
  inclusion of `intrinsicFiniteTorsionConstructible`. Its type is a natural
  isomorphism of the required two functors, with no arbitrary map supplied.
- `properFiniteNormalization` first asserts that every intrinsic bounded
  constructible K has a bounded-below etale representative L whose underlying
  complex is bounded constructible, and an actual derived isomorphism from
  the canonical comparison/realization image to K. This retains the witness
  needed for the comparison domain, rather than assuming it as a hypothesis.
- Its second conjunct is exactly `C(c,c') ≪≫ alpha(c') = alpha(c)` in Lean's
  left-to-right composition order. C is the published common-refinement
  comparison: `clopenSupportCanonicalComparison_existsUnique` specifies its
  components for EVERY etale antecedent and EVERY identification with K,
  using `fixedCompactSupportOriginIso`. The latter transports the actual
  canonical etale common-refinement comparison through the specified site
  and coefficient realization maps. Thus the independence of the common
  refinement and of the witness is inherited from this canonical comparison,
  not replaced by bare existence of isomorphisms. Naturality and invertibility
  are in its NatIso type. No independence is asserted for general unbounded
  pro-etale inputs.
- `properFiniteNormalization_quotient` quantifies over every surjective ring
  homomorphism `φ : P.properNextLevel.Ring →+* P.Ring`. Its statement is an
  equality of natural transformations on the WHOLE unbounded derived
  category. The left side is alpha_A after restriction followed by
  `sfDerivedImageRestriction f φ` (rho_*). The right is exactly
  `sfCompactSupportRestriction (Compactification.ofIsProper f) φ` (rho_!)
  followed by restriction of alpha_B. The recorded restriction node's
  published `sfCompactSupportRestriction` is the open-extension comparison
  `sfOpenRestriction` derived termwise, followed by `sfDerivedImageRestriction`.
  Its endpoints are precisely the ordinary constant-direct-image model of
  this node. The same module is publicly imported by its newer recorded
  `IntrinsicCompactSupportRestriction` interface; the latter's distinct
  `intrinsicCompactSupportRestriction` uses the identified-ringed
  `directImageConstantPush` coordinates. The declared sf-version is explicitly
  in the dependency's lean.declarations and is the compatible recorded factor.
- `properFiniteNormalization_successive` quantifies over arbitrary successive
  surjective homomorphisms A_(n+2) -> A_(n+1) -> A_n and every unbounded input K.
  Its first conjunct is the ordinary comparison's composition equation;
  its second is the compact-support equation. Both include exactly the
  canonical `sfDerivedCoefficientRestrictionComp` on source and target,
  accounting for the termwise scalar associator. The final conjunct is the
  quotient square for the composite map. Together with the individual
  squares, these state that the pasted square is the composite square.
  The natural-transformation equality in the quotient theorem gives
  naturality for arbitrary derived arrows, without a constructibility or
  boundedness restriction.

Dependency declarations used (source and full signatures/docstrings read):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and
  `.CoefficientDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the original integer-ring,
  uniformizer and quotient definitions reexported from CoefficientExtension.
- `def-weil-scheme-morphism-properties` is a convention node, so no module of
  its own is manufactured. The actual morphism classes are Mathlib
  `AlgebraicGeometry.IsProper`, `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact`; `IsProper` agrees with the definition since universally
  closed implies quasi-compact.
- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement`, `.category`, with
  `Compactification.ofIsProper` from its public Defs import.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`:
  `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport`.
- `Sheaf.Paper.SfDerivedDirectImage`: finite-level ordinary functor
  `AlgebraicGeometry.Scheme.proEtaleConstantDerivedDirectImage` (used in
  `WeilConjectures.sfFiniteDerivedDirectImage` in that recorded module).
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero` and the canonical
  `sfIntrinsicModuleEquivalence`.
- `Sheaf.Paper.ProEtaleConstructibleOrigin`:
  `AlgebraicGeometry.ProEtale.constructible_proEtale_origin`,
  `ConstructibleOriginComparison`, and its intrinsic/etale origin predicates.
- `Sheaf.Paper.CompactificationCoherence`:
  `AlgebraicGeometry.ProEtale.compactification_coherence`, whose common
  refinements and comparisons are restricted to witnessed etale-origin
  objects, with no arbitrary-unbounded extension.
- `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction` publicly retains
  `AlgebraicGeometry.Scheme.sfCompactSupportRestriction`,
  `sfDerivedImageRestriction`, `sfOpenRestriction`, and
  `sfDerivedCoefficientRestrictionComp` from SfCompactSupportRestrictionOfScalars.
- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`.
- `Sheaf.Paper.ClopenCommonCompactSupport`:
  `WeilConjectures.PurityFiniteSetting.clopenSupportCanonicalComparison`,
  its unique normalization and coherence; this already supplies the full
  bounded-constructible comparison needed here (no new helper is needed).
- `Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange`, owned by the definition
  node `def-sp-finite-intrinsic-open-square`: the existing
  `AlgebraicGeometry.Scheme.sfIntrinsicDerivedOpenId`, including its
  `sfIntrinsicOpenId` sheaf normalization. This item defines
  `WeilConjectures.PurityFiniteSetting.properFiniteIdentityNormalization`
  by whiskering this isomorphism with ordinary derived direct image and
  composing the left unitor. No conclusion of prop-exc-base-change-proper
  is used, and that theorem is not a statement dependency.
- Proof imports retain `sfIntrinsicExtensionByZero_exact`, Mathlib
  `PresheafOfModules.sheafification` and `Functor.mapDerivedCategoryFactors`,
  and the recorded `ProEtaleFixedScalarRestrictionDirectImage` and
  `FixedEtaleOriginDerivedCategory` interfaces. The exact-functor node is a
  Mathlib leaf with its `mathlib_match`; it does not need a lean record.

Only the three already-landed nodes for the setting, common comparison and
intrinsic open definitions are added to stmt_deps. All were checked for a path back to this
item: none, so these additions do not close a dependency cycle. They are not new
nodes or redefinitions. The source statement, proof and proof_deps are unchanged.

Edge cases checked: n=1 is included (no division by n or positive shift is used);
the empty scheme and zero complexes are included, with the zero etale antecedent;
negative cohomological degrees are not excluded (L is in D+, not nonnegative
complexes). All unbounded inputs remain in the quotient square and successive
comparison laws. An arbitrary compactification, including an extra disjoint
proper boundary component, is allowed; the construction uses the canonical
common refinement and never assumes X dense in the compactification. Any
surjective quotient homomorphism is allowed, not just the standard transition.
The composite quotient remains among the explicitly asserted squares. No field
characteristic hypothesis is added beyond the recorded finite-field datum and
l != p. The small-site universe convention is unchanged (schemes u, site
objects u+1, coefficient modules u+1).

Searches (prescribed msearch.py, group Q60/item binding):

- LeanFinder: "Extension by zero along identity is the identity and proper
  compact support equals derived pushforward with coefficient restriction
  compatibility". Eight results, chiefly HasCompactSupport.extend_zero and
  Function.extend_id, none about sheaf-derived normalization.
- Loogle: "CategoryTheory.Sheaf, AlgebraicGeometry.IsProper": zero results.
- LeanSearch: "proper compact support direct image canonical identity extension
  by zero coefficient restriction": eight function-support results, no match.
- msearch grep: "openImmersionLowerShriekId|compactSupportRestriction|
  properFiniteNormalization": zero Mathlib results.
- rg of `lean/WeilConjectures` found `openImmersionLowerShriekIdIso` and
  module-object analogues; these give the identity-open construction only,
  not refinement and finite quotient compatibilities. The item id itself
  had no upstream hit. rg of `lean/Sheaf` located and was followed by reading
  `sfIntrinsicOpenId`, `sfIntrinsicDerivedOpenId`, `sfProperSupportNormalization`,
  and `clopenSupportCanonicalComparison`. The identity-open and common-refinement
  constructions are reused; the returned H2 correction (b) requests an explicit
  whiskering recipe in this item instead of importing the proper/open theorem
  module just for its plain definition.
- rg of `dag/lean_names_upstream.json`, Mathlib, WeilConjectures and Sheaf for
  properFiniteNormalization, properFiniteComparison, properNextLevel: no
  existing declaration with any of the proposed names.

No STATEMENT-DISPUTED flag or node fault remains. All theorem proofs are `sorry`.
Every definition contains concrete data; there is no choice from bare existence.

## Second reading by Q60

This is a second pass by the same dispatcher-started worker, not an independent
agent review: the human brief prohibits starting other agents and assigns the
independent reading to the maintainer. I reopened the node and complete module.

The pass checked the bundled datum against every field in the first paragraph,
the three finite-type/separated instances for each scheme, properness of f and
its base compatibility. It checked that the comparison is a NatIso on the full
intrinsic bounded-constructible category, that the origin witness is a conclusion,
and that the equality has Lean's left-to-right order C(c,c') then alpha(c').
It read the unique all-origin normalization of the reused common-refinement
comparison and the bodies of identity-open and proper normalization. It checked
that the rho_! body uses the open factor then its actual direct-image factor.

One omission found and repaired: the successive-map theorem initially stated
both composition equations but did not explicitly state the square for the
composite map A_(n+2) -> A_n (the adjacent-level theorem alone could not be
instantiated with that composite). The final theorem includes that square as
its third conjunct. The final equations also include both scalar associators,
so they do not silently treat termwise restriction composition as definitional.
There are no local instances/notations/private helper copies or auto-bound
variables. Compiler probes with #check were removed before final validation.

## Returned H2 repair

Returned immutable head: 3e4aba0cfcb7. The maintainer found one H2 issue:
prop-exc-base-change-proper was a statement dependency only because its module
contained the plain recipe sfProperSupportNormalization, although this item
uses no conclusion of that theorem.

Implemented the requested option (b) exactly. Removed the direct public import
of ProperExceptionalOpenBaseChange and the stmt_dep prop-exc-base-change-proper.
Added the public import ProEtaleOpenSquareExchange and stmt_dep
`def-sp-finite-intrinsic-open-square`, whose statement expressly includes
intrinsic open functors with their derived identity comparisons. Read its current
node and the full signatures and bodies of sfIntrinsicOpenId and
sfIntrinsicDerivedOpenId. Added `properFiniteIdentityNormalization` in this item's
namespace, with the same explicit body:
`Functor.isoWhiskerRight (sfIntrinsicDerivedOpenId A X) _ ≪≫ Functor.leftUnitor _`.
Its endpoint uses the recorded sfIntrinsicCompactSupport. Replaced every call
in properFiniteComparison, _quotient and _successive, updated the proof-plan
reference, and listed the helper in lean.declarations. This is the reviewer's
authorized in-item recipe, not a new independent notion or unowned theorem use.

Compared the retained sandbox with the returned version recorded in this
conversation and with current-main source files, without direct Git commands.
The current-main item has no Lean record; its other fields agree with the
returned item's base apart from the intended stmt_deps additions. Rebuilt the
sandbox node from current main, applying only lean and the three landed
statement dependencies; the wrapper will construct the delivery on its current
base. No source statement, hypothesis, proof, proof_deps or other node metadata
changed. The theorem signatures change only by the explicit replacement of the
normalization recipe, which has the same data and endpoints. The maintainer
accepted the remaining mathematics and the common-comparison prerequisite.

Repair second reading (same worker, no other agents started): searched the
whole module and node again. There is no remaining reference to
sfProperSupportNormalization or direct import/dependency on the returned
proper/open theorem. The new helper is before the setting section, binds A,
X, Y and f explicitly, has a source/blueprint docstring, and has no sorry.
The main constructible-origin/refinement theorem, adjacent quotient square,
successive ordinary and compact-support laws and composite quotient square
retain precisely their reviewed hypotheses and map order. The current main
was also checked for a dependency path from the replacement definition node
back to this item, to avoid introducing a cycle.

Repair validation: prescribed scompile.py passed the repaired module in sandbox
mode (10.9 s) and library-module mode (6.1 s), without errors or warnings.
The prescribed deliver2.py --no-push passed preflight and per-file compilation
on the current base: `OK (dry run): commit a63726e18af`. No direct repository
edits, Git commands or global builds were run.
