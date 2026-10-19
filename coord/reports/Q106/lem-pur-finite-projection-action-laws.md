## Worker report

The module Sheaf.Paper.FiniteProjectionActionLaws states eight theorems, each with
proof `sorry`: the proper, open, open-counit and chosen-compactification identities
in AlgebraicGeometry.ProEtale and AlgebraicGeometry.Etale. It defines no replacement
projection maps, tensor products, pullbacks or compact-support functors. The only
helpers expose the canonical pro-etale tensor associator and register finiteness
of the already defined lifted coefficient quotient using the named theorem
Padic.finite_coefficientExtensionRing and Finite.of_equiv through Equiv.ulift.symm.

Hypotheses and clauses, individually:

- The finite ring A=A_{E,n}, n>=1, and field k are supplied by the existing
  `(P : WeilConjectures.PurityFiniteSetting.{u})`. P.level_pos is the positive-level
  witness, P.extension is the finite subextension, P.field.k is the fixed field,
  and P.Coefficient is precisely the conventional ULift of P.Ring=O_E/(varpi^n).
  The field characteristic and coefficient prime conventions are retained in P.
- Every theorem explicitly binds `{X Y : Scheme.{u}}`, the two `.Over
  (Spec (CommRingCat.of P.field.k))` instances, and IsSeparated,
  LocallyOfFiniteType, QuasiCompact of both structure morphisms. These are exactly
  the separated finite-type k-schemes of the node; none is a section variable
  that could disappear during elaboration. The morphism f has its `.IsOver`
  instance for the same base.
- The ambient pro-etale categories are `DerivedCategory (Sheaf
  (Scheme.ProEt.topology X) (ModuleCat.{u+1} P.Coefficient))`, and similarly for Y.
  This is the existing fixed-scalar constant-module presentation in the finite
  maps of def-exchange-projection and lem-cbc-extension-zero-projection-formula.
  The ordinary etale statements use the corresponding smallEtaleTopology
  categories of def-weil-pbc-derived-categories. No input object is bounded,
  constructible, of finite Tor amplitude, or required to originate on another site.
- In `finiteProjectionAction_proper`, `[IsProper f]` is exactly properness.
  M is arbitrary on X and N1,N2 arbitrary on Y. The projection is the actual
  `rightDerivedLowerStarProjectionMap`, whose upstream definition is the
  right-adjoint mate of the canonical tensor comparison followed by counit tensor
  identity. The left side first reassociates `(Rf_*M tensor N1) tensor N2`,
  applies the single projection for N1 tensor N2, then applies Rf_* to
  `1_M tensor mu` followed by the inverse associator. The right side tensors the
  first actual projection with identity on N2, then applies the second actual
  projection. This writes out precisely the node's suppressed associators and mu.
- In `finiteProjectionAction_open`, `[IsOpenImmersion f]` is exactly openness,
  M,N1,N2 again have the stated arbitrary domains. Delta is `.inv` of the
  existing `derivedOpenImmersionLowerShriekProjectionIso`, in the required
  direction. The same explicitly displayed associator/mu equation uses exact
  extension by zero `D((f)_!open[...])` in place of the proper image.
- In `finiteProjectionAction_open_counit`, F,N are arbitrary on Y. The first
  factor is the exact inverse image `D((f)^*[...]).obj F`. The left composite
  is delta followed by extension by zero of the canonical comparison and the
  exact open counit at F tensor N. The comparison is
  `mapDerivedCategoryUpperStarDerivedTensorIso.hom`, whose source is
  `(D f^* F) tensor (L f^* N)` and target `D f^*(F tensor N)`.
  Its upstream definition inserts `L f^* ~= D f^*` and then uses the inverse
  tensor comparison. Thus it is exactly the node's mu^{-1}, with the existing
  canonical exact/derived identifications explicitly retained. The right side
  is tensor's map on that same open counit at F, evaluated at N.
- In `finiteProjectionAction_compactification`, f is explicitly separated,
  locally of finite type and quasi-compact, and `(c : Compactification f)` is
  arbitrary, not a selected compactification. The functor is exactly
  `rightDerivedLowerShriekOfCompactification ... c = D(c.i)_! ⋙ R(c.g)_*`.
  The maps are exactly `projectionMapOfCompactification ... c`; no new map is
  defined. The equation has the same reassociation, mu_f and successive tensor
  factors as the proper clause, using Lf^* and the actual chosen-candidate functor.
- The four AlgebraicGeometry.Etale statements repeat these clauses on the
  ordinary small etale site with its own named maps, derived tensors, open
  counits and compactified functors. Its Lf^* is canonically identified with
  exact termwise inverse image by leftDerivedUpperStarIsoMapDerivedCategory;
  the mixed comparison above includes that identification where needed.
- There is no IsIso assumption on proper or compactification projection maps.
  Only the existing canonical open tensor isomorphism is inverted, as in the node.
  There is no assertion of compactification independence or coefficient change.

Dependency declarations read and used:

- Sheaf.Paper.PurityFiniteSetting: WeilConjectures.PurityFiniteSetting,
  .Ring, .Coefficient and .coefficientCommRing.
- def-exchange-projection records Sheaf.Paper.ExchangeProjection,
  AlgebraicGeometry.ProEtale.finiteExchangeProjection and
  coefficientExtensionExchangeProjection. Their finite definitions return the
  existing upstream projection maps unchanged. We import the smaller owning
  WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekProjection and use
  projectionMapOfCompactification and rightDerivedLowerStarProjectionMap directly.
  Importing all of ExchangeProjection initially triggered duplicate
  upperStarIsoLowerStarInv between standard and FiniteCoefficient modules in
  its overlay import closure. The prescribed repair is to import only the
  smaller owning modules; no dependency JSON needs changing.
- WeilConjectures.SixFunctors.ProEtale.Derived.Tensor and
  UpperStarMonoidal.Comparison: derivedTensor, leftDerivedUpperStarTensorIso;
  OpenImmersionLowerShriekProjection: derivedOpenImmersionLowerShriekProjectionIso
  and mapDerivedCategoryUpperStarDerivedTensorIso. These are the actual
  dependency constructions, not private tensor/comparison copies.
- lem-cbc-extension-zero-projection-formula's finite-coefficient owning module
  was read through `scompile.py --source`; its recorded projection isomorphism
  is the same declared canonical isomorphism supplied through the standard
  upstream owning module. Importing both parallel copies would duplicate names.
- Sheaf.Paper.DerivedPullbackTensorHom: finiteDerivedPullback and
  finiteIntrinsicDerivedTensor were read. Their intrinsic constant-ring
  presentation is distinct from the already recorded fixed-scalar presentation
  of the projection maps. We use the latter exactly as def-exchange-projection
  and the open-projection dependency specify, rather than introducing any new
  intrinsic tensor or unproved change-of-presentation map.
- WeilConjectures.SixFunctors.Etale.Derived.Tensor: derivedTensor;
  Derived.TensorStructure: derivedTensorAssociator;
  Derived.LowerStarProjection: rightDerivedLowerStarProjectionMap;
  Derived.OpenImmersionLowerShriekProjection: derivedOpenImmersionLowerShriekProjectionIso
  and mapDerivedCategoryUpperStarDerivedTensorIso;
  Derived.LowerShriekProjection: projectionMapOfCompactification;
  Derived.LowerShriek: rightDerivedLowerShriekOfCompactification
  (def-amb-etale-compact-support);
  Derived.Coefficients: DerivedCategoryModule (the type is expanded here).
- Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons was read and
  imported for the node's ordinary unbounded compact-support context. The
  chosen-candidate functor remains precisely its existing underlying candidate;
  its comparison theorem is not used as an invertibility assumption.
- Mathlib.AlgebraicGeometry.OpenImmersion: AlgebraicGeometry.IsOpenImmersion;
  Mathlib.AlgebraicGeometry.Morphisms.Proper: AlgebraicGeometry.IsProper, with
  IsSeparated, UniversallyClosed and LocallyOfFiniteType; finite type follows
  from QuasiCompact of a universally closed map. The convention-only
  def-weil-scheme-morphism-properties adds no independent declaration.
- Recorded proof dependencies with usable declarations are imported (including
  DerivedPullbackCompositionMonoidal, RingedTopoiCanonicalTensorPullbackOfUniverses,
  WeilSiteDerivedTensorDescent and the etale open-adjunction module). The
  unrecorded proof prerequisites need no new statement objects for this delivery.

Sources checked: the current blueprint projection-purity agreement proof and
node's expanded eight-step proof; Stacks sites-cohomology.tex's
 equation-projection-formula-map (0B56) and lemma-j-shriek-and-tensor (0GL1),
and sites-modules.tex lemma-j-shriek-and-tensor (0E8I). The latter uses the actual
open adjunction, and the derived statement applies its sheaf comparison with a
K-flat second factor. These agree with the actual upstream map definitions.

Edge cases checked before writing: identity proper/open morphisms, the empty
scheme and empty open, zero M or N1/N2, degree-zero complexes, and arbitrary
unbounded complexes. All endpoints and comparisons exist in these cases.
There is no nonempty-scheme, positive-rank, boundedness or invertibility condition.
The coefficient level is the specified positive level; no division of n or
additional ramification condition is imposed. Associators only reassociate,
so no braiding signs are silently inserted. Site object universe u+1 and
morphism universe u are retained, with coefficient module carrier universe u+1.

Searches made (2026-10-17 UTC):

- msearch.py leanfinder: 'Counit defined projection formula maps respect tensor
  action associativity and open extension counits'. Eight hits, including
  CategoryTheory.Adjunction.map_mu_comp_counit_app_tensor and its reassociated
  version; the other hits concerned coalgebra counits. No match for this package.
- msearch.py loogle: `CategoryTheory.Adjunction, "counit"`. Twelve hits for generic
  counit, naturality, transport and composition declarations; no action identities.
- msearch.py grep: `projectionFormula|projection_formula|projection.*[Aa]ssociativ`.
  Zero Mathlib hits.
- rg of upstream WeilConjectures and shared lean/Sheaf for projection action,
  associativity, the item ID, projectionMapOfCompactification and
  finiteExchangeProjection. Existing proper/open/compactification maps and
  base-change comparisons were found, but not these tensor-action identities.
- rg of upstream tensor APIs found the ordinary etale derivedTensorAssociator.
  No pro-etale explicit bifunctor associator wrapper was present, so the real
  canonical associator is exposed in the owning item's module before concrete
  specialization. No theorem or mathematical structure is postulated for it.
- rg found an existing finiteCoefficient theorem in
  Sheaf.Paper.FiniteTypeExceptionalInverseImage. The present instance is a direct
  registration of the underlying already named quotient-finiteness theorem,
  not another postponed theorem or new coefficient notion.

No statement correction, new node or dependency-node repair is made.
No STATEMENT-DISPUTED flag: the typed equations preserve every source clause.

## Second reading by Q106

I performed a separate second pass with the DAG statement and generated Lean
module open. No second agent was started, as the dispatcher brief forbids it;
the maintainer supplies the independent review. This section records the actual
second pass rather than claiming review by another worker.

The pass checked all eight equation endpoints. In particular it checked the
proper/open action common target after applying mu and inverse reassociation,
the forward delta versus inverse upstream open projection isomorphism, the
exact first inverse-image factor in the counit equation, and the preservation
of the chosen compactification c in both compactification statements. It found
that section-variable scheme hypotheses might be omitted by elaboration; these
were replaced with explicit binders on every theorem. The typeclass pass found
that P.Coefficient finiteness was not registered; its direct proof term was
installed as an instance, without an extra mathematical hypothesis. A formatting
pass wrapped all lines to at most 100 characters and kept universe tokens intact.
Every proof remains `sorry`, and every helper has real defining data.

Validation: scompile.py compiled the sandbox and library forms without errors or
warnings (23.2 s and 24.8 s respectively). Direct owning-module imports were then
made explicit for the stated proof plan; the delivery preflight recompiles this
final file. No global build was run and no shared source was edited.
