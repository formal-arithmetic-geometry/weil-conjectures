## Worker report

Repair of the return at immutable head 3138839ce213 (also ea5f51a2e0b8). This packet retains and continues the interrupted
repair's thirteen modules. It replaces arbitrary endpoints and the predicate
`PurAdicCompatibleFamily` by actual constructions, and states the exact quotient-linear
reduction identity. No `U`, `V`, `hU`, `hV`, or compatible-family hypothesis remains.
The finite derived-tensor normalization is first stated for abstract exact
realization functors. AdicPurityDerivedTensorModel packages a comparison with that
full K-flat counit equation. Its specialization uses the recorded realization,
explicitly typed with codomain scalarReductionTarget, and the original ordinary
scalar-unit comparison. IsAdicPurityDerivedFiniteTensor identifies the concrete
comparison with the comparison of such a normalized model by heterogeneous equality.
HasAdicPurityDerivedTensorModel states this identification generically, preserving
the same equation without expanding coefficient-category instances in its specialization.
AdicPurityFiniteTensorIsoType names the unchanged full natural-isomorphism type,
so specializing the normalized comparison does not re-expand its tensor structure.
The concrete package has named existence and subsingleton statements, so selection
from it determines all data. The ordinary realization is the recorded functor itself;
its tensor comparison is fixed by equality to the original scalar-unit comparison.
The cached ordinary finite tensor is identified with finiteComplexTwist by
adicPurityFiniteTwistPresentation for the twist/restriction adjunction. No coefficient
object or normalization is replaced.
All postponed proofs are named theorems; definitions contain actual constructions or
choices characterized by universal section, localization, or adjunction equations.

Hypothesis and clause correspondence (namespace `WeilConjectures`):

1. The global field datum is `D : FiniteFieldDatum.{u}`. The coefficient datum is
   `C : D.CoefficientDatum`; it supplies the prime, primality instance, coefficient
   closure, and `C.different : C.l ≠ D.p`. The finite extension in that fixed closure is
   `E : IntermediateField (Padic C.l) C.Qbar`, with `FiniteDimensional (Padic C.l) E`.
   The integer ring, uniformizer, and quotients are the published Padic constructions.
2. `X Y : Scheme.{u}`, their `Over (Spec (.of D.k))` instances, and locally finite type,
   quasi-compact, separated structure morphisms give exactly separated finite-type
   k-schemes. `f.IsOver` makes f a k-morphism. Its separated, locally finite type and
   quasi-compact instances are the domain required by the exceptional construction;
   finite type follows in this geometric setting and is also explicit in the node's
   conventions. `d : ℕ` and `SmoothOfRelativeDimension d f` give pure dimension d≥0.
3. `K : DerivedCategory (scalarReductionSource C.l E Y)` is an actual module complex
   over the completed coefficient sheaf, not a constant O_E coefficient replacement.
   `hK : finiteTorConstructibleIntegral C.l E Y K` includes derived completeness,
   all constructible reductions, one common cohomological interval and one common Tor
   interval. There are no extra constructibility or completeness hypotheses.
4. Every positive exponent appears once as `n+1`, for `n : ℕ`.
   `purAdicFiniteSetting D C E n : PurityFiniteSetting.{u}` has precisely this level.
   `purAdicReductionFiniteTor` extracts the required finite predicate for the actual
   `K_n = (scalarReductionDerivedExtension C.l E Y n).obj K` from hK.
5. `purAdicSource D C E f d K` is literally integralDerivedPullback applied to K,
   then integralComplexTwist by `(d : ℤ)`, then cohomological shift `2 * (d : ℤ)`.
   The twisting functor is exact tensor by the locally free completed Tate line.
6. `purAdicTarget D C E f K` is literally integralExceptionalInverseImage applied
   to K. This is strict derived reduction, the explicit quotient-coordinate equivalence,
   the etale/pro-etale system comparison, the ordinary etale compact-support system
   right adjoint, inverse site comparison, inverse coordinates and total derived limit.
   The transitions belong to actual systems, rather than independently chosen levels.
7. `purAdicFiniteArrow ... n` is `Arrow.mk` of the recorded
   `(purAdicFiniteSetting ... n).smoothPurityMap f d K_n hK_n` itself.
   Its endpoints, including all intrinsic/fixed scalar transports, are used verbatim.
8. `purAdicSourceReduction ... n` is b^U_n. It composes exact shift commutation,
   the adjoint of the root-normalized twist/restriction comparison, the actual
   pullback reduction counit, and the fixed finite source identification. That last
   isomorphism uses the K-flat tensor counit and the root-normalized diagonal line,
   rather than an arbitrary endpoint isomorphism.
9. `purAdicTargetReduction ... n` is b^V_n. It is the actual reduction/limit counit
   followed by `purAdicExceptionalEvaluation`, whose factors are the coordinate
   counit, section-normalized site comparisons and compact-support adjunction mate.
10. The conclusion `∃ gamma : purAdicSource ... ⟶ purAdicTarget ..., IsIso gamma ∧ ...`
    is the integral purity isomorphism. The next two conjuncts prove (rather than
    assume) the integral finite-Tor constructibility of both endpoints. The level
    clause proves both canonical comparison maps invertible and asserts
    `red.map gamma ≫ bV = bU ≫ (purAdicFiniteArrow ... n).hom`.
    Lean composition reads left-to-right, so this is exactly
    b^V_n ∘ red_n(gamma) = gamma_(f,K_n) ∘ b^U_n in D(A_(E,n+1)).
11. The final existential G is a morphism in the derived category of strict
    completed-coefficient towers, from the actual reduction tower of U to the actual
    exceptional system after scalar restriction. Its evaluation equation is the
    scalar restriction of these specific finite purity maps; hence it retains
    coherent transitions. The displayed equality for gamma identifies it with the
    derived-completion unit followed by the limit of G. No uniqueness is asserted.

Explicit universe check: D, E, X and Y use u, the small pro-etale site has objects
in u+1 and morphisms in u, and fixed finite modules use ULift.{u+1} A with value
universe u+1. `purAdicFiniteSetting ... : PurityFiniteSetting.{u}` matches
`PurityFiniteSetting.isIso_smoothPurityMap` exactly. The generic system coefficient
ring is ULift.{u+1} O_E; `integralExceptionalQuotient` identifies its quotient with
ULift.{u+1} A_(E,n+1). No equality of the site's object and morphism universes,
ramification divisibility condition or restriction to cofinal quotient levels is used.

Dependency declarations used (module / declaration):

- Sheaf.Paper.PurityFiniteSetting / WeilConjectures.PurityFiniteSetting.
- Sheaf.Paper.FiniteTorAmplitude / finiteTorConstructibleIntegral,
  finiteTorConstructible; Sheaf.Paper.SfIntegralConstructible / sfIntegralConstructible.
- Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction /
  scalarReductionDerivedExtension, scalarReductionRestriction and
  derivedScalarExtensionRestrictionAdjunction.
- Sheaf.Paper.IntegralDerivedOperations / integralDerivedPullback, reexported by
  the recorded IntegralDerivedOperationsOnSlices interface; its global functor is
  reused unchanged, and no new completed tensor is introduced.
- Sheaf.Paper.CoefficientTwistsDetailed / integralComplexTwist, integralTwistLine,
  finiteCoefficientTwist, finiteComplexTwist. These original interfaces are publicly retained by the recorded
  IntrinsicCoefficientTwistsUnrestricted module.
- Sheaf.Paper.FiniteCoefficientSmoothPurity /
  PurityFiniteSetting.isIso_smoothPurityMap and its imported smoothPurityMap.
- Sheaf.Paper.FiniteReductionOfPurity /
  PurityFiniteSetting.finiteReductionOfPurity, the recorded quotient comparison square.
- Sheaf.Paper.CompletedPullbackTensorComparison / pullbackTensorCalculus,
  pullbackTensorIntegralPullbackModel, pullbackTensorDerivedEvaluation.
- Sheaf.Paper.IntegralReductionTower / coefficientSequenceDerivedEvaluation,
  coefficientSequenceDerivedRestriction, coefficientSequenceLimit,
  coefficientConstantTowerEvaluation and coefficientConstantTowerLimit.
- Sheaf.Paper.NormalizedDVRTower / normalizedDVRQuotient,
  normalizedDVRRestrictionCompIso; Sheaf.Paper.NormalizedDVREffectivity supplies
  the normalization/effectivity proof interface.
- Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt / ProEtale.sfFiniteExceptionalAt;
  Sheaf.Paper.EtaleCoefficientSystemAdjoint / StrictEtaleCompactSupport and
  StrictEtaleExceptionalAdjoint; the recorded coefficient-compatible System is retained verbatim. The owned ambient realization is naturally identified with its integral operation on the finite-Tor subcategory.
- Mathlib.AlgebraicGeometry.Sites.Proetale / Scheme.ProEt and ProEt.topology;
  Mathlib.AlgebraicGeometry.Morphisms.Smooth / SmoothOfRelativeDimension.
- The new-node declaration lists in their `lean.declarations` record all subsidiary
  constructions and named property statements in their owning modules.

Edge cases checked against the definitions: exponent one is n=0; exponent zero is
never introduced. All positive levels are used even if the ramification index does
not divide the exponent. For d=0 the ordinary root power is the coefficient unit,
the shift is zero and the diagonal comparison uses the tensor unit. Identity f is
allowed, including relative dimension zero. Empty schemes impose no nonemptiness
hypothesis: residue-unit quantification is empty and global units map to the zero
ring's unit. The zero complex is allowed; its source and target conditions are
conclusions. The completed reduction functor is left derived scalar extension;
no flatness of a quotient projection is assumed. The integral prime/unit helpers
use l≠p from C, never an additional unit hypothesis in the final theorem.

Searches retained from the interrupted repair (`searches.jsonl`): LeanFinder query
"A compatible system of finite coefficient smooth purity isomorphisms induces an
adic purity isomorphism with the prescribed reductions" returned eight arithmetic
completion/de Rham hits, none a sheaf purity theorem. Loogle query
"WeilConjectures.NormalizedDVRTower, CategoryTheory.IsIso" returned no hits (unknown
project identifier). Grep "adic.*[Pp]urity|[Pp]urity.*adic|normalized.*[Tt]ower" in
Mathlib CategoryTheory returned no hits. For the missing comparisons, LeanFinder
"canonical finite reduction of integral smooth purity via coefficient systems,
root-normalized Tate twist and exceptional adjunction realization" returned eight
smooth-algebra/de Rham hits. Loogle on mapDerivedCategoryCompIso,
QObjTensorSingleFunctorObjIso and Adjunction.homEquiv returned no hits because the
service did not recognize the derived-functor name. LeanSearch on canonical
realization of coefficient systems and Tate twists returned eight generic module,
derived-category and representation adjunction results; none gives the normalized
comparison. Project/upstream rg for adicPurity, integralExceptional,
purAdicReconstruction and the item id finds no existing declaration. Blueprint
search for "exceptional realization" returns zero nodes; blueprint ancestor search
confirms thm-pur-adic-reconstruction as the new nodes' ancestor. All new records
retain these search results. Existing tensor, localization, quotient and adjunction
APIs are used, rather than copied. The item statement and all existing dependency statements are unchanged;
no STATEMENT-DISPUTED issue remains from the returned arbitrary-endpoint formulation.

## Repair validation

The returned independent-head check reported cached side overrides throughout the
shared library and one timeout in `Sheaf/Algebra/Homology/DerivedPullbackTensorHom.lean`;
it did not report an error in this packet's declarations. The retained packet was
re-run through the complete 13-file private-overlay, preliminary, sandbox, library,
and metadata preflight sequence in `scratchpad/resume-final/final-dry.log`, which
finished `OK` at commit `785e81b0a6`. This repair preserves that successful source
and metadata validation while refreshing the delivery packet after the independent
head failure.

## New nodes

`def-pur-adic-root-comparisons` owns `Sheaf.Paper.AdicPurityRootComparisons` and its recorded declarations. For the coefficient datum [def-pur-conventions] and the actual coefficient lines [def-coefficient-twists-detailed], define the canonical quotient maps of all nonnegative integral Tate powers. Their zeroth component is the coefficient projection, their first component sends a root tensor to its finite root projection, and their higher components preserve ordered pure tensors. These equations determine the family uniquely. Identify the shifted affine-line tensor powers with the corresponding degree-zero Tate powers shifted by $2d$, using the specified K-flat tensor counit, tensor unit and shift comparisons. The etale/pro-etale comparison is uniquely normalized on every local pure root tensor. Flatness is asserted only when the coefficient prime is invertible in residue fields. Source: the canonical reduction identifications in the five-step reconstruction proof, and the current main-20261015 purity transport statement. The LeanSearch, LeanFinder/Loogle and Mathlib/upstream/project grep searches above are retained in its mathlib_searches; none provides this normalized composite. This is a missing comparison construction, not a replacement for the underlying coefficient, tensor, site or exceptional operation.

`def-pur-adic-finite-tensor-realization` owns `Sheaf.Paper.AdicPurityFiniteTensor` and its recorded declarations. Using the root quotient maps [def-pur-adic-root-comparisons], define finite tensor by the actual Tate line. It is additive and exact when the coefficient prime is invertible. Define the unique ordinary integral-twist/restriction comparison which sends each local balanced tensor $x\otimes y$ to $x\otimes c_d(y)$. Define the unique comparison of fixed and intrinsic finite tensor realizations which carries every scalar-unit pure tensor to that same pure tensor. These equations hold for every module and every test object. Source: the canonical reduction identifications in the five-step reconstruction proof, and the current main-20261015 purity transport statement. The LeanSearch, LeanFinder/Loogle and Mathlib/upstream/project grep searches above are retained in its mathlib_searches; none provides this normalized composite. This is a missing comparison construction, not a replacement for the underlying coefficient, tensor, site or exceptional operation.

`def-pur-adic-twist-reduction` owns `Sheaf.Paper.AdicPurityTwistReduction` and its recorded declarations. Derive the ordinary normalized tensor comparisons [def-pur-adic-finite-tensor-realization]. The finite tensor realization is the unique natural isomorphism whose square on every K-flat representative is the specified K-flat tensor counit square. Define the canonical reduction of an integral Tate twist by transposing the scalar-extension unit followed by the derived ordinary restriction comparison under the actual derived extension/restriction adjunction [def-weil-integral-derived-reduction]. Retain every quotient coefficient action. Source: the canonical reduction identifications in the five-step reconstruction proof, and the current main-20261015 purity transport statement. The LeanSearch, LeanFinder/Loogle and Mathlib/upstream/project grep searches above are retained in its mathlib_searches; none provides this normalized composite. This is a missing comparison construction, not a replacement for the underlying coefficient, tensor, site or exceptional operation.

`def-pur-adic-etale-realization` owns `Sheaf.Paper.ExceptionalFiniteRealization` and its recorded declarations. In the actual exceptional construction [def-weil-exceptional-inverse-image], identify the lifted uniformizer quotient with the lifted original finite coefficient ring by the quotient ring equivalence. Realize ordinary etale modules in fixed scalar coordinates by this equivalence and constant scalar restriction; this realization is additive and an exact equivalence. Its comparison with ordinary direct image is the unique map equal to the recorded underlying-set map on every section. The inverse-image comparison is its adjunction mate, characterized by the full Hom-transpose equation. The derived direct-image comparison is uniquely characterized by the universal right-derived-unit square on all cochain complexes. Source: the canonical reduction identifications in the five-step reconstruction proof, and the current main-20261015 purity transport statement. The LeanSearch, LeanFinder/Loogle and Mathlib/upstream/project grep searches above are retained in its mathlib_searches; none provides this normalized composite. This is a missing comparison construction, not a replacement for the underlying coefficient, tensor, site or exceptional operation.

`def-pur-adic-support-realization` owns `Sheaf.Paper.ExceptionalFiniteSupportRealization` and its recorded declarations. For a compactification and the actual strict etale compact-support construction [def-weil-exceptional-inverse-image], define the fixed-coefficient realization of its open extension by the full Hom-transpose equation relative to the inverse comparison [def-pur-adic-etale-realization]. Derive this exact comparison with its square on every cochain representative. Compose it with the universal-unit-normalized proper direct-image comparison to obtain the compact-support comparison at that same compactification. Its right-adjoint comparison is uniquely specified by the Hom-transpose equation for every pair of objects and every compact-support morphism. Source: the canonical reduction identifications in the five-step reconstruction proof, and the current main-20261015 purity transport statement. The LeanSearch, LeanFinder/Loogle and Mathlib/upstream/project grep searches above are retained in its mathlib_searches; none provides this normalized composite. This is a missing comparison construction, not a replacement for the underlying coefficient, tensor, site or exceptional operation.

`def-pur-adic-proetale-realization` owns `Sheaf.Paper.ExceptionalProEtaleRealization` and its recorded declarations. Realize the pro-etale quotient modules of [def-weil-exceptional-inverse-image] in the same explicit finite scalar coordinates as [def-pur-adic-etale-realization]. This is an additive exact equivalence. Its comparison with intrinsic finite realization is uniquely fixed on all scalar-unit sections. Derive it by exact localization. The strict coefficient-coordinate functor commutes with ordinary evaluation as an equality of functors. Identify every normalized derived evaluation package with exact derived evaluation by its factorization square on all complexes. Compose these maps and the actual coordinate-equivalence counit to define the direct and inverse coordinate/evaluation identifications. Source: the canonical reduction identifications in the five-step reconstruction proof, and the current main-20261015 purity transport statement. The LeanSearch, LeanFinder/Loogle and Mathlib/upstream/project grep searches above are retained in its mathlib_searches; none provides this normalized composite. This is a missing comparison construction, not a replacement for the underlying coefficient, tensor, site or exceptional operation.

`def-pur-adic-site-realization` owns `Sheaf.Paper.ExceptionalSiteRealization`. For a prime $\ell$, a finite extension $E/\mathbf Q_\ell$, a scheme $W$, and the actual etale/pro-etale system comparison in [def-weil-exceptional-inverse-image], use the quotient scalar coordinates of [def-pur-adic-proetale-realization] and [def-pur-adic-etale-realization]. Define the ordinary direct-image comparison uniquely by equality with the recorded underlying set-sheaf map on every section. Define the inverse-image comparison as its unique adjunction mate, with the full Hom-transpose equation for every pair of modules and every morphism. Its source is the canonical exceptional finite-reduction identification in the current reconstruction proof. The recorded LeanSearch, LeanFinder/Loogle and Mathlib/upstream/project grep searches give no such normalized comparison.

`def-pur-adic-derived-site-realization` owns `Sheaf.Paper.ExceptionalDerivedSiteRealization`. For the ordinary normalized etale/pro-etale site comparison of [def-pur-adic-site-realization], derive its inverse-image comparison by exact localization, characterized by its full factorization square on every cochain representative. Derive its direct-image comparison by the universal right-derived-unit square on every cochain representative, using the ordinary direct-image comparison. These equations uniquely determine both natural isomorphisms. It serves the same source identification, reuses the recorded ordinary site comparison, and has the same documented searches with no exact match. Ordinary and derived portions are separate modules to remain within the per-file compilation limit.

`def-pur-adic-purity-objects` owns `Sheaf.Paper.AdicPurityObjects` and its recorded declarations. Fix the finite-field and coefficient setting of the finite smooth-purity theorem [thm-pur-finite-coefficient-smooth-purity] in exactly its universe. For the input integral finite-Tor constructible object [def-weil-finite-tor-amplitude], set $K_n$ to its actual positive derived reduction and prove its finite-Tor constructibility. Define $U=Lf^*K(d)[2d]$ using the integral pullback [def-pur-integral-derived-operations] and twist [def-pur-adic-twist-reduction], and define $V$ by the actual inverse limit of the exceptional system underlying [def-pur-adic-support-realization]. Define the finite arrow to be literally the recorded smooth-purity map at $K_n$. The pullback reduction map is the actual reduction/limit counit, transported by the pullback model and its evaluation maps. Unit hypotheses needed by twists are derived from the coefficient characteristic condition, not assumed. Source: the canonical reduction identifications in the five-step reconstruction proof, and the current main-20261015 purity transport statement. The LeanSearch, LeanFinder/Loogle and Mathlib/upstream/project grep searches above are retained in its mathlib_searches; none provides this normalized composite. This is a missing comparison construction, not a replacement for the underlying coefficient, tensor, site or exceptional operation.

`def-pur-adic-source-reduction` owns `Sheaf.Paper.AdicPuritySourceReduction` and its recorded declarations. For the actual source and finite arrow [def-pur-adic-purity-objects], define $b^U_n:\operatorname{red}_n U\to U_n$ as the composite of exact shift commutation, the twist-restriction mate [def-pur-adic-twist-reduction], the pullback reduction counit, and the finite source identification. That identification uses the actual finite pullback presentation, the scalar-unit-normalized derived tensor realization and the root-normalized shifted diagonal comparison [def-pur-adic-root-comparisons]. No arbitrary source object or endpoint isomorphism is supplied. Source: the canonical reduction identifications in the five-step reconstruction proof, and the current main-20261015 purity transport statement. The LeanSearch, LeanFinder/Loogle and Mathlib/upstream/project grep searches above are retained in its mathlib_searches; none provides this normalized composite. This is a missing comparison construction, not a replacement for the underlying coefficient, tensor, site or exceptional operation.

`def-pur-adic-exceptional-reduction` owns `Sheaf.Paper.AdicPurityExceptionalReduction` and its recorded declarations. For the actual exceptional system and finite arrow [def-pur-adic-purity-objects], define its finite evaluation isomorphism by composing the explicit coefficient-coordinate counit, the site comparison maps [def-pur-adic-derived-site-realization], and the compact-support right-adjoint mate [def-pur-adic-support-realization], all at the same canonical compactification. Define $b^V_n:\operatorname{red}_n V\to V_n$ as the actual derived reduction/limit counit followed by this normalized evaluation isomorphism. No arbitrary exceptional functor, map, or endpoint isomorphism is supplied. Source: the canonical reduction identifications in the five-step reconstruction proof, and the current main-20261015 purity transport statement. The LeanSearch, LeanFinder/Loogle and Mathlib/upstream/project grep searches above are retained in its mathlib_searches; none provides this normalized composite. This is a missing comparison construction, not a replacement for the underlying coefficient, tensor, site or exceptional operation.

`def-pur-adic-exceptional-system-realization` now owns
`Sheaf.Paper.IntegralExceptionalInverseImage` and all its declarations. It introduces
only the ambient strict-system realization required by the reconstruction, with
explicit quotient coordinates, the specified ordinary etale system right adjoint,
site transport, and total derived inverse limit. Its new named theorem
`integralExceptionalInverseImage_on_ctf` identifies this functor naturally with
`S.ring.operation c (.integral { carrier := E }) |>.G` followed by the full
inclusion, for every recorded `ConstructibleExceptionalCoefficients.System S`.
The theorem compares functors on the whole finite-Tor constructible subcategory,
so it includes all morphisms and proves preservation without assuming it. It has
no smoothness or purity hypothesis and does not depend on this reconstruction.
No object is selected from its Nonempty natural-isomorphism conclusion.

The new node also records three characterizing statements for the selected helpers:

- `integralExceptionalComparison_characterization` gives unique isomorphisms of
  the derived inverse and direct images against any package with the same ordinary
  geometric image. It fixes them by the full cochain representative equation and
  right-derived unit equation, respectively.
- `integralExceptionalSupport_characterization` gives the unique isomorphism from
  the selected ordinary open extension to any left adjoint of the same geometric
  open inverse image, fixed by its Hom transpose. The proper part is already fixed
  by its universal right-derived unit; exact localization fixes their composite.
- `integralExceptionalAdjoint_characterization` gives the unique isomorphism from
  the selected system right adjoint to any right adjoint of that same compact-support
  functor, with its Hom-transpose equation. This fixes the corresponding finite
  evaluation and quotient mates by their existing adjunction equations.

All three selected helpers retain the section, derived-unit, transpose, transition,
and evaluation normalizations of the original recorded structures. The statements
assert uniqueness of compatible isomorphisms, not equality of chosen resolutions.
All four added theorems have source citations and full natural-language proof
instructions. Their proofs are `sorry`, as required in stage 2.

Fresh searches: LeanFinder for the canonical comparison of an integral exceptional
strict-system inverse limit with the constructible right adjoint gave eight unrelated
condensed/inverse-system hits. Loogle found the general
`Adjunction.homEquiv_symm_rightAdjointUniq_hom_app`, which supports the characterization
route, but no specialized realization. LeanSearch returned rightDerivedUnique,
leftDerivedUnique, rightDerived_ext and general derived-adjunction results. Mathlib
CategoryTheory grep for integralExceptional/exceptional System returned no hits.
Upstream and shared-library rg found only the distinct condensed-ring
IntegralExceptionalRestriction theorem; blueprint_refs search for exceptional system
realization found zero nodes. The raw msearch results are retained in the new node.
The existing ordinary coefficient System is used rather than duplicated.

## Dependency modules

`def-weil-derived-pullback-tensor-hom` owns the dependency repair in
`Sheaf.Paper.DerivedPullbackTensorHom`. Its recorded implementation exceeded the
60-second file limit during the immutable-head check. The saved repair retains
all 51 declaration signatures and bodies, enables the two backward definitional
equality transparency settings, and marks only nine scalar/common-stage comparison
maps `no_expose`. Object definitions and stage projections remain exposed. The
canonical K-flat/evaluation and scalar normalization equations, all coefficient
universes, and all mathematical data are unchanged. The node changes only `lean`,
with a note explaining this compiler-interface repair. A fresh exact comparison
confirmed that removing these attributes and options recovers the published source.

The sandbox copy of `def-weil-exceptional-inverse-image` has NM's current
43-declaration, `existing: true` record verbatim. It produces no dependency-record
change in the delivery. The existing node's statement, stmt_deps and all other
fields are also unchanged. The ambient construction has been reassigned to the
new definition node above, and every declaration docstring names that owner.
The item gains that new definition dependency. The new etale-realization and
purity-object nodes explicitly cite this realization where they use its ambient data.

## Repair of the immutable-head return

H13/H4: restored NM's binding, reassigned the ambient module to the owned new node,
and added the natural identification with System on all ctf objects and maps.
The original U, V, actual positive reductions, finite smoothPurityMap, IsIso gamma,
ctf endpoint conclusions, exact quotient-linear reduction identity at every n+1,
and coherent strict-tower lift G are retained literally. The selected comparison,
compact-support and right-adjoint helpers now have the named characterization
statements above. This is a source and node repair, not a report-only re-push.

## Second reading by N0

Author self-check only; the maintainer performs independent review. I read the
immutable-head return, NM's live node binding, the full System/Operation/RingSystem
signatures and their normalizations, the ambient strict-system module, and the
current main-20261015 reconstruction statement and proof. The eleven clause
correspondences in Worker report remain valid. The new identification has exactly
the same integral coefficient field and the canonical compactification as the
construction. It quantifies over every normalized System and its ambient natural
isomorphism entails constructible preservation; no extra preservation premise or
arbitrary replacement exceptional map is introduced. The three characterization
equations retain the actual representative, universal-unit and Hom-transpose data.
I checked exponent one, identity f, d=0, empty schemes and the zero input again;
none is excluded by these changes. Site objects remain in u+1 and morphisms in u;
no new universe equality or ramification restriction is used.

## Validation

The modified IntegralExceptionalInverseImage module compiled cleanly through
scompile.py, including both sandbox and library-file passes. The complete repaired
packet then passed deliver2.py --no-push: commit 5983a139a9 passed current-server
compilation of all thirteen modules and the 43 retained declaration checks, followed
by the server preflight. The wrapper confirmed against current server sources after
the local cache lacked OrdinaryFiniteP1Arrows. The staged list contains the twelve
owned new definition nodes, the item, thirteen modules and this report; it contains
no change to def-weil-exceptional-inverse-image. Final local checks verified exact
module ownership, all 37 declarations of the newly owned ambient module, verbatim
primary signatures, explicit autoImplicit false, line widths, and sorry-only theorem
proofs. No compiler limits or launcher tools were changed.

## Revalidation of the 76c20af30ac6 return

On 2026-10-18, the required first dry run of the saved packet passed as commit
5b7202ccd9 against current server sources. All thirteen delivered modules compiled
in both sandbox and library-path checks, and the retained 43-declaration dependency
probe and server preflight passed. The reported DerivedPullbackTensorHom timeout
did not recur. Following the repair brief's saved-packet instruction, the Lean
sources and node records are retained without further changes.

The author self-check reread the actual source, target, canonical reduction maps,
finite smooth-purity arrow and coherent-lift clauses. Each remains the construction
described in the eleven clause correspondences above. All thirteen modules have
exactly one owning node, verbatim primary signatures, explicit autoImplicit false,
lines of at most 100 characters, and no debug commands or axiom declarations.
Comparison with the current shared DAG confirms that the item changes only lean
and adds the twelve new definition dependencies; the existing
def-weil-exceptional-inverse-image node is unchanged. No compiler limits, launcher
tools, live sources or published artifacts were edited.

## Current saved-packet repair

The required first dry run in this session failed before compilation: ten helper
node copies lacked their `lean` records, although all thirteen Lean modules were
retained. Restored those records from the retained packet metadata and regenerated
the primary signatures and declaration lists from the actual current modules.
Restored the twelve helper ancestry paths, the item's missing exceptional-system
realization dependency, and that dependency in the two modules using its ambient
construction. The exceptional-reduction node cites the derived site comparison
that its module actually imports. The ordinary site node describes its ordinary
comparison; the separate derived node continues to own the derived comparison.
The live `def-weil-exceptional-inverse-image` record is retained unchanged.
No Lean source was changed in this repair.

The current base attaches the upstream
`AlgebraicGeometry.Etale.exists_iso_realization_twistShiftPullbackLevel` to the item.
I opened its full signature and docstring in
`WeilConjectures.EtaleCohomology.Purity.Smooth.Adic`. It explicitly covers only the
reconstruction step, assuming normalized systems S,T, level identifications eS,eT,
compatible arbitrary isomorphisms and arbitrary homotopy limits. It does not state
the full unchanged blueprint claim. The item's `lean.note` records this distinction;
the retained theorem uses the actual integral input, source, exceptional target,
finite smooth-purity maps, coherent lift and quotient-linear reduction equation.

Author self-check reread the current blueprint statement, the complete main theorem,
the source/target definitions and canonical reduction composites, and the ambient
exceptional construction with its characterizations and comparison to every System.
The eleven hypothesis/clause correspondences above still apply. Exponent one,
dimension zero, identity morphisms, empty schemes and zero inputs remain included.
Static checks confirm thirteen unique module owners, all twelve added dependencies,
verbatim primary signatures, explicit autoImplicit false, 100-column lines, no debug
commands or axioms, and sorry-only theorem proofs. The current delivery dry run passed file compilation by current-server confirmation
after the side overlay lacked a published dependency artifact. Server preflight
then reported two missing dependency citations in the new etale-realization and
purity-object statements. Added those explicit citations to the already listed
exceptional-system-realization dependency. No Lean declaration changed. Earlier
validation entries describe earlier runs; final preflight is being repeated.

## Saved-packet author self-check, 2026-10-18

Retained the saved thirteen Lean modules and all node records. Reread the main
statement, actual integral source and exceptional target, finite smooth-purity
arrow, canonical source and target reduction composites, and coherent-lift equation.
The eleven clause correspondences in the Worker report still describe these exact
terms. The edge cases remain exponent one, dimension zero, identity morphisms,
empty schemes, and zero complexes; the site universes remain distinct.

A fresh static check verified thirteen unique module owners, verbatim primary
signatures in every owning record, explicit autoImplicit false, 100-column lines,
and absence of debugging commands or axiom declarations. Compared with the current
shared DAG, the item changes only lean and adds the twelve owned definition
dependencies. The def-weil-exceptional-inverse-image copy is unchanged. No Lean
source, compiler limit, launcher tool, live source, or published artifact was edited.



## Dependency modules: immutable-head timeout repair

`def-weil-derived-pullback-tensor-hom`, module
`Sheaf.Paper.DerivedPullbackTensorHom`, is an inherited prerequisite of
`thm-pur-finite-coefficient-smooth-purity`. The first dry run reproduced the
returned 60-second timeout in both the side overlay and current-server confirmation.
A profiler-only sandbox copy localized repeated expansion of coefficient-category
instance terms across the scalar and common-stage comparison declarations.
The module is repaired under §1(B), preserving all 51 declaration signatures and
bodies: only nine comparison-map definitions gain `@[no_expose]`, and the two
backward definitional-equality transparency settings already used throughout this
packet are enabled. The object definitions and their literal coefficient-stage
projections remain exposed. No compiler limit is changed and no file is split.
The canonical K-flat/evaluation, scalar, and common-stage normalization equations
and all finite/integral/rational/common-stage operations are unchanged.
The dependency node changes only lean, with an explanatory note.

The diagnostic all-definitions no_expose test was rejected because object stage
projections must unfold in the public statements; it is not delivered. The retained
repair hides only comparison implementation bodies. Final validation follows via
the prescribed complete packet dry run and independent maintainer review.

## Current repair self-check, 2026-10-18

The required first saved-packet dry run compiled all fourteen delivered modules
and the retained dependency-declaration probe successfully. Server preflight then
reported one report-format fault: the exact `## Dependency modules` section did
not name `def-weil-derived-pullback-tensor-hom`. Moved its repair explanation into
that section. No Lean declaration or node record changed during this session.

Author self-check reread the main statement and its actual source/target, positive
reductions, finite smooth-purity arrows, canonical comparison maps and coherent
strict-tower lift. The eleven clause correspondences above remain applicable.
Static checks verified one owner per delivered module, explicit autoImplicit false,
100-column lines, and absence of debug commands and axiom declarations. The
dependency repair differs from the published implementation only by the two
elaboration options and nine no_expose attributes; all signatures and bodies
are identical. The main node changes only lean and adds the twelve definition
dependencies; the repaired dependency changes only lean, and the exceptional
inverse-image dependency copy remains unchanged.
