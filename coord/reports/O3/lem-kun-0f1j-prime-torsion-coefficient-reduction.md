## Worker report

This repairs return L at immutable head 43dd54e8d55d, using the retained
Q127 maintenance packet. The main declaration is
`AlgebraicGeometry.Etale.primeTorsionCoefficientReduction` in
`Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReduction`. Its statement and
sole theorem `sorry` are retained. The ten helper modules contain constructions,
aliases of the published functors, or explicit predicates; they prove no theorem.
The mathematical item statement and its proof plan are unchanged. Its statement
dependencies gain all ten helper nodes, including the two explicitly requested
in F4. The item record is based on the current read-only newtargets-dag copy.

Sources reread: Stacks `etale-cohomology.tex`, Tag 0F1J,
`lemma-punctual-base-change-upgrade`, especially the prime-torsion paragraph;
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/` followed by
`sk-prop-sf-kunneth-ordinary/lem-kun-0f1j.proof.md`, reduction to prime torsion;
and all eight steps of this item's DAG proof. The quotient and representative
constructions expand Tags 03EK and 06YU as specified by that proof.

Hypotheses and clauses, matched individually:

- The field is `(K : Type u) [Field K]`; `aX` and `aS` are the two displayed
  structure maps to `Spec (CommRingCat.of K)`.
- The five schemes and five projections are explicit. `left : IsPullback p f'
  aX aS` expresses X'=X times_K S', and `right : IsPullback e h g f'` expresses
  Y=X' times_S' T. These permit all isomorphic choices of the fibre products.
- `[QuasiCompact g] [QuasiSeparated g]` are exactly the qcqs hypothesis on g.
  There are no finite-type, Noetherian, or flatness assumptions on these maps.
- `n ell : ℕ`, `hn : 1 ≤ n`, `hnK : IsUnit (n : K)`,
  `hell : Nat.Prime ell`, and `hd : ell ∣ n` give every modulus hypothesis.
- The coefficient rings are `ULift.{u+1} (ZMod n)` and
  `ULift.{u+1} (ZMod ell)`. `primeCoefficientHom n ell hd` conjugates
  `ZMod.castHom hd` by the ULift ring equivalences: it is the canonical quotient.
- E ranges over small-etale R-module sheaves on X. `ObjectProperty.flat E`
  expresses exactness of both tensor functors in the published constant-ring
  presentation. The symmetry of sheaf tensor identifies the two exactness
  conditions, so this is the node's flatness hypothesis. This uses the upstream
  specialization without rebinding `def-pc-flat-sheaf-modules`.
- F ranges over small-etale k-module sheaves on T. Its R-module sheaf is
  `(Sheaf.restrictScalars ...).obj F`. Since R to k is the quotient by ell,
  these are exactly R-module sheaves annihilated by ell, with their induced
  k-action. The canonical coefficient restriction is the published
  ModuleCat-valued functor; the general ring-sheaf dependency record is retained.
- `primeCoefficientQuotient` is `Sheaf.composeAndSheafify` of
  `ModuleCat.extendScalars`. For this ring quotient it is the sheaf E/ell E,
  rather than an unjustified sectionwise equality. `primeCoefficientQuotientUnit`
  is the unit of the extension/restriction adjunction.
- The first conjunct of `PrimeTorsionCoefficientReduction` asserts flatness of
  this quotient for every flat E. No flatness of R to k is assumed.
- `sourceIso` is a natural isomorphism of functors of F. Its source is scalar
  restriction followed by `primeTensorSource R`; its target is
  `primeTensorSource k` for the quotient of E followed by derived restriction.
  Expanding the functor gives exactly p-inverse E tensor^L
  (f')-inverse Rg_*F on the two coefficient sides.
- `targetIso` similarly gives Rh_*(h-inverse p-inverse E tensor^L e-inverse F).
  `primeTensorTarget` tensors before applying Rh_*.
- The next two equations impose naturality for every map `δ : E ⟶ E'` between
  flat sheaves, using `primeTensorSourceMap` and `primeTensorTargetMap` and
  the map of the quotient functor. Together with the natural isomorphisms in F
  these render joint naturality in E and F.
- `PrimePunctualCoefficientNormalized` fixes those same isomorphisms by two
  coefficient isomorphisms Φp and Φhp, after p and after h followed by p.
  The pulled coefficient map is the inverse image of the quotient unit followed
  by the canonical inverse-image/scalar-restriction comparison. The supplied
  rho and rho-prime are the exact degree-zero pullback computations.
- `PrimeTensorCoefficientNormalized` now quantifies over EVERY cochain complex C
  of k-sheaves. `primeTensorInputComplex` is M[0] tensor U_C(C), and
  `primeTensorOutputComplex` is U_C(N[0] tensor C). Thus bounded-below complexes,
  all shifted sheaves, and every former input C=Z[0] are included. Step 4 of the
  DAG proof explicitly computes the tensor for any C using the flat first factor.
- For each C there is a chain map t; `PrimeTermwiseTensorCompatibility` requires
  its formula on EVERY total tensor summand i+j=k. Its equation is the input
  summand inclusion followed by t.f k equals q_0.f i tensor 1, followed by the
  canonical lax restriction tensor map and the restricted output inclusion.
  `primeTensorTermMap` is the degree-zero q with the exact restriction/single
  interchange. This is precisely x tensor y maps to q(x) tensor y, including
  the zero first-factor terms in nonzero degrees and every differential of C.
- `PrimeTensorLocalizationCompatibility` compares Q(t) with Φ at Q_B(C), using
  the same Φ witnesses as the source and target equations. Its six typed arrows
  are fixed by HEq to rho, rho-prime, the canonical restriction-factor components,
  and Q's lax tensor maps. The final equality is the homogeneous localization
  diagram. No arrow is an unconstrained presentation. This retains maintenance's
  conversion repair; the expensive prefix/postfix wrappers are not restored.
- In particular, take C to represent (f')-inverse Rg_{*,k}F. The source equation
  uses the canonical direct-image restriction mate for g and inverse-image
  comparison for f', followed by Φp at THAT derived object. This component is
  now constrained by the representative formula, not only by its values at Z[0].
- The target equation uses Φhp at e-inverse F and the direct-image mate for h.
  In diagrammatic order it reads b followed by V_h equals Rh_* of the local
  tensor coefficient map. The source equation reads tensor(Lf'(V_g)) followed
  by a equals tensor(U_f') followed by Φp. These are Steps 5 and 6 with their
  stated canonical map directions.
- The final equation is `kappa_R ≫ b = a ≫ U(kappa_k)`.
  `primeTensorComparison` is the retained alias of
  `punctualTensorBaseChangeMap`. I read its definition: it is the adjunct along
  h of the pullback tensor comparison, the right-square inverse-image
  identification, and tensor with e-inverse of the counit for g. Therefore the
  equation compares the specified counit-adjoint maps, not arbitrary arrows.
- The ambient categories are the recorded `DerivedCategoryModule` and global
  K-flat-derived tensor. E and F start in degree zero; exact inverse image,
  bounded-below direct image and tensor with the flat first factors keep the
  expressions in D+. Since D+ is strictly full, these are exactly its morphisms.

Recorded declarations and actual source interfaces read:

- `Mathlib.AlgebraicGeometry.Scheme`, the pullback API and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `Scheme`, `IsPullback`,
  `QuasiCompact`, `QuasiSeparated` supply the geometry.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`; Mathlib `DerivedCategory.Plus`
  supplies the strictly full bounded-below subcategory.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`:
  `AlgebraicGeometry.Etale.derivedTensor` and `laxMonoidal_Q` are the existing
  K-flat-derived tensor and localization structure, not replacements.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `upperStar`, `lowerStar`, `upperStarLowerStarAdjunction`, with their published
  derived functors. The primeSingle/Pullback/Pushforward aliases fix universes.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars`:
  `CategoryTheory.Sheaf.restrictScalars`, composition with
  `ModuleCat.restrictScalars`; its exact derived functor and localization
  factorization are used through the published derived interfaces.
- `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic`:
  `CategoryTheory.ObjectProperty.flat`, exactness of tensorLeft and tensorRight.
  This is used directly for constant-coefficient sheaves, as requested in F1.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite` retains the general ring-sheaf binding and is
  imported for the proof dependencies. It is not rebound to ObjectProperty.flat.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` retains the general ring-sheaf binding. It is
  not rebound to `CategoryTheory.Sheaf.restrictScalars`.
- Mathlib `Sheaf.composeAndSheafify`, `Sheaf.adjunction`,
  `ModuleCat.extendScalars`, `ModuleCat.extendRestrictScalarsAdj` give the
  sheafified quotient and its actual unit. The restriction lax tensor map is
  supplied by `WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal`.
- `Sheaf.Paper.EtaleUnboundedRestrictionComparison`:
  `scalarRestrictionPullbackIso` and `scalarRestrictionDirectImageMap` are the
  canonical ambient inverse-image square and its direct-image mate.
  `Sheaf.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons` supplies
  `upperStarRestrictScalarsIsoSheaf` and the degree-zero pullback computation.
- `Sheaf.AlgebraicGeometry.PunctualTensorBaseChange`:
  `AlgebraicGeometry.Etale.punctualTensorBaseChangeMap` supplies the actual
  counit-adjoint arrow. Its theorem is not used. A stage-3 proof import from
  that parent back to this item would close a module cycle and must be omitted.

The helper declarations listed below are imported through their recorded modules.
The main module retains its canonical-comparison imports and the comparison alias.
The proof docstring retains all eight DAG steps. No proof is attempted.

Edge cases checked: n=1 has no prime divisor, hence the hypotheses are vacuous;
n=ell is the identity coefficient case; n=ell squared with E=R permits the
non-flat quotient ring map, while E=k is not flat over R and cannot be substituted.
E=0, F=0 and empty schemes are allowed. C=0, C=Z[0], shifted degree-zero complexes
and a bounded-below representative of Rg_*F all occur in the normalization.
For nonzero first-factor degrees, the total tensor summand has a zero first
factor; its formula is still required. No site/coefficient universe equality is
added: schemes use u, module carriers and coefficients use u+1 as recorded.

Searches retained from the original packet (raw results are in mathlib_searches):

- LeanFinder: `Flat etale Z/n module sheaf tensor F_l sheaf derived direct image
  scalar restriction comparison` and `Prime torsion coefficient reduction for
  the punctual etale tensor comparison with counit compatibility`: generic
  flatness and tensor hits; no exact statement.
- Loogle: `"restrictScalars", "tensor"`: ordinary module tensor restriction
  results, no punctual derived comparison.
- LeanSearch: `Derived etale tensor comparison under quotient coefficient
  restriction for a flat sheaf`: ordinary quotient tensor and flatness results.
- msearch grep: `restrictScalars.*[Tt]ensor|[Tt]ensor.*restrictScalars` in
  `Algebra/Category/ModuleCat`: ordinary scalar restriction infrastructure.
- For representative normalization: LeanSearch `Sheaf quotient coefficient
  tensor chain map normalization via localization of complexes` returned generic
  localization and ordinary quotient results; Loogle `"mapDerivedCategoryFactors",
  "tensor"` returned no hits. Mathlib grep `mapDerivedCategoryFactors|
  singleMapHomologicalComplex` identified the exact functor/single interfaces used.
- DAG and blueprint searches found the ordinary module change-of-rings lemma and
  the degree-zero-only `lem-trf-site-derived-tensor-restriction`, neither of which
  specifies this item's two canonical derived arrows and their mate compatibility.
  rg of WeilConjectures and lean/Sheaf found no duplicate prime coefficient or
  representative normalization notion. This repair generalizes those existing
  helper definitions rather than introducing any new notion or helper extraction.

No mathematical statement correction or STATEMENT-DISPUTED issue is needed.

## Repairs of return L

F1: removed BOTH sandbox dependency files `def-pc-flat-sheaf-modules.json` and
`def-pc-sheaf-restrict-scalars.json`. Their newtargets-dag records are retained
unchanged. The item uses the upstream constant-coefficient flatness and scalar
restriction declarations directly, as explained above. There is no §1(B) repair.

F2: generalized the second factor to an arbitrary cochain complex C in the input
and output complexes, Termwise, Localization and Compat, and in all four owning
new-node statements. The same Φ is now fixed on Q(C) for every representative,
including (f')-inverse Rg_*F. Every degree-zero Z[0] case remains included. The
choice of arbitrary C follows the item's existing proof Step 4 verbatim; restricting
to bounded-below representatives is unnecessary for the flat-first-factor identity.
The source and target direct-image comparisons are still used only on D+ inputs.

F3: added the Termwise module's Source line and exact blueprint tag
`def-kun-prime-coefficient-termwise-normalization`.

F4: added `def-kun-prime-coefficient-constructions` and
`def-kun-prime-coefficient-termwise-normalization` to the item's direct stmt_deps.
All ten helper nodes are now cited directly, as well as through the helper DAG.

F5: replaced the stale second reading with the actual N3 reading below and the
clause-by-clause checks above. Removed the earlier incorrect claims that testing
only Z[0] already fixed the component at (f')-inverse Rg_*F.

The maintenance repair is retained: explicit arrow endpoints, HEq to canonical
arrows, the homogeneous localization diagram, and the original main imports and
comparison alias. No backups were restored, no helper extraction restarted, and
no proof or additional sorry was introduced.

## New nodes

All ten nodes below are new definition nodes owned by this packet, in the item's
chapter and unit. Their original searches and source provenance are retained.
The four complex/normalization node statements and their Lean records are updated
together for F2. Every module path starts with `Sheaf.AlgebraicGeometry.`.

| Helper node | Module suffix |
| --- | --- |
| `def-kun-prime-coefficient-constructions` | `PrimeTorsionCoefficientReductionFoundation` |
| `def-kun-prime-coefficient-functors` | `PrimeTorsionCoefficientReductionFunctors` |
| `def-kun-prime-coefficient-pullbacks` | `PrimeTorsionCoefficientReductionPullbacks` |
| `def-kun-prime-coefficient-complexes` | `PrimeTorsionCoefficientReductionComplexesCore` |
| `def-kun-prime-coefficient-iso` | `PrimeTorsionCoefficientReductionNorm2` |
| `def-kun-prime-coefficient-complexes-input-output` | `PrimeTorsionCoefficientReductionNorm3` |
| `def-kun-prime-coefficient-term-map` | `PrimeTorsionCoefficientReductionNorm4` |
| `def-kun-prime-coefficient-termwise-normalization` | `PrimeTorsionCoefficientReductionTermwise` |
| `def-kun-prime-coefficient-localization-compatibility` | `PrimeTorsionCoefficientReductionLocalization` |
| `def-kun-prime-coefficient-normalization` | `PrimeTorsionCoefficientReductionCompat` |

`def-kun-prime-coefficient-constructions` supplies the lifted quotient map,
sheafified extension of scalars, its adjunction unit and the balanced tensor arrow;
it aliases the existing single, inverse-image and direct-image functors. Source:
0F1J's coefficient identity, expanded by 03EK and 06YU. The common searches above
found the generic upstream operations, which are used, but no bundled coefficient
construction node. No new tensor or scalar-restriction functor is defined.

`def-kun-prime-coefficient-functors` names the two displayed punctual tensor
expressions and their natural maps in E. Source: the two terms in 0F1J and the
item's Steps 5-6. The same searches found the generic functors, not this interface;
the definitions compose those published functors.

`def-kun-prime-coefficient-pullbacks` constructs the pulled coefficient arrow with
the canonical restriction comparison and aliases the exact single-pullback
computation. Source: 0F1J and the item's Step 3. The same searches found generic
comparison isomorphisms, reused here, but no node owning this specific arrow.

`def-kun-prime-coefficient-complexes` names M[0], termwise restriction, Q, its
canonical restriction factors and its given lax structure. Source: 06YU as used
in 0F1J and Step 4. The searches found these upstream constructions, reused
verbatim; the node supplies their fixed-universe interface for this normalization.

`def-kun-prime-coefficient-iso` is the type of natural coefficient tensor
isomorphisms D tensor U(-) iso U(D' tensor -). Source: 0F1J's coefficient
identification and Step 4. The common searches found no separate node naming this
interface. This is a type abbreviation, not an existence assertion or a choice.

`def-kun-prime-coefficient-complexes-input-output` defines M[0] tensor U_C(C)
and U_C(N[0] tensor C), with arbitrary cochain complex C. Source: 0F1J,
03EK/06YU and Step 4. The common searches found the total tensor construction,
which is reused, but no node naming this pair of coefficient complexes.

`def-kun-prime-coefficient-term-map` constructs q_0 from singleFunctor.map q and
the exact single/restriction interchange. Source: 0F1J and Step 4. The common
Mathlib grep located singleMapHomologicalComplex; it is used directly rather than
reconstructing that canonical comparison. No previous node owns this q_0.

`def-kun-prime-coefficient-termwise-normalization` requires the canonical
coefficient formula on every i+j=k tensor summand, with arbitrary C. Source:
03EK/06YU and Step 4 of the 0F1J reduction. The searches found generic total tensor
inclusions, reused here, but no predicate prescribing this coefficient formula.

`def-kun-prime-coefficient-localization-compatibility` gives the homogeneous
localization equation for that t and the same Phi at Q(C). Source: 06YU and
Step 4 of the 0F1J reduction. The searches found the exact restriction factors
and Q's lax structure, but no predicate relating this t and Phi. Each typed
witness is fixed to the corresponding canonical arrow by HEq.

`def-kun-prime-coefficient-normalization` requires termwise and localization
compatibility for every C, including every Z[0], together with the ordinary
coefficient isomorphism. Source: 0F1J's coefficient identification, 03EK/06YU and
Step 4. The common searches found no equivalent representative normalization.
This is an explicit proposition; no arbitrary chosen data or helper theorem is
postponed in any of these definitions.

## Second reading by N3

I reopened the item's statement and proof, the source prime-torsion paragraph,
the main module and all ten helper modules after making the repairs. This is the
worker's separate second pass; the maintainer supplies the independent review.

I checked the field, both scheme structure maps, the two pullback witnesses, qcqs,
n>=1, invertibility, primality and divisibility against the exact binders. I
expanded the lifted quotient map, the sheafified coefficient quotient and its unit.
The two flatness predicates match the constant-coefficient specialization, while
the two shared general ring-sheaf records are absent from the delivery.

I expanded the source and target functors and their E-maps. sourceIso and targetIso
are natural in F, their two δ-equations give E-naturality, and the last equation
is kappa_R followed by b equals a followed by U(kappa_k). The comparison alias
uses the parent's counit-adjoint definition. I checked both normalization equation
directions against Steps 5-6, including the direction of the direct-image mate.

For F2 I specifically followed the formerly missing case: choose C representing
(f')-inverse Rg_{*,k}F. The outer universal quantifier now includes C; t is fixed on
all i+j=k summands, its localization uses Φp at Q(C), and derived naturality
transports this component to Φp at the displayed derived object. The same
normalization applies to Φhp. C=Z[0] for every sheaf Z and shifted sheaves are
still included. The six HEq constraints identify their typed witnesses with
canonical data; the remaining localization equality is not reflexive.

The ordinary IsIso conjunct is retained as an ordinary quotient-tensor identity;
it is not used as a substitute for the all-complex representative normalization.
No arbitrary ring-map flatness, pointwise quotient equality, arbitrary map or
unconstrained isomorphism replaces a specified construction. The geometric and
coefficient edge cases above still apply. Definitions have no sorry; the sole
postponed proof is the named main theorem with its eight-step proof docstring.
The main theorem signature, item statement and proof plan are unchanged.

## Validation

Validation of the retained maintenance packet was run first with the prescribed
`deliver2.py N3 lem-kun-0f1j-prime-torsion-coefficient-reduction --no-push`.
The repaired packet passed the prescribed scompile.py invocation on all 11 files
(exit 0, no diagnostics). The final library checks took 20.8 seconds for Termwise,
5.5 seconds for Localization, 3.6 seconds for Compat and 21.8 seconds for the main
module, all within the unchanged 60-second limit. Every file was checked
separately in dependency order against the published library plus its private
overlay. Static checks confirmed exact signatures, line width, all ten direct
helper dependencies, no shared dependency record changes, and exactly one sorry.
A fresh deliver2.py --no-push runs the server preflight before normal delivery.
