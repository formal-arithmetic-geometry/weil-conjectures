## Worker report

The delivery states `lem-pur-etale-compact-scalar-coherence` in
`Sheaf.Paper.EtaleCompactScalarCoherence`. All six theorem proofs are `sorry`;
definitions have actual data. The natural scalar transformation packages the
already published componentwise proper/open map, rather than choosing a map or
an unrelated isomorphism. No source statement was corrected, no dependency record
was repaired. The repair adds one definition node recording two existing helper definitions.

Hypothesis and clause correspondence:

- Finite commutative unital coefficient rings and their unital map are
  `{A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]`
  and `φ : A →+* B`. The coefficient universe is the prescribed u+1 for
  ModuleCat-valued sheaves on the small etale site of `Scheme.{u}`.
- Schemes X,Y and separated finite-type f are `Scheme.{u}`, `f : X ⟶ Y`,
  `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`.
  `[IsNoetherian X] [IsNoetherian Y]` is the existing locally Noetherian plus
  quasi-compact scheme condition, equivalent to the stated finite affine
  Noetherian cover condition. There is no condition on the characteristic.
- A selected compactification is `c : Compactification f`: `c.i : X ⟶ c.Z`
  is open, `c.g : c.Z ⟶ Y` is proper, and `c.comm : f = c.i ≫ c.g`.
- D(T_et,A) is exactly `DerivedCategoryModule A T`, the derived category of
  `Sheaf T.smallEtaleTopology (ModuleCat.{u+1} A)`. Every unqualified input
  K or M uses this entire category. Q_T is the existing `scalarExtension φ T`.
- F_(f,R) for c is the existing
  `rightDerivedLowerShriekOfCompactification (ModuleCat R) c`.
  This unfolds to exact derived open extension followed by total derived
  proper direct image; it is not a right derived functor of their underived composite.
- The specified q_f is `compactScalarMap φ c`. Its components are literally
  `ExceptionalCoefficients.compactSupportMap φ c`: `scalarMate φ c.g` at
  the open extension, followed by proper direct image of
  `(ExceptionalCoefficients.openIso φ c.i).hom`.
  `compactScalarMap_naturality` states the component naturality equation;
  the definition packages those components and this proof as a NatTrans.
- The open balancing map is the existing adjoint-conjugate `openIso`, not
  free comparison data. `compactScalarOpen_normalization` explicitly equates
  its inverse with `properOpenCoefficientOpenInverse`. The latter is exactly
  the B open-adjunction transpose of Q applied to the A open unit followed
  by inverse scalar/pullback. Its ordinary realization is identity scalar
  tensor on the unique open summand and zero on every other summand.
- P_(f,R;K,M) is `compactScalarProjection R c K M`: tensor symmetry,
  the existing `projectionMapOfCompactification` (proper counit, inverse open
  projection, and pullback composition), and F of tensor symmetry. Thus the
  order is K tensor F(M) to F(f^*K tensor M), exactly as specified.
- The first conjunct of `etaleCompactScalarCoherence` says every component
  of q_f is `IsIso`. Since q_f is a NatTrans, this states a natural isomorphism
  on the whole derived category, without boundedness restrictions.
- The second conjunct, for every K and M, is Q(P_A) followed by q at
  f_A^*K tensor M and then F_B of `compactScalarProjectionTarget`.
  The other route is the canonical scalar tensor identification, tensoring
  q_M with the identity of QK, and P_B(QK,QM). The target helper is the
  canonical scalar tensor identification followed by the inverse of
  `scalarPullbackIso φ f` on the first factor. All source and target
  identifications are actual morphisms in the displayed equality.
- `etaleCompactScalarComposition` states the exact equation for the
  proper/open triangle-normalized `unboundedEtaleLowerShriekCompIso`.
  Lean composition runs left to right, so its left path is Q(alpha_A)
  followed by q_gf; its right path is q_g at F_f M, F_g of q_f, then alpha_B.
  `compactScalarChosenMap` selects the existing chosen compactification of
  each map, as does that comparison package. All choices are covered by the
  arbitrary-compactification comparison clause below.
- The composition input is M in `DerivedCategory.Plus` and an explicit
  existential N in the B `DerivedCategory.Plus` with N.obj = Q_X M.obj.
  These are exactly the two bounds in the node. There is no assertion that
  nonflat scalar extension preserves bounded-below objects.
- `etaleCompactScalarOpenRestriction` uses an arbitrary specified cartesian
  square `sq : IsPullback vx fv f v`, with `[IsOpenImmersion v]`.
  Thus XV is X times_Y V, vx is the induced open immersion, and fv is f_V.
  The compactification is exactly `c.ofIsPullback sq`, hence the restricted
  compactification required in the node. The source open V and its pullback
  are Noetherian as consequences of the assumptions, not extra restrictions.
  Its left path is v^*(q_c), C_B, and F_B of the scalar/vx identification.
  Its right path is the scalar/v identification, Q_V(C_A), and q at vx^*M.
  Every M in the unbounded category is quantified, with no Q(M) bound.
- The third conjunct of `etaleCompactScalarCoherence` states compatibility
  with the canonical comparison from c to every compactification d on
  M and Q_X M bounded below. This includes every proper refinement and
  every comparison through a common refinement, with the existing normalized
  isomorphisms `rightDerivedLowerShriekOfCompactificationIso`.
- The canonical coefficient unit is the existing
  `ExceptionalCoefficients.unitIso`, uniquely specified by ordinary
  multiplication B tensor_A A to B on the K-flat unit complex.
  `etaleCompactScalarUnit` states the tensor left-unit and pullback/unit
  equations. `CompactScalarTensorUnitLaw` and `CompactScalarPullUnitLaw`
  are fully defined equation predicates with shared categorical endpoints;
  they prevent expensive comparison of two syntactic presentations of the
  derived monoidal structure. The tensor predicate uses the raw normalized
  comparison, which `ExceptionalCoefficients.siteTensorIso_existsUnique`
  identifies with the site tensor comparison used in the projection square.
  The all-K projection square includes K = the coefficient unit, and the
  existing unital projection-mate statement identifies its unit specialization.
- There is no flatness, projective-dimension, smoothness, orientation,
  constructibility, dimension, or exceptional-pullback comparison hypothesis.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Mathlib.RingTheory.Noetherian.Defs: `IsNoetherianRing` and its ideal-FG meaning.
- The morphism-property convention node introduces no declaration; the
  corresponding Mathlib `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsProper`, `IsOpenImmersion`, and `IsNoetherian` encode its relevant clauses.
- Sheaf.AlgebraicGeometry.CompactifiableOverField: the record reexports
  `Compactification` and `HasCompactification` from WeilConjectures.Compactification.Defs.
  Only these definitions, not the existence theorem over a field, are needed here.
- WeilConjectures.AlgebraicGeometry.DerivedCategories and
  WeilConjectures.SixFunctors.Etale.Derived.Coefficients:
  `DerivedCategoryModule`, with the existing `DerivedCategory.Plus`.
- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and its existence statement.
  The published constant-ring specialization is `scalarExtension` and its
  `scalarExtensionRepresentative` from Sheaf.Paper.EtaleDerivedScalarTensor.
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses:
  the recorded `ringedTopoiCanonicalDerivedTensorPullback` and its unique
  representative square. The constant-coefficient normalization used in formulas
  is `scalarPullbackIso` from Sheaf.Paper.PurEtaleScalarMateProjection.
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriek:
  `rightDerivedLowerShriekOfCompactification`.
- Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension:
  `properFiniteCoefficientExtension`, on the actual `scalarMate`.
- Sheaf.AlgebraicGeometry.ProperProjectionFormula:
  `isIso_proper_projection_formula_reordered`; the compactification version
  uses `projectionMapOfCompactification` from the upstream LowerShriekProjection module.
- WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection:
  `derivedOpenImmersionLowerShriekProjectionIso`.
- Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons:
  `unboundedEtaleLowerShriekCompIso`, `unboundedEtaleCompactSupportExchange`,
  and the canonical compactification comparison maps, with their normalizations.
- Sheaf.Paper.ExceptionalCoefficientComparison: only the already published
  ordinary-etale helpers `ExceptionalCoefficients.openIso`, `compactSupportMap`,
  `tensorIso`, `tensorIso_existsUnique`, `siteTensorIso_existsUnique`, and `unitIso`.
  Neither `mateMap` nor `exceptional_coefficient_comparison` is used or assumed.
  Its DAG node remains in stmt_deps because `tensorIso` is `.choose` of
  `siteTensorIso_existsUnique`, `etaleCompactScalarUnit` directly uses
  `(tensorIso_existsUnique φ Y).choose`, and `unitIso` is `.choose` of
  `unitIso_existsUnique`. These uniquely normalized existence theorems are
  genuine statement dependencies. No exceptional-pullback comparison is assumed;
  a graph search verified no dependency path back to the present item.
- Sheaf.Paper.ProperOpenCoefficientRefinement:
  `properOpenCoefficientPullbackIso` and `properOpenCoefficientOpenInverse`.
  These two plain definitions are recorded by the new definition node
  `def-pur-open-coefficient-normalizations` in stmt_deps. The theorem node
  `lem-sf-proper-open-coefficient-refinement` remains only in proof_deps.
  Neither `.choose` nor a theorem from that module is used in the statement.

The available modules of proof dependencies are explicitly imported without public
when used only by the proof plan, including proper/open coefficient mate and refinement,
K-flat resolutions, ringed exchange/tensor coherence, projection-unit coherence,
site tensor descent, module inverse-image composition, and direct-image composition.
The recorded Noetherian and mate-pasting Mathlib matches are used through their actual
Mathlib modules. Current source for the generalized tensor-pullback interface was
also read using `scompile.py --source`, rather than guessing from an older checkout.

Edge cases checked before finalizing the statement: zero coefficients, zero objects,
empty source and empty restricting open, identity maps and identity coefficient map,
arbitrary shifts and unbounded complexes, and a nonflat change Z/4 to Z/2. In the
last case an arbitrary bounded-below object can acquire unbounded-below Tor; the
composition and refinement clauses retain exactly the additional Q(M) bound.
The projection and open-restriction clauses impose neither bound. Scheme and
coefficient universes retain the documented small-site size convention.

Searches made, all before choosing the final interfaces:

- `msearch.py ... leanfinder "Derived change of coefficients commutes with etale compact
  support and projection formula"`: 8 results, all unrelated commutative-algebra
  etale/Kaehler declarations; no compact-support coherence package.
- `msearch.py ... loogle "Sheaf.extendScalars, rightDerivedLowerShriekOfCompactification"`:
  0 hits, unknown identifier Sheaf.extendScalars. This did not justify inventing a notion.
- `msearch.py ... grep "scalarExtension|compact.*scalar" CategoryTheory`:
  0 Mathlib hits.
- `rg` through the source WeilConjectures and the shared Sheaf tree for scalar,
  lower-shriek, tensor, projection, and unit names found the published proper scalar
  mate, the open tensor package, two normalized scalar tensor interfaces, and the
  ExceptionalCoefficients structural helpers. The final module reuses the latter
  tensor/unit and proper/open components, rather than restating these constructions.
- Search for the exact item id in the older WeilConjectures source found no declaration.
  Search for the new names found no existing declaration. The theorem itself is new:
  existing scalar-extension results concern pro-etale finite-free situations or
  exceptional-pullback/finite-Tor domains, not all the ordinary-etale equations here.

Source checked: Stacks more-etale.tex, the actual remark-Rf-lower-shriek-change-of-rings
(Tag 0GL6) and its immediately preceding projection formula proof. The remark gives
ordinary scalar commutation by proper/open factorization; the node's extracted
coherence proof fixes the normalizations through Tags 0F7I, 0F7J, 0F7L and 0E48.
No disputed statement or node fault remains.

Validation: every delivered Lean declaration was compiled through scompile.py in
both sandbox and final library paths, with no errors or warnings. Early concrete
monoidal presentations timed out; the final version reuses existing canonical
comparisons and shares monoidal endpoints in the two transparent equation predicates.
The timeout limit was not raised. The final compile took 8.7 s (sandbox) and 9.9 s
(library path). No global build or direct repository write was run.

## Second reading by NB

The dispatcher explicitly prohibits starting other agents and assigns the independent
reading to the maintainer. No independent worker reading is claimed here. I reread the
node and final module, matched every hypothesis and clause above, and checked the
composition order, the directions of both open-restriction scalar identifications,
the restricted compactification, and the two bounded-below conditions. The self-check
found duplicate helper constructions in the first draft; these were replaced by the
published normalized interfaces before the successful compile. The maintainer's
independent review remains the delivery's separate review gate.

## New nodes

`def-pur-open-coefficient-normalizations` records, with `existing: true` on
`Sheaf.Paper.ProperOpenCoefficientRefinement`, exactly
`AlgebraicGeometry.Etale.properOpenCoefficientPullbackIso` and
`AlgebraicGeometry.Etale.properOpenCoefficientOpenInverse`. The first transports
the K-flat-normalized scalar/pullback comparison along the canonical exact
inverse-image identifications; the second is the B-open-adjunction transpose of
Q of the A-open unit followed by the inverse of that exact comparison. Its source
is the proper/open coefficient construction of Stacks 0GL6 and the scalar/pullback
normalization of 07A4 and 0G7E. No invertibility theorem is bundled into this node.
Its statement applies to arbitrary commutative rings and arbitrary derived inputs,
with no Noetherian or finiteness restriction. The two existing definitions have
exactly those binders. Empty opens, zero rings, zero objects, identity maps and
unbounded inputs are admitted. No Lean module or duplicate definition is added.

Fresh LeanSearch and LeanFinder queries for canonical scalar/pullback and the
open-adjunction-unit coefficient map returned eight hits each, all ordinary
module/sheaf pullback or adjunction results. Mathlib grep found zero hits for
`properOpenCoefficientPullbackIso|properOpenCoefficientOpenInverse`; upstream
WeilConjectures grep found zero. Shared lean/Sheaf grep found exactly the published
definitions and their uses in ProperOpenCoefficientRefinement. DAG grep found
only the theorem node that owns this module, not a definition node for these
plain constructions; blueprint searches for "open coefficient" and
"scalar/pullback" found no blueprint nodes. The full results are recorded in the
new node's mathlib_searches, and the wrapper searches are in searches.jsonl.

## Returned-delivery repair

The independent maintainer review of immutable head `7aa75df5b5a6` identified H2
and the theorem-stmt_dep distinction. The item now cites
`def-pur-open-coefficient-normalizations` instead of
`lem-sf-proper-open-coefficient-refinement` in stmt_deps; the latter stays in the
unchanged proof_deps. The new node records exactly the two requested plain defs.
`lem-pur-exceptional-coefficient-comparison` remains a genuine statement dependency
for its uniquely normalized tensor and unit existence theorems, as the return
explicitly permits. The Lean module and all mathematical clauses are unchanged.
Compared with the current shared base, the item changes only lean and stmt_deps;
all original statement dependencies and proof dependencies are preserved. The
delivery wrapper rebuilds the packet on current newtargets-dag.

The self-check reopened the full item statement, the Lean module, both helper
definitions and their complete signatures/docstrings, and the scalar tensor/unit
existence theorems. The new node's first clause matches the exactness transport
in properOpenCoefficientPullbackIso; its second matches the homEquiv.symm
transpose and composition order in properOpenCoefficientOpenInverse. No theorem
from ProperOpenCoefficientRefinement supplies either definition's data. The
existing second-reading clause correspondence above remains valid. No independent
agent was started because the dispatcher prohibits it.

Repair validation: scompile.py compiled the retained module cleanly in the sandbox
(8.3 s) and library path (9.5 s). The two added dependencies have no statement/proof
dependency path back to the item. All nine citations in the new definition node
match its stmt_deps exactly. The item delta is limited to lean and stmt_deps.

The first repaired dry run compiled both referenced modules but required separate
[id] citations for the two adjunction dependencies in the new node. The grouped
citation was split into two individual citations; the statement is unchanged.
