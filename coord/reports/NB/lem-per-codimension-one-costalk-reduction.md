## Worker report

This retained stage-2 packet states `AlgebraicGeometry.Etale.codimensionOneCostalkReduction`
in `Sheaf.AlgebraicGeometry.CodimensionOneCostalkReduction`. It defines the ordinary
and geometric costalk functors separately in
`Sheaf.AlgebraicGeometry.EtaleGeometricCostalk`. The only postponed proof in this
packet is the named main theorem, whose docstring reproduces all nine proof steps
and names their DAG dependencies. All auxiliary definitions have real data.

Hypotheses and clauses, checked with the node and both modules open:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`; the coefficients are
  `ULift.{u + 1} (ZMod ℓ)`, the same prime field in the coefficient universe.
- `X : Scheme.{u}` and `[IsNoetherian X]` mean the stated Noetherian scheme.
  Mathlib's `isNoetherian_iff_of_finite_affine_openCover` identifies this with
  a finite cover by Noetherian affine schemes.
- `hExcellent : ∀ z : X, ∃ U : X.affineOpens, z ∈ U.1 ∧ IsExcellent Γ(X, U.1)`
  expresses precisely an excellent affine cover. `hInvertible` requires that
  ell is a unit in every residue field, equivalently that it is invertible on X.
- Bounded below small-etale module complexes are
  `DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))`.
  No constructibility, boundedness above, regularity or perfectness is imposed.
- `localClosedPoint X z` is `Spec.map (X.residue z)` on the ordinary local ring.
  `etaleCostalk R X z` first applies inverse image along `X.fromSpecStalk z`,
  then `closedSupportPlus R (localClosedPoint X z)`. The published closed
  adjunction constructs this last functor as the derived supported kernel,
  uniquely determined as the right adjoint of exact closed pushforward.
- `etaleDerivedGeometricStalk` derives the exact `pointSmallEtale` sheaf fibre.
  `etaleGeometricCostalk` composes the ordinary costalk with that functor at
  `Spec.map ((Scheme.SpecToEquivOfField Ω X) s).2`. This uses the specified
  geometric residue embedding, rather than choosing another geometric point.
- The theorem's first universal clause compares `geometricCostalkPresentation` with
  `strictLocalCostalkPresentation`. Their `.functor` fields unfold to the original
  `etaleGeometricCostalk` and `strictLocalSupportedCostalk`. The predicate contains
  their natural isomorphism and `NatTrans.CommShift e.hom ℤ`.
- Geometric points are `x : Spec (.of Ωx) ⟶ X` and `y : Spec (.of Ωy) ⟶ X`
  with explicitly bound algebraically closed fields. The specialization is
  `s : strictLocalization y ⟶ strictLocalization x`, with the exact over-X
  equation `s ≫ strictLocalizationToBase x = strictLocalizationToBase y`.
- `codimensionOneClosureIdeal s` is the vanishing ideal of the closure of
  the image of `Spec.map (strictHenselizationEval y) ≫ s`.
  `codimensionOneClosure s` is its subscheme, with the canonical immersion
  `codimensionOneClosureι s`. Mathlib's vanishing ideal gives the reduced
  induced structure. The immediate-specialization hypothesis is exactly
  `topologicalKrullDim (codimensionOneClosure s) = 1`.
- The conclusion supplies `hIntegral : IsIntegral (codimensionOneClosure s)`;
  this is concluded, not assumed. The predicate then asserts Noetherianity
  and an isomorphism with `Spec B` for an excellent strictly henselian local
  ring B. The dimension is already the immediate-specialization hypothesis.
- `codimensionOneComplex R s` is precisely L: inverse image of K to the strict
  localization followed by `closedSupportPlus R (codimensionOneClosureι s)`.
- Normalization and its map are the published
  `(codimensionOneClosure s).normalization` and `.fromNormalization`.
  `IsFinite` and `(topologically IsHomeomorph).universally` state the two
  claimed properties of that actual map. The next existential identifies
  the actual normalization with `Spec D`, for D a domain, a discrete
  valuation ring, and a strictly henselian local ring.
- Generic-point equality under `.fromNormalization`, together with `IsIso`
  of its generic residue-field map, states that the generic point and its
  field are unchanged.
- The existential closed points `z₀,t₀` are closed and every point specializes
  to them; their images agree. `HasPrimeToResidueDegree` uses the algebra
  structure from this very normalization map's `residueFieldMap t₀`.
  Its four conjuncts are finiteness, pure inseparability, degree one in
  characteristic zero or a characteristic power otherwise, and invertibility
  of the degree in `ZMod ℓ`. No unrelated algebra structure is supplied.
- The set-valued `lowerStar` is an equivalence, equivalently its inverse-image
  left adjoint is an equivalence. The next conjunct explicitly states the
  module-valued `upperStar` equivalence used on the complexes.
- `yZ,xZ,yN,xN` are geometric points with the original fields. Their equations
  fix the two points on the closure and their lifts to the normalization.
  Their image equations identify generic and closed points, and the two
  universal equality clauses express uniqueness of both normalization lifts.
- The final four `HasTwistShiftCompatibleIso` conjuncts render, in order,
  `C_y(K) ≅ C_y(L)`, `C_y(L) ≅ (ν*L)_eta`, `C_x(K) ≅ C_x(L)`, and
  `C_x(L) ≅ RΓ_{t₀}(normalization,ν*L)`. Each is a functor isomorphism in K.
- Tate compatibility now evaluates the actual `supportTensorPlus` at
  `finiteEtaleTateSheaf (ULift (ZMod ℓ)) ℓ X hℓ a`, for every integer a. Over the
  coefficient field exact degreewise tensor computes tensor derived from the
  ordinary tensor, hence this is precisely `K(a)=K ⊗ᴸ Λ(a)` on D+.
  The output twist is tensor by the geometric fibre of that SAME Tate sheaf.
  Each presentation is constructed, not existentially chosen: inverse image uses
  `supportTensorPullbackPlus`, support uses `supportTensorMatePlus` (the mate of
  inverse closed projection), and stalk uses `Functor.Monoidal.commTensorRight`.
  Coefficient fibres are identified by `upperStarCompSheafFiberIso`. The last
  supported-sections computation uses one actual sheaf basis and its image in the
  geometric fibre; unitors normalize both sides. The predicate asserts existence
  of these section-leaf bases, invertibility of each fixed passage, and the concrete
  square `P.passage ≫ e(K(a)) = (e(K) ⊗ id) ≫ Q.passage` for EVERY basis.
  Thus it does not quantify over arbitrary endofunctors or arbitrary passage maps.

Dependency declarations used (all read with their signatures and docstrings):

- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`;
  `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsNoetherian`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the module-valued
  `DerivedCategory`, `DerivedCategory.Plus` encoding documented there;
  current source was read through `scompile.py --source` because the older
  local upstream checkout lacks that module.
- `Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction`:
  `AlgebraicGeometry.Etale.supportedKernel` and `supportedClosedInverseImage`.
- `Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange`:
  `AlgebraicGeometry.Etale.closedSupportPlus`, its adjunction and shift
  instance, and `indEtale_closedSupport_baseChange` for the proof plan.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `residue`,
  `Hom.residueFieldMap`, `SpecToEquivOfField`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`.
- `Sheaf.AlgebraicGeometry.StrictHenselization`: `Scheme.strictHenselizationRing`,
  now an abbreviation for the upstream `strictHenselization`; the compatibility
  module publicly imports this recorded dependency. The scheme, its base map,
  and evaluation are upstream's `strictLocalization`,
  `strictLocalizationToBase`, `strictHenselizationEval`.
- `Sheaf.AlgebraicGeometry.EtaleSupportedSections`: `supportedEtaleSections`
  and its `rightDerivedFunctorPlus`.
- `WeilConjectures.Mathlib.RingTheory.Henselian`:
  `IsStrictlyHenselianLocalRing`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`:
  `Scheme.normalization`, `Scheme.fromNormalization`.
- `Mathlib.CategoryTheory.MorphismProperty.Limits`: `MorphismProperty.universally`,
  with `AlgebraicGeometry.topologically` and `IsHomeomorph`.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`: `Scheme.finiteEtaleTateTwist`;
  `Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf`: `Scheme.finiteEtaleTateSheaf`;
  the inverse-image comparison is the exact degreewise monoidal comparison rather
  than a selected unbounded comparison from `etaleFiniteTwistPullback`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint` and the sites
  point API: `Scheme.pointSmallEtale`, `Point.sheafFiber`, with exact derived
  functor machinery. These supply the recorded geometric-stalk notion.

The main module retains all recorded proof-dependency modules. Mathlib leaves
(such as adjunction composition, localization Noetherianity, irreducible closed
subsets of a spectrum, and field degree multiplicativity) are already available
through those modules' public imports. No new prerequisite theorem is assumed.

Edge cases checked: the empty scheme gives vacuous geometric-point and
specialization quantifiers; dimension zero is excluded only by the required
immediacy hypothesis; the normalization is not assumed integral before its
integrality witness is produced; zero complexes and all bounded-below complexes
are allowed; ell=2 is allowed; positive residue characteristic different from ell
and characteristic zero are both covered; residue degree p^0=1 is included;
residue fields need not be perfect. Negative twists use duals, and shifts range
over all integers. Schemes and geometric fields share universe u, while module
sheaves and coefficients use u+1, following the project's small-site convention.
Every universe and variable is explicitly bound; `autoImplicit` is false.

Searches retained from `searches.jsonl` and the new node's `mathlib_searches`:
LeanFinder queries for geometric costalks, strict localization, and normalization
of an immediate specialization returned structure-sheaf stalk/localization
lemmas, not this costalk statement. LeanSearch queries for derived supported
inverse images returned `Scheme.kerAdjunction` and module pullback/stalk lemmas,
not the required module-valued geometric costalk. Loogle `"costalk"` returned no
hits; the DVR/strictly henselian queries returned no matching combined statement.
The msearch grep queries `costalk|supportedClosedInverseImage|strictLocalization`
and `etaleCostalk|etaleGeometricCostalk|supportedModuleKernel` returned no Mathlib
match. Direct searches in `WeilConjectures`, `lean/Sheaf`, and `dag/nodes` plus
`tools/blueprint_refs.py search costalk` were repeated on the current sources:
only unrelated closed-costalk duality and downstream uses of geometric costalks
were found. No existing ordinary/geometric costalk functor or this reduction
statement was found. The existing support adjunction and strict-localization
constructions are reused, not copied.

Source checked: the saved Exposé XVII text, Definition 1.1.1 and its footnote,
section 1.3 and Definition 1.4.1 (printed pp. 258–262), agrees with the node's
ordinary-local definition, strict-local comparison and normalization reduction.
There is no statement correction or disputed statement.

Repair validation: both packet modules compiled separately through `scompile.py`.
The main statement typechecks in about four seconds. The published
`RegularClosedSupportBaseChange` source was supplied read-only to the wrapper as a
prerequisite overlay because its olean was absent from the live build; it compiled
cleanly too. No source or artifact in either read-only checkout was edited.

## New nodes

`def-per-etale-geometric-costalk` packages the ordinary-local costalk, its
specified geometric fibre, and the strict-local supported-cohomology target.
Source: Exposé XVII Definition 1.1.1 and its footnote. Searches above, retained
verbatim in its `mathlib_searches`, found the existing ingredients but no DAG
node defining this combined notion. The module only composes the published
inverse-image, closed support, geometric-stalk and supported-sections functors;
it does not assert the comparison later proved by the item. Its finite-ring
setting includes the item's prime field. The item cites this node explicitly.

## Returned points repaired

H3/H5: removed the arbitrary T,S naturality square, its old basis-only proposition,
and the interrupted attempt's ill-typed existential over a theorem proof. The actual
Tate tensor endofunctor now occurs in the square. Every passage is fixed by a
constructed presentation of the original costalk computation. Closed support uses
`supportTensorMatePlus` with its projection/counit normalization; inverse image and
stalk use the canonical monoidal maps. The supported-sections leaf removes a real
sheaf basis and inserts its geometric fibre, so the two bases are linked by the
actual monoidal fibre functor. Both existence and invertibility are stated, avoiding
vacuous universal quantification over bases. All four original comparisons and the
strict-local comparison receive this same concrete condition.

H2: removed `lem-asd-etale-finite-twist-pullback` from stmt_deps, as expressly allowed
in the return. Its existential c/d witnesses are not needed when using exact
D+ tensor and pullback, computed on complexes by the fixed ordinary monoidal maps.
The native signed sheaves remain `finiteEtaleTateSheaf`, not copies or arbitrary
trivial endofunctors. Generic monoidal pullback keeps their literal inverse images;
there is no need to choose a native-line identification at intermediate stages.
This is the exact-representative form of the same canonical pullback comparison.
The tensor and mate definition nodes were added to stmt_deps. The general helper
constructions in `RegularClosedSupportBaseChange` are reused; its regular-base-change
theorem and its Tate-isomorphism theorems are not invoked.

## Second reading by NB

Author self-check, with the node and both modules open: each hypothesis and geometric
conclusion listed above is preserved from the returned head. The geometric
presentations unfold to exactly the same five functors (including each of the four
final comparisons). The new square's input really is the signed Tate sheaf tensor,
and its output really is the fibre of that same sheaf. In the stalk and closed
support branches there is no basis choice: monoidal fibre and projection mate fix
the passage. Section-leaf bases are linked to their fibres by `sheafFiber.mapIso`,
so changing a basis cannot choose an independent output map. The old universal
arbitrary-endofunctor square is absent. Empty X, ell=2, zero complexes, negative
Tate powers and arbitrary integer shifts remain covered. No statement correction,
extra geometric hypothesis, or unrecorded theorem was introduced. Every new helper
has real data and a source/blueprint docstring. The only postponed proof is the
main named theorem, with its nine-step source proof plan retained.

## Delivery gate failure

Final saved packet: both delivered modules compile without errors or warnings through
`scompile.py`, when the existing published `RegularClosedSupportBaseChange.lean` is
supplied as a read-only prerequisite in the same invocation. The main file takes
about four seconds. The helper source is not part of this delivery and was not edited.

The required `deliver2.py NB lem-per-codimension-one-costalk-reduction --no-push`
failed before preflight: `INFRASTRUCTURE RETRY (stale live olean)` and
`object file .../Sheaf/AlgebraicGeometry/RegularClosedSupportBaseChange.olean
of module Sheaf.AlgebraicGeometry.RegularClosedSupportBaseChange does not exist`.
The source was verified with `scompile.py --source`; compiling that exact source as
an additional prerequisite succeeds. The delivery wrapper has no prerequisite-file
argument and omits that published source from its private overlay. No launcher tool
was modified, no dependency source was copied or restated, and no delivery was pushed.

Retry validation (2026-10-18 UTC): inspected the retained packet and reran the required
dry run before making any changes. It failed on the same missing published olean.
Then `scompile.py` with the read-only published prerequisite plus both packet modules
returned exit code 0: the prerequisite compiled in 5.0 seconds, the costalk definition
in 2.5 seconds, and the main module in 9.8 seconds, without errors or warnings.
A subsequent `deliver2.py --no-push` again returned exit code 1 on the missing
`RegularClosedSupportBaseChange.olean`, explicitly identifying it as
`INFRASTRUCTURE RETRY (stale live olean)` and saying it is not the delivery's fault.
The interrupted compilation result was unavailable, so that read-only validation was
rerun; no delivery mutation or push was repeated. Both retained Lean modules and node
records are unchanged. The prescribed delivery remains blocked by the wrapper's
omission of this published prerequisite from its private overlay.

Dispatcher retry validation (2026-10-18 UTC): the required first dry run again
failed on the missing published `RegularClosedSupportBaseChange.olean`. The retained
packet was compared with the current shared node: only `lean` and the authorized
`stmt_deps` additions differ, and the recorded main signature matches the source.
Both retained module sources and the concrete Tate-tensor square were reread.
`scompile.py` with the existing read-only prerequisite and both packet files then
completed successfully: costalk 2.5 seconds, prerequisite 5.2 seconds, main statement
7.5 seconds (library check 9.8 seconds), with no errors or warnings. A second dry run
still failed before preflight on exactly the same missing prerequisite olean, with
`INFRASTRUCTURE RETRY (stale live olean)`. The Lean and node files remain intact;
no launcher tool or read-only checkout was modified and nothing was pushed.

Dispatcher retry validation (2026-10-19): inspected the retained repair before the
required first dry run. That dry run and a retry after successful compilation both
failed with `INFRASTRUCTURE RETRY (stale live olean)` because the published
`Sheaf.AlgebraicGeometry.RegularClosedSupportBaseChange.olean` is absent. A search
of the current library confirms that the actual tensor/pullback/projection-mate
helpers used by this packet remain in that module; replacing them would duplicate
existing notions. The authorized `scompile.py` invocation supplied the unmodified
read-only prerequisite and both packet modules and returned exit code 0 with no
errors or warnings (costalk 2.5 s, prerequisite 5.0 s, main 7.5 s, library check
9.8 s). The recorded main signature still matches the file verbatim; both files
respect the 100-character limit. Compared with the current shared node, only
`lean` and the four recorded `stmt_deps` additions differ. The concrete signed
Tate-tensor square, canonical pullback/support/stalk passages, basis existence,
and absence of the arbitrary-endofunctor square were checked again. The unused
finite-twist-pullback theorem dependency remains removed. No Lean or node record
was changed, no launcher script was modified, and nothing was pushed. Delivery
requires the published prerequisite artifact or delivery-tool overlay repair.

Continuation after provider interruption (2026-10-19): checked all completed tool
results before repeating any delivery. The required initial dry run and the retry
after validation both exited 1 before preflight with the explicit tool diagnostic
`INFRASTRUCTURE RETRY (stale live olean)` for the missing published
`Sheaf.AlgebraicGeometry.RegularClosedSupportBaseChange.olean`. Nothing was pushed.
The authorized `scompile.py` invocation with the unmodified read-only published
prerequisite and both packet modules exited 0, without errors or warnings:
costalk 2.5 s, prerequisite 5.2 s, main sandbox 7.5 s, main library check 9.8 s.
Compared the retained node with the current shared node without Git: only `lean`
and the four documented statement-dependency additions differ; the new definition
node is still absent from the shared base. Both recorded signatures are verbatim
and both modules satisfy the 100-character limit. Reread the concrete signed-Tate
tensor square and its pullback, closed-projection-mate, stalk and linked-basis
passages; the arbitrary-endofunctor square remains absent. No Lean or node record
needed further change. The published prerequisite is reused rather than duplicated.
No launcher script or read-only checkout was modified. Delivery remains blocked
by the delivery wrapper not providing that published prerequisite artifact.

Final retry validation (2026-10-19): the initial dry run still reported the
missing published prerequisite artifact. The authorized scompile.py invocation
with the unmodified read-only prerequisite and both packet modules passed without
errors or warnings (costalk 2.5 s, prerequisite 5.0 s, main sandbox 7.5 s, main
library check 9.8 s). The subsequent required deliver2.py --no-push passed
preflight and compilation, producing dry-run commit ad4723628f. Both recorded
signatures are verbatim and all Lean lines meet the 100-character limit. Compared
with the current shared node, only lean and the four documented stmt_deps
additions differ. The concrete Tate-tensor compatibility square and its canonical
pullback, projection-mate, stalk and linked-basis passages remain intact; the
unused theorem dependency and arbitrary-endofunctor square remain absent. The
earlier delivery gate failure is now resolved. No Lean or node changes were
necessary in this retry; the saved mathematical repair is retained.
