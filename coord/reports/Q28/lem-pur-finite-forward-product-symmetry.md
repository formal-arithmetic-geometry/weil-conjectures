## Worker report

This is the repair of the H3 return at immutable head `3e6529fad425`.
The required first dry run of the retained packet passed at `21fe001531`.
The saved concrete constructions are retained. The self-check makes the witness threading
explicit in the formal conclusion and rebases the imports on the current recorded dependency.

`Sheaf.Paper.FiniteForwardProductSymmetry` supplies the concrete construction helpers
and the single postponed theorem
`AlgebraicGeometry.ProEtale.finiteForwardProduct_symmetry`.
The theorem now concludes `FiniteForwardPurityProductSymmetry C f g M N wM wN`:
the specified `wM` and `wN` pairs are parameters of that conclusion. Unfolding the
predicate gives `FiniteForwardProductEquation`, which quantifies over both five-field
ordered tensor-domain hypotheses before asserting the concrete morphism equality.
The ambient canonical maps are independent of the antecedent choices, as ensured by
the fully faithful comparison in the recorded normalized compositor.
No natural-language statement correction, new node or new dependency module is needed.

Hypotheses and clauses, checked against the full natural statement:

- The finite purity conventions are `C : WeilConjectures.PurityFiniteSetting`.
  The coefficient ring is exactly `C.Coefficient`, the standard ULift of
  `O_E/(varpi_E^n)`, with the fixed prime, finite subextension and positive level
  retained in C. `finiteForwardCoefficient` derives its finiteness from the
  existing coefficient-extension finiteness theorem, rather than assuming an
  arbitrary finite coefficient ring.
- The three schemes B, X, Z have `Over (Spec (CommRingCat.of C.field.k))` instances.
  For each structure map, `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`
  render separated finite type. The named maps f and g have `IsOver`,
  `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` hypotheses. The latter
  two classes together mean finite type.
- P is the dependency's chosen Mathlib `pullback f g`; p and q are its
  `pullback.fst` and `pullback.snd`, furnished by `IsPullback.of_hasPullback f g`.
  The forward target uses h = q followed by g. The swapped target uses p followed
  by f; `finiteForwardProductSwap` transports along the cartesian equation
  `sq.w : p ≫ f = q ≫ g`. Thus h=fp=gq is retained, with no freely chosen map h.
- M and N are `DerivedCategory.Plus` objects of ordinary fixed-scalar module
  sheaves on the small pro-etale sites. `wM` and `wN` are the recorded
  `Scheme.FixedEtaleOriginWitness` structures, retaining each bounded-below
  etale antecedent and its specified comparison isomorphism. Both values are
  explicit parameters of the conclusion predicate. The canonical ambient maps
  themselves depend only on the underlying complexes.
- `d` and `d'` are `FiniteForwardProductDomain` conditions for the two orders.
  Each has five fields: `input` is Rf_!M tensor Rg_!N on B;
  `firstProjection` is N tensor Lg^*Rf_!M on Z;
  `transposedProjection` is Lg^*Rf_!M tensor N on Z;
  `exchanged` is Rq_!Lp^*M tensor N on Z; and `external` is
  Lp^*M tensor Lq^*N on P. Every field asserts the existing
  `DerivedCategory.plusEtaleOrigin`, which includes boundedness below.
  The opposite-order condition includes the reversed input tensor on B and
  the corresponding three tensors on X and external tensor on P. These ten
  conditions cover every tensor in both displayed composites; no boundedness
  of auxiliary ambient tensors inside compactifications is assumed.
- `finiteForwardProduct` defines Xi, in the exact order of the six arrows:
  (1) `finiteForwardTensorSymmetry` on B;
  (2) the component of `projectionMap` for g at (N,Rf_!M);
  (3) `Rg_!.map` of the symmetry on Z;
  (4) `Rg_!.map` of `(derivedTensor ...).map Ex`, evaluated at N;
  (5) `Rg_!.map` of `projectionMapOfCompactification` for q at (Lp^*M,N);
  (6) the normalized composition comparison at the external tensor, using
  `finiteForwardCompactificationComparison` followed by
  `(originCompositionAmbient A q g).hom.app ⟨_, d.external⟩`.
  The implementation combines arrows (3) and (4) inside one functor-map call.
  `Ex` is the actual `rightDerivedLowerShriekOfCompactificationBaseChangeMap`.
  PF_q uses exactly the base change of the chosen compactification of f,
  so its compact-support functor is definitionally the codomain of Ex.
  A `HasCompactification` instance alone would not prescribe its chosen data.
  Accordingly, the last arrow explicitly includes the canonical compactification
  comparison to the independently chosen q compactification before the recorded
  normalized compositor. The comparison descends the etale canonical refinement
  comparison through the fully faithful site comparison; it is not an arbitrary
  isomorphism. This is alpha for these explicit compactification coordinates.
- `finiteForwardTensorSymmetryNat` uses `leftDerived₂Lift` on the existing
  `derivedTensor`, its `DerivedCategory.Qh` comparison, and the actual signed
  homotopy-complex braiding. This is the same universal-property construction
  as `DerivedMonoidal.braidingNatTrans`, exposed directly on the finite tensor
  interface to avoid expensive instance conversion. `finiteForwardTensorSymmetry`
  evaluates it at the two objects. No braiding is chosen from a Nonempty assertion.
  `finiteForwardProjectionMap` only exposes the two components of the existing
  `projectionMapOfCompactification`, with their actual source and target; it
  defines no alternative projection transformation.
- Both cartesian orders are represented on the same P, the second by `sq.flip`.
  This is the unique canonical identification with the swapped fibre product:
  the legs on P are exchanged, so the scheme map is the identity in these
  coordinates. `finiteForwardProductSwap` is the canonical h-equality transport
  followed by `Rh_!.map` of the signed tensor symmetry on P. This is precisely
  the source's S after identifying the two cartesian presentations, rather than
  an arbitrary comparison arrow.
- `FiniteForwardProductEquation` is the displayed equation over a general finite
  ring A, quantifying over the two ordered tensor-domain proofs.
  `FiniteForwardPurityProductSymmetry` specializes it to the prescribed purity
  ring and has a real Prop-valued body. It derives
  CompactSpace and QuasiSeparatedSpace for B, X, Z from their separated finite-type
  structure maps. It retains the two specified witness values as parameters,
  then quantifies over both ordered tensor-domain proofs and states the actual equality. This wrapper avoids adding topological
  assumptions merely to synthesize the Nagata instances.
- The theorem states the actual equality Xi = input sigma followed by the
  swapped Xi followed by S. No constructibility, finite-Tor, invertibility,
  exceptional-adjoint or abstract six-functor datum is an input. Compactifications
  are supplied by the existing Nagata instance under the stated finite-type
  hypotheses, not by additional hypotheses in the theorem.

Dependency declarations used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  its field/coefficient/extension/level data, and `Coefficient`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; the cartesian cone and its flip.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: the current recorded
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage` interface.
  The finite components are the existing upstream transformations
  `rightDerivedLowerShriekOfCompactificationBaseChangeMap` and
  `projectionMapOfCompactification`, imported directly from the finite-coefficient
  `Derived.LowerShriekBaseChange` and `Derived.LowerShriekProjection` modules.
  These are exactly the three finite components identified in the original
  dependency's `finiteExchangeProjection`; no alternative exchange or projection
  transformation is defined. The separate supplied-domain module is imported as
  recorded, preserving Q14's current dependency record.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`:
  `originCompositionAmbient`, the ambient component of the recorded
  `originComposition` on the full bounded-below origin subcategory.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness`.
- `Sheaf.Paper.DerivedPullbackTensorHom` is imported for the dependency's
  derived-operation interfaces. The ordinary fixed-scalar coordinates here use
  the existing upstream `derivedTensor` and exact derived `upperStar`, whose
  ringed-site equivalents the dependency also supplies. No new tensor or
  pullback functor is defined. The concrete derived signed braiding is used.

Proof dependencies already stated are imported: the finite direct-image compositor,
finite derived tensor functoriality, and
finite pullback-composition interface, plus the Mathlib adjunction, mate-pasting and
Grothendieck-sheaf modules of the matched leaves. Unstated proof-dependency nodes have no module
to import. The theorem docstring records all seven proof steps from the node:
compactification reduction, open comparison symmetry by full faithfulness, the two
proper transposes, normalization of the composite adjunction, tensor counit symmetry,
and substitution of the compactification factorizations.

Edge cases: zero complexes and the empty scheme are permitted. Identities and
arbitrary fibre products are covered by the same constructions. No nonempty or
nonzero condition is introduced. The degree-zero pair Z/2,Z/2 over Z/4 demonstrates
why boundedness of inputs alone would not imply the external-tensor hypothesis;
the repaired domain retains it explicitly and never replaces it by finite Tor
amplitude. Signed symmetry is used in every degree, including odd shifts. The
positive coefficient level comes from C.level_pos, as in the source.

Searches repeated during repair:

- `msearch.py ... leanfinder "compact support forward external product symmetry derived sheaves"`:
  eight generic sheaf/condensed tensor and pushforward-composition results;
  none identifies the compactification-based Xi composites.
- `msearch.py ... loogle "CategoryTheory.Functor.LaxBraided"`: twelve generic
  LaxBraided results, requiring a supplied braided functor; none constructs Xi.
- `msearch.py ... grep "derivedTensor.*(symm|braid)|rightDerivedLowerShriekProjection"`:
  zero hits. Direct source inspection found the relevant finite-coefficient
  projection and exchange modules and the concrete derived braiding.
- `rg -n "finiteForward|forward product|Xi_"` on the named upstream SixFunctors
  directory and project Paper directory: no exact prior theorem.
- `grep -rn "lem-pur-finite-forward-product-symmetry"` on upstream
  WeilConjectures: no declaration for this node.
- Read the full dependency signatures and docstrings, using `scompile.py --source`
  for the current finite-coefficient modules absent from the older checkout.
  Read Stacks sites-cohomology.tex, section Projection formula and
  remark-compatible-with-diagram, and the DAG proof. The source tag states the
  projection/base-change compatibility; the DAG explicitly identifies this
  compact-support symmetry as an agent-formulated consequence with its own proof.

## Repair of returned delivery

H3 asks to thread the retained M/N witnesses and every ordered tensor-domain
hypothesis into the formal conclusion. The theorem has the explicit binders
`wM : Scheme.FixedEtaleOriginWitness X C.Coefficient M` and the corresponding `wN`.
Its conclusion now passes both values to `FiniteForwardPurityProductSymmetry`.
That predicate evaluates `FiniteForwardProductEquation` at the chosen cartesian
square and the actual underlying objects, which binds both `d` and `d'` of
`FiniteForwardProductDomain`. Each record requires all five fields listed above;
therefore the equation is asserted under all ten conditions. Only `external`
is needed to type each normalized compositor; the other fields remain part of
the theorem's quantified hypotheses. None is replaced by an inferred finite-Tor
condition or omitted because an ambient arrow can be typed without it.

The saved dependency packet predates Q14's recorded
`Sheaf.Paper.ExchangeProjectionSuppliedDomains` repair. The current main record
was read and retained. Our stale dependency node/module copies were removed
from the delivery, and the theorem imports the recorded module plus the existing
finite transformations directly. This preserves every body of the saved concrete
construction and avoids replacing another group's newer dependency interface.
The packet contains only the item's module, its node's lean-field update, and
this report. The earlier report's claim to include four adapted consumer modules
was inaccurate; no such consumer changes are part of this delivery.

## Second reading by Q28

This is a direct second reading by the same worker: the dispatcher explicitly
prohibits starting other agents. I reopened the natural statement, the complete
module, and the current dependency signatures and docstrings. The retained
construction already defines Xi and S concretely, fixes the purity
coefficients and field schemes, binds the witness pairs, and quantifies over both
ordered domains. This reading found two remaining issues: the named conclusion
predicate did not take the witnesses explicitly, and the dependency override was
stale against Q14's newer record. Both are repaired as detailed above.
Both orders use the same cartesian
scheme with the legs exchanged, so no factor-swap map is lost. The two targets
are connected by the actual cartesian structure-map equation and Rh_! of the
actual signed external symmetry. The product's last arrow evaluates the recorded
normalized compositor at exactly the external tensor, using its explicit origin
condition. Its intermediate projection compactification is exactly the
base-changed one used by the exchange, so there is no arbitrary endpoint
identification. The current recorded dependency is imported without editing it.
No natural-language
node statement is changed. The theorem signature in lean.statement was regenerated
verbatim after threading wM and wN into its conclusion.


## Validation

The initial required retained-packet dry run passed at `21fe001531`, including
its per-file checks and maintainer preflight. After the two self-check repairs,
scompile.py compiled the delivered module both as a sandbox file (22.7 s) and at
its library path (30.3 s), with no errors or warnings. The final packet is then
checked again using the prescribed deliver2.py --no-push wrapper before pushing.
All introduced variables and universes are explicit (`autoImplicit false`),
all Lean lines are at most 100 characters, and the only postponed proof is
`finiteForwardProduct_symmetry := by sorry`, with its seven-step proof docstring.
No diagnostic commands, raised time limits, hollow data or alternative operation
maps are included. The item's natural statement, statement dependencies and proof
are unchanged; only lean is updated, in the prescribed JSON layout.
