## Worker report

The module `Sheaf.TraceFormula.SemistableNormalTargetFactorization` states
`AlgebraicGeometry.Temkin.semistable_normal_target_factorization`, with one `sorry`
and no new definitions. Its docstring carries all eight proof steps and their dependencies.
The construction of normalization is Mathlib's actual relative integral closure, rather
than an existential normal model. The embedded marking is an existential presentation
of the specified schematic closure, characterized by equality of ideal sheaves, as in the
existing `FlatClosure` interface. No object is defined by choosing from a postponed theorem.

Source checked: Temkin, *Stable modification of relative curves*, arXiv:0707.3953v3,
§1.2 (printed p. 2), §4 opening conventions and Remark 4.1 (pp. 24--25), Lemma
4.4.1(i) (p. 30), and the first sentence of the proof of Lemma 4.4.4 (p. 31).
The author-hosted PDF timed out; the identical v3 was read at
[arXiv](https://arxiv.org/pdf/0707.3953).
The source agrees with the node: normalization in the smooth generic fibre is the
absolute normalization; it is finite and an S-curve, and its marking is the closure
of the generic marking. The contraction equivalences are the finite-fibre argument
expanded in the node's final proof step, not an additional quoted theorem of Temkin.

Hypotheses and clauses, in order:

| Node clause | Lean rendering |
| --- | --- |
| Separably closed field K | `B : HorizontalValuationBase.{u}` supplies `B.K`, `B.fieldK`, and `B.sepClosedK : IsSepClosed B.K`. |
| V is a valuation subring of K with fraction field K | The same existing structure supplies `B.V`, its `CommRing`, `IsDomain`, `ValuationRing`, `Algebra B.V B.K`, and `IsFractionRing B.V B.K`. The algebra map is injective, so an abstract V with this map is exactly an embedded valuation subring; no chosen embedding condition is lost. |
| Finite chain of prime ideals | `B.finitePrime : Finite (PrimeSpectrum B.V)` and `B.primeChain : ∀ p q, p ≤ q ∨ q ≤ p`. |
| T = Spec V and eta = Spec K | `B.T` is definitionally `Spec (.of B.V)` and `B.genericMap` is `Spec.map (CommRingCat.ofHom (algebraMap B.V B.K))`. |
| Original multipointed T-curve (X,D) | `P : MultipointedCurve B.T`, with its original curve, marking, structure maps, and closed immersion. Flatness, finite presentation and relative purity are fields of this existing definition. |
| Smooth generic curve | `hSmooth : Smooth (pullback.snd P.x B.genericMap)`. |
| Etale generic marking | `hEtale : Etale (pullback.snd P.d B.genericMap)`. |
| f : (Y,E) -> (X,D) is a semistable eta-modification | `Q : MultipointedCurve B.T`, `f : Q.Hom P`, `hf : f.IsEtaModification B.genericMap`, and `hQ : Q.IsSemistable`. Both curve and marking properness, schematic density, and generic isomorphisms are exactly the recorded dependency predicate. |
| Specified relative normalization N and its map nu | `(pullback.fst P.x B.genericMap).normalization` and `.fromNormalization`, using `Mathlib.AlgebraicGeometry.Normalization`. The first existential witnesses prove the qcqs conditions needed by that construction; these are conclusions, not added hypotheses. |
| N is normal | For every `z` of this exact normalization, `IsDomain (N.presheaf.stalk z) ∧ IsIntegrallyClosed (N.presheaf.stalk z)`. This includes reducible/disconnected normal schemes without asserting `IsIntegral N`. |
| N flat and finitely presented over T, pure relative dimension one | `hn : RelativeCurve (nu ≫ P.x)`, whose fields are flatness, local finite presentation, quasi-compactness, quasi-separatedness, and purity of every fibre in dimension one. |
| nu is finite | `IsFinite (pullback.fst P.x B.genericMap).fromNormalization`. |
| nu is an eta-modification and N_eta is isomorphic to X_eta | The concluded `horizontalClosurePairMap ... .IsEtaModification B.genericMap` contains the curve modification and `IsIso` of its canonical generic base-change map. This is the specified isomorphism over Spec K, not an unrelated abstract isomorphism of schemes. |
| D_N is the schematic closure of D_eta inside N | `D`, `i`, and `hD : FlatClosure (nu ≫ P.x) B.genericMap (horizontalGenericMarkingι P B.genericMap nu) i`. Its `closureIdeal` is precisely `i.ker = (j ≫ pullback.fst _ _).ker`, the ideal of functions restricting to zero on the generic marking. The generic marking is canonically pulled back along the generic normalization isomorphism. |
| (N,D_N) is a multipointed T-curve | `horizontalClosurePair ... i hn hD`, whose curve is definitionally N, marking is D, and marking inclusion is i. Its full multipointed data are constructed by the dependency definition from hn and hD. |
| nu extends to an eta-modification of pairs | `r : D ⟶ P.D`, `hr`, `hi` give the base and marking commutativities; `horizontalClosurePairMap ... r hr hi` has the asserted pair `IsEtaModification`. |
| Factorization of pairs f = nu after g | The existential `g : Q.Hom (horizontalClosurePair ...)` satisfies `f.curve = g.curve ≫ nu` and `f.marking = g.marking ≫ r`; these are exactly equality on both components of pair morphisms. |
| g is a semistable eta-modification with unchanged source and marking | `g.IsEtaModification B.genericMap`, and g's source is definitionally the original Q. The original `hQ` supplies semistability for this very source. The fields Q.X, Q.D, Q.i, Q.x and Q.d are all unchanged. |
| Contracted components in each ordinary fibre agree | For every `t : B.T` and `C ∈ irreducibleComponents (Q.x.fiber t)`, the images under `Q.x.fiberι t ≫ f.curve` and `Q.x.fiberι t ≫ g.curve` are subsingleton iff each other. These are images in the original targets, as in the node. |
| Same assertion after any geometric base change | The last universal clause ranges over every `Ω : Type u`, `[Field Ω]`, `[IsAlgClosed Ω]`, every `s : Spec (.of Ω) ⟶ B.T`, and every irreducible component of `pullback (C := Scheme) Q.x s`. It compares the images under the existing canonical `f.curveBaseChange s` and `g.curveBaseChange s`. It does not assume that a component is the base change of an original component. |
| Singleton, not possibly empty image | Every member of `irreducibleComponents` is irreducible and nonempty. Its image under either total map is nonempty. Consequently `Set.Subsingleton` is equivalent here to being a singleton, in both the ordinary and geometric clauses. |

Dependency declarations read and reused:

- `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed` (the field hypothesis; the node's other
  recorded declaration `IsSepClosure` was also read but no separable-closure extension
  occurs in this statement).
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`.
- `Sheaf.TraceFormula.MultipointedCurve`: `AlgebraicGeometry.MultipointedCurve`.
- `Sheaf.AlgebraicGeometry.MultipointedCurveModification`:
  `MultipointedCurve.Hom`, `.Hom.IsEtaModification`, `.IsSemistable`,
  `.Hom.curveBaseChange`, `.Hom.markingBaseChange`, and `.markingBaseChange`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Normalization`: `Scheme.Hom.normalization`,
  `.fromNormalization`, and the integral-closure diagram specifying their meaning.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`;
  normality is the existing inline conjunction with `IsDomain`, stalk by stalk.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents` and `IsIrreducible`.
- `Sheaf.TraceFormula.ValuationHorizontalCurveModels`: `HorizontalValuationBase`, its
  `T` and `genericMap`, `RelativeCurve`, `horizontalGenericMarkingι`, `FlatClosure`,
  `horizontalClosurePair` and `horizontalClosurePairMap`. The existing definitions are now owned by
  `def-trf-horizontal-valuation-curve-data`, cited in `stmt_deps`. The theorem
  `lem-trf-valuation-horizontal-curve-models` remains solely in `proof_deps`; no theorem
  conclusion or `.choose` is used by the signature. The item's mathematical statement is unchanged.

All recorded project proof-dependency modules are imported: NormalSectionsFiniteProduct,
FlatInvertibleSectionsTorsionFree, GeometricallyReducedEtaNormal,
SmoothGeometricallyNormal, ValuationCurveProjectivePreparation, and
ValuationHorizontalCurveModels. The Mathlib proof leaves are imported through their
own modules for residue-field fibres, quasi-finite discrete spectra, properness,
Noetherianity, qcqs permanence, finite presentation, normalization and closed-immersion
kernel factorization. No dependency interface needed repair.

Edge cases checked before writing: V = K (height zero and generic map an isomorphism);
empty original and source curves; empty markings; disconnected and reducible curves with
smooth generic fibre; nonseparated and nonproper curves over T; arbitrary residue
characteristic, including separably closed imperfect K; empty ordinary or geometric
fibres, which have no components; identity modifications; and geometric components not
descending as an irreducible ordinary component. None require an extra hypothesis.
All schemes, field extensions and pullbacks live in the same explicit universe u,
matching Scheme's established size convention; no independent smaller test-field
universe makes the geometric clause vacuous. All binders are explicit and
`set_option autoImplicit false` is set.

Searches for an existing statement, before writing:

- `msearch.py ... leanfinder` with query "A semistable marked curve modification factors
  through the finite normalization of its target over a finite height valuation ring":
  8 hits, headed by `Scheme.Hom.normalizationDesc`, `normalizationDiagramMap`,
  `toNormalization`, and their factorization lemmas. These do not state the finite normal
  target with its closure marking, unchanged semistable source, or contraction clauses.
- `msearch.py ... loogle` with query `AlgebraicGeometry.Scheme.Hom.normalization`:
  12 hits for normalization, its cover, the canonical two maps and their instances.
  The needed construction exists and is reused; this theorem does not.
- `msearch.py ... grep` with query `semistable|normalizationDesc` under
  `AlgebraicGeometry`: 5 hits, all the general relative-normalization universal property
  in `Mathlib/AlgebraicGeometry/Normalization.lean`. Its `normalizationDesc` goes FROM
  normalization to an arbitrary integral factor, rather than stating this normal-source
  factorization and its pair and fibre properties.
- `msearch.py ... leansearch` with query "A semistable marked curve modification factors
  through the finite normalization of its target over a valuation ring": 8 hits for
  the same general normalization construction and maps, no matching statement.
- `rg -n 'semistable.*[Nn]ormal|[Nn]ormal.*factor|lem-trf-semistable-normal-target-factorization'`
  on the upstream `WeilConjectures` and side `lean/Sheaf` sources found the shared
  valuation-preparation interface and downstream proof-docstring citations, plus
  unrelated uses of normalized factorizations. None declares this theorem.
- The more precise search
  `normal_target_factorization|semistable_normal_target|lem-trf-semistable-normal-target-factorization`
  on `dag/lean_names_upstream.json`, upstream `WeilConjectures`, and side `lean/Sheaf`
  found only the downstream `ValuationExceptionalClosedImageCriterion` docstring citation.

Validation: the first compile diagnosed a category-inference ambiguity for a geometric
pullback used as a set. Explicit `(C := Scheme)` annotations repaired it. The final
`scompile.py Q81 lem-trf-semistable-normal-target-factorization` run compiled both the
sandbox and named library module cleanly (3.0 s and 3.3 s), with no errors or warnings.
The only postponed theorem is the item's named theorem. The repair adds the existing-definition ownership node below. There are no dependency
modules, mathematical statement corrections, or disputed statements.


## New nodes

`def-trf-horizontal-valuation-curve-data` records `existing: true` ownership of nine
already published definitions in `Sheaf.TraceFormula.ValuationHorizontalCurveModels`.
No Lean module or definition is copied. Its statement defines the valuation base, its
actual spectrum and generic map, relative curves, canonical generic maps and markings,
flat closure data, and the pair and pair-map constructions. Sources are Temkin §1.2,
§4 opening conventions, Remark 4.1, §4.2 opening and Lemma 3.5.1, exactly as in the existing
declaration docstrings. The shared source and `scompile.py --source` agree.
LeanSearch returned eight general valuation declarations, including `ValuationSubring`;
Loogle returned zero hits (unknown `AlgebraicGeometry.HorizontalValuationBase`);
Mathlib grep returned zero hits. Direct grep found the exact definitions only in the
published side module, and the DAG/blueprint searches found only the horizontal-model
theorem and its consumers for this interface. The existing valuation-ring definition
node is reused. Thus the new node supplies ownership, not a second definition.

Clause-by-clause check of the new node:

| Clause | Existing declaration or fields |
| --- | --- |
| Specified valuation domain, fraction field, separable closedness, finite prime chain | `HorizontalValuationBase`: `V`, `K`, `commRingV`, `isDomainV`, `valuationV`, `fieldK`, `algebraVK`, `fractionVK`, `sepClosedK`, `finitePrime`, `primeChain`. |
| Actual base spectrum and generic map | `HorizontalValuationBase.T`, `.genericMap`, given by `Spec` and `Spec.map (algebraMap ...)`. |
| Flat finitely presented pure relative curve | `RelativeCurve.flat`, `.finitelyPresented`, `.quasiCompact`, `.quasiSeparated`, `.pure`. |
| Canonical generic curve map | `horizontalGenericCurveMap`, defined using `Over.pullback`, without any existence theorem. |
| Pulled-back marking as a specified closed subscheme | `horizontalGenericMarkingι`, the actual pullback projection of `P.markingBaseChange`. |
| Closed immersion and closure ideal | `FlatClosure.closed` and `.closureIdeal`, using Mathlib `Scheme.Hom.ker`. |
| Flat finitely presented pure-zero closure | `FlatClosure.flat`, `.finitelyPresented`, `.quasiCompact`, `.quasiSeparated`, `.pureZero`. |
| Prescribed embedded generic fibre | `FlatClosure.prescribedGenericFibre`, equality of the pulled-back ideal with `j.ker`. |
| Pair constructed from the supplied data | `horizontalClosurePair`, all structure fields filled from the given schemes, maps and proofs. |
| Compatible pair map | `horizontalClosurePairMap`, with components `q` and `r`, and the two supplied commutativities `hr`, `hi`. |

Empty markings and fibres, valuation bases that are fields, and nonproper/nonseparated
curves remain allowed. The general closure interfaces quantify over an arbitrary
specified `S ⟶ T`; the node neither asserts existence of a flat closure nor assumes the
horizontal-model theorem. No additional axiom or postponed theorem is introduced.

## Repair of return L

The return on immutable head `0e2ab812e4d3` identified H2: a theorem was incorrectly
added to `stmt_deps` merely to obtain its module's definitions. The saved packet's first
required dry run passed (`453766a7f5`), but that mechanical pass did not resolve H2.
The repaired item replaces this added theorem dependency with
`def-trf-horizontal-valuation-curve-data`; the theorem is retained in `proof_deps` and
its existing import remains. The Lean module is byte-identical to the returned packet.
The item's mathematical statement, all hypotheses, all conclusions, proof and proof
dependencies are unchanged against current shared main. Only `lean` and the authorized
new-definition addition to `stmt_deps` differ from main.

The maintainer's independent reading in return L already checked the theorem clause
by clause against the node and Temkin, including ordinary and geometric components,
and found only this ownership fault. This repair's self-check re-read the existing
nine definitions and matched every new-node clause above; it does not claim to be a
new independent worker review. The maintainer also noted the same ownership pattern
in landed projective-preparation and finite-fibre-valuation-domination. Those consumers
are outside this packet and were not edited; this new definition node can be cited by
the maintainer when repairing their dependency metadata.


Repair validation (2026-10-19 UTC): `scompile.py Q81
lem-trf-semistable-normal-target-factorization` compiled the sandbox module in 2.4 s
and the named library module in 2.6 s, with no errors or warnings. The new ownership
record's declaration header is verbatim `structure HorizontalValuationBase where`;
all nine recorded declarations were read in the published module. The new node's
`stmt_deps` are exactly the ids cited in its TeX, all existing, and the item keeps the
horizontal-model theorem in `proof_deps` only. No source or tool outside this sandbox
was edited.

## Second reading by Q81

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
