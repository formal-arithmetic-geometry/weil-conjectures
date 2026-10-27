## Worker report

The module `Sheaf.Paper.DualizingSigmaCocycleLocality` states
`AlgebraicGeometry.ProEtale.DualizingLocality.dualizing_sigma_cocycle_locality`.
Its proof is the only `sorry`. All auxiliary definitions contain real terms.
The item statement, dependencies and proof are unchanged. No statement correction,
new node, dependency repair or disputed statement is needed.

The source read was main-20261015/sec-smooth-purity/sk-prop-sp-composition/
thm-pur-composition-coherence.proof.md, Step 1, together with the item's seven
refined proof steps. The module docstring and theorem docstring explain this route.

Hypothesis and clause correspondence:

* `P : WeilConjectures.PurityFiniteSetting.{u}` supplies the finite-field datum,
  ell distinct from p, the finite extension inside its fixed algebraic closure,
  and positive coefficient level. `P.Coefficient` is the canonical size lift of
  the quotient O_E/(varpi_E^n), not an arbitrary finite ring.
* Every scheme has an `Over (Spec (.of P.field.k))` structure and the two
  `LocallyOfFiniteType` / `QuasiCompact` structure-map instances. No structure
  morphism is required to be separated. Every arrow is `IsOver` and has precisely
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`. Each smooth arrow carries
  an explicit natural relative dimension and `SmoothOfRelativeDimension`.
* The existing `FiniteEtaleNormalization` coordinates are used throughout.
  `omega`, `pull`, `comp`, `beta`, `sourceEtale`, `eta` and `rho` are the published
  constructions. Its `domain` is the pro-etale constructible-finite-Tor predicate
  on every etale-origin representative. These morphism equalities are written in
  those etale-origin coordinates, as in the normalization dependency; fully
  faithful constructible site comparison and its tensor/pullback constraints
  identify them with the original pro-etale equalities. There is no new
  exceptional adjoint or independently chosen map.
* `SigmaIsIso P` asserts invertibility of the actual published sigma for every
  smooth pair, specializing its compactification arguments to the canonical
  `compactification P`. Sigma is theta in omega-first order followed by inverse
  c at the coefficient unit; omega-first theta includes the statement's symmetry.
* `Cocycle P` renders the first displayed equality. The left route tensors sigma
  with identity and applies sigma of the composite; exceptional `congr` inserts
  associativity of the scheme arrows. The right route inserts the derived tensor
  associator, the derived pullback compositor and inverse tensor-pullback
  comparison, then pullback of sigma and the other sigma. Both routes have domain
  (omega_f tensor f*omega_g) tensor (fg)*omega_h and the same codomain.
* `SourceEtale P` adds `Etale f` and gives the second displayed equality with
  `sourceEtale P f g` and `sourceEtale P f (g ≫ h)` as E. Thus removal of omega_f
  uses exactly the normalization dependency's eta, rather than an orientation.
* `SourceBaseChange P` quantifies a smooth Cartesian square and the Cartesian
  pullback of an etale source arrow. `sqe.paste_vert sqh` is the square for he;
  its lower arrow is v. Its equality is exactly beta followed by E on the left,
  and pullback of E, canonical pullback-square interchange, then e'*beta on the
  right. The arbitrary chosen pullback square covers X_1 times_X X' up to its
  canonical identification; no additional choice or hypothesis is used.
* `SigmaBaseChange P` gives the tower base-change equation with two Cartesian
  squares. The lower arrow for the composite is c. `pullSquare` and the published
  tensor-pullback isomorphism insert all canonical identifications. Universal
  quantification includes every further open base change.
* `OpenSigma P`, `OpenE P`, `OpenBeta P` state actual restriction equations for
  the three primitive maps. Only the base-change faces in `OpenBeta` are
  Cartesian. All other restriction faces are `CommSq`, with the indicated open
  immersions. In particular, no source-open square is assumed Cartesian.
  `restriction` is the composite E inverse, exceptional congruence, c, and
  exceptional pullback of target eta. With identity target restriction it is E
  inverse; with Cartesian target restriction normalization identifies it with
  beta. These are normalized restrictions, never arbitrary isomorphisms.
* `RestrictionExpression P j φ φ₀ rM rN` is indexed by an actual open immersion
  `j : T₀ ⟶ T`, the original arrow `φ` in D(T), the restricted arrow `φ₀` in
  D(T₀), and isomorphisms `rM : (pull P j).obj M ≅ M₀` and likewise for N.
  Its sigma, beta and sourceEtale primitives are the actual canonical maps,
  paired with exactly the restriction isomorphisms in `OpenSigma`, `OpenBeta`
  and `OpenE`. They assume the geometric diagrams and no morphism equality.
  The identity constructor allows the identity factors in tensor expressions.
  Composition shares the middle restriction isomorphism; inverse requires
  `IsIso` for each arrow. Tensor uses `Etale.derivedTensorHom` and stores
  `Etale.leftDerivedUpperStarTensorIso` followed by tensor of the two input
  restriction isomorphisms. Pullback takes arbitrary `g`, `g₀` and a compatible
  `CommSq a g₀ g j`, and stores `(pullSquare P a g₀ g j sq).app M` followed by
  `(pull P g₀).mapIso rM`, and likewise for N. It imposes no smoothness or
  Cartesian condition on g, g₀ or their square.
* `FiniteExpressionLocality P` asserts for every such expression the actual
  equation `(pull P j).map φ ≫ rN.hom = rM.hom ≫ φ₀` in D(T₀). Both the
  coefficient setting and actual derived restriction occur in this conclusion.
  The constructors allow the pullback of any finite expression along a section
  and its restricted section. The categories are the normalization dependency's
  existing etale-origin coordinates for the constructible pro-etale operations;
  no coefficient, site or universe equality is added.

Dependency declarations read and used:

* `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `.Coefficient`, and its commutative-ring instance.
* `Sheaf.Paper.FiniteTorAmplitudeSites`: `finiteTorConstructibleEtale`, with
  native `ProEtale.DerivedCategory.constructibleFiniteTor` publicly imported.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, its topology.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`,
  `SmoothOfRelativeDimension`; `Morphisms.Etale`: `Etale`.
* `def-weil-scheme-morphism-properties` is a convention record; its named
  Mathlib morphism predicates, not a replacement private predicate, are used.
* `Sheaf.Paper.DerivedPullbackTensorHom` and
  `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` provide the
  recorded derived operations and transported constructible exceptional system.
* `Sheaf.Paper.PurityFiniteExceptionalComposition`:
  `PurityFiniteSetting.finiteExceptionalComposition`, the actual conjugate of
  `Etale.unboundedEtaleLowerShriekCompIso`; normalization's `comp` uses this
  identical formula and adjunctions with the supplied compactifications.
* `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`:
  `IsCohomologicallySmoothFiniteCompared`, `finiteComparedDualizing`, and
  its specified tensor/base-change clauses. The normalization dependency exposes
  these same counit mates as `tensorMap`, `beta`, and `sigma`.
* `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `integralTowerGeneralPullbackComposition` with its K-flat characterization;
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `ringedTopoiCanonicalDerivedTensorPullback` with independent site universes.
  In etale-origin coordinates these become `Etale.leftDerivedUpperStarComp`
  and `Etale.leftDerivedUpperStarTensorIso`, both used explicitly.
* `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization`: the full signatures
  and docstrings of `compactification`, `exceptional`, `pull`, `omega`, `comp`,
  `congr`, `sigma`, `sourceEtale`, `beta`, `eta`, `rho` and the normalization
  theorem were read; these supply the actual maps throughout.
* `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `ChosenCartesianSquare`.
  The equations use its equivalent universal-property `IsPullback` interface
  and the associated `CommSq`; canonical comparison is independent of the
  presentation of the chosen pullback.
* Proof imports include `Sheaf.Paper.CompositionTensorMate`,
  `Sheaf.Paper.FiniteSiteCounitProjectionTransport`,
  `Sheaf.Paper.CanonicalOriginCompactSupportComposition`, and Mathlib's
  `CategoryTheory.Adjunction.Mates` (`conjugateEquiv`, `mateEquiv_vcomp`).
  The proof dependency `lem-pur-smooth-exceptional-tensor-pasting` has no Lean
  record yet, so there is no module to import for that proof step; the theorem
  docstring names its mathematical role explicitly. It is not needed to type
  this statement, and no copy of its statement is introduced.

Edge cases checked: dimension zero and identity arrows are allowed; etale source
arrows use the normalized E and eta; empty schemes are not excluded; all positive
coefficient levels (including ramified extensions) remain covered by P; no global
separatedness, purity orientation, section smoothness or Cartesian source-open
hypothesis was introduced. Opens of these Noetherian finite-type schemes remain
quasi-compact, so the open-arrow instances omit no open restriction. The finite
expression includes identity and arbitrary finite depth, and inverse only when
both arrows are invertible. Tensor and pullback cross the actual derived
restriction functor via the specified isomorphisms. A section need not be smooth:
instantiate `pullback` with the section as g and its restriction as g₀. Their
commutative open square is sufficient, and is not assumed Cartesian.

Searches actually run through msearch.py (and saved by that tool):

* LeanFinder: `dualizing tensor composition cocycle smooth maps etale source locality`:
  eight unrelated Kaehler-differential/manifold hits, no statement match.
* Loogle: `CategoryTheory.conjugateEquiv, CategoryTheory.MonoidalCategory.associator`:
  zero hits; the latter identifier is unknown. The actual conjugacy declarations
  were subsequently opened directly in Mathlib Adjunction/Mates.lean.
* Mathlib grep: `dualizing.*(cocycle|assoc)|sigma.*cocycle`: zero hits.
* Direct rg of both `lean/WeilConjectures` and `lean/Sheaf` for the node id,
  `dualizing.*(cocycle|assoc)|sigma.*[Cc]ocycle`: only unrelated finite coefficient
  cocycle mentions; the normalization module gives the maps, not this theorem.

## Repair of returned head 9806081abd66

The saved packet was inspected before editing and its required initial dry run
passed (03fe52f2f31). The self-check nevertheless confirmed the return's H3/H5
fault: its generic primitive assumed `CommSq`, so its finite-expression clause
contained no geometric restriction assertion. Retained all clauses the return
explicitly checked OK: SigmaIsIso, Cocycle, SourceEtale, SourceBaseChange,
SigmaBaseChange, OpenSigma, OpenE, OpenBeta, pullSquare and restriction.
Replaced only the expression inductive, its locality predicate, the final
conjunct's argument and the associated docstrings. The item node differs only in
`lean`. No new dependency, new node or statement correction is needed: these
constructors spell out the original item's finite-expression consequence.
The current read clone has no module or matching declaration superseding this
item; the delivery wrapper refreshes and rebases against the current server.

H3/H5 repair: the three primitive constructors contain sigma/beta/E themselves
and the normalized restriction isomorphisms. No constructor takes a commuting
square of derived morphisms as a premise. Only geometric squares are premises.
The tensor constructor uses the published derived tensor and monoidal pullback
comparison; the pullback constructor uses the published derived pullback and
`pullSquare` for arbitrary compatible restricted maps. Its conclusion is exactly
`(pull P j).map φ ≫ rN.hom = rM.hom ≫ φ₀`.

## Second reading by Q107

This is the dispatcher's required self-reading; no independent worker was
started. The independent maintainer review remains separate. With the full node
and module open, the following clause-by-clause check was performed after repair:

| Node hypothesis or clause | Lean rendering and result |
| --- | --- |
| Fixed finite coefficient datum, positive n, ell distinct from the characteristic | `P : PurityFiniteSetting.{u}` and `P.Coefficient`; unchanged, no arbitrary coefficient ring substituted. |
| Finite-type k-schemes, without absolute separatedness | Each geometric primitive and geometric law binds `Over`, `LocallyOfFiniteType` and `QuasiCompact` for the structure maps, with no `IsSeparated` structure-map assumption. |
| All geometric morphisms separated of finite type | Each relevant arrow has `IsOver`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`. The closure's general pullback needs no additional operation hypothesis and hence also covers every such arrow. |
| Smooth arrows have pure nonnegative dimension | Explicit natural numbers and `SmoothOfRelativeDimension` in every smooth geometric law and primitive. Dimensions zero and identities are retained. |
| Bounded constructible finite-Tor objects and specified operations | `omega`, `sigma`, `beta`, `sourceEtale` are the normalization dependency's actual etale-origin representatives of those operations, as accepted in the return. The closure interprets expressions of these representatives; no alternative exceptional system is quantified over. |
| Specified exceptional compositor c and tensor transpose theta, sigma formula | The published sigma receives the canonical `compactification P` and `comp P`; its definition is theta in omega-first order then inverse c. |
| Canonical derived pullback compositions, tensor and unit comparisons | `pullSquare`, `Etale.leftDerivedUpperStarComp`, `Etale.leftDerivedUpperStarTensorIso`, associator and `coefficientUnit`; retained in all laws and now stored in expression indices. |
| Counit-normalized rho, eta, E | Published `sourceEtale P e h` and `restriction` use that exact rho/compositor; restriction is E inverse, exceptional congruence, c and exceptional pullback of eta. |
| Sigma is invertible for every smooth pair | `SigmaIsIso P`; unchanged, covers every pair separately. |
| Threefold sigma cocycle | `Cocycle P` compares the two typed composites with associator, pullback compositor and inverse tensor comparison. Domains/codomains and equality unchanged. |
| Removing omega_u when u is etale | `SourceEtale P` binds `[Etale f]` and uses the normalized E on both sides; no orientation added. |
| Etale source localization commutes with smooth base change | `SourceBaseChange P`, `sqe.paste_vert sqh`, uses the same lower arrow v, not e, for beta of the composite. |
| Cartesian tower base change intertwines sigma, including further opens | `SigmaBaseChange P` for every pair of Cartesian squares, hence every further open specialization. |
| Compatible open restrictions in every scheme | `OpenSigma`, `OpenE`, `OpenBeta` and the three primitive constructors include all open arrows in each diagram. Only the beta base-change faces are Cartesian. |
| Source-open comparison is E, without Cartesian source-open square | `restriction` factors through `sourceEtale`; `CommSq` suffices for the open faces in the laws and all three primitives. No `IsPullback` is imposed on an open face. |
| Finite composition | `RestrictionExpression.comp` takes two expressions sharing rN and has indices φ ≫ ψ, φ₀ ≫ ψ₀, rM, rK. |
| Inverse | `RestrictionExpression.inverse` requires `IsIso φ`, `IsIso φ₀` and swaps rM/rN. No inverse is silently taken for an arbitrary beta. |
| Tensor product | `RestrictionExpression.tensor` uses the actual derived tensor on T and T₀. Each output restriction is the canonical tensor-pullback iso followed by tensor of the input restrictions. |
| Derived pullback | `RestrictionExpression.pullback` uses `pull P g` and `pull P g₀`, with the actual `pullSquare` and then g₀ pullback of rM/rN. It changes from D(T) to D(S), not an abstract functor within a single category. |
| Pullback along sections of restricted diagrams | The same constructor accepts a section as g and its restricted section as g₀. No smoothness or Cartesian hypothesis excludes it; `CommSq a g₀ g j` is exactly compatibility. |
| Every such finite expression commutes with restriction | `FiniteExpressionLocality P` concludes `(pull P j).map φ ≫ rN.hom = rM.hom ≫ φ₀`. This replaced the generic tautological `CommSq` conclusion. |

The rereading found and removed the generic-category fault described above; the
other clauses were retained. Definitions and inductive constructors have real
data, and only the node theorem is `sorry`. The theorem proof docstring now
explains the primitive geometric cases and naturality of the precise tensor and
pullback comparisons used for the induction. No statement is disputed.

Validation: the repaired file compiled through scompile.py. Its first compile
reported two long-line warnings; both lines were wrapped. The final repaired
packet then passed deliver2.py --no-push (3aa584cfb55), including server preflight
and clean compilation of the single module in sandbox and library contexts.
The recorded signature matches the file verbatim; only `lean` differs in the
node; the sole `sorry` is the item theorem; no Lean line exceeds 100 characters.
