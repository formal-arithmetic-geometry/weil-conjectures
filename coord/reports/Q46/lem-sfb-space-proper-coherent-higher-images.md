## Worker report

The delivery states Stacks Tag 08AR in
`Sheaf.AlgebraicGeometry.SpaceProperCoherentHigherImages`, declaration
`AlgebraicGeometry.AlgebraicSpace.isFinitePresentation_moduleHigherDirectImage_of_proper`.
Its only proof is `sorry`. No definition, axiom, helper theorem, dependency repair,
or statement correction is introduced.

Sources read: `literature/stacks-project/spaces-cohomology.tex`,
lemma-proper-pushforward-coherent (Tag 08AR), including its entire proof, and
lemma-coherent-Noetherian (Tag 07UB), including all five equivalent conditions.
The theorem docstring contains the accepted six-step proof, naming its DAG inputs.

Hypotheses and conclusion, clause by clause:

- The arbitrary base scheme is `{S : Scheme.{u}}`. The universe `u` is explicitly bound.
- `{X Y : AlgebraicSpace S}` are the recorded fppf-sheaf algebraic spaces over the
  same S, and `(f : X ⟶ Y)` is their actual morphism of sheaves.
- Properness is `(hf : MapIsProper f)`. Unfolding the recorded definition gives
  `MapIsSeparated f ∧ MapIsFiniteType f ∧ MapIsUniversallyClosed f`.
  `MapIsSeparated` tests the relative diagonal by closed immersions on scheme tests.
  `MapIsFiniteType` is quasi-compactness together with `MapIsLocally
  (@LocallyOfFiniteType) f` on every compatible pair of etale scheme charts.
  `MapIsUniversallyClosed` is closedness of the point map from the sheaf fibre
  product after every algebraic-space base change. These are all the clauses in
  the node's expansion of properness; no representability of f is imposed.
- Local Noetherianity of Y is
  `(hY : ∀ T : Y.EtaleSite, IsLocallyNoetherian (Y.etaleForget.obj T))`.
  This quantifies over precisely the etale scheme charts in the node.
- A module on the small etale ringed site is `(F : X.Modules)`. This is the recorded
  `ringedSiteModules` / Mathlib `SheafOfModules` category, with the regular-functions
  structure sheaf. It is not a category of coherent modules.
- Coherence of F is `(hF : F.IsFinitePresentation)`. Tag 07UB, conditions (1)--(4),
  identifies coherence, finite presentation on the ringed site, quasi-coherent finite
  type, and coherence on all etale scheme charts. On an affine Noetherian chart,
  finitely generated modules are finitely presented, and the associated module has
  sections `B ⊗[R] N` on affine etale maps. Hence this is precisely the node's
  description, using an existing predicate, not an added hypothesis. X is locally
  Noetherian as a consequence of properness over Y, not a further assumption.
- The degree `(i : ℕ)` ranges over exactly the integers i >= 0.
- The higher image is `Functor.rightDerived` of `smallModuleDirectImage f`, evaluated
  on `X.smallModuleRestriction.obj F`, and returned to Y.Modules by
  `Y.smallModuleEquivalence.inverse.obj`. The recorded `smallModuleDirectImage`
  is the conjugate of the canonical `moduleDirectImage f`, whose sections are the
  limits of the actual compatible chart sections with their canonical scalar maps.
  Mathlib rightDerived is the i-th homology of the functor applied to an injective
  resolution. `InjectiveResolution.isoRightDerivedObj` gives exactly this computation
  for any injective resolution. The small-model equivalences are actual affine-chart
  restriction equivalences; their exactness transports resolutions and their images.
  Thus the object is R^i f_* F as specified, not an arbitrary replacement functor.
- The explicit `InjectiveResolution.instHasInjectiveResolutions` argument is obtained
  from `IsGrothendieckAbelian.enoughInjectives` and
  `SheafOfModules.isGrothendieckAbelian X.smallStructureRings`. It is a construction
  of the required instance, not an assumption. No `HasDerivedCategory` or localization
  universe is needed for ordinary nonnegative right derived functors.
- The final `.IsFinitePresentation` is coherence of the higher image on the original
  Y_et, by the same 07UB criterion and the hypothesis hY. There are no additional
  vanishing, boundedness, flatness or finite-dimension conclusions.

Dependency declarations read and used (the signatures and docstrings were opened):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `EtaleSite`, `etaleForget`, `structureSheaf`,
  and `Modules`. These retain the scheme universe and the actual regular functions.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules` is
  transparently Mathlib SheafOfModules, with its sectionwise linear morphisms.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and `.Resolution`:
  `CategoryTheory.Injective`, `InjectiveResolution` and its canonical resolution instance.
- `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`,
  including the induced module direct image and its scalar-action compatibility.
  This general interface is imported as required; the specialized canonical direct
  image is the already recorded algebraic-space compatible-chart construction.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsProper` and
  its component definitions, in the `AlgebraicGeometry.AlgebraicSpace` namespace.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`: `SmallModules`,
  `smallStructureRings`, `smallModuleRestriction`, and `smallModuleEquivalence`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `smallModuleDirectImage`
  and `smallModuleDirectImage_additive`. The module was read in full; the unbounded
  derived constructions are not needed in this theorem's signature.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsFinitePresentation`, exactly the predicate used by the landed
  `AlgebraicSpaceCoherentAbelian` and `AlgebraicSpaceClosedCoherentModules` statements.
- `Mathlib.CategoryTheory.Abelian.RightDerived`: `Functor.rightDerived` and
  `InjectiveResolution.isoRightDerivedObj` (resolution computation).

Three already landed definition nodes are appended to stmt_deps:
`def-sfb-space-morphism-properties`, `def-sfb-space-small-ringed-model`, and
`def-sfb-space-derived-module-calculus`. This makes the reused properness and
small-model interfaces explicit. The original statement, proof and proof dependencies
are unchanged. No node file other than the item's is delivered.

All recorded proof-dependency modules are imported with plain imports, including the
fibre-product theorem, integral/closed morphism facts, Grothendieck category theorem,
long exact sequence, quasi-coherent higher-image theorem, coherent abelian closure,
closed coherent pushforward and affine higher-image vanishing. Mathlib enough-injectives
is public because the resolution instance appears in the statement. At preparation,
these proof nodes have no recorded declaration and therefore no module to import:
`lem-sfb-space-proper-base-change`, `lem-sfb-space-higher-image-etale-restriction`,
`lem-sfb-space-qcoh-kernels-colimits`, `lem-sfb-space-noetherian-coherent-support`,
`lem-sfb-space-closed-subspace-proper`, `lem-sfb-space-proper-composition`,
`lem-sfb-space-chow-acyclic-full-support-witness`, `lem-sfb-ringed-topos-relative-leray`,
`lem-sfb-space-closed-immersion-quasi-coherent-modules`, and
`lem-sfb-space-coherent-two-of-three-devissage`. These are proof inputs only; none
is needed to elaborate the statement. No import is omitted for a cycle.

Edge cases checked before writing:

- i = 0 is included and states coherence of ordinary direct image.
- The zero module and empty algebraic space are allowed. The small affine model
  includes empty charts, and finite presentation includes the zero presentation.
  There is no Nonempty, nonzero-ring or nonempty-support binder.
- The identity morphism recovers coherence of F; no positive-degree assumption is used.
- Y may be locally Noetherian without global quasi-compactness or separatedness.
- X and Y need not be schemes, and f need not be representable, flat, or finite.
- The base S is arbitrary; no characteristic or Noetherian hypothesis is placed on S.
- The large chart category is never forced to have equal object and morphism
  universes. The existing small ringed model preserves the section universe u.

Searches for an existing statement:

- `msearch.py ... leanfinder "Higher direct images of coherent sheaves under proper
  morphisms of algebraic spaces to locally Noetherian algebraic spaces are coherent"`:
  8 hits. The relevant hit was scheme local-Noetherian permanence; other hits were
  coherent topology sheaf facts, IsFiniteType, and condensed modules. No match.
- `msearch.py ... loogle "SheafOfModules.IsFinitePresentation,
  CategoryTheory.Functor.rightDerived"`: 0 hits.
- `msearch.py ... grep "proper.*coherent|coherent.*proper|higherDirectImage"
  AlgebraicGeometry`: 0 hits in Mathlib.
- `rg` in `lean/WeilConjectures` for the node id: no hits.
- `rg` in `lean/WeilConjectures` for proper/coherent higher-image phrases found
  the scheme finiteness and higher-image results in `Cohomology/ProperFinite.lean`,
  `NoetherianProperBoundedCoherentImage.lean`, and related scheme modules; these
  have schemes as objects, not arbitrary algebraic spaces.
- `rg` in `lean/Sheaf` found the algebraic-space quasi-coherent higher-image result
  and coherent closure statements, but no proper coherent higher-image theorem.
  `ValuationProperCoherentHigherDirectImages.lean` concerns proper flat schemes over
  valuation rings with finite locally free coefficients, so is a different theorem.
- `rg` of the proposed full declaration name in project modules and
  `dag/lean_names_upstream.json`: no existing declaration.

No STATEMENT-DISPUTED flag or mathematical node fault was found.

## Second reading by Q46

Reopened the node statement, Tag 08AR, the five clauses of Tag 07UB, and the final
Lean signature for a separate clause-by-clause pass. S, X, Y, f and arbitrary degree
are bound; MapIsProper expands to all four properness conditions in the item; hY is
exactly the chartwise local-Noetherian hypothesis; hF and the conclusion use the same
existing finite-presentation predicate. The small-model restriction equivalence and
canonical conjugate direct image retain the original module categories and scalar
actions, and Mathlib rightDerived retains the injective-resolution computation.
There is no additional hypothesis or lost clause. The only repair after the first
compile was splitting the final signature line to meet the 100-character limit.
This pass is by the assigned worker; the dispatcher explicitly forbids starting
another agent. The maintainer's independent review remains the external reading.

## Validation

Compiled the complete module with the required scompile.py wrapper, in both sandbox
and library module names. The first compile reported only one overlong line; this
was shortened and the final compile was clean. The theorem proof remains `sorry`
as required for stage 2. Delivery dry-run and final delivery results are recorded
below when available.

The required `deliver2.py Q46 lem-sfb-space-proper-coherent-higher-images --no-push`
completed successfully: `OK (dry run): commit 51d1816e061 passes the preflight and
compiles; nothing pushed`.
