## Worker report

The module `Sheaf.AlgebraicGeometry.ConductorSmoothBaseChange` states
`AlgebraicGeometry.Scheme.conductor_smooth_base_change`, with its sole theorem proof
`sorry`. Three helpers belong to the conductor notion introduced by this very node:
`reducedNormalizationStructureMap` is the canonical structure-sheaf morphism,
`reducedNormalizationCokernel` is its actual categorical cokernel, and
`IsReducedNormalizationConductor` is the sectionwise characterization of its annihilator.
All three definitions have real data, no postponed proof and no choice of an arbitrary map.
The theorem supplies an ideal characterized by precisely that annihilator condition.
No separate independent notion or dependency module is needed.

The signature maps the node's hypotheses and clauses as follows:

- A scheme S: `(S : Scheme.{u})` with the explicitly bound universe `u`.
- A Q-scheme: `q : S ⟶ Spec (.of (ULift.{u} ℚ))`. The canonical universe lift is
  ring-isomorphic to Q; it permits every scheme universe instead of restricting S
  to the universe of the concrete type `ℚ`. The node names no coefficient extension.
- Reduced: `[IsReduced S]`, the recorded Mathlib notion.
- Finite type over Q: `[LocallyOfFiniteType q] [QuasiCompact q]`, exactly the
  recorded conjunction; no separatedness, integrality, connectedness, nonemptiness,
  or additional Noetherian hypothesis is introduced.
- The componentwise normalization and canonical morphism are the recorded
  `S.reducedNormalization` and `S.fromReducedNormalization`.
- Finiteness of nu: `IsFinite S.fromReducedNormalization`.
- Injectivity of O_S -> nu_*O: `∀ U : S.Opens, Function.Injective
  (S.fromReducedNormalization.app U)`. These are the components of the canonical
  module morphism `reducedNormalizationStructureMap`, defined using Mathlib's
  `SheafOfModules.unitToPushforwardObjUnit` and `toRingCatSheafHom`.
- C_S: `S.reducedNormalizationCokernel = cokernel S.reducedNormalizationStructureMap`.
  This is the cokernel in the category of sheaves of modules, so it is the
  sheafification of the sectionwise cokernel, including on nonaffine opens.
- Coherence of C_S: `RingedSpace.IsCoherent S.toRingedSpace
  S.reducedNormalizationCokernel`.
- Definition D_S = Ann(C_S): `∃ D : S.IdealSheafData,
  S.IsReducedNormalizationConductor D ∧ ...`. Unfolding the predicate gives,
  for every open U and scalar section a, `a ∈ D.idealOfOpens U` if and only if
  `∀ V h s, S.presheaf.map (homOfLE h).op a • s = 0`, with V any smaller open
  and s any local section of C_S on V. This characterization determines the ideal
  uniquely: it fixes every affine ideal and therefore the entire `IdealSheafData`.
  Thus the existential does not replace a canonical ideal by arbitrary data.
- Coherent ideal: `RingedSpace.IsCoherent S.toRingedSpace D.toModules`, using
  the existing bridge from quasi-coherent ideal data to an O_S-module.
- Precisely the nonnormal locus: `(D.support : Set S) = {x | ¬ (IsDomain
  (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x))}`.
  Here `D.support` is the zero set V(D), not the support of the ideal module.
- Nowhere dense: `interior (closure (D.support : Set S)) = ∅`.
- Unit ideal iff normal: `D = ⊤ ↔ ∀ x, IsDomain (S.presheaf.stalk x) ∧
  IsIntegrallyClosed (S.presheaf.stalk x)`. This is normality of every local
  ring, allowing distinct irreducible components and the empty scheme.
- Every quasi-compact smooth h: `∀ T h [Smooth h] [QuasiCompact h]`, with
  no extra assumption on T. Reducedness and finite type of T follow from these
  hypotheses and those on S and are not assumed separately.
- D_T = D_S O_T as ideals: `∀ E : T.IdealSheafData,
  T.IsReducedNormalizationConductor E ↔ E = D.comap h`.
  Mathlib's `comap` is extension of the ideal, defined by the kernel of the
  pulled-back closed immersion. The equivalence asserts both that the extended
  ideal has the annihilator sections and that every ideal with those sections
  equals it; existence of D_T follows by taking E = D.comap h. This is an
  equality of ideals, rather than an uncharacterized module isomorphism.
- Identity compatibility: `D.comap (𝟙 S) = D` and the smooth-pullback clause
  applies also to h = identity.
- Composition compatibility: for every quasi-compact smooth g : R -> T,
  every conductor F on R equals `(D.comap h).comap g`, and
  `(D.comap h).comap g = D.comap (g ≫ h)`. Together these give the same
  conductor for direct and iterated pullback, in the prescribed order.

Dependency declarations and interfaces read:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`
  (all open section rings reduced; stalk form supplied by the Mathlib instances).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.ReducedNormalization`:
  `Scheme.reducedNormalizationComponent`, its integrality instance,
  `Scheme.reducedNormalization`, `Scheme.fromReducedNormalization`; read their
  constructions and source docstrings, including the actual component coproduct.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  and `IsDomain`; the node's normal-domain notion is exactly their conjunction.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`,
  with its affine-local smooth-ring-map condition; relative dimension is unused.
- `WeilConjectures.AlgebraicGeometry.Regular`: `Scheme.normalization_properties`.
  The current source's grouping of the conclusions differs from the historical
  recorded signature; this theorem is imported for the proof route only, not used
  to define a different normalization or assume an integral S.
- `WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent`:
  `Scheme.Modules.isCoherent_pushforward_of_isFinite` and
  `isCoherent_unit_of_finite_to_locallyNoetherian`, both full signatures/docstrings
  read through the current-source wrapper.
- `WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum`:
  `RingedSpace.coherent_kernel_cokernel_sum`, read through the current-source
  wrapper; the cokernel is in the same sheaf-of-modules category.
- `WeilConjectures.AlgebraicGeometry.SchemeTheoreticSupport`:
  `Scheme.schemeTheoreticSupport`, its all-opens annihilator formula and its
  affine ideal construction were read through the current-source wrapper.
- `Sheaf.AlgebraicGeometry.ReducedAlgebraicNormalizationFieldChange`:
  `reduced_algebraic_normalization_field_change`, especially its finite-map
  and dense normal-open clauses.
- `Sheaf.RingTheory.AnnihilatorFiniteFlatBaseChange`:
  `Module.annihilator_tensorProduct_flat_base_change`.
- `Sheaf.RingTheory.AnnihilatorLocalizationAway`:
  `Module.annihilator_localization_away_of_finite`.
- Auxiliary existing constructions used directly:
  `SheafOfModules.unitToPushforwardObjUnit`, `Scheme.Modules.pushforward`,
  `CategoryTheory.Limits.cokernel`, `Scheme.IdealSheafData.idealOfOpens`,
  `.toModules`, `.support`, `.comap`. Their source definitions were read.

Proof-only imports are included for every proof dependency with a recorded module,
except the already-public smooth/coherence/direct-image imports. The proof nodes
`lem-trf-normalized-blowup-calculus`, `lem-weil-pbc-finite-module-support-annihilator`,
`lem-weil-pbc-finite-type-over-noetherian`, `lem-weil-pbc-noetherian-finite-components`,
and `lem-weil-pbc-smooth-ring-map-flat` do not currently have recorded Lean modules;
no guessed import is added. Their steps remain explicit in the main theorem docstring.
They are not missing notions needed to type this statement.

Sources checked: local Stacks `algebra.tex`, lemma-annihilator-flat-base-change
(Tag 07T8), including the finite-module assertion; local `more-morphisms.tex`,
lemma-normalization-and-smooth (Tag 07TD), including its hypotheses and proof.
The item's source description mentions morphisms.tex for Tag 07TD, but this tag is
in More on Morphisms; the module docstring names the correct chapter. The reduced
normalization and coherence source interfaces were checked as above. No mathematical
statement correction is needed, and no STATEMENT-DISPUTED flag remains.

Edge cases checked semantically against the node and definitions: the empty scheme
has the empty component coproduct, zero quotient, unit ideal and empty nonnormal
locus; normal S gives the unit ideal, preserved by every extension; a smooth source
mapping into the normal open may have unit conductor even when S does not; multiple
intersecting components are covered by the componentwise normalization and fail the
local-domain test at an intersection; the empty source and identity morphisms are
included. Arbitrary successive smooth quasi-compact maps have no surjectivity
hypothesis. No characteristic or independent coefficient field is quantified: the
base is exactly Q, lifted solely for universe size.

Searches for an existing statement (2026-10-17 UTC):

- `msearch.py`, LeanFinder: "The conductor ideal of the componentwise normalization
  of a reduced scheme of finite type over Q commutes with smooth base change".
  Eight hits, all morphism-normalization infrastructure; no conductor theorem.
- `msearch.py`, Loogle: "Module.annihilator, Ideal.map". Zero hits.
- `msearch.py`, grep: "conductor|normalizationPullback", AlgebraicGeometry.
  Seven hits in Mathlib Normalization and ZariskisMainTheorem; only relative
  normalization comparisons, not this statement.
- `msearch.py`, LeanSearch: "The annihilator ideal sheaf of the cokernel of the
  normalization structure sheaf map". Eight hits (Module.annihilator, module
  annihilator/colon lemmas, relative normalization, sheaf relations, Hom.ker);
  none states this scheme theorem or supplies its conductor.
- `rg` over upstream WeilConjectures and side `lean/Sheaf` for conductor,
  annihilator, reducedNormalization and fromReducedNormalization: the component
  construction, ring annihilator facts and general scheme-theoretic-support
  infrastructure exist, but no scheme conductor construction/theorem exists.
- `rg` over upstream WeilConjectures for the exact node id, and over both source
  roots for normalizationConductor, normalizationCokernel and
  conductor_smooth_base_change: no matches.
- `rg` over `dag/lean_names_upstream.json` for conductor/annihilator/normalization:
  found existing general support and annihilator dependencies; no exact theorem.

Validation: `scompile.py Q125 lem-trf-conductor-smooth-base-change` compiled the
single delivered module against the current overlay and confirmed its library
path. Clean output: no errors and no warnings. No global build was run. Every
variable and universe is explicitly bound; only the theorem proof is postponed.

## Second reading by Q125

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
