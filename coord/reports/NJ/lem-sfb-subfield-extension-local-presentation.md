## Worker report

The delivery states `AlgebraicGeometry.ProEtale.subfieldExtension_localPresentation` in
`Sheaf.AlgebraicGeometry.SubfieldExtensionLocalPresentation`. Its sole proof is `sorry`.
The node statement, statement dependencies and proof plan are unchanged. No definitions,
new nodes, dependency repairs, or statement corrections were needed.

Source read: main-20261015, sec-six-functors-basics,
sk-thm-sfb-qlbar-two-colimit/lem-sfb-extend-subfield-constructible.proof.md, second
sentence, tensoring the local finite presentation on the same stratification. The node
makes explicit the two raw pullbacks required for that application, first to a stratum
and then to a member of a witnessing presentation cover.

Clause correspondence:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- Finite extensions inside the fixed algebraic closure are
  `{E F : PadicAlgCl.FiniteIntermediateField ℓ}`; their specified inclusion is
  `(hEF : E ≤ F)`. This is the upstream finite-intermediate-field encoding, not the
  finite-type-algebra predicate on a field.
- The schemes and arbitrary morphism are `{X Z : Scheme.{u}} (f : Z ⟶ X)`.
  No condition on `f`, no qcqs condition, and no Noetherian assumption is present.
- The actual pulled-back coefficient rings are `padicSubfieldRingObj X ℓ E` and
  `padicSubfieldRingObj X ℓ F`; their inclusion is
  `padicSubfieldRingObjMap X ℓ hEF`.
- `M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)`
  is precisely an internal module object over E_X.
- `Functor.mapMod (upperStar Ab.{u + 1} f) R` is raw module pullback to modules over
  `(upperStar Ab.{u + 1} f).obj R`, for both R = E_X and R = F_X. In particular the
  target rings are literal inverse images, not coefficient rings silently identified
  with them.
- `Mod.extendScalars (padicSubfieldRingObjMap X ℓ hEF)` is G_X = F_X tensor over E_X.
- The hypothesis `hM` is exactly `IsLocallyFinitelyPresented` for the raw E_X-pullback
  of M over the raw inverse-image ring.
- The first conjunct is `IsLocallyFinitelyPresented` for the raw F_X-pullback of
  the scalar extension of M, over the raw inverse-image F_X ring.
- The second conjunct quantifies over every
  `𝒰 : Scheme.Cover Scheme.proetalePrecoverage Z`. Its premise is the defining
  finite-presentation condition for every `i : 𝒰.I₀` on the raw E_X-pullback. Its
  conclusion is that same condition on the raw F_X-pullback of the scalar extension,
  for every index of the very same `𝒰`. It retains the family, its arrows and its
  indexing type; no refinement or finite-subcover replacement is made.
- `Mod.IsFinitelyPresented` is the existing cokernel-of-a-map-between-finite-free-
  modules predicate. The statement does not replace it by finite constant local models.

Dependency declarations read and used:

- sk-def-sfb-pulled-back-coefficients: `coefficientRing`, `condensedRingObj`,
  `isCommMonObj_condensedRingObj`, from
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`. The latter defines the
  actual unbundled coefficient object used by `padicSubfieldRingObj`.
- def-sfb-subfield-coefficient-map: `padicSubfieldRingObjMap` and the associated
  coefficient objects, from
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`.
- sk-def-sfb-change-of-scalars: `CategoryTheory.Mod.extendScalars`, from
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`, the balancing
  coequalizer functor on internal module objects.
- def-sfb-finite-upper-star: `AlgebraicGeometry.ProEtale.upperStar`, from
  `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`.
- def-sfb-finite-upper-star-monoidal: `monoidal_upperStar`, from
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal`.
- sk-def-sfb-transport: the current record lists `CategoryTheory.Functor.mapMod`,
  defined in `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod` and publicly
  supplied by `WeilConjectures.CategoryTheory.ModuleObjects.MapMod`. Its action is
  the lax tensorator followed by the image of the original action. The record's
  owning module `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`
  publicly imports that same MapMod interface; this statement uses its smaller
  defining import. No replacement construction is introduced. The projection-formula
  constructions recorded for the other clauses are not needed by this statement.
- sk-def-sfb-module-objects: `CategoryTheory.Mod`, in
  `Mathlib.CategoryTheory.Monoidal.Mod`.
- def-sfb-locally-finitely-presented: `IsLocallyFinitelyPresented`, from
  `WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`. The second conjunct expands
  its defining cover-witness condition with exactly the same cover universe.

The modules of the stated proof dependencies are imported privately:
`Sheaf.AlgebraicGeometry.InternalExtensionInverseImage` (the actual inverse-image
comparison), `Sheaf.AlgebraicGeometry.InternalExtensionFinitePresentation` (finite-free
and cokernel comparison, including preservation of finite presentation),
`WeilConjectures.CategoryTheory.ModuleObjects.Free` (finite presentation), and
`WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic` (the audited closed
finite-subfield condensed-ring definition). The remaining proof dependencies are already
public statement imports. The theorem docstring follows the node's four proof steps.

Edge cases checked against the signatures and mathematical construction: E = F; identity
f; empty Z and empty covers when permitted by the precoverage; zero modules and rank-zero
presentations; arbitrary, including infinite, covering families. No flatness assumption
is needed to tensor a cokernel presentation. Schemes use arbitrary universe u and abelian
coefficients use the framework's u+1 convention; the cover universe is the same one used
in `IsLocallyFinitelyPresented`.

Searches for an existing statement (2026-10-21):

- msearch.py leanfinder, "Raw inverse image of an internal module after extension of
  scalars between finite l-adic subfields is locally finitely presented on the same
  pro-etale cover": eight hits, including RingHom.finitePresentation_isLocal and
  Algebra.Etale.finitePresentation, all ordinary ring/algebra results; no exact match.
- msearch.py loogle, `"extendScalars", "Presentation"`: four hits, the localized ordinary
  module mapExtendScalars/linearEquivMapExtendScalars declarations; no internal-module,
  raw-pullback, same-cover result.
- msearch.py grep, `extendScalars.*(Presentation|FinitelyPresented)|IsLocallyFinitelyPresented`,
  subdirectory Algebra: one hit in Mathlib/Algebra/Module/FinitePresentation.lean:662,
  `Module.FinitePresentation.linearEquivMapExtendScalars_apply`; no exact match.
- msearch.py leansearch, "Extension of scalars preserves local finite presentations
  after inverse image of sheaves of modules": eight hits, including ordinary module
  finite-presentation tensor product and presheaf-module pullback; no exact match.
- rg in project WeilConjectures and Sheaf for `IsLocallyFinitelyPresented`,
  `padicSubfield`, `subfieldExtensionLocalPresentation`, and the node id: the local
  presentation definition, constructible-preservation statements, and scalar extension
  helper proofs occur, but no public exact same-cover raw-pullback statement. In
  `Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars`, `lfp_extend` and
  `pullbackExtendScalarsIso` are private helpers; its public theorem is about derived
  bounded constructibility and requires exactness. It is not the current statement.

Validation (2026-10-21): the required recovery dry run with deliver2.py --no-push
passed server preflight and separately compiled the sandbox and library module. The
previous attempt's published-library failure no longer occurs. The Lean module is
retained unchanged. Self-check against the current node and source confirms the prime,
finite subfields and their inclusion, arbitrary scheme morphism, raw coefficient rings,
local-finite-presentation hypothesis, both conclusion clauses and unchanged cover.
The current local-finite-presentation definition uses the same cover and raw mapMod
construction. The node copy was refreshed from the current shared node, preserving only
this delivery's lean field; no maintainer audit data is changed. Its recorded signature
matches the file verbatim, autoImplicit is disabled, and the only proof remains sorry.
No STATEMENT-DISPUTED flag or node fault was found.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
