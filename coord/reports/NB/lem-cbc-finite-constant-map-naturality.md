## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteConstantMapNaturality` states
`AlgebraicGeometry.ProEtale.finiteConstantMap_naturality`, with `sorry` as its only proof.
It introduces no Lean definitions. The node's mathematical statement is unchanged.
The repair adds a definition node owning two existing coefficient-map definitions.

Hypotheses and clauses, checked against the node:

- The arbitrary scheme morphism is `{T' T : Scheme.{u}} (g : T' ⟶ T)`. There is no
  geometric restriction on it. The small pro-etale inverse image/direct image are
  `Scheme.proEtaleSheafInverseImage g RingCat.{u + 1}` and
  `Scheme.proEtaleSheafDirectImage g RingCat.{u + 1}`; their specified adjunction is
  `Scheme.proEtaleSheafAdjunction`, used in the definition of the canonical map.
- Finite commutative coefficient rings are `{B C : Type (u + 1)}` with `[CommRing B]`,
  `[Finite B]`, `[CommRing C]`, `[Finite C]`. The topology and `DiscreteTopology`
  instances express the discrete coefficient realization required by the recorded
  coefficient presheaf. Every finite ring admits this topology; no ring is excluded.
  The size is the mandated sheaf-value universe, leaving site object universe u+1
  and morphism universe u unchanged. Smaller rings can be lifted to this universe.
- The unital coefficient homomorphism is `(φ : B →+* C)`.
- The coefficient sheaf `B_W` is exactly `finiteCoefficientRingSheaf W B` from the
  recorded dependency, not a replacement by an ordinary constant-sheaf model.
- The map `φ_W` is exactly `finiteScalarRingMap φ W`. Its defining module first forms
  `finiteScalarPresheafMap φ W` by postcomposition on continuous functions and then
  applies `presheafToSheaf`. Thus no continuity hypothesis on φ is added: discreteness
  supplies continuity, including for noninjective φ.
- The map `c_{g,B}` is `finiteCoefficientInverseImageMap g B`, defined as the adjunct
  of `finiteCoefficientDirectImageMap g B` (the node's rho). The latter pulls continuous
  functions back along the fibre-product projection and extends by sheafification.
- The first conjunct reads `c_B ≫ φ_T' = g⁻¹(φ_T) ≫ c_C`, precisely
  `φ_T' ∘ c_B = c_C ∘ g⁻¹(φ_T)` in the node's right-to-left composition notation.
- The second conjunct reads `rho_B ≫ g_*(φ_T') = φ_T ≫ rho_C`, precisely the node's
  adjunct equality. Both formulations are asserted; the docstring explains why the
  specified adjunction identifies them, via unit/counit naturality. No arbitrary
  adjunction, comparison map or isomorphism is quantified over.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: the inverse image, direct image and
  adjunction named above, whose source definitions retain the original sites.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`:
  `finiteCoefficientDirectImageApp`, `finiteCoefficientDirectImagePresheafMap`,
  `finiteCoefficientDirectImageMap`, `finiteCoefficientInverseImageMap`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `finiteCoefficientPresheaf` and
  `finiteCoefficientRingSheaf`, continuous functions on connected components followed
  by ring-valued sheafification.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction`; the dependency definitions use this exact sheafification.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteScalarUnitComparison`:
  `finiteScalarPresheafMap`, `finiteScalarRingMap`. The new definition node
  `def-pur-finite-coefficient-ring-map` owns these existing definitions and replaces
  `lem-exc-proetale-finite-scalar-unit-comparison` in stmt_deps. The latter theorem
  is not used. No dependency module is modified. All four original statement/proof
  dependencies remain imported.

Sources read: the current blueprint ancestor proof
`main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/lem-cbc-completed-extension-zero-comparison.proof.md`;
Stacks `sites.tex`, proposition-sheafification-adjoint (00WH), and `proetale.tex`,
section-morphism (09A5). The declaration docstring carries all three steps of the
node's natural-language proof and their dependency IDs.

Edge cases checked mathematically before writing: the zero ring is permitted (no
Nontrivial assumption); an empty scheme is permitted and the sheaf maps there are
unique; identity coefficient maps and identity scheme maps are included. A quotient
Z/4 → Z/2 can merge open fibres; restricting both composites to the original fibre
cover still gives the same constants. A diagonal Z/2 → Z/2 × Z/2 is likewise allowed.
No injectivity, surjectivity or flatness hypothesis occurs. There is no index set or
cohomological degree to restrict. No statement fault or dispute was found.

Searches for reuse (2026-10-21):

- `msearch.py ... leanfinder "Canonical inverse image maps of finite constant ring
  sheaves are natural in the coefficient ring homomorphism"`: eight hits, beginning
  with `StructureSheaf.comap_const` and ΓSpec naturality; none states this pro-etale
  coefficient-sheaf square.
- `msearch.py ... loogle "CategoryTheory.Sheaf, CategoryTheory.NatTrans"`: zero hits.
- `msearch.py ... leansearch "Pullback of constant ring sheaves commutes with changes
  of finite coefficient rings"`: eight hits including `TopCat.continuousFunctions.pullback`,
  `SheafOfModules.pullback`, and `LocallyConstant.comapRingHom`; none is this statement.
- `msearch.py ... grep "finiteCoefficient.*naturality|constantSheaf.*naturality|homEquiv_naturality"
  CategoryTheory`: 25 generic adjunction/functor hits, no exact coefficient theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for coefficient maps, naturality and
  this node ID found no existing declaration of the complete statement. It did find
  `finiteScalarPresheafMap` and `finiteScalarRingMap`, which are reused. The private
  `finiteScalarRingMap_directImage` proves the direct-image half for general finite
  rings, but is not a public reusable declaration. The similarly named public
  `finiteCoefficientDirectImageMap_naturality` in `Paper/FiniteCoefficientDirectImage`
  concerns a derived coefficient projection and naturality in a complex morphism,
  not the present ring-sheaf maps. The upstream-name index has no matching name.
- Read the review's suggested `lem-weil-pbc-profinite-coefficient-inverse-image` and
  its module `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`. The public
  `Scheme.proEtaleConstantInverseImageMap_naturality` concerns `CommRingCat` ordinary
  constant sheaves, not the fixed `RingCat` continuous-function sheafification and
  its specified c and rho. Reusing it requires the normalization comparison; rebinding
  this item to it would omit that work and the explicit direct-image clause. The new
  statement therefore does not duplicate its actual Lean signature.

Prior-packet validation (before this metadata-only repair): prescribed `scompile.py NB lem-cbc-finite-constant-map-naturality <module>`
passed both sandbox (3.6 seconds) and library (3.0 seconds) compilation with no errors
or warnings. All universes and variables are explicitly bound; autoImplicit is false.

## Second reading by NB

Worker self-check, with the node and delivered source open; independent maintainer
review remains the delivery reviewer’s task (this worker was instructed not to start
other agents). Checked the direction of both composites: Lean's `≫` is the reverse
of the node's displayed composition order, and both sides have the correct source
and target. Checked that φ is a ring homomorphism rather than an arbitrary sheaf map,
that c and rho are exactly the recorded constructions, and that both rings remain
finite and commutative. The two conjuncts render the two stated formulations without
extra geometric hypotheses. Checked the scalar-map definition body and reused it,
avoiding a second construction. No signature correction was needed after compilation.


## New nodes

`def-pur-finite-coefficient-ring-map` defines the presheaf coefficient map by
pointwise composition with a unital homomorphism of finite discrete rings and its
image under ring-valued sheafification. Its source is the finite-reduction coefficient
compatibility in the same main-20261015 ancestor proof as the item. It uses the
coefficient presheaves and sheaves of `def-weil-pbc-proetale-modules` and the functor
of `def-weil-pbc-sheafification`, with schemes from `def-pc-scheme`.
Its `existing: true` binding owns the unchanged `finiteScalarPresheafMap` and
`finiteScalarRingMap` in `Sheaf.AlgebraicGeometry.ProEtaleFiniteScalarUnitComparison`;
there is no new module or duplicate construction. It covers noncommutative finite
rings as those existing definitions do, and the item specializes them to commutative
rings. In the section variables, R and S have type `Type (u + 1)` with `Ring`, `Finite`,
`TopologicalSpace` and `DiscreteTopology` instances, phi is `R →+* S`, and T is
`Scheme.{u}`. The presheaf component sends s to x ↦ phi (s x); discreteness provides
continuity, the RingHom fields give pointwise ring identities, and naturality is the
commutation of precomposition with postcomposition. The sheaf-map definition is
literally `(presheafToSheaf (Scheme.ProEt.topology T) RingCat.{u + 1}).map
(finiteScalarPresheafMap φ T)`.

The new node records complete msearch output for LeanSearch and LeanFinder (eight
hits each) and Mathlib grep (eleven hits). These return generic continuous-function
maps, module sheafification, or generic sheafifyMap; the exact RingCat pro-etale
construction is already in the project and is reused. DAG grep finds the theorem
node and a scalar comparison-data consumer, neither a definition node for these
plain maps. WeilConjectures grep finds no such declarations. Sheaf grep locates the
two real-data definitions at lines 40 and 54 of the reused module. Blueprint search
`finite scalar` returns seven nodes about larger scalar/duality operations; none
owns these maps. `blueprint_refs.py ancestor` confirms
`lem-cbc-completed-extension-zero-comparison`. These searches are recorded in the
new node with queries and outputs.

## Returned-delivery repair

Return H2/stmt_deps at immutable head `15d7dc1c1918` required definition-node ownership
of phi_T rather than citing a theorem only for its helper definitions. Added
`def-pur-finite-coefficient-ring-map` with `existing: true`, listing both helpers;
removed `lem-exc-proetale-finite-scalar-unit-comparison` from the item's stmt_deps and
cited the new definition instead. The theorem does not occur in proof_deps and is
not added there. Kept the reviewed Lean statement and all its definitions unchanged.
Compared the saved node to the current shared base: apart from its lean record,
the resulting item differs only by this new definition dependency. No statement
correction, dependency repair or source change is required.

Repair self-check by NB: opened both existing definition bodies and the new node.
The new statement's finite rings, discrete topologies, unital ring map, scheme,
pointwise formula, restriction naturality and sheafification all match those bodies.
No comparison theorem, `.choose` or arbitrary sheaf map defines phi_T. Both zero
rings and the empty scheme remain allowed; identity and noninjective ring maps are
covered by pointwise composition. The item still has the same two correctly typed
composition equalities and only its matching theorem has a postponed proof.


## Repair validation (2026-10-21)

The saved-packet dry run was attempted first as instructed. It failed before checking
the item: the local fallback cannot import Mathlib while compiling the infrastructure
overlay `WeilConjectures.Mathlib.CategoryTheory.NatIso`, and server confirmation says
`Live published library is unavailable`.
After completing the ownership repair, ran prescribed
`scompile.py NB lem-cbc-finite-constant-map-naturality
lean/Sheaf/AlgebraicGeometry/FiniteConstantMapNaturality.lean`, then repeated
`deliver2.py NB lem-cbc-finite-constant-map-naturality --no-push`.
Both again failed with the same infrastructure error, `unknown module prefix
'Mathlib'`, followed by `Live published library is unavailable`. The repaired dry
run recognized two Lean sources (including the existing definitions) but could not
compile the infrastructure overlay. No item diagnostic or preflight result was
produced and nothing was pushed. Launcher tools and live library were not modified.

Sandbox self-check passed: valid JSON with indent 1 and final newlines; the only
mathematical dependency change is replacement of theorem ownership by the new
definition node; the item signature equals the recorded statement verbatim; the
new existing-definition signature occurs verbatim in the unchanged published source;
all item Lean lines have at most 100 characters; the sole postponed proof is the
item's named theorem. Full compile and preflight remain unverified due to the
reported tool failure. The repaired packet is retained for retry.


## Infrastructure retry (2026-10-21 04:11 UTC)

Inspected the retained report first and ran the prescribed saved-packet
`deliver2.py NB lem-cbc-finite-constant-map-naturality --no-push`. It failed
before checking the delivery while compiling the infrastructure overlay
`WeilConjectures.Mathlib.CategoryTheory.NatIso`: the object file
`Mathlib/CategoryTheory/Functor/Category.olean` does not exist in the live
published Mathlib build. Server confirmation again reports
`Live published library is unavailable`. The prescribed standalone
`scompile.py` invocation for `FiniteConstantMapNaturality.lean` reproduced
that same missing-object-file error and server confirmation (exit 1).
This is not the busy-server/no-answer timeout.

Rechecked the retained ownership repair against the current shared node and
opened both existing definition bodies: the new definition node owns
`finiteScalarPresheafMap` and its sheafified `finiteScalarRingMap`, and the
item cites it instead of the theorem. The current-base item delta remains
only `lean` and addition of the new definition dependency. The item signature
is verbatim, all Lean lines fit 100 characters, both JSON files retain the
required layout, and the new definition id is absent on the shared base.
The previously reviewed Lean statement and the repair are retained unchanged.
No live library, compiler artifacts, launcher scripts or Git state were
manually changed; compilation and delivery remain blocked by infrastructure.

## Infrastructure retry (2026-10-21 04:13 UTC)

Inspected the retained report and first ran the saved-packet prescribed
`deliver2.py NB lem-cbc-finite-constant-map-naturality --no-push`.
It failed before checking the item while compiling the infrastructure overlay
`WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Preserves`:
`Mathlib/CategoryTheory/Abelian/GrothendieckAxioms/Basic.olean` does not exist.
The prescribed standalone `scompile.py` invocation for
`FiniteConstantMapNaturality.lean` reproduced the same missing object file;
both wrappers confirmed on the server `Live published library is unavailable`
and exited 1. This is not a busy-server timeout or an item elaboration error.

Compared the saved packet with the current shared base. Refreshed the item's
stale `lean_audit` value to the current empty record; its only remaining field
changes are `lean` and addition of the new definition in `stmt_deps`. The new
node is still absent from the shared base. Rechecked both definition bodies,
their declaration ownership, the verbatim signatures, JSON layout, and Lean
line lengths. The reviewed Lean statement is unchanged. No launcher script,
live Lean source, build artifact, or Git state was manually changed. The
ownership repair is retained, but compilation/preflight remain unverified
because of the published-library failure; nothing was pushed.

## Infrastructure retry (2026-10-21 04:19 UTC)

Read the retained report and ran the saved-packet prescribed
`deliver2.py NB lem-cbc-finite-constant-map-naturality --no-push` first.
The dry run recognized both Lean sources. Its local fallback progressed through
the imported infrastructure but timed out after 60 seconds on
`WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`;
server confirmation reported `Live published library is unavailable`.
No diagnostic concerned the item's declaration or the ownership repair.

Then ran the prescribed standalone
`scompile.py NB lem-cbc-finite-constant-map-naturality
lean/Sheaf/AlgebraicGeometry/FiniteConstantMapNaturality.lean`.
The local fallback again timed out on the same infrastructure module. This time
server confirmation compiled a sequence of infrastructure modules, but stopped at
`Sheaf/CategoryTheory/SiteInverseImageTensor.lean:6:0` because the object file
`/home/ubuntu/weil-conjectures-sheaf/lean/.lake/build/lib/lean/WeilConjectures/Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.olean`
does not exist. The wrapper exited 1 before compiling the item. This is an
explicit missing published dependency artifact, not a busy-server/no-answer
timeout. No compiler limit, launcher script, live source or artifact was changed.

Reopened the node, the delivered Lean statement, both existing coefficient-map
definition bodies and the current dependency interfaces. The packet still differs
from the current shared item only in `lean` and addition of the new definition
dependency. `def-pur-finite-coefficient-ring-map` remains absent from the current
shared DAG and owns both existing real-data definitions, without using the
scalar-unit theorem or its conclusion. The main theorem is unchanged from the
reviewed statement: arbitrary g, finite discrete commutative B and C, arbitrary
unital phi, and both correctly ordered equalities. Its signature equals the node
record verbatim; the existing definition signature matches its source verbatim;
all item Lean lines fit 100 characters; JSON layout and exact new-node statement
citations pass. The ownership repair remains complete and retained. Compile and
preflight cannot be certified through the prescribed tools in this retry, and
nothing was pushed.

## Infrastructure retry (2026-10-21 04:25 UTC)

Read the retained report and first ran the saved-packet prescribed
`deliver2.py NB lem-cbc-finite-constant-map-naturality --no-push`.
The dry run recognized both Lean sources but failed before compiling the item.
Both its local attempt and server confirmation reported that
`WeilConjectures/Mathlib/AlgebraicGeometry/Limits.olean` does not exist, while
compiling the infrastructure module
`WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.EssSurj`.

The prescribed standalone `scompile.py NB
lem-cbc-finite-constant-map-naturality
lean/Sheaf/AlgebraicGeometry/FiniteConstantMapNaturality.lean` also exited 1
before reaching the item. Its local attempt and server confirmation failed in
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` because the published
`WeilConjectures/Mathlib/CategoryTheory/Functor/KanExtension/Preserves.olean`
is missing. Neither failure is the busy-server/no-answer timeout.

Reopened the retained theorem and both existing coefficient-map definition
bodies. Compared both node files with current main without running Git:
the item differs only in `lean` and addition of
`def-pur-finite-coefficient-ring-map` to `stmt_deps`; the new node remains
absent on current main. The new node owns both the pointwise presheaf map and
its sheafification with real data, without using the scalar-unit theorem's
conclusion. Both signatures match their sources verbatim; JSON layout, the
single named postponed proof, explicit universe and variable binding, and
100-character Lean lines pass the sandbox self-check. The reviewed statement
and the completed ownership repair are retained unchanged. No live sources,
artifacts, launcher scripts or Git state were manually modified.

After that self-check and report update, repeated the prescribed saved-packet
dry run. It again exited 1 before the item: both local compilation and server
confirmation failed in
`WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude` on missing published
`WeilConjectures/Topology/Stratification.olean`. The earlier infrastructure
modules progressed, but the complete published dependency closure is still
unavailable. No delivery diagnostic concerns the ownership repair or theorem.
Preflight and compilation cannot be certified; nothing was pushed.

## Infrastructure retry (2026-10-21 04:27 UTC)

Read the retained report first and ran the prescribed saved-packet dry run
`deliver2.py NB lem-cbc-finite-constant-map-naturality --no-push`.
It recognized both Lean sources, but local compilation and server confirmation
both failed in the infrastructure overlay
`WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude` at line 6: the published
`WeilConjectures/Topology/Stratification.olean` does not exist.
The prescribed standalone `scompile.py NB
lem-cbc-finite-constant-map-naturality
lean/Sheaf/AlgebraicGeometry/FiniteConstantMapNaturality.lean` reproduced
that exact missing published object file locally and on server confirmation;
both commands exited 1 before compiling the item. This is an explicit missing
artifact, not the busy-server/no-answer timeout.

Reopened the saved theorem, current shared node, both existing scalar-map
construction bodies, and the canonical rho/c and coefficient-sheaf definitions.
The H2 repair remains complete: the new definition node owns pointwise
composition and its sheafification, and the item cites that definition instead
of the scalar-unit theorem. The current shared item already omits that theorem
from stmt_deps; the saved node differs from it only in lean and addition of
`def-pur-finite-coefficient-ring-map`. The new definition remains absent from
the shared base. The theorem retains arbitrary g, finite discrete commutative
B/C, arbitrary unital phi, and both correctly ordered equalities. Checked
verbatim signatures, indent-1 JSON and final newlines, all new-node statement
citations, the single named sorry, and 100-character Lean lines. These checks
pass. No mathematical or source modification is necessary. No launcher tool,
live source, published artifact or Git state was manually changed. The packet
is retained; compilation/preflight remain blocked by the missing published
artifact and nothing was pushed.


## Successful infrastructure retry (2026-10-21 04:31 UTC)

Inspected the retained packet and ran the prescribed saved-packet dry run first.
The missing published artifacts from the prior attempts no longer prevent progress.
The standalone prescribed scompile.py invocation with the absolute sandbox source
path passed: the scalar-unit module overlay compiled in 24.9 seconds, the sandbox
statement in 4.4 seconds, and the library-named statement in 3.5 seconds, with
no errors or warnings.

Reopened the reviewed statement, the two existing coefficient-map bodies, and the
canonical coefficient sheaf, rho, c, inverse-image/direct-image and adjunction
interfaces. The new definition node owns pointwise composition and its
sheafification with real data; the item cites it rather than the theorem. Both
composition equalities retain their reviewed order, with arbitrary g and unital
phi and finite discrete commutative rings, including zero rings, empty schemes,
identity and noninjective maps. The source blueprint ancestor was read again.

Compared the saved item with the current shared base without Git: only lean and
addition of def-pur-finite-coefficient-ring-map in stmt_deps differ. The new node
is absent on the base. Both signatures are verbatim, JSON layout and final
newlines conform, autoImplicit is false, all universes and variables are bound,
and all Lean lines fit 100 characters. The sole postponed proof remains the
item's named theorem. Retained the completed H2 ownership repair and unchanged
reviewed Lean statement; no additional mathematical repair was needed.

The prescribed dry run completed successfully: `OK (dry run): commit 2217e9ef2a9 passes the preflight and compiles; nothing pushed`. Both delivered node records and both referenced Lean sources passed the wrapper checks. Proceeding with the prescribed delivery wrapper.
