## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleFiniteStalkSpecializationCriterion` states
`AlgebraicGeometry.Scheme.finiteLocallyConstant_of_finite_stalks_of_bijective_specialization`.
The node's statement is unchanged. This is the finite-ring, Noetherian-base case of
Stacks Tag 0GKC, implication (2) to (1). The source's finite-type stalk condition becomes
set finiteness over a finite ring, as the node explicitly requires.

Hypotheses and conclusion, clause by clause:

- Scheme S: `{S : Scheme.{u}}`.
- Noetherian means quasi-compact and locally Noetherian: `[IsNoetherian S]`, whose
  Mathlib fields are exactly `IsLocallyNoetherian S` and `CompactSpace S`.
- Finite commutative coefficient ring: `{Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]`.
- Module sheaf on the small étale site:
  `G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, the constructible-material
  encoding specified in the standing brief and dependency record.
- Every geometric stalk is a finite set: `hfinite` quantifies over geometric points
  `s : Spec (.of Ω) ⟶ S` and asserts `Finite` of the underlying type of
  `(pointSmallEtale s).sheafFiber.obj G`.
- Every geometric point of each strict henselization: `hsp` quantifies independently
  over Ω and Ξ with their fields and algebraic-closure instances, then over s and
  `t : Spec (.of Ξ) ⟶ strictHenselizationScheme s`.
- Bijective specialization: `Function.Bijective (etaleModuleStalkSpecialization s t G)`.
  The map has target stalk at `t ≫ strictHenselizationStructuralMap s`, precisely the
  image point in S. Its definition is uniquely fixed by affine pointed-neighbourhood
  germs; no arbitrary linear map or unspecified action is assumed.
- Étale covering: `∃ 𝒰 : Cover.{u} etalePrecoverage S`. This is a jointly surjective
  family of étale morphisms, and allows the empty cover of the empty scheme.
- Finite modules and local constant trivializations: for each i,
  `∃ M : ModuleCat.{u + 1} Λ, Finite M ∧ Nonempty (...)`, with the isomorphism from
  `G.over (𝒰.etalePrecoverageToEtale i)` to the constant sheaf with value M on the
  localized site. This is exactly the restriction convention of
  `LocallyConstantDatum` and `IsLocallyConstantSheaf`; the localized site is the small
  étale site of the covering member up to its canonical equivalence. The finite
  trivializing module is supplied explicitly, rather than only asserting local constancy.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the existing étale-sheaf framework;
  module coefficients use `CategoryTheory.Sheaf` with `ModuleCat`, as its record directs.
  Its source was absent in the local pinned source tree but was read from the live
  library, and its availability was verified by a server import and #check.
- `Mathlib.CategoryTheory.Sites.Point.Basic`: `Point.sheafFiber`,
  `Point.toPresheafFiber`; `Mathlib.AlgebraicGeometry.Sites.EtalePoint`:
  `Scheme.pointSmallEtale`. The stalk is the pointed-neighbourhood colimit.
- `Sheaf.AlgebraicGeometry.StrictHenselization`: `strictHenselizationRing`,
  `strictHenselizationScheme`, `strictHenselizationCone`,
  `strictHenselizationNeighbourhoods`, `strictHenselization_properties`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`.
- `WeilConjectures.ConstructibleSheaf.Defs`: `LocallyConstantDatum`,
  `IsLocallyConstantSheaf`, `Cover.etalePrecoverageToEtale`. Their full signatures
  and the localized-site definition were read, rather than using a set-sheaf predicate
  for the module-valued conclusion.
- `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `strictHenselizationStructuralMap`, `exists_strictHenselizationStructuralMap`.
  The base record, repaired by NA on 2026-10-15, now names this model directly.

The main module imports the stated proof-dependency modules
`Sheaf.Paper.InverseImageStalkGerm`,
`Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk`,
`Sheaf.AlgebraicGeometry.GeometricStalkComparisonConstant`,
`Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`, and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
Other proof-only leaves with no recorded module are not invented or restated.
Its docstring carries all six proof steps and the dependency IDs, including the finite
operation-table construction, germ calculations, two-way specialization stability,
component shrinking and stalkwise-isomorphism argument.

Edge cases checked: S empty (empty covering); the zero module (one-element finite
stalks); the zero ring and all characteristics; disconnected S and different finite
modules on different covering members; distinct Ω and Ξ; reflexive specialization.
No nonemptiness or connectedness is required. All universes and variables are explicit.
Geometric points use the algebraically closed field model of the recorded strict
henselization dependency; field sizes are the scheme universe, as in that declaration.
The coefficient ring and stalk modules lie in u+1 as required by the existing
constructible-sheaf API. There is no independent smaller universe of test objects.

Searches for existing statements and notions:

- `msearch.py leanfinder` with “finite geometric stalks bijective specialization maps
  locally constant etale module sheaf”: 8 hits, on topological stalks, structure sheaves,
  and algebraic étale loci; none states this criterion.
- `msearch.py loogle` with `"specialization", "sheaf"`: 0 hits.
- `msearch.py grep` with `specialization.*(stalk|sheaf)|stalk.*specialization`
  under AlgebraicGeometry: 0 hits.
- `msearch.py leansearch` with “specialization map geometric stalks etale sheaf strict
  henselization germs”: service unavailable (Internal Server Error).
- `msearch.py leanfinder` with that specialization query: 8 hits, all about
  structure-sheaf stalks on schemes or locally ringed spaces; none gives geometric
  module-sheaf stalk specialization.
- `rg` in the pinned WeilConjectures source, project `lean/Sheaf`, and the upstream
  declaration-name index found no exact criterion or proposed declaration-name collision.
  Searching the item ID in the pinned source found no match.
- DAG text search and `tools/blueprint_refs.py search specialization` found mentions
  in this criterion and the strict-local lifting lemma but no definition node for the
  specialization map. The five blueprint-name results were unrelated.
- The live upstream `Sites.StrictHenselization` source was also read: it supplies
  `strictLocalizationConeAll` and `strictLocalizationToBase`, but no geometric module
  stalk specialization map. Its strict-localization model is distinct as a Lean term
  from the small representative construction in this node's recorded dependency.

Both delivered modules compile cleanly with scompile.py on the server, nice 19,
two threads, 60 seconds per file. No local compiler or lake build was run.
No mathematical statement dispute or statement correction is needed.

## New nodes

`def-weil-pbc-etale-module-stalk-specialization` defines the specialization map needed
by the criterion, following Stacks Tag 0GJ2, section-specialization. It takes exactly
the existing stalk colimit, strict henselization, limit projections and structural map.
`IsEtaleModuleStalkSpecialization` prescribes the value on every affine pointed germ:
the target lift is explicitly required to equal t followed by the specified cone leg.
The structural-map identity ensures such a lift exists for every representative.
`existsUnique_etaleModuleStalkSpecialization` states the colimit universal property;
its docstring explains existence and uniqueness. The definition chooses that unique
map, so its data are determined, as permitted by AGENTS.md §5. The equality hypothesis
on v records the actual cone projection, rather than quantifying over unrelated lifts.
Affine cofinality makes this characterization equivalent to using all neighbourhoods.
The searches above found no existing declaration or DAG node defining this notion.
The new node is cited directly from the item; its source, searches, ancestry, and
complete Lean record are included.

## Repair of the previous attempt

The structural-map record is now repaired on newtargets-dag by group NA (2026-10-15).
Its declaration is `AlgebraicGeometry.Scheme.strictHenselizationStructuralMap` in
`Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`, with source
`strictHenselizationScheme s`, exactly as required here. The previous attempt's
sandbox copy would redundantly change that already-correct record. It has been
removed. This delivery now reuses the landed record without changing it, and adds
its id to the item's statement dependencies under STMT_DEPS MAY GAIN LANDED NODES.
There are no dependency modules or dependency-record repairs in this delivery.
The specialization definition and the main theorem are unchanged.

The earlier preflight rejection is thus resolved by the base record repair, with
no mathematical statement correction, substitute object, or change to the tools.
The independent second reading remains the next worker's responsibility.


## Second reading by NB

Independent second reader, 2026-10-15. Read the item and the new definition node,
both delivered modules, Stacks etale-cohomology.tex section-specialization (0GJ2)
and lemma-characterize-locally-constant-module (0GKC), including its proof, with
these texts open together. No mathematical mismatch was found; no Lean or node
change was needed. The only change is this independent review record.

The node's objects, hypotheses and conclusions, matched individually:

1. A scheme S: `{S : Scheme.{u}}`, the recorded Mathlib scheme category, not an
   affine-only or field-base model. Verdict: exact.
2. S is quasi-compact and locally Noetherian: `[IsNoetherian S]`. Opened
   Mathlib.AlgebraicGeometry.Noetherian: this class extends precisely
   `IsLocallyNoetherian S` and `CompactSpace S`; the former says that every affine
   open has Noetherian sections. Verdict: exact; no separatedness assumption.
3. A finite commutative coefficient ring: `{Λ : Type (u + 1)} [CommRing Λ]
   [Finite Λ]`. Verdict: exact, including the zero ring.
4. G is a module sheaf on S's small etale site:
   `G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
   Read the dependency record's explicit two-encoding convention and the source
   ConstructibleSheaf.Defs module. This is its module-valued encoding, with no
   additional field, torsion, constructibility, or finite-presentation hypothesis
   on G. Verdict: exact.
5. Every geometric stalk is a finite set: `hfinite` universally quantifies Ω,
   its `Field` and `IsAlgClosed` instances, and `s : Spec (.of Ω) ⟶ S`, then
   asserts `Finite` of the underlying type of `((pointSmallEtale s).sheafFiber).obj G`.
   Opened Mathlib's EtalePoint and Point.Basic: the point's fiber consists of
   lifts over S, `presheafFiber` is the colimit over the opposite category of
   those lifts, and `sheafFiber` applies that functor to the underlying presheaf.
   Verdict: the recorded geometric stalk, with set finiteness as required.
6. All specified specializations are bijective: `hsp` universally quantifies
   independent algebraically closed fields Ω and Ξ, s, and every
   `t : Spec (.of Ξ) ⟶ strictHenselizationScheme s`, and asserts
   `Function.Bijective (etaleModuleStalkSpecialization s t G)`.
   Its target is the stalk at `t ≫ strictHenselizationStructuralMap s`, not at
   an unrelated point or a stalk on another base. Stacks 0GJ2 explicitly explains
   this same abuse of notation in writing the target as G_t. Verdict: exact.
7. An etale covering: `∃ 𝒰 : Cover.{u} etalePrecoverage S`.
   Opened Mathlib's Etale site definition (`precoverage @Etale`) and the source's
   `Cover.etalePrecoverageToEtale` and `LocallyConstantDatum`. These are the
   jointly surjective etale covers and their small-site objects. Verdict: exact.
8. For each covering member a finite Λ-module and a trivialization:
   `∀ i : 𝒰.I₀, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧ Nonempty (...)`.
   The displayed isomorphism restricts G with `G.over` and compares it with
   `(constantSheaf (S.smallEtaleTopology.over ...)
   (ModuleCat.{u + 1} Λ)).obj M`. Opened the source's locally constant datum
   and Mathlib's constantSheaf body: restriction is on precisely the localized
   site, and constant sheaf is sheafification of the constant presheaf.
   Verdict: all clauses and quantifier order agree; M may vary with i.

The source 0GKC allows a more general base and a Noetherian coefficient ring.
The item explicitly asks for its Noetherian-scheme, finite-commutative-ring case.
Over a finite ring, finite generation and finiteness of the underlying module
are equivalent. Thus the specialization of the source in the node and Lean
agrees; it does not require a correction record. Neither node has statement_change.

New-node reading (H12): `def-weil-pbc-etale-module-stalk-specialization` is a
separate, previously unrepresented notion. Its objects S, Λ, G, s, t and ρ
and its germ formula agree with Stacks 0GJ2. I opened the recorded
StrictHenselization and StrictHenselizationStructuralMap project modules: the
former takes the coordinate-ring colimit on the small representative category,
the latter is its map to S, characterized by the same cone legs. In
`IsEtaleModuleStalkSpecialization`, j runs through that representative category;
its inverse-equivalence image supplies the pointed affine object and its lift.
The equality constraining `v.left` is exactly t followed by the cone projection,
then `Spec.map (ΓSpecIso ...).inv` to the original affine spectrum. The
structural-map characterization makes this an actual lift over S, so the
condition is not vacuous. `toPresheafFiber` is the colimit coprojection, as
confirmed by opening its body. The equation therefore prescribes the image of
every affine pointed germ, with the correct direction of composition.
Affine cofinality determines every stalk element. The named theorem
`existsUnique_etaleModuleStalkSpecialization` states existence AND uniqueness of
that linear map; the definition chooses from this unique specification. This is
permitted determined data, not an unconstrained choice from mere existence.
Its docstring explains the colimit proof. All other theorems in the two delivered
files also have whole-proof `sorry`; no proof was supplied in this stage.

The new node has the required definition/split status, null mathlib_match,
empty proof/proof_deps, source, created ancestry and via chain, matching
chapter/unit, none audits, searches, and Lean record. Its six cited dependency
IDs are exactly its stmt_deps. The item cites it. There are no delivered
dependency modules and no dependency-record edits to review under H13.
The already-landed structural-map dependency is used directly.

Edge cases: the cover may have empty index type for the empty scheme;
there is no Nonempty S or Nonempty index hypothesis. The zero module has a
one-element finite stalk and is admitted. The zero ring is admitted. There is
no n or characteristic restriction, no connectedness hypothesis, and no single
module is forced across different components. Reflexive specializations and
geometric points with distinct fields are included. All scheme and test-field
universes are the common u of the recorded geometric-point and strict-localization
APIs; coefficients and stalks are in u+1, matching ConstructibleSheaf.Defs.
There is no independent smaller test universe, and all variables and universes
are explicitly bound. No extra instances remain in the theorem signature.

Independent searches, using words different from the first reader's queries:

- msearch leanfinder: `etale sheaf locally constant finite fibers invariant under
  generization`: eight hits, concerning algebraic etale loci, spreading out and
  module rank. None states this criterion or defines its specialization map.
- msearch loogle: `"sheafFiber", "Bijective"`: one hit,
  `Point.toPresheafFiber_map_bijective`, concerning a morphism of presheaves
  which is locally bijective, not strict-localization specialization.
- msearch leansearch: `canonical map between geometric fibers of etale module
  sheaf induced by strict localization`: service unavailable, Internal Server
  Error; no mathematical verdict inferred from the unavailable search.
- rg for both specialization/generization spellings near sheaf/stalk/fiber in
  the pinned WeilConjectures source, Mathlib AlgebraicGeometry and project
  lean/Sheaf found structure-sheaf/Zariski stalk maps and unrelated references,
  not this etale module-stalk map or criterion. Searching the proposed names
  in the upstream-name index and both project source roots found no collision.
- DAG searches for stalk specialization give the criterion and the strict-local
  lift discussion, not a pre-existing definition node carrying this map.

The module and declaration docstrings identify the source and blueprint IDs;
the theorem docstring follows all six proof steps of the node, including finite
operation-table relations, pullback and constant germ calculations, two-way
specialization stability, removal of components, and stalkwise isomorphism.
The main signature and definition signature are verbatim in their lean.statement
records. Both delivered files compiled cleanly through scompile.py on the server:
EtaleModuleStalkSpecialization in 1.6 seconds and
EtaleFiniteStalkSpecializationCriterion in 1.7 seconds, nice 19, two threads,
60-second per-file limit. No local compiler or global build was used.
