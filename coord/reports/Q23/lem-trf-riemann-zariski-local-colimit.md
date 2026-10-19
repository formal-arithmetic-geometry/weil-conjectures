## Worker report

Delivered module: `Sheaf.TraceFormula.RiemannZariskiLocalColimit`.
Main declaration: `AlgebraicGeometry.RiemannZariski.riemann_zariski_local_colimit`.
The theorem has proof `sorry`; all definitions have actual data. Only the item's
`lean` field changes. There are no new nodes or dependency modules.

The source was read at [Temkin, Stable modification of relative curves, §3.2](https://arxiv.org/html/0707.3953v3#S3.SS2),
including the definition of quasi-modifications, Lemma 3.2.2 and Corollaries
3.2.4--3.2.5. The node's eight-step proof is reproduced in the theorem docstring,
including the explicit finite-subalgebra construction and both cofinal restrictions.
The helper declarations unpack notions already introduced in this node, rather
than introducing independent mathematical notions.

Hypothesis and clause correspondence:

- Integral finite-type-over-ℤ base: `T : Scheme.{u}`, `[IsIntegral T]`,
  `t : T ⟶ Spec (.of (ULift.{u} ℤ))`, `[LocallyOfFiniteType t] [QuasiCompact t]`.
  These are the dependency's exact Mathlib finite-type conventions. `ULift ℤ`
  expresses the integer spectrum in the scheme universe.
- Chosen separable closure: `(L : Type u) [Field L] [Algebra T.functionField L]
  [IsSepClosure T.functionField L]`. The generic map is the spectrum of this
  algebra map followed by `T.fromSpecStalk (genericPoint T)`.
- Valuation ring inside `L`, with fraction field `L`: `V : ValuationSubring L`.
  Mathlib supplies the fraction-field property for this actual subring. The given
  map is `s : Spec (.of V) ⟶ T`; `hs` is exactly its prescribed generic restriction.
- An integral separated finite-type generic quasi-model is the recorded
  `RiemannZariski.QuasiModel T L η`. `CenteredQuasiModel.model` uses this existing
  structure. `lift`, `lift_map`, `lift_generic` add the prescribed valuation lift
  and both compatibility equations. `centre` and `lift_centre` record the image
  of the closed point of `Spec V`.
- Refinement from `U'` to `U`: `CenteredRefinement U U'` has
  `hom : U'.model.X ⟶ U.model.X`, with `over`, `valuation`, `generic`, and `centre`.
  Its `localMap` is the actual `hom.stalkMap`, transported along its equality of
  centres. It is not an independently chosen ring homomorphism.
- One representative of each isomorphism class: `CenteredQuasiModelIso` records
  an actual scheme isomorphism preserving the base map and both generic and
  valuation maps. `CenteredLocalSystem.complete` represents every admissible
  model, and `representatives` prohibits duplicate isomorphism classes.
- Small directed system ordered by refinement: `I : Type u`, Mathlib
  `[PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]`, and
  `le_iff_refinement`. `refinement_unique` states uniqueness of the actual
  refinement morphisms between representatives.
- Injective local transitions: `ringMap_local`, `ringMap_injective`, and
  the definition `CenteredLocalSystem.ringMap` identify each transition with the
  corresponding refinement stalk map. `ringMap_id` and `ringMap_comp` make the actual ring functor.
- Local maps to `V`, as subrings of `L`: `localToValuation` is constructed from
  `Scheme.stalkClosedPointTo` and the equality of centres. `CenteredLocalSystem.intoV`
  defines each cocone leg by this construction; `intoV_local` and
  `intoV_injective` give its local injective properties. `insideL` identifies its
  composite with `V.subtype` with `localToField`, the canonical stalk embedding
  into the model's function field followed by the recorded generic field embedding
  into `L`. `intoV_compat` is precisely compatibility of these inclusions.
- Filtered colimit: `CenteredLocalSystemData.ringDiagram` is a genuine Mathlib functor
  to `CommRingCat.{u}`, and `ringCocone` has vertex `.of V` and the above canonical
  legs. `LocalColimitData.ring_colimit` is Mathlib `IsColimit` of that exact cocone.
- Inverse limit: `schemeDiagram` is `ringDiagram.op ⋙ Scheme.Spec`;
  `schemeCone` is `Scheme.Spec.mapCone ringCocone.op`. Its vertex is `Spec V`
  and its legs and transitions are exactly the spectra of the canonical ring maps.
  `LocalColimitData.scheme_limit` is Mathlib `IsLimit` of that exact cone in the
  category of schemes.
- Full family: the first conjunct gives `LocalColimitData` for every centred
  quasi-model, with no admissibility restriction.
- Refinements of any fixed centred quasi-model: the second conjunct quantifies
  over `U₀` and gives the same data for the predicate
  `fun U ↦ Nonempty (CenteredRefinement U₀ U)`.
- Affine models mapping into a fixed affine centre neighbourhood: the final
  conjunct quantifies over `U₀`, an affine open `W : U₀.model.X.Opens`, and
  `hx : U₀.centre ∈ W`. Its admissibility predicate explicitly requires
  `IsAffine U.model.X` and a refinement `r` factoring through `W`, with equation
  `f ≫ W.ι = r.hom`. Completeness again ranges over every admissible model.

`Nonempty LocalColimitData` asserts existence of representative systems with all
these properties. No construction chooses data from this theorem. In particular,
the canonical stalk maps and canonical cones are fully constructed before the
postponed theorem, and the Mathlib universal-property predicates are used directly.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.RiemannZariskiFiniteRefinement`:
  `AlgebraicGeometry.RiemannZariski.QuasiModel`, `GenericScheme.fieldEmbedding`;
  the recorded `ValuationPoint` and `ValuationPoint.LiftsTo` were also read.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `...QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.FunctionField`: `Scheme.functionField`,
  `stalkFunctionFieldAlgebra`, and the fraction-field instances on centre stalks.
- `Mathlib.AlgebraicGeometry.Stalk`: `Scheme.stalkClosedPointTo` and its localness;
  `Mathlib.Topology.Sheaves.Stalks`: `Presheaf.stalkCongr`.
- Mathlib's `PartialOrder`, `IsDirected`, preorder category, `Functor`, `Cocone`,
  `Cone`, `IsColimit`, `IsLimit`, and `Scheme.Spec` are used without private copies.
- Stated proof-dependency modules are imported, including Mathlib's Noetherian,
  affine, closed-immersion, finite-presentation, localization and limit modules,
  and the upstream `WeilConjectures.AlgebraicGeometry.Modules.VeryAmple`.

Proof-dependency record fault observed: `lem-pc-closed-imm-base-change` currently
records `IsVeryAmple.pullback_of_field`, although its intended proof step uses
base change of a closed immersion. That recorded proof module and the actual
Mathlib closed-immersion module are both imported; its node is outside this
item's statement-dependency repair scope and has not been edited. The current
statement needs no missing dependency interface.

Edge cases checked: `V = L` (trivial valuation) is included, as are elements `0`
and arbitrary characteristic. Nonemptiness and directedness of the index are
explicit. There is no assumption that a quasi-model is proper or affine in the
full family. Affineness occurs only in the last restricted family. The base may
be nonseparated. The empty affine open is excluded only by the required centre
membership, exactly as in the node. Arbitrarily large fields and schemes use the
explicit common universe `u`; the skeleton index lies in that same universe.

Searches made (all required service searches used `msearch.py Q23` with this item):

- LeanFinder: `valuation ring filtered colimit centre local rings quasi-model`:
  eight hits about valuation rings, local subrings, and general ring colimits;
  none states this centred-quasi-model theorem.
- LeanSearch: `A valuation ring is the filtered colimit of local rings at centres
  on finite type models`: eight valuation-ring definitions/instances; no match.
- Loogle: `ValuationSubring, CategoryTheory.Limits.IsColimit`: zero hits.
  Earlier query `CommRingCat.FilteredColimits.colimit, Scheme limits Spec colimit`
  also had zero hits and an unknown `Scheme` identifier.
- Mathlib grep: `Riemann.?Zariski|quasi.?model|ValuationPoint` in
  `AlgebraicGeometry`: zero hits.
- Direct `rg` of `WeilConjectures/` and `lean/Sheaf/` by those concepts and the
  node id found the recorded finite-refinement framework and unrelated general
  localization/colimit results, but no theorem giving this statement.
- Direct `rg` of the proposed helper names in Mathlib/upstream/project source
  and `dag/lean_names_upstream.json` found no existing declarations with those names.

The statement is unchanged and is not disputed. Validation uses only the prescribed
`scompile.py` and `deliver2.py` wrappers; no global build or live-file edit is made.

## Repair of returned delivery

The returned review correctly identified that the prior `CenteredLocalSystem` stored
`ringMap` and `intoV` as arbitrary homomorphisms. I repaired this by separating
`CenteredLocalSystem` (the index, admissible family, explicit completeness/representative
coverage, and refinement data) from `CenteredLocalSystemData` (properties of the maps).
The maps are now definitions: `CenteredLocalSystem.ringMap d h :=
(d.refinement h).localMap` and `CenteredLocalSystem.intoV d i :=
(d.U i).localToValuation`. Thus `ringDiagram`, `ringCocone`, `schemeDiagram`, and
`schemeCone` use these canonical maps definitionally. `CenteredLocalSystem.complete`
explicitly states that every admissible centred quasi-model is represented up to
`CenteredQuasiModelIso`; this is the required representative coverage. The data bundle
only records localness, injectivity, identity/composition, the embedding into `L`, and
compatibility for those already-fixed maps.

## Second reading by Q23

Independent maintainer reading of immutable delivery
`1f0c037da343f0a4a35a153fb112c27a45da77d5`, performed 2026-10-18.
This section replaces the worker's explicit placeholder; it is the maintainer's
reading, not an assertion that a second group worker read the delivery.
Verdict: FIX for documentation and record completeness only. No mathematical
statement, declaration signature, definition body, or proof body is changed.

I read packet.md, check-brief2.md in full, the item's immutable node and module,
all three statement-dependency nodes, their exact relevant declarations, and this
report. I read Temkin §3.2 online at
https://arxiv.org/html/0707.3953v3#S3.SS2 (opening definitions, Lemma 3.2.2 and
Corollaries 3.2.4--3.2.5), including the standing integral/qcqs assumptions.
The finite-type-over-integers hypothesis supplies qcqs here. I also read Stacks
01OK and 01T2 for the dependency definitions, and 01YW for the scheme limit.

Clause audit (all pass):

1. `T : Scheme.{u}`, `[IsIntegral T]`, the morphism to `Spec (ULift ℤ)` and its
   locally-finite-type and quasi-compact instances say integral and finite type
   over the integers. Mathlib `Properties.lean:240`, `FiniteType.lean:43` and
   `QuasiCompact.lean:43` are the recorded definitions, with no extra separatedness
   of T, Noetherian instance, properness, or characteristic restriction.
2. The field/algebra/`IsSepClosure` binders give the specified separable closure;
   the displayed generic map is the algebra map followed by `fromSpecStalk` at
   the generic point. `V : ValuationSubring L` gives a genuine subring of L,
   its valuation property, localness, and fraction field L. `s` and `hs` state
   precisely the prescribed morphism and its generic restriction.
3. `CenteredQuasiModel.model` reuses the recorded `QuasiModel`: its underlying
   `GenericScheme` is integral, has a generic map with generic-point image, and
   a factorization over T. Its instances impose separated finite type, not
   properness. The lift and its two equations add exactly the centred structure;
   `lift_centre` identifies the stored centre with the closed-point image.
4. `CenteredRefinement U U'` has the required direction U' → U and compatibility
   over T and from both spectra. Its centre equation follows from the valuation
   equation; it adds no hypothesis. `CenteredQuasiModelIso` uses an actual scheme
   isomorphism and preserves all specified maps.
5. `CenteredLocalSystem` has a small nonempty directed partial order, all models
   satisfy P, `complete` covers EVERY admissible model up to the specified
   isomorphism, and `representatives` prevents duplicates. The order is exactly
   refinement. The selected refinements are actual scheme maps; their uniqueness
   is asserted, not assumed in the theorem's hypotheses.
6. `localMap` is the actual stalk map with centre transport. `localToValuation`
   is `Scheme.stalkClosedPointTo` with centre transport. `localToField` is the
   stalk-to-function-field algebra map followed by the dependency's canonical
   `GenericScheme.fieldEmbedding`. I checked those definitions in Mathlib
   Stalk.lean:280, FunctionField.lean:81 and the group clone's
   RiemannZariskiFiniteRefinement.lean:115. No arbitrary transition or cocone leg
   is chosen. `ringMap` and `intoV` are definitionally these maps.
7. `CenteredLocalSystemData` asserts localness, injectivity, identities,
   composition and compatibility for those fixed maps. `insideL` identifies the
   valuation inclusion composite with the canonical generic embedding. Thus the
   transitions really are the local subring inclusions in L.
8. `ringDiagram` is a CommRingCat functor on the refinement order; `ringCocone`
   has vertex V and the canonical legs. `ring_colimit : IsColimit ...` asserts
   its full universal property. `schemeDiagram` reverses arrows and applies
   `Scheme.Spec`; `schemeCone` applies Spec to the opposite cocone and therefore
   has vertex Spec V and the prescribed legs. `scheme_limit : IsLimit ...` is
   in all schemes, not merely affine schemes or topological spaces.
9. The three theorem conjuncts use respectively P=True, existence of a refinement
   to any fixed U₀, and affine source with a refinement factoring through the
   specified affine centre neighbourhood W. The W binder is an actual open of U₀,
   its affineness and centre membership are explicit, and the factorization is
   a morphism with equality, not a condition on its set-theoretic image.
   Each restricted system retains full representative coverage and both universal
   properties. Nonempty here asserts the stated existence of systems; no later
   definition uses choice from this theorem to introduce unspecified maps.

Edge cases and sizes: the trivial valuation V=L and zero elements are included;
there is no discrete/rank-one valuation hypothesis. Empty T and empty models
are excluded exactly by integrality. The indexing family must be nonempty as
stated; an empty affine neighbourhood is excluded by centre membership. There
is no characteristic restriction, and T need not be separated. The explicit
universe u binds schemes, rings, L and the small skeleton index consistently.
The same-universe convention does not lose the mathematical case: a larger
ambient universe accommodates any field extension, and finite-type generic
models admit a small skeleton by finite affine presentations. No site-universe
identification or independent too-small test universe is introduced.

Source/proof audit: all eight node proof steps appear in the theorem docstring.
The finite-subalgebra construction gives common affine refinements and contains
any chosen valuation element; common refinements make the union universal and
remain available in both restricted families. Stacks 01YW supplies the scheme
limit from the exact ring colimit. No missing independent prerequisite is needed
for these helper definitions. The report's noted wrong proof-only binding of
`lem-pc-closed-imm-base-change` is pre-existing: the actual Mathlib closed-immersion
module is imported as well. This delivery neither uses that wrong declaration
in a definition nor copies its notion. There are no new dependency records or
statement changes requiring a §1(B)/(C) repair or citer audit.

Searches: I independently searched Mathlib AlgebraicGeometry, upstream
WeilConjectures, and the Q23 clone's lean/Sheaf with rg for Riemann-Zariski,
centred quasi-model/system names, and valuation/colimit combinations. Hits gave
the existing finite-refinement framework, the distinct stable-modification
spreading consumer, and unrelated evaluation/colimit lemmas; no duplicate of
this centred local-colimit theorem or these helpers was found. The worker's
LeanFinder, LeanSearch, Loogle and grep records are preserved above.

Findings repaired: H8, eight helper docstrings lacked a source and/or blueprint
citation; all now have both. H2/§1 helper-record completeness, the declaration
list omitted `CenteredLocalSystem.ringMap` and `CenteredLocalSystem.intoV`;
both are now listed. H11, the second-reading section was only a placeholder;
this substantive audit replaces it. Stale worker prose named removed fields
`ringMap_canonical`, `intoV_canonical`, and the former ringDiagram namespace;
those references are corrected. The source-based statement and exact stored
`lean.statement` remain unchanged, with byte-for-byte signature equality checked.

The fixed file has real definition data, exactly one theorem with proof `sorry`,
no hollow construction, no local theorem proved beyond `sorry`, no local notation
or unbound implicit variable, and no line exceeding 100 characters. Small
functor-law and naturality proofs merely assemble actual diagram data from the
bundle's equations. The source-place/module blueprint and eight-step theorem
proof docstrings are present. No pro-etale substitute or dropped route-pivot
machinery is used. No item repair note exists at the checked shared DAG ref;
none of the delivered nodes' statement/proof dependencies occurs on the
route-pivot dropped list. Only review.md and fixes/ are written; no repository
or branch head is changed, no global build, landing, delivery, or direct SSH is run.

Compiler evidence for the corrected complete module: prescribed command
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q23 lem-trf-riemann-zariski-local-colimit fixes/RiemannZariskiLocalColimit.lean`
returned exit code 0. The wrapper checked sandbox `Sheaf/Stage2/Sandbox0.lean`
(12.0 s reported) and library `Sheaf/Stage2/Check.lean` (69.8 s reported, including
wrapper/slot overhead); neither emitted a Lean error or warning. The wrapper
advertised 60 s per invocation after slot acquisition; no limit was raised.
The installed scompile.py is the 2026-10-17 server-overlay implementation, rather
than the older locally running implementation described by check-brief2.md;
I used that prescribed wrapper without bypassing it. Its output names a private
/dev/shm overlay, not a live project write. A redundant rerun of the original immutable file under its recorded module path
completed the sandbox phase and announced the library phase but produced no final
result after more than six minutes in the wrapper; I stopped that local wrapper
and its connection after the complete corrected module had already passed both
phases. I do not claim a successful final result for that original-file rerun.
The corrected compile and unchanged declaration bodies are the landing evidence.
