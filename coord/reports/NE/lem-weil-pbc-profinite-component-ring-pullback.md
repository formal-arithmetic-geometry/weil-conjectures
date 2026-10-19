## Worker report

The module `Sheaf.RingTheory.ProfiniteComponentRingPullback` states
`Algebra.exists_profinite_component_ring_pullback`, with its entire proof `sorry`.
It introduces no definition, instance, axiom, or replacement for an existing notion.
The node is unchanged except for `lean`.

Hypothesis and clause correspondence:

- A commutative ring with w-local spectrum: `(C : Type u) [CommRing C] [IsWLocalRing C]`.
  The recorded w-local class means `WLocalSpace (PrimeSpectrum C)`; its closed-point
  uniqueness agrees with the connected-component formulation, as checked in
  `WLocalSpace.isHomeomorph_connectedComponents_closedPoints` and its docstring.
- `P` is the connected-component quotient, with its quotient topology:
  `ConnectedComponents (PrimeSpectrum C)`. The underlying space of the recorded
  `AlgebraicGeometry.Spec (CommRingCat.of C)` is precisely `PrimeSpectrum C`.
- `P` is profinite: the first three conjuncts are `CompactSpace P`, `T2Space P`,
  and `TotallyDisconnectedSpace P`. These are conclusions, not added hypotheses.
- The canonical map from closed points to `P` is a homeomorphism: the next conjunct
  is `IsHomeomorph (fun x : closedPoints (PrimeSpectrum C) ↦ ConnectedComponents.mk x.val)`.
  Here `closedPoints` is exactly the subspace of points with closed singleton.
- Every profinite `T` and continuous `u : T → P`: the universal binders on `T`
  include its topology and precisely compactness, Hausdorffness and total
  disconnectedness, followed by `(u : C(T, ConnectedComponents (PrimeSpectrum C)))`.
  The universe parameter is explicit and arbitrary, as in the upstream pullback
  construction and the recorded ind-Zariski/ind-etale predicates.
- There exist a commutative `C`-algebra `D` and the topological pullback homeomorphism:
  `∃ (D : Type u) (_ : CommRing D) (_ : Algebra C D) (e : PrimeSpectrum D ≃ₜ
  {z : PrimeSpectrum C × T // ConnectedComponents.mk z.1 = u z.2}) ...`.
  This subtype has the subspace topology and is the actual topological fibre product.
- The homeomorphism is over `Spec C`: the first witness conjunct says
  `(e q).val.1 = PrimeSpectrum.comap (algebraMap C D) q` for every prime `q`.
- `π₀(Spec D) ≅ T` over `P`: witness `eπ : ConnectedComponents (PrimeSpectrum D) ≃ₜ T`,
  together with `eπ (ConnectedComponents.mk q) = (e q).val.2`, ties it to the second
  projection of the same pullback homeomorphism. The next equality
  `u (eπ p) = (PrimeSpectrum.continuous_comap (algebraMap C D)).connectedComponentsMap p`
  explicitly expresses compatibility over `P` for each component `p`.
- The ring map is ind-Zariski and ind-etale: `IsIndPrincipalZariski C D ∧ IndEtale C D`.
  The former is the dependency's exact finite-products-of-principal-localizations
  predicate, rather than upstream's wider `Algebra.IndZariski` predicate.
- For every prime of `D`, the induced local-ring map is an isomorphism:
  `∀ q : PrimeSpectrum D, Function.Bijective (Localization.localRingHom
  (q.asIdeal.comap (algebraMap C D)) q.asIdeal (algebraMap C D) rfl)`.
  This map has domain `Localization.AtPrime (q.asIdeal.comap (algebraMap C D))`
  and codomain `Localization.AtPrime q.asIdeal`; bijectivity of this ring homomorphism
  is exactly being a ring isomorphism, with no unrelated equivalence substituted.
- The spectrum of `D` is w-local: `IsWLocalRing D`.
- Its closed points are exactly the inverse image of those downstairs:
  `closedPoints (PrimeSpectrum D) = PrimeSpectrum.comap (algebraMap C D) ⁻¹'
  closedPoints (PrimeSpectrum C)`.
- Its closed points map homeomorphically onto `T`: `IsHomeomorph
  (fun q : closedPoints (PrimeSpectrum D) ↦ (e q.val).val.2)` uses the same projection.
- If `u` is surjective, the spectrum map is surjective:
  `Function.Surjective u → Function.Surjective (PrimeSpectrum.comap (algebraMap C D))`.

Dependency declarations read and used:

- `WeilConjectures.RingTheory.ProEtale.WLocal`: `IsWLocalRing`, together with
  `WLocalSpace` and its connected-component/closed-point homeomorphism in
  `WeilConjectures.Topology.SpectralSpace.WLocal.ConnectedComponents`.
- `Sheaf.RingTheory.IndPrincipalZariski`: `Algebra.IsIndPrincipalZariski`, with
  `Algebra.IndEtale` publicly imported from
  `WeilConjectures.RingTheory.ProEtale.IndEtale`. The latter's filtered stages are etale,
  hence finitely presented, exactly as the dependency states.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`;
  their underlying space/map are `PrimeSpectrum` and `PrimeSpectrum.comap` as used here.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime` and
  `Localization.localRingHom`, whose full signature and induced-map docstring were read.
  The residue-field and fibre-ring clauses of the dependency are not needed by this item.

All statement-dependency modules are publicly imported. Every already-recorded
proof-dependency module is one of these imports; the remaining proof-only nodes have
no recorded Lean module in the supplied DAG, so there is no further proof import to add.
The theorem docstring records all eight proof steps, including their named inputs.

Sources checked directly: `literature/stacks-project/proetale.tex`,
`lemma-construct-profinite` (097D), `lemma-silly` (096C),
`lemma-ind-zariski-implies` (096T), and `remark-slightly-stronger` (0A0D).
The last explicitly permits the stronger principal-localization presentation.
The upstream `WContractification.PullbackProfinite` construction, `fiberHomeo`,
`isPullback` and `projSpec_surjective` were read in full. They provide parts of the
assertion but no single exact match for its complete conjunction, especially its
principal ind-Zariski predicate and all the closed-point/local-ring clauses.
No statement correction or disputed assertion was necessary.

Edge cases checked:

- The zero ring has empty spectrum, empty component quotient and empty closed-point
  subspace. A map `T → P` then forces `T` empty; the zero algebra is a valid witness.
- For empty `T` over any `C`, the pullback and `Spec D` can be empty, with `D` the zero
  ring. The recorded principal ind-Zariski predicate permits an empty finite product.
  Prime-local conditions are then vacuous, and no `Nontrivial` or `Nonempty` binder
  excludes this case.
- Nonsurjective `u` is allowed throughout. Spectrum surjectivity is conditional only.
- A singleton `T` selects one entire connected component, not only its closed point;
  this is enforced by the pullback subtype, and all its local rings are retained.
- No connectedness, Noetherianity, field, characteristic, or finite-cardinality
  hypothesis has been added. Profinite spaces may be infinite.

Searches (2026-10-15):

- `msearch.py leanfinder`, query “A profinite pullback of connected components of a w
  local ring spectrum preserves local rings and closed points”: eight hits, including
  `AlgebraicGeometry.Spec_closedPoint`, `SpecToEquivOfLocalRing`, and
  `pointsPi_surjective`; none states the complete result.
- `msearch.py loogle`, query `ConnectedComponents, PrimeSpectrum.comap`: zero hits.
- `msearch.py grep`, query `PullbackProfinite|IsIndPrincipalZariski`: zero Mathlib hits.
- `msearch.py leansearch`, query “profinite pullback of connected components of a w
  local ring”: service unavailable (Internal Server Error), recorded as unavailable.
- `rg` of the source repository for `PullbackProfinite`, `profinite`, `closedPoints`,
  `indZariski` and `localization` found the partial upstream results described above.
  Searching the exact item id found no attached upstream declaration.
- `rg` of `lean/Sheaf` for profinite component pullbacks found no existing statement.
  Exact name `exists_profinite_component_ring_pullback` was absent in Mathlib,
  `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`.

Validation: `scompile.py NE lem-weil-pbc-profinite-component-ring-pullback` compiled
this delivered file on the server cleanly in 1.5 seconds, nice 19, two threads,
60 seconds per file. The tool also built the side-only principal ind-Zariski import
in its private overlay (1.3 seconds). No local compiler or global build was run.
The independent second reader is to add their own reading after the worker dry run.


## Second reading by NE

Independent reading of the sandbox node, the complete delivered Lean module,
all four statement-dependency records and their actual declarations, and the
Stacks source. Verdict: every hypothesis and conclusion is represented; no
statement, module, or dependency repair was needed. The only change in this
second reading is this report section.

The node's objects, hypotheses, and conclusion clauses, matched in order:

1. A commutative ring C with w-local spectrum is `(C : Type u) [CommRing C]
   [IsWLocalRing C]`. I opened `IsWLocalRing` in `RingTheory/ProEtale/WLocal.lean`
   and `WLocalSpace` in `Topology/SpectralSpace/WLocal/Basic.lean`:
   the class asserts spectrality, uniqueness of closed specializations, and
   closedness of `closedPoints`. For an affine spectrum spectrality is automatic.
   The connected-component interpretation is confirmed by
   `WLocalSpace.isHomeomorph_connectedComponents_closedPoints` in the recorded
   ConnectedComponents module. Thus there is no extra ring hypothesis. Pass.
2. P is the quotient of Spec C by its connected components:
   `ConnectedComponents (PrimeSpectrum C)`. I checked Mathlib's quotient
   definition in `Topology/Connected/Clopen.lean`, and `Spec`/`Spec.map` in
   `AlgebraicGeometry/Scheme.lean`. The spectrum and its ring-map-induced map
   used here are their underlying space `PrimeSpectrum` and map `comap`.
   No alternate component or spectrum notion is introduced. Pass.
3. P is profinite: the first three conjuncts are `CompactSpace`, `T2Space`,
   and `TotallyDisconnectedSpace` on precisely P. They are asserted conclusions,
   not hypotheses restricting C. Pass.
4. Closed points map homeomorphically to P: `IsHomeomorph (fun x :
   closedPoints (PrimeSpectrum C) ↦ ConnectedComponents.mk x.val)`.
   Mathlib `closedPoints` in `Topology/JacobsonSpace.lean` is exactly the set
   whose singletons are closed; its subtype topology is the required topology.
   The map is the canonical quotient map on this subspace. Pass.
5. For every profinite T and continuous u: `∀ (T : Type u) [TopologicalSpace T]
   [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
   (u : C(T, ConnectedComponents (PrimeSpectrum C)))`. There is no surjectivity,
   nonemptiness, finite cardinality, or discreteness assumption. Pass.
6. There exist a commutative C-algebra D and a homeomorphism to the pullback:
   `∃ (D : Type u) (_ : CommRing D) (_ : Algebra C D) (e : PrimeSpectrum D ≃ₜ
   {z : PrimeSpectrum C × T // ConnectedComponents.mk z.1 = u z.2}) ...`.
   This is the actual graph-equality subspace of the product, with no prescribed
   substitute ring or abstract space. Its projection to Spec C equals the
   spectrum map by `(∀ q, (e q).val.1 = PrimeSpectrum.comap (algebraMap C D) q)`.
   This renders both the pullback and the phrase 'over Spec C'. Pass.
7. The components of Spec D identify with T over P: the witness
   `eπ : ConnectedComponents (PrimeSpectrum D) ≃ₜ T` is tied to e by
   `∀ q, eπ (ConnectedComponents.mk q) = (e q).val.2`.
   The next clause `∀ p, u (eπ p) =
   (PrimeSpectrum.continuous_comap (algebraMap C D)).connectedComponentsMap p`
   expresses 'over P' for the induced component map. These are compatibility
   conditions for the required identifications, not stronger ring properties.
   Quantifiers use the same D, algebra structure, and e throughout. Pass.
8. C → D is ind-Zariski and ind-etale: `IsIndPrincipalZariski C D ∧ IndEtale C D`.
   I opened the whole recorded `Sheaf.RingTheory.IndPrincipalZariski` module:
   its definition uses a filtered colimit presentation whose stages are
   algebra-equivalent to finite products of `Localization.Away (f j)`.
   It permits `n = 0`. This is exactly the dependency node's principal
   localization convention. Upstream `Algebra.IndEtale` explicitly quantifies
   over filtered presentations with `Algebra.Etale` stages, hence finite
   presentation is included. The broader upstream `Algebra.IndZariski` would
   not render the specified presentation verbatim. Pass.
9. For each prime q the induced local ring map is an isomorphism:
   `∀ q, Function.Bijective (Localization.localRingHom
   (q.asIdeal.comap (algebraMap C D)) q.asIdeal (algebraMap C D) rfl)`.
   I opened the definition and its induced-map docstring in Mathlib
   `Localization/AtPrime/Basic.lean`. Its domain is C localized at the actual
   contraction and codomain is D localized at q; its fraction formula is
   `localRingHom_mk'`. Bijectivity of this ring homomorphism states exactly
   that this induced map is an isomorphism. Pass.
10. Spec D is w-local: `IsWLocalRing D`, with the same recorded class as C.
    Its closed point set is exactly the inverse image of the downstairs set:
    `closedPoints (PrimeSpectrum D) = PrimeSpectrum.comap (algebraMap C D) ⁻¹'
    closedPoints (PrimeSpectrum C)`. This is equality, not a one-way inclusion.
    Pass.
11. Those closed points map homeomorphically to T:
    `IsHomeomorph (fun q : closedPoints (PrimeSpectrum D) ↦ (e q.val).val.2)`.
    This is the same pullback projection, not an unrelated homeomorphism. Pass.
12. If u is surjective the spectrum map is surjective:
    `Function.Surjective u → Function.Surjective
    (PrimeSpectrum.comap (algebraMap C D))`. This hypothesis is local to this
    final implication, not assumed for the construction. Pass.

Source comparison: I read `proetale.tex` at `definition-w-local`, its following
paragraph, `lemma-silly` (096C), `lemma-construct-profinite` (097D),
`lemma-ind-zariski-implies` (096T), and `remark-slightly-stronger` (0A0D).
The ambient assumption for w-local spaces is spectrality, automatic for Spec C;
there is no hidden Noetherian, nonzero, characteristic, field, or connectedness
assumption. 097D supplies the topological pullback, 096C supplies the component,
w-local, and closed-point clauses, 096T supplies identification of the induced
local rings, and 0A0D explicitly allows the principal-localization refinement.
No correction of the natural-language node is necessary, and no
`statement_change` or citer audit is therefore needed.

Edge cases: if C is the zero ring, P and Spec C are empty, so the map from T
forces T empty; D can be the zero ring. Empty T over an arbitrary C also admits
the zero C-algebra, with empty pullback and empty spectrum. Empty finite products
are permitted in the principal ind-Zariski predicate. Every local-ring assertion
then has no primes to check. A one-point T selects an entire component rather
than just its closed point. Infinite profinite T and nonsurjective maps remain
allowed. The universe u is explicitly declared and polymorphic: C, T, and the
constructed D lie in one chosen ambient universe, as in both recorded filtered
presentation predicates and the upstream PullbackProfinite construction; the
ambient universe can be chosen to contain both input objects. No index universe
below the objects, `Nonempty`, or `Nontrivial` binder excludes a source case.
There is no numeric n in this statement; the dependency's finite product allows
n = 0. No characteristic restriction appears.

Independent searches, 2026-10-15:

- LeanFinder through `msearch.py`, query 'A continuous profinite change of the
  connected components of Spec of a w-local ring is induced by a ring map
  inducing isomorphisms on localizations': eight hits, including
  `PrimeSpectrum.toPiLocalization_bijective`,
  `MaximalSpectrum.toPiLocalizationEquiv`, and
  `Localization.AtPrime.mapPiEvalRingHom`; none states this result.
- Loogle through `msearch.py`, query `IsHomeomorph, ConnectedComponents`: zero hits.
- Grep through `msearch.py`, query `connectedComponentsMap|localRingHom`:
  existing component-map and localization-map declarations, no complete match.
- LeanSearch through `msearch.py`, query 'There exists an algebra whose spectrum
  is the fibre product along a profinite map to connected components and whose
  local rings are unchanged': unavailable, Internal Server Error; this is not
  negative mathematical evidence.
- Direct `rg` on Mathlib, the upstream project, this project's `lean/Sheaf`, and
  `dag/lean_names_upstream.json`, using component/pullback, profinite/pullback,
  and ind-Zariski words, found the upstream PullbackProfinite family. I opened
  its construction context and the actual `fiberHomeo`, `isPullback`, and
  `projSpec_surjective` signatures in `WContractible.lean`, and the imported
  `PullbackProfinite.lean` module. These state partial ingredients for the
  broader ind-Zariski predicate, not the whole present conjunction with the
  required principal-localization presentation. No existing declaration of
  this complete statement was found. The exact delivered theorem name is
  absent from those library sources and the upstream-name index.

There are no new definition nodes or dependency modules in this delivery, no
private copies, hollow data definitions, local notation, or added instances.
The sole theorem has `sorry` as its entire proof. Its module and declaration
docstrings carry the source and blueprint id, and its eight numbered proof
steps cover all eight node proof steps. All statement-dependency modules are
public imports; the recorded proof dependencies introduce no additional module
not already imported (the other proof-only nodes have no recorded module).
I mechanically confirmed that `lean.statement` is verbatim the theorem signature
and that no Lean line exceeds 100 characters. All variables and the universe
are explicitly bound.

Second-reader validation: the required `scompile.py` compiled the delivered
`ProfiniteComponentRingPullback.lean` on the server in 1.5 seconds, with nice 19,
two threads and a 60-second per-file limit. Its side-only dependency
`IndPrincipalZariski.lean` also compiled in the private overlay in 1.3 seconds.
There were no errors or warnings. No local compiler or global build was run.
