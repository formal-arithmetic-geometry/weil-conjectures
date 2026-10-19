## Worker report

The original worker account below is retained. The current delivery repairs the
ind-Zariski predicate, duplicate notions, missing colimit interface, and proof
documentation as detailed in the second reading.

The module `Sheaf.RingTheory.StoneanCoverSecondStage` states
`Algebra.stonean_cover_second_stage`, with the expected stage-2 `sorry` proof.  It
also records the canonical data named in the source statement:
`Algebra.StoneanClopenPartition`, `Algebra.stoneanClosedRestriction`,
`Algebra.stoneanPartitionStage`, `Algebra.stoneanCoverRing`, and
`Algebra.stoneanCoverPointMap`.  The cover ring is the existing
`WContractification.PullbackProfinite` graph restriction; that construction is the
canonical filtered colimit of the finite clopen-partition stages (the locally constant
function algebra is itself the filtered colimit over finite discrete quotients).
No new DAG node or dependency repair is needed, and the node statement is unchanged.

Hypothesis and clause correspondence:

- `C : Type u` with `[CommRing C] [IsWStrictlyLocalRing C]` is the arbitrary
  w-strictly-local ring.  The superclass supplies the w-local spectrum and the
  strictly henselian localizations; no field, noetherian, reduced, or characteristic
  hypothesis is added.
- `S : Type u` has `[TopologicalSpace S] [CompactSpace S] [T2Space S]`,
  `[TotallyDisconnectedSpace S]`, and `[ExtremallyDisconnected S]`.  These are
  exactly the compact Hausdorff totally disconnected (profinite) and Stonean
  hypotheses in the node.
- `f : C(S, ConnectedComponents (PrimeSpectrum C))` is the continuous map to
  `P = pi_0(Spec C)`, and `hf : Function.Surjective f` is its stated surjectivity.
- `StoneanClopenPartition` contains a finite set of pairwise disjoint, nonempty,
  clopen parts covering `S`.  `stoneanClosedRestriction C Z` is the colimit over
  clopen neighbourhoods of `Z`, implemented by the existing
  `WContractification.Restriction`.  `stoneanPartitionStage` is the product over
  the parts of `Q` of the corresponding restrictions at `f '' A`.
- `stoneanCoverRing C S f` is the prescribed ring `D`, implemented by the canonical
  `WContractification.PullbackProfinite C S f`.  Its `CommRing` and `Algebra C`
  instances are inherited from the existing graph-restriction construction, so the
  definition has real data and contains no choice or `sorry`.
- `stoneanCoverPointMap` sends a prime of `D` to the pair `(x,s)` obtained from
  `PullbackProfinite.fiberHomeo`, exchanging the factors and reversing its graph
  equality.  Thus its codomain is exactly
  `{z : Spec C × S // pi_0(z.1) = f z.2}`.

Clause (1) is the first three conjuncts:
`Algebra.IndZariski C D`, `RingHom.FaithfullyFlat (algebraMap C D)`, and
`Algebra.IndEtale C D`.  The last is the explicit “in particular” conclusion.
Clause (2) is `Function.Bijective (stoneanCoverPointMap C S f)` together with the
local-ring assertion, rendered for every prime `q` by bijectivity of the canonical
`Localization.localRingHom C_q -> D_q`.  The first coordinate of the point map is
`Spec C -> Spec D`'s contraction, and its second coordinate is the existing
`PullbackProfinite.projT` map to `S`.
Clause (3) is the `IsWLocalRing D` conjunct, the exact closed-point equality
`closedPoints (Spec D) = comap(algebraMap C D) ⁻¹' closedPoints (Spec C)`, and the
`IsHomeomorph` sending a closed point to its `S` coordinate.  Clause (4) is
`IsWContractibleRing D`, which is precisely w-locality, strictly henselian local
rings, and extremal disconnectedness of the component space.

Dependency declarations read and used:

- `WeilConjectures.RingTheory.ProEtale.WContractible`:
  `IsWStrictlyLocalRing`, `IsWContractibleRing`,
  `WContractification.PullbackProfinite`,
  `WContractification.PullbackProfinite.fiberHomeo`,
  `WContractification.PullbackProfinite.projT`,
  `WContractification.PullbackProfinite.indZariski`, and
  `WContractification.PullbackProfinite.faithfullyFlat`.  The full source was read;
  `PullbackProfinite` is the explicit restriction of locally constant functions to
  the closed graph and `fiberHomeo` identifies its spectrum with the pullback.
- `Sheaf.Topology.WLocalComponents` (`det-pe-wlocal-components`):
  `WLocalSpace.spectralSpace_closedPoints_components`, which supplies the profinite
  component space and the closed-point/component correspondence used by the source.
- `Sheaf.Topology.StoneanCover` (`det-pe-stonean-cover`):
  `Algebra.stonean_cover`, whose compact Hausdorff extremally disconnected
  ultrafilter cover supplies the Stonean map in the existence argument.  The present
  statement takes the stated arbitrary surjective `f` as input.
- `Mathlib.AlgebraicGeometry.Scheme` (`def-weil-affine-spectrum`):
  `AlgebraicGeometry.Spec` and `Spec.map`, with `PrimeSpectrum` as the underlying
  affine spectrum.
- `Mathlib.GroupTheory.MonoidLocalization.Away` (`def-weil-ring-localization-away`):
  `Localization.Away` and `IsLocalization.Away`, used by the existing restriction
  construction.
- `Mathlib.CategoryTheory.Limits.HasLimits` (`def-weil-pbc-category-colimit`):
  `CategoryTheory.Limits.colimit`, `Cocone`, `IsColimit`, and `colimit.desc`, used
  in the existing restriction and locally constant colimit.
- `Sheaf.RingTheory.IndPrincipalZariski` (`def-weil-pbc-ind-etale-algebra`):
  `Algebra.IndEtale`, `Algebra.IndZariski`, and the corresponding ring-map
  predicates.  The source framework's `IndZariski` instance supplies the finite
  localization presentation.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`
  (`def-weil-pbc-faithfully-flat-ring-map`): `RingHom.FaithfullyFlat`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`
  (`def-weil-pbc-localization-at-prime`): `Localization.AtPrime`,
  `Localization.localRingHom`, and the prime-spectrum localization interface.

Edge cases checked before writing: `C` may be the zero ring (then the component
space and the Stonean cover can be empty); `S` may be empty, and surjectivity then
forces the component space to be empty; a one-part partition gives the original
component restriction; arbitrary finite partitions, including the empty partition in
the empty-space case, are admitted; `f` need not be injective; disconnected `Spec C`
and disconnected `S` are retained; the local-ring clause is quantified over every
prime, not only closed points; no characteristic, noetherian, or nonemptiness
hypothesis is silently introduced.

Searches made on 2026-10-17:

- `msearch.py ... leanfinder "explicit ind-Zariski faithfully flat cover from a
  Stonean cover of connected components"`: eight generic hits, including
  `Module.FaithfullyFlat.of_specComap_surjective` and Stonean category results; no
  complete statement.
- `msearch.py ... loogle "Stonean, PullbackProfinite, IsWContractibleRing"`:
  zero hits (`PullbackProfinite` is project-specific).
- `msearch.py ... grep "Stonean|PullbackProfinite|IsWContractibleRing" RingTheory`:
  zero Mathlib hits.
- `rg` over the specified upstream and `lean/Sheaf` trees for
  `stoneanCoverRing|stoneanCoverPointMap|stonean_cover_second_stage|PullbackProfinite`:
  only the existing upstream `PullbackProfinite` infrastructure, with no duplicate
  of the declarations in this module.  The node id search also found no prior module.
- The recorded dependency declarations and their full docstrings were opened in the
  upstream framework or Mathlib before writing.

Validation: `scompile.py Q78 det-pe-wc-cover-second-stage
lean/Sheaf/RingTheory/StoneanCoverSecondStage.lean` compiled the sandbox and library
copies cleanly.  The only postponed proof is the expected theorem `sorry`.

## Earlier second reading (a previous round; superseded)

I reread the target node, its blueprint source, every statement dependency, and the
complete Lean module independently.  The binders match the node exactly: the only
ring hypothesis is w-strict locality; `S` is compact Hausdorff totally disconnected
and extremally disconnected; `f` is continuous and surjective.  The finite-partition
record enforces nonempty clopen disjoint parts covering `S`, the closed restriction is
the canonical neighbourhood colimit, and the cover ring is the existing graph
restriction rather than an arbitrary chosen algebra.

The four conclusions were checked in order.  The first conjuncts state ind-Zariski,
faithful flatness of the algebra map, and ind-etaleness.  The point map has exactly
`Spec C ×_P S` as its subtype codomain and is bijective.  The localization map at
every prime is bijective, which is the local-ring identification `D_(x,s) ≅ C_x`.
The closed-point equality and homeomorphism to `S` state precisely the two parts of
clause (3), while `IsWContractibleRing D` states clause (4) without dropping strict
henselianity or extremal disconnectedness.  No extra conclusion or hypothesis is
present.  The zero-ring, empty-space, empty-partition, noninjective-map, and
arbitrary-characteristic cases remain covered by the binders.

The source construction in `WContractification.WContractible` was checked at
`Restriction`, `PullbackProfinite`, `fiberHomeo`, `isPullback`, and
`exists_isWContractibleRing_of_isWStrictlyLocal`; these are canonical constructions
with real data.  No private duplicate of a Mathlib or upstream notion was introduced,
and all variables and universes are explicit.  No statement dispute or correction is
needed.


## Second reading by Q78

Read independently against the node's complete statement and twelve proof steps,
the blueprint source `sk-thm-pe-wc-cover/det-pe-wc-cover-second-stage.md`, and
`literature/stacks-project/proetale.tex`, lemmas `lemma-construct` (097C) and
`lemma-construct-profinite` (097D), including their surrounding assumptions.
097D assumes a commutative ring and a profinite source, with no Noetherian,
characteristic, nonzero-ring, or finiteness assumption. This node additionally
assumes w-strict locality, extremal disconnectedness, and surjectivity.

Object/hypothesis/conclusion checklist and verdicts:

1. **C and its hypotheses.** `C : Type u`, `[CommRing C]`,
   `[IsWStrictlyLocalRing C]`. Read the recorded declarations of
   `det-pe-wlocal-strict-contractible` in upstream `WLocal.lean` and
   `WContractible.lean`: the superclass is w-locality and the added condition is
   strict henselianity of `Localization.AtPrime m` for every maximal ideal.
   Verdict: exact; no field, reducedness, Noetherian, or extra locality instance.
2. **X, P, and pi.** `PrimeSpectrum C`,
   `ConnectedComponents (PrimeSpectrum C)`, and `ConnectedComponents.mk`.
   The affine-spectrum dependency records the underlying space `PrimeSpectrum`.
   Read `AlgebraicGeometry.Spec` and `Spec.map`; the induced point map is prime
   contraction. Read `WLocalSpace.spectralSpace_closedPoints_components` in
   `Sheaf.Topology.WLocalComponents`: it identifies closed points with components
   under w-locality and gives the profinite topology. Verdict: exact spaces and
   quotient map, not an arbitrary profinite substitute.
3. **S.** `S : Type u`, `[TopologicalSpace S]`, `[CompactSpace S]`, `[T2Space S]`,
   `[TotallyDisconnectedSpace S]`, `[ExtremallyDisconnected S]`.
   Verdict: exactly an extremally disconnected profinite space. No nonempty or
   countability condition. The arbitrary fixed universe `u` is shared by the ring,
   space, and discrete-quotient index, as in the upstream construction; no extra
   universe equality is assumed in a hypothesis.
4. **f.** `f : C(S, ConnectedComponents (PrimeSpectrum C))` and
   `hf : Function.Surjective f`. `C( , )` is continuous maps. Read the recorded
   `stonean_cover` theorem (in the root namespace, despite the original report's
   mistaken `Algebra.stonean_cover` name): it constructs an ultrafilter Stonean
   cover. This item accepts every such surjective continuous map, rather than
   specializing to that cover. Verdict: exact.
5. **C_Z and its transitions.** Reuse `WContractification.Restriction Z` and
   `Restriction.diag Z`, whose objects are `Localization.Away` at the unique
   clopen idempotents and whose arrows are the universal localization maps.
   Clopens upstairs are exactly preimages of component clopens: they are saturated
   under connected components, and the component topology is the quotient topology.
   Thus the upstream neighbourhood indexing category is exactly the node's.
   New helper `stoneanRestrictionMap h` is `colimit.pre` for inclusion of these
   indexing categories when `Z ⊆ Z'`. Verdict: correct canonical map
   `C_Z' → C_Z`; no arbitrary choice of a homomorphism.
6. **Finite partitions and D_Q.** Use Mathlib `DiscreteQuotient S` instead of a
   second partition structure. `Q.proj` is surjective and continuous; its fibres
   are nonempty clopen sets, and compactness makes `Q` finite. Conversely every
   finite clopen partition gives such a quotient. `stoneanPartitionStage` is the
   `CommAlgCat C` object with carrier
   `∀ a : Q, Restriction (f '' (Q.proj ⁻¹' {a}))`.
   Images are closed by compactness and Hausdorffness. Verdict: precisely the
   prescribed product, including its diagonal C-algebra structure.
7. **Refinements and D.** `stoneanPartitionMap f h` evaluates at the containing
   coarse part and applies the restriction map to the finer part;
   `stoneanPartitionDiagram` indexes these maps by `(DiscreteQuotient S)ᵒᵖ`.
   The infimum gives common refinements and the top quotient gives a starting
   object. The first conjunct of the theorem now states an equivalence between
   `colimit (stoneanPartitionDiagram C S f)` and the existing
   `WContractification.PullbackProfinite C S f`. Its displayed equation on every
   `Q → C` identifies the images of all finite-stage functions with their pullbacks
   to S followed by graph restriction. Since the individual restrictions are
   surjective C-algebras, this characterizes the comparison on every stage, hence
   on the colimit. Verdict: the specific construction of D is retained formally;
   no unproved claim of definitional equality or uncharacterized algebra is used.
8. **Clause 1.** `Algebra.IsIndPrincipalZariski C D`,
   `RingHom.FaithfullyFlat (algebraMap C D)`, and `Algebra.IndEtale C D`, with
   `D = WContractification.PullbackProfinite C S f` through the preceding
   characterized comparison. Read `Sheaf.RingTheory.IndPrincipalZariski`:
   its predicate means a filtered colimit of finite products of principal
   localizations, including the empty product. Read `RingHom.FaithfullyFlat` and
   the ind-etale declaration. Verdict: exact after replacing the original wider
   upstream `Algebra.IndZariski` predicate, which the dependency explicitly warns
   does not express this definition verbatim.
9. **Clause 2, points.** `Function.Bijective (stoneanCoverPointMap C S f)`.
   Its codomain is precisely `{z : PrimeSpectrum C × S // mk z.1 = f z.2}`.
   It swaps the factors of existing `PullbackProfinite.fiberHomeo`; read that
   declaration and `fst_fiberHomeo`, `snd_fiberHomeo`, `projT`, and `projSpec`.
   Its first coordinate is contraction along `algebraMap C D`; its second is
   the canonical projection to S. Verdict: the prescribed maps, not an unrelated
   bijection or only the closed points.
10. **Clause 2, local rings.** For every `q : PrimeSpectrum D`, bijectivity of
    `Localization.localRingHom (q.asIdeal.comap (algebraMap C D)) q.asIdeal
    (algebraMap C D) rfl`. Read its signature and fraction formula in Mathlib.
    Verdict: exactly the canonical isomorphism `C_x → D_q` at all primes, in the
    correct direction, not an abstract isomorphism of unrelated rings.
11. **Clause 3.** `IsWLocalRing D`; equality of `closedPoints (PrimeSpectrum D)`
    with the inverse image of `closedPoints (PrimeSpectrum C)` under contraction;
    `IsHomeomorph` of the S-coordinate on that closed-point subtype.
    Verdict: every clause is present, including both directions of the closed-point
    characterization and the subspace topology on closed points.
12. **Clause 4.** `IsWContractibleRing D`. Read its actual fields: w-strict
    locality plus extremal disconnectedness of the component quotient.
    Verdict: exactly w-contractibility; strict henselianity is retained.

Mismatches repaired:

- Replaced `Algebra.IndZariski` with the dependency's recorded
  `Algebra.IsIndPrincipalZariski` and imported its owning module.
- Removed duplicate `StoneanClopenPartition`, `stoneanClosedRestriction`, and
  `stoneanCoverRing` with their redundant instances. Reused `DiscreteQuotient`,
  `WContractification.Restriction`, and `PullbackProfinite` directly.
- The old partition stages were unused by the theorem and had no transition
  diagram. Supplied the actual restriction maps, refinement diagram, and the
  characterized comparison of its colimit with the graph ring. The original
  assertion that these are definitionally equal was false.
- Expanded the theorem docstring from a short sketch to all twelve node proof
  steps, their named dependencies, and the colimit comparison argument. Added
  the missing stated proof-dependency imports and standardized source/blueprint
  docstrings. The underlying mathematical node statement is unchanged; this is
  a repair of its Lean rendering, so no `statement_change` is called for.
- Read the two citers `sk-thm-pe-wc-cover` and `det-pe-wcb-cover`; both use the
  resulting faithfully flat ind-etale w-contractible cover and remain valid.

Edge cases: C may be the zero ring; then its component quotient is empty and the
existence of f forces S empty. Empty S is allowed and surjectivity forces P empty.
Its unique discrete quotient has no elements; each stage product is the zero ring.
The partition indexing category itself remains nonempty, so the colimit is defined.
All prime/local-ring clauses are vacuous in that case, as required. For nonempty
S the coarsest quotient gives the one-part partition; empty parts are never added.
No finiteness of S, injectivity of f, characteristic restriction, reducedness, or
nontriviality instance is assumed. All binders and the universe are explicit.

Independent searches (2026-10-17):

- LeanFinder via `msearch.py`: "local rings unchanged after changing the profinite
  connected component space of a ring spectrum"; eight generic spectrum and local
  ring hits, none this complete statement.
- Loogle via `msearch.py`: `DiscreteQuotient`; twelve hits, including the existing
  partition notion and `DiscreteQuotient.finsetClopens`. Read the actual structure,
  projection, refinement maps, fibre inclusions, and finite instance in Mathlib.
- Grep via `msearch.py`: `colimit.*partition|partition.*colimit|Restriction.*map|
  discreteQuotient` in RingTheory; seven irrelevant restriction hits.
- Independent `rg` on the specified Mathlib, upstream WeilConjectures, and
  repository `lean/Sheaf` trees for partitions, `PullbackProfinite`, and
  `IsIndPrincipalZariski`. Opened the upstream graph restriction and locally
  constant colimit constructions and the existing
  `exists_profinite_component_ring_pullback`. The latter is existential over D
  and has neither the specified partition-colimit interface nor the
  w-contractibility conclusion, so is not an exact existing match for this node.
  No existing restriction-inclusion/refinement diagram declaration was found.

No new DAG node or dependency module is introduced: the added helper definitions
are the canonical maps and diagram explicitly introduced in this node itself.
Every definition has real data; the sole postponed theorem is
`Algebra.stonean_cover_second_stage`, with the matching node and complete proof
in its docstring. No theorem was proved. The node's `lean.statement` is copied
verbatim from the current multiline theorem signature, and `lean.declarations`
lists every helper of the delivery.

Validation of the final file: prescribed `scompile.py Q78 det-pe-wc-cover-second-stage lean/Sheaf/RingTheory/StoneanCoverSecondStage.lean` passed for both sandbox and library copies (2.5 s and 2.6 s), without any warnings or errors. Independent text checks confirmed the verbatim signature, unchanged node statement, one theorem sorry, and all lines at most 100 characters.
