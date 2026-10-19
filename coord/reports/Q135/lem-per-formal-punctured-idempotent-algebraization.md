## Worker report

This delivery states `AlgebraicGeometry.Scheme.formal_punctured_sections_comparison`
in `Sheaf.AlgebraicGeometry.FormalPuncturedSections`, with one `sorry` and real definitions
of its indexing diagrams. The node's statement is unchanged. Its statement dependencies
gain the already landed `def-per-local-cohomological-dimension`, whose exact definition
was absent from the item's original dependency list. There are no new nodes or dependency
repairs. The previous worker's stale-dispatch conclusion concerned the reviewed stage-1
split: the current node has neither `lean` nor `reviewed_lean`, so it still needs stage 2.

Source read: `literature/stacks-project/algebraization.tex`,
`lemma-application-theorem` (Tag 0DXR) and the first half of
`lemma-punctured-still-connected` (Tag 0ECR). The former compares neighborhood sections
and formal sections; the latter supplies the complete-local reduced-ring application.
The delivered statement asserts the ring comparison of the DAG node, not the connectedness
conclusion of 0ECR, and does not add the finiteness conclusion of 0DXR.

Hypotheses, in node order:

- A nonzero commutative Noetherian local ring: `(A : Type u) [CommRing A]
  [IsNoetherianRing A] [IsLocalRing A]`. Mathlib's local-ring class includes nontriviality.
- Completeness for the maximal-ideal topology:
  `[IsAdicComplete (IsLocalRing.maximalIdeal A) A]`, using the recorded completion API.
- Finite dimension: `hfinite : topologicalKrullDim (Spec (.of A)) < ⊤`.
- A proper ideal: `(I : Ideal A) (hI : I ≠ ⊤)`. No generator or principal-ideal assumption
  is imposed; Noetherianity supplies finite generation.
- `X = Spec A` is `Spec (.of A)`. The open `U` is bound explicitly, with
  `hU : ∀ x, x ∈ U ↔ x ≠ IsLocalRing.closedPoint A`. This specifies exactly the puncture.
- `Y = V(I)` is `PrimeSpectrum.zeroLocus (I : Set A)` in `Neighborhoods`.
- The local cohomological dimension is the landed `ModuleCat.localCohomologicalDimension I`.
  Its source is Stacks 0DX8/0DX7: the supremum of nonvanishing degrees of the right derived
  ideal-power torsion functor on all modules, with bottom representing -1. It therefore
  implements exactly the node's all-modules vanishing definition, not étale cohomological
  dimension or the cohomology of `A` alone.
- The minimum component dimension is bound as `d : WithBot ℕ∞`, with `hd : IsLeast
  {e | ∃ Z ∈ irreducibleComponents (Spec (.of A)), topologicalKrullDim Z = e} d`.
  Membership says that the minimum is attained; its lower-bound condition covers every
  component, including components of differing dimensions.
- The numerical hypothesis is `hbound : ModuleCat.localCohomologicalDimension I + 1 < d`.
  The proper ideal in a nonzero ring has nonzero degree-zero torsion on `A/I`, so its
  cohomological dimension is nonnegative: there is no use of bottom arithmetic as -1 + 1.

Objects, maps, and every conclusion clause:

- `FormalPuncturedSections.Reduction A` is literally `A ⧸ (⊥ : Ideal A).radical`, the
  node's `B`. It imposes no reducedness assumption on `A`.
- `reductionMap A` is `Spec.map` of the actual quotient map `A → B`, giving `π`.
  `reducedIdeal I` is `I.map` of that quotient map, giving `IB`.
- `Neighborhoods I U` consists of exactly the opens `V` satisfying `V ≤ U` and
  `U ∩ V(I) ⊆ V`. It uses inclusion order; `neighborhoodSections` takes its opposite.
  Consequently its arrows go from larger neighborhoods to smaller ones and its maps are
  the structure-presheaf restrictions on `π⁻¹(V)`, exactly `Γ(V_red,O)`.
- The source ring is the categorical `colimit (neighborhoodSections I U)` in
  `CommRingCat.{u}`, with its canonical maps `colimit.ι`.
- `quotientMap J n` is the quotient-spectrum morphism for `B/J^(n+1)`. Positive powers
  are indexed by `n : ℕ` as `n+1`, so no positive level is omitted and no exponent-zero
  thickening is substituted for the first level.
- `thickeningOpen J W n` is the inverse image of `W` in that quotient spectrum. With
  `J = reducedIdeal I` and `W = reductionMap A ⁻¹ᵁ U`, its open subscheme is precisely
  `T_(n+1)` of the node.
- `thickeningTransition` restricts the spectrum map induced by `Ideal.Quotient.factor`
  for `J^(n+2) ≤ J^(n+1)`. Applying global sections contravariantly gives exactly reduction
  from level `n+2` to `n+1`. `formalSectionsDiagram` uses `Functor.ofSequence` and
  `Scheme.Γ`; functoriality for nonconsecutive levels is inherited from Mathlib.
- The target ring is `limit (formalSectionsDiagram (reducedIdeal I)
  (reductionMap A ⁻¹ᵁ U))`, with all canonical projections `limit.π`.
- The conclusion gives an isomorphism `e` in `CommRingCat`, which is a ring isomorphism,
  and specifies its composite with every source injection and every target projection.
  After `topIso.hom` identifies sections on the open subscheme with sections of its
  ambient structure sheaf, the left side restricts from the inverse image of `U` to the
  inverse image of `V`. The right side is exactly
  `(quotientMap (reducedIdeal I) n).app (reductionMap A ⁻¹ᵁ V.val)`.
  These are equal as ring homomorphisms, not merely as maps of sets or modules.

The coordinate equations uniquely characterize the canonical restriction map. To check
this, a point of `Spec(B/(IB)^(n+1))` contracts to a prime of `A` containing `I`.
Indeed every `a ∈ I` maps to an element whose `(n+1)`st power is zero in that quotient,
so it belongs to every prime. Thus, among points lying over `U`, every such point lies
over `V`, because `U ∩ Y ⊆ V`. The inverse images of `V` and `U` on this quotient are
equal. The final restriction on the left is therefore an isomorphism. For each `V,n`
the equation fixes the projected homomorphism, and the limit and colimit universal
properties fix `e.hom` uniquely. Existence of the displayed `e` is consequently exactly
the assertion that the canonical comparison is invertible. This supplies its full
canonical normalization without choosing an arbitrary comparison map or adding a
hypothesis that such a map exists.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (and its ideal finite-generation
  characterization), recording `def-weil-pbc-noetherian-ring`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`, the actual
  spectrum and its contravariant ring-map functor, recording `def-weil-affine-spectrum`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, recording
  `def-kun-topological-krull-dimension`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete`, recording the companion
  completeness notion of `def-weil-pbc-adic-completion`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, the exact `mathlib_match` of
  `def-weil-irreducible-components`; it is not redefined.
- `Sheaf.Algebra.Homology.LocalCohomologicalDimension`:
  `ModuleCat.localCohomologicalDimension`, recording the added landed definition node.
  Its real definition and that of `ModuleCat.idealPowerTorsion` were opened and read.
- Proof-only imports retain the already stated proof dependencies:
  `Sheaf.RingTheory.CompleteLocalSubideal` (`IsAdicComplete.of_le_maximalIdeal`),
  `Sheaf.RingTheory.Depth` (`Ideal.depth`, `IsLocalRing.depth`),
  `Sheaf.RingTheory.SerreCriterionReduced`
  (`Ring.isReduced_iff_serreR_zero_and_serreS_one`), and
  `Mathlib.AlgebraicGeometry.Modules.Tilde` (the recorded quotient-pushforward interface).
  `PrimeSpectrum.zeroLocus_minimalPrimes` is available through Mathlib's spectrum topology.
  The four unstated support/completion/generator proof lemmas have no modules to import;
  they remain the named proof plan in the theorem docstring, with no added assumptions.

All helper definitions are parts of this item's indexing diagrams and quotient maps and
are listed in `lean.declarations`. Each has a source/blueprint docstring and concrete
data. No independent replacement for a recorded notion is introduced. The only proof
inside a helper is the structural open-containment check for the quotient transition;
it is fully discharged, not postponed. Every universe and binder is explicit, and
`autoImplicit` is disabled. No local notation, local instance, private declaration, or
statement `let` is used.

Edge cases checked mathematically:

- `I = 0`: `Y = X`, the only neighborhood is `U`, `IB = 0`, and the quotient tower is
  constant. The comparison is the identity on sections of the reduced puncture.
- Nilpotent `I`: again `Y = X`; the tower is eventually constant, and no regular-element
  or cancellation hypothesis is used.
- A field or zero-dimensional local ring: the puncture is empty and both diagrams
  give the zero ring; the strict dimension bound fails as expected. The zero ring itself
  is excluded precisely by the node's nonzero/local-ring assumption.
- `I = m`: the formal puncture is empty, and the empty open is an allowed neighborhood.
  Both rings are zero; the dimension hypothesis cannot hold, consistently with
  `cd(A,m) = dim A`.
- Nonreduced `A` is retained, with `B` formed by the genuine nilradical quotient. Different
  component dimensions use their actual minimum; no equidimensionality is assumed.
- For `k[[x,y,z]]` and `I=(x)`, the bound `3 > 1+1` is the expected permitted case.
  For `k[[x,y]]` and `I=(x)`, equality at the boundary is excluded by the strict inequality.
- All indices and section rings live in universe `u`, with no independent test universe
  or assumption that would make a quantification vacuous.

Searches made (real wrapper results are retained in sandbox `searches.jsonl`):

- LeanFinder: “The canonical ring map from the colimit of sections on neighborhoods in
  a punctured complete local spectrum to the inverse limit of infinitesimal sections is
  an isomorphism”: eight hits about stalks, structure-sheaf localizations, and global
  sections; no formal comparison theorem.
- Loogle: `localCohomology, IsAdicComplete`: zero hits.
- Mathlib grep: `formalSections|formal_sections|localCohomologicalDimension|localCohomology`:
  five hits in `Mathlib.Algebra.Homology.LocalCohomology`; none is this comparison.
- LeanSearch: “For a complete Noetherian local ring, sections of the reduced structure
  sheaf on neighborhoods in the punctured spectrum algebraize compatible sections on
  all ideal-power thickenings when component dimension exceeds local cohomological
  dimension plus one”: eight hits about the structure sheaf and local fractions; no
  formal comparison theorem.
- Direct `rg` in the prescribed upstream source tree for the item id, `formalSections`,
  and `formal_sections`: no match. Searching `dag/lean_names_upstream.json` and both Lean
  trees for the new namespace and main declaration: no existing declaration.
- Direct `rg` in `lean/Sheaf` for formal sections and local cohomological dimension found
  the landed `LocalCohomologicalDimension` definition, which is reused, and principal
  formal comparison lemmas with depth-three hypotheses, which are different statements.
  The existing adic finite-etale interfaces do not implement this neighborhood colimit.
- DAG search located `def-per-local-cohomological-dimension`, already landed and reviewed.
  `python3 tools/blueprint_refs.py search 'formal sections'` returned zero blueprint nodes;
  the item's own node is the reviewed auxiliary statement. The upstream-name tool has
  no attachment for it. No duplicate node is added.

Validation: the prescribed `scompile.py` compiled both the sandbox and installed module
forms in under five seconds each, clean after removing unused simp arguments and closing
the namespaces. The final proof-dependency import set is compiled again before delivery.
The final dry run and delivery use `deliver2.py`; no direct Git commands, shared-source
edits, or global builds are used. No statement dispute or correction is needed.

## Second reading by Q135

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
