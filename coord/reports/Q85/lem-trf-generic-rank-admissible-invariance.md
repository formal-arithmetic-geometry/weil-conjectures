## Worker report

The delivery states `AlgebraicGeometry.Scheme.Modules.generic_rank_admissible_invariance`
in `Sheaf.TraceFormula.GenericRankAdmissibleInvariance`. Its proof is `sorry`.
Two item-local helpers spell out constructions explicitly present in the node:
`moduleResidueRank` is the residue-field tensor dimension, with real tensor-product data,
and `AdmissibleModuleTransformChain` is the finite sequence of actual admissible centres,
recursive fibre products and strict-transform quotients. There are no new independent notions,
new DAG nodes, dependency repairs or statement corrections.

Source checked: `literature/stacks-project/flat.tex`, Tag 0811,
`lemma-flatten-module-pre`, hypotheses (1)--(4) and the first two proof paragraphs;
Tag 080Y, `remark-successive-blowups`. The current blueprint ancestor
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`
was read; this item is a subordinate flattening input, not that unit's statement.
No repair note exists for this item.

Hypothesis-by-hypothesis correspondence:

- Schemes and morphism: `{X S : Scheme.{u}}` and `f : X ⟶ S`. The universe is explicit;
  `set_option autoImplicit false` rejects any unbound variable.
- Quasi-compact and quasi-separated S: `[CompactSpace S] [QuasiSeparatedSpace S]`.
- Affine, flat, finitely presented family: `[IsAffineHom f] [Flat f]
  [LocallyOfFinitePresentation f]`. An affine morphism is quasi-compact and separated,
  hence quasi-separated, so this is exactly finite presentation in the convention node.
- Geometrically integral fibres, after every field extension: `[GeometricallyIntegral f]`.
  Mathlib's `GeometricallyIntegral.iff_geometricallyIntegral_fiber` identifies this with
  geometric integrality of every fibre. The definition quantifies over all field-valued
  points and pullbacks, so no geometric-reducedness-only substitute is used.
- Finite-type quasi-coherent module: `F : X.Modules`, `[F.IsQuasicoherent] [F.IsFiniteType]`.
- Quasi-compact open: `U : S.Opens`, `hU : IsCompact (U : Set S)`.
- Finite presentation over the inverse image of U: `hfp` is finite presentation of
  `(restrictFunctor (f ⁻¹ᵁ U).ι).obj F`.
- The phrase "write ξ_u for the unique generic point": `ξ : (s : U) → f.fiber s.val`,
  `hξ : ∀ s, IsGenericPoint (ξ s) Set.univ`. Integral fibres have exactly one such point,
  so this is an arbitrary naming of the unique points, not a condition beyond the node.
  It does not require a point of U and is valid for U empty.
- Flatness over S at those generic points: `hflat : ∀ s : U,
  moduleFlatAt f F (f.fiberι s.val (ξ s))`. The existing pointwise predicate restricts
  scalars along the actual stalk map and asserts flatness over the base stalk.

Conclusion-by-conclusion correspondence:

- The stated formula for r is `∃ r : U → ℕ, ∀ s, r s = moduleResidueRank F
  (f.fiberι s.val (ξ s))`. `moduleResidueRank` uses the actual module stalk functor,
  the canonical residue map and `Module.finrank` of `κ(x) ⊗[𝒪_x] F_x`.
  This is the tensor in the node with its factors interchanged by tensor symmetry.
  Finite type makes this vector space finite dimensional. No freeness assumption
  is needed to define it.
- Freeness of the same rank on an open neighbourhood in X_U: the first free-neighbourhood
  clause gives `W ≤ f ⁻¹ᵁ U`, membership of the fibre generic point in W, and an isomorphism
  from F restricted to W to the restriction of the free sheaf with `ULift (Fin (r s))`
  as basis index. `Nonempty` packages an actual sheaf isomorphism, not a statement only
  about the stalk dimension. Opens W contained in X_U are exactly its open subschemes.
- Local constancy: `IsLocallyConstant r` on the subtype U.
- Finite partition into nonempty quasi-compact clopen levels: `Set.Finite (Set.range r)`
  and `∀ i ∈ Set.range r, IsClopen {s : U | r s = i} ∧ IsCompact {s : U | r s = i}`.
  The index set is exactly the attained ranks `Set.range r`. These level sets are
  nonempty by that definition, pairwise disjoint, and cover U by the definition of
  a function. No extra empty levels are asserted to be part of the partition. An open
  subset compact in U is also compact in S under the continuous open inclusion.
- Every finite sequence: the final universal quantifier ranges over `n`, final schemes
  Y and T, family q, module G and maps b and p to the original base and total space,
  with `AdmissibleModuleTransformChain f U F n q G b p`. The `nil` constructor is exactly
  the original family; `snoc` uses `B : IsAdmissible T (b ⁻¹ᵁ U)`, its actual `B.I.blowup`,
  the family `pullback.snd q B.I.blowupMap` and the quotient
  `cokernel (kernel.ι (moduleStrictTransformRestriction q B.I G))`.
  This is definitionally the existing `moduleStrictTransform q B.I G` whenever its
  finite-type and quasi-coherence witnesses are available. Writing its underlying
  expression avoids assuming the very intermediate quasi-coherence being concluded.
  No intermediate hypotheses are hidden in the relation. Inductive finiteness includes
  all lengths and, by applying the theorem to prefixes, all intermediate stages.
- Transformed qcqs base: `CompactSpace T ∧ QuasiSeparatedSpace T`.
- The base-changed family properties: `IsAffineHom q ∧ Flat q ∧
  LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q ∧
  GeometricallyIntegral q`. Finite presentation uses all three of its factors explicitly.
  The chain records recursive pullbacks, canonically representing X ×[S] T.
- The successive strict transform is quasi-coherent finite type:
  `G.IsQuasicoherent ∧ G.IsFiniteType`.
- Identification over the original open: `IsIso (b ∣_ U)` and an isomorphism between
  G restricted to `q ⁻¹ᵁ (b ⁻¹ᵁ U)` and the restriction of `(tensorPullback p).obj F`.
  The latter is precisely the transport of F|X_U along the induced isomorphism over U;
  p is the composite of the actual pullback projections, never a freely chosen map.
- Finite presentation there: finite presentation of that restricted G.
- Same generic ranks: for every `t : T`, `ht : b t ∈ U` and generic point
  `η : q.fiber t`, `moduleResidueRank G (q.fiberι t η) = r ⟨b t, ht⟩`.
- Freeness at those generic points: the final neighbourhood clause gives an open W
  inside the inverse image of U containing `q.fiberι t η`, with the same free sheaf
  isomorphism of rank `r ⟨b t, ht⟩`. This includes rank zero.
- Centres are retained: each `snoc` stores the admissible datum B and uses its I in
  both blowup projections and the strict-transform restriction map. Neither blowups
  nor strict transforms are replaced by unrelated morphisms or modules. Arbitrary
  isomorphic presentations of a blowup are represented by this canonical-centre model,
  as in the dependency's existing interface.

Dependency declarations used (their source signatures and docstrings were read):

- `WeilConjectures.Blowup.AdmissibleBlowup`: `AlgebraicGeometry.IsAdmissible`
  and `IsAdmissible.isIso_blowupMap_restrict` (retained finite-type centre and preserved open).
- `Sheaf.AlgebraicGeometry.ModuleStrictTransform`: `moduleStrictTransformRestriction`,
  `moduleStrictTransformKernel`, `moduleStrictTransform` in `AlgebraicGeometry.Scheme.Modules`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-weil-pbc-scheme-conventions` has a convention-only record, with no module or
  declaration: its finite-presentation convention is respected as explained above.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: exposes the exact Mathlib
  `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType`; the node does not
  require coherence. Its conjunction is not redefined.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` and `.Quasicoherent`:
  `SheafOfModules.IsFiniteType` and `SheafOfModules.IsFinitePresentation`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `Scheme.Modules.IsFlatOver`; its stalkwise specialization is the existing
  `AlgebraicGeometry.moduleFlatAt` from `Sheaf.TraceFormula.FlatAssociatedEquidimensional`,
  also the exact interface used by the proof dependency `exists_free_neighbourhood`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField` and `isPullback_fiberToSpecResidueField_of_isPullback`.
- `Mathlib.Topology.Sober`: `IsGenericPoint`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.residue`,
  `Scheme.Hom.residueFieldMap`.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor` (publicly reached through the
  pointwise-flatness interface): `RingedSpace.moduleStalkFunctor`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral`.
- Proof-only imports include the recorded Mathlib modules for scheme sobriety,
  function fields, vector-space flatness, qcqs/finite-presentation permanence,
  openness, affine permanence and flat base change, and the two recorded project
  modules `Sheaf.TraceFormula.FlatFibreFreeNeighbourhood` and
  `Sheaf.AlgebraicGeometry.ModuleAdmissibleBlowupCalculus`. The theorem docstring
  reproduces every proof step and its dependencies.

Edge cases checked before writing and on rereading:

- U empty: ξ and r have empty domain, the range of r is empty, and there is no
  nonempty-stratum or generic-freeness obligation; the invariant still asserts global
  family permanence and quasi-coherent finite-type transforms.
- S empty: no nonemptiness restriction on schemes, U or the family was imposed.
- F zero and generic rank zero: `Fin 0` gives the zero free sheaf and neighbourhood
  vanishing is correctly stronger than merely a zero-dimensional residue stalk.
- Disconnected U and several ranks: r is a function, not a single global rank;
  only its nonempty level sets form the finite partition.
- Zero-dimensional fibres, arbitrary characteristic, nonreduced qcqs bases: none is
  excluded. Geometric integrality concerns the fibres, not the base or total space.
- Sequence of length zero: `nil` uses f, F and the two identities. The invariance
  statement specializes to the hypotheses and the initial rank-neighbourhood conclusion.
- Unit-ideal blowup and centres disjoint from U: the actual centre is retained even
  when the blowup morphism is an isomorphism. No centre is reconstructed from a morphism.
- The sequence relation has no flatness, freeness, quasi-coherence or finite-type
  assumptions on G or on any intermediate transform. These are theorem conclusions.

Searches for an exact existing statement or helper:

- `msearch.py ... leanfinder "Generic fibre rank locally constant on base and unchanged
  by successive admissible blowups"`: eight hits, led by
  `Module.isLocallyConstant_rankAtStalk_freeLocus`, `Module.isLocallyConstant_rankAtStalk`,
  `Module.rankAtStalk` and ring-module base-change rank lemmas. None states generic
  fibre ranks on the base of a family or their strict-transform invariance.
- `msearch.py ... loogle "Module.rankAtStalk, IsLocallyConstant"`: exactly two hits,
  `Module.isLocallyConstant_rankAtStalk` and `Module.isLocallyConstant_rankAtStalk_freeLocus`.
  Both concern a fixed ring-module rank on its own prime spectrum, not this statement.
- `msearch.py ... leansearch "Generic fibre ranks of a finitely presented flat module
  are locally constant and invariant under admissible blowups"`: eight hits including
  the preceding rank lemmas and `Module.free_of_flat_of_finrank_eq`,
  `Module.nonempty_basis_of_flat_of_finrank_eq`, and `Module.finrank_baseChange`;
  no exact match.
- `msearch.py ... grep "generic.*rank|rank.*generic|Admissible.*Sequence"
  AlgebraicGeometry`: zero hits in Mathlib's AlgebraicGeometry subtree.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for generic rank, admissible sequence
  and successive-transform names found generic freeness over rings, the two-step
  `successiveModuleStrictTransform`, and `AffineGenericRankBlowup`. They are different
  statements (ring generic freeness, two-centre comparison, or existence of a modification).
  The exact item id has no upstream declaration. `moduleResidueRank`,
  `AdmissibleModuleTransformChain` and `fibreGenericRank` had no hits in Mathlib or
  either project source tree. The upstream declaration-name index was also searched.

Validation: `scompile.py Q85 lem-trf-generic-rank-admissible-invariance <module>` passed
both the sandbox and library checks on the first version (16.6 s and 10.1 s) and on
the final module with explicit dependency imports (7.9 s and 7.8 s). The required
`deliver2.py ... --no-push` returned `OK (dry run)` at commit `256c052fe3a`, passing
preflight and compilation. The report was then updated with these results; no Lean or
node change followed that successful check. No STATEMENT-DISPUTED flag or source fault found.

## Second reading by Q85

The dispatcher explicitly prohibits starting another agent and supplies the maintainer's
independent review after delivery. This section records a separate self-rereading, not
an invented independent worker review.

I reopened the node and compared its full statement with the final signature. The
initial affine hypothesis supplies quasi-compactness and quasi-separatedness of f,
so using only local finite presentation adds no missing hypothesis. The relative
flatness is at the original total-space point under `fiberι`, not at the fibre local
ring. The rank uses κ of that total-space point, matching the printed formula. The
neighbourhood is required to be contained in X_U. The partition is indexed by attained
ranks rather than all natural numbers; this handles empty U and omits empty levels.
Every successor uses its centre and the exact existing strict-transform cokernel. In
particular I checked that its constructor does not ask for intermediate quasi-coherence,
which would hide part of the conclusion. The maps b and p are forced by the chain,
so the module identification over U is with the pullback of the original module,
not an arbitrary comparison object. The final generic-point clause gives both the
residue dimension equality and a sheaf-level free neighbourhood of that rank.
No hypothesis or clause mismatch was found. The only change during rereading was to
make every recorded statement-dependency module and Mathlib proof-dependency module
an explicit import. All theorem proofs remain `sorry`; definitions contain no `sorry`.
