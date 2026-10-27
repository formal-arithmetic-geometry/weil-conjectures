## Worker report

The module `Sheaf.AlgebraicGeometry.IteratedTransformExceptionalSupport` states
`AlgebraicGeometry.Scheme.Modules.moduleIteratedStrictTransform_no_exceptional_sections`.
Its proof is `sorry`. Two helpers give the actual iterated transform on the specified
fibre product and the open complementary to the total exceptional support. They are
compositions of existing constructions, with real data, and are listed in
`lean.declarations`; they introduce no independent notion needing a new node.
The node is unchanged except for its `lean` record.

Hypothesis-by-hypothesis and clause-by-clause rendering:

- The schemes are `{X S : Scheme.{u}}` and the arbitrary scheme morphism is
  `(f : X ⟶ S)`. The universe `u` is explicitly declared and `autoImplicit` is false.
- The first finite-type quasi-coherent ideal is `(I : S.IdealSheafData)` together
  with `[I.toModules.IsFiniteType]`. `IdealSheafData` is the affine-compatible encoding
  of a quasi-coherent ideal. No coherence, Noetherian or finite-presentation hypothesis
  is substituted for finite type.
- The first blowup `S₁` and `b` are exactly `I.blowup` and `I.blowupMap` from the
  recorded gluing construction. The second ideal is `(J : I.blowup.IdealSheafData)`
  with `[J.toModules.IsFiniteType]`, and `S₂`, `c` are `J.blowup`, `J.blowupMap`.
- `Z`, `Z₁` are represented by the underlying closed sets `I.support`, `J.support`.
  The set `E` is `I.blowupMap ⁻¹' (I.support : Set S)`.
- The arbitrary quasi-coherent module is `(F : X.Modules) [F.IsQuasicoherent]`.
  It is not required to have finite type.
- `X₁` is `pullback f I.blowupMap`, with `f₁ = pullback.snd f I.blowupMap`.
  `X₂` is literally `pullback f (J.blowupMap ≫ I.blowupMap)`, and its second projection
  is the node's `f₂`.
- `F₁` is `moduleStrictTransform f I F`. The helper `moduleIteratedStrictTransform`
  applies `moduleStrictTransform` to `F₁` with morphism `f₁` and retained centre `J`.
  The recorded theorem `moduleStrictTransform_properties` supplies its quasi-coherence
  via `.the project server`. This is a proof of a property of a fixed, constructed module; it does
  not choose data from an existence theorem or add an assumption. To obtain `F₂` on
  the literal `X₂`, tensor pullback along the inverse of
  `pullbackLeftPullbackSndIso f I.blowupMap J.blowupMap` transports from the iterated
  fibre product. This canonical isomorphism commutes with both projections.
- `moduleIteratedStrictTransformOpen` is the preimage under `f₂ ≫ c` of
  `J.support.compl ⊓ (I.blowupMap ⁻¹ᵁ I.support.compl)`. By De Morgan and inverse image,
  this is precisely the complement of `f₂⁻¹ c⁻¹ (|Z₁| ∪ |E|)`.
- The first conjunct quantifies over **every** open `W` of the literal `X₂` and every
  `s : Γ(moduleIteratedStrictTransform f I J F, W)`. The restriction-adjunction unit
  restricts sections to `W` intersected with that complementary open. Its component
  vanishing implies `s = 0`. There is no compactness restriction on `W`.
- The second conjunct is equality of subsets of `J.blowup`: the left side is
  `c⁻¹ (|Z₁| ∪ b⁻¹ |Z|)`, using `Set.preimage` and `Set.union`; the right side is
  `(c ≫ b)⁻¹ (|Z| ∪ b '' |Z₁|)`, using the actual set-theoretic image under `b`.
  Lean's composition order `c ≫ b` is the node's `bc`. No scheme-theoretic image or
  schematic union is silently substituted for these subsets.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: exposes the recorded coherence
  predicates; here the relevant components are `SheafOfModules.IsQuasicoherent`
  and `SheafOfModules.IsFiniteType`. Its conjunction
  `Scheme.Modules.IsQuasiCoherentFiniteType` was read but is not imposed on `F`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`,
  `pullback.fst`, `pullback.snd`.
- `Sheaf.AlgebraicGeometry.ModuleStrictTransform`: `moduleStrictTransform` and its
  actual cokernel-of-supported-kernel definition; the open/restriction/kernel helpers
  were read as well.
- `Sheaf.AlgebraicGeometry.ModuleStrictTransformKernel`: `moduleStrictTransform_properties`.
  It is publicly imported because the constructed second transform uses its
  quasi-coherence clause, as well as being an input to the postponed proof.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting`:
  `pullbackLeftPullbackSndIso` and its projection identities.
- `WeilConjectures.AlgebraicGeometry.TensorPullback`: `Scheme.Modules.tensorPullback`;
  the transport is along a specified isomorphism, not an arbitrary equivalence.
- Proof imports: `Sheaf.AlgebraicGeometry.StrictTransformDifferentCenters`
  (`moduleStrictTransform_kernel_eq_of_cartier_factor`),
  `WeilConjectures.Blowup.AdmissibleBlowup`
  (`exists_blowup_mul_isInvertible_iso`),
  `WeilConjectures.Blowup.Principalization` (`isInvertible_comap_blowupMap`),
  `WeilConjectures.Blowup.Complement` (`isIso_blowupMap_restrict_support_compl`).
  Together with the kernel theorem and pullback declarations these include every
  stated proof dependency. The four proof steps in the theorem docstring match
  the four node steps, including the argument for the image-set equality.

Source and edge checks: read `literature/stacks-project/divisors.tex`,
`lemma-strict-transform-different-centers` (080H) and the full proof of
`lemma-strict-transform-composition-blowups` (080I), especially its last paragraph.
The first Cartier ideal is obtained by blowup principalization (02OS), rather than
assumed on `S`. Checked the empty scheme, the zero module, the empty open, arbitrary
non-quasi-compact opens, either centre the unit ideal, either centre the zero ideal
(the relevant blowup is empty), and a nontrivial already Cartier first centre.
In the Cartier case the first exceptional support need not be empty: removing its
supported sections remains essential. Both centres remain arguments throughout.
No node fault, statement correction, extra hypothesis or disputed statement was found.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Iterated strict transforms of a quasi-coherent module
  have no sections supported on the total exceptional locus of two blowups"`: eight
  hits, including `exists_of_res_zero_of_qcqs_of_top`, `exists_of_res_zero_of_qcqs`,
  `exists_of_res_eq_of_qcqs_of_top`, `exists_appTop_map_eq_zero_of_isLimit`, and
  `IdealSheafData.mkOfMemSupportIff_ideal`. These concern structure-sheaf localization
  or limits, not successive module strict transforms or the stated set equality.
- `msearch.py ... loogle '"strictTransform"'`: zero hits.
- `msearch.py ... grep 'strictTransform|strict_transform' AlgebraicGeometry`:
  zero hits in Mathlib's algebraic geometry directory.
- `rg` on `lean/WeilConjectures` for `moduleStrictTransform`,
  `moduleIteratedStrictTransform`, `no_exceptional_sections`, and `grep -rn` for the
  item id: no existing declaration or attachment. The broader blowup and
  compactification search finds scheme strict transforms and blowup geometry,
  not this module support assertion.
- `rg` and file inventory on `lean/Sheaf`: existing module strict-transform definition,
  kernel, different-centres, comparison-epimorphism, and admissible-blowup calculus
  modules; no iterated exceptional-support assertion. `dag/lean_names_upstream.json`
  has no matching new declaration name. Existing kernel and different-centres
  interfaces were reused, not copied.

Validation: the prescribed `scompile.py` compiled both its sandbox module and the
library-named module cleanly (7.7 s and 12.9 s respectively). All variables/universes
are bound explicitly; all module lines have at most 100 characters.

## Second reading by Q51

A separate second pass reopened the node and the finished module. This was performed
in this worker session; no other agent was started. The maintainer's independent
reading remains the external review described in the assignment.

Matched `S`, `I`, `b`, `J`, `c`, `f`, `F` with the binders and retained blowup
constructions. In particular, finite type is imposed on the two ideals and not on
`F`. Confirmed that the first transform's quasi-coherence comes from the already
recorded kernel theorem, with no extra `hF₁` hypothesis. Checked the direction of the
pasting isomorphism: its inverse maps the direct fibre product to the iterated one,
so tensor pullback puts the second transform on the correct `X₂`, with `f₂` the
ordinary second projection. Checked that intersecting the two complement opens
removes exactly `c⁻¹ (|Z₁| ∪ |E|)`, including the first Cartier exceptional support.
Checked that the unit component on every `W` is the desired restriction, so its
zero implication has the same strength as the node's local-section assertion.
Finally matched the independent second conjunct point-for-point with the node's
support equality, including the actual image `b '' |Z₁|` and composition order.
The proof docstring preserves the four source-based proof steps. No mismatch was
found and no correction or additional node was needed.
