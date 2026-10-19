## Worker report

The module `Sheaf.Paper.ProperOpenRefinementAdjointProjection` states
`AlgebraicGeometry.Etale.properOpenRefinement_adjoint_projection`, with one `sorry`.
It also defines `unboundedProperOpenRefinementComparison` by specializing the
**normalized** witness of `unboundedProperOpenInterchange` to the square with
left edge `𝟙 U`, inserting the canonical derived identity direct-image isomorphism.
Its data is real: the existence theorem specifies the representative on every
K-injective complex and resolution, which determines the natural isomorphism.

Clause-by-clause correspondence:

- Finite commutative A: `(A : Type (u + 1)) [CommRing A] [Finite A]`. This is the
  coefficient-size convention of the recorded derived-category dependency; any
  finite ring admits this representation. The zero ring is allowed.
- Noetherian U,V₁,V₂: the three `[IsNoetherian ...]` binders. Mathlib's
  `isNoetherian_iff_of_finite_iSup_eq_top` identifies this with the node's finite
  Noetherian affine-cover condition.
- Proper p and open j₁,j₂: `[IsProper p]`, `[IsOpenImmersion j₁]`,
  `[IsOpenImmersion j₂]`. Commutativity is exactly `h : j₁ ≫ p = j₂`.
- Ordinary constant-module sheaves: `Sheaf U.smallEtaleTopology
  (ModuleCat.{u + 1} A)` and the analogous categories on V₁,V₂. No constructibility,
  invertibility, or dimension hypothesis occurs.
- The specific b_p: `unboundedProperOpenRefinementComparison A p j₁ j₂ h` is the
  second witness in the recorded `unboundedProperOpenInterchange A`, specialized
  to `(j₁,𝟙 U,p,j₂)`. It retains that theorem's sheaf support-identification
  and K-injective representative normalization, rather than choosing any iso.
- Exact extension: `(jᵢ)_!open[...]`, and its ordinary unbounded descent
  `D((jᵢ)_!open[...])`; exact inverse image is `(p)^*[...]` and `D((p)^*[...])`.
- The sheaf map π and its naturality: the first existential output is a natural
  transformation `(j₂)_!open[...] ⋙ (p)^*[...] ⟶ (j₁)_!open[...]`.
- The component projection construction is encoded by its component universal
  characterization, **independent of the derived adjoint**. The first conjunct
  gives its restriction to j₁(U) explicitly: undo `upperStarComp j₁ p j₂ h.symm`,
  undo the j₂ open unit, and apply the j₁ open unit. Under the two open-unit
  identifications this is exactly `𝟙 M`.
- The second conjunct makes restriction zero on every open disjoint from j₁(U).
  In particular take c to be the complementary open in W, composed with W → V₁.
  By `open_section_clopen` this is an open immersion. It is precisely the zero
  component specified in the node. These equations determine the sheaf map:
  `j₁! → j₁*` is monic, and the inverse/direct-image adjunction determines the
  composite into j₁* from its restriction to j₁. Equivalently use the binary
  clopen sheaf decomposition on W; outside W the source vanishes by open base
  change. Thus the existential is a specified projection, not an arbitrary map
  assumption or a choice from uncharacterized existence.
- The second existential output Dπ has exactly the derived source and target.
  The third conjunct is its localization formula on **every** cochain complex J,
  using `mapDerivedCategoryFactors` twice on the source and once on the target,
  and `Q.map ((NatTrans.mapHomologicalComplex π (.up ℤ)).app J)`. This specifies
  the degreewise descent, independently of the comparison. Localization uniquely
  determines that natural transformation.
- The last conjunct is equality of natural transformations, not just objectwise
  isomorphism: pull back b_p by `Functor.whiskerRight`, reassociate, apply
  `mapDerivedUpperStarLowerStarAdjunction ... p`'s counit, and remove the identity
  functor. The result equals Dπ.
- No Cartesian hypothesis appears. The fibre product W is used in the proof and
  in the interpretation of the component equations, rather than made an additional
  object or hypothesis in the theorem's signature.

Dependency declarations inspected and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; the Noetherian scheme
  encoding is `Mathlib.AlgebraicGeometry.Noetherian.IsNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`,
  including its separatedness and base-change instances.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`
  and stability under base change.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, the ordinary ModuleCat-valued
  small-etale derived category. The bounded categories and torsion predicate are
  not used to restrict the statement.
- `Sheaf.Paper.UnboundedProperOpenInterchange`:
  `AlgebraicGeometry.Etale.unboundedProperOpenInterchange`, including its full
  signature, support-identification clause, and K-injective representative clause.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `openImmersionLowerShriek`, `preservesFiniteLimits_openImmersionLowerShriek`,
  `openImmersionLowerShriekUpperStarAdjunction`.
- `Sheaf.AlgebraicGeometry.ExactUnboundedExchange`: `exactDerivedBaseChangeMap`,
  whose canonical adjunction is `mapDerivedUpperStarLowerStarAdjunction` from
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`.
- `Sheaf.AlgebraicGeometry.OpenSectionClopen`: `AlgebraicGeometry.open_section_clopen`.
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`:
  `AlgebraicGeometry.Etale.etaleLowerShriekBaseChangeMap`, and
  `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules`:
  `AlgebraicGeometry.Etale.isIso_etaleLowerShriekBaseChangeMap`.
- `Sheaf.AlgebraicGeometry.EtaleSheafClopenProduct`:
  `AlgebraicGeometry.Etale.sheaf_clopen_product`. Its recorded signature is for
  abelian sheaves. It is a proof dependency for the component calculation; the
  maps here are module maps and the same sheaf gluing is componentwise A-linear.
  No second module-category equivalence is introduced or assumed.

The first four modules and the remaining functors are exposed by the public
imports. Other already-stated proof dependencies (proper-support composition,
exact inverse image, open/proper base change) are reachable through
`UnboundedProperOpenInterchange`. The proof-only node
`lem-asd-derived-counit-k-injective-termwise` has no recorded declaration, so no
import of a nonexistent module was added; its role is explicitly retained in the
proof docstring. No import cycle or additional dependency node is required.

Edge cases checked mathematically: U empty (zero extensions and zero natural
transformations), p identity (projection and comparison identities), V₁ containing
an additional proper component over U (identity on the section, zero on the extra
component), A the zero ring (zero module categories), one-degree complexes, and
arbitrary unbounded complexes. In particular W need not equal U or V₁, so no
Cartesian restriction was introduced. The identity restriction fixes the map even
when j₁(U) is not closed in V₁: it is clopen in W, which is what the source uses.

Searches performed:

- msearch LeanFinder, `proper open refinement derived counit clopen projection`:
  eight hits including `Profinite.Nobeling.ι` and locally constant counits; none is
  the small-etale unbounded comparison/projection identification.
- msearch Loogle, `"Adjunction", "counit"`: twelve generic adjunction declarations,
  including `CategoryTheory.Adjunction.counit`; no exact statement.
- msearch LeanSearch, `The adjoint of the unbounded proper open comparison is the
  clopen section projection on sheaves of modules`: eight hits, including
  `SheafOfModules.PullbackConstruction.adjunction` and scheme-module adjunctions;
  no exact statement.
- msearch grep, `properOpen|clopen.*counit|counit.*clopen` in Mathlib CategoryTheory:
  zero hits.
- rg in project `lean/Sheaf` and upstream `WeilConjectures` for `properOpen`,
  clopen/projection combinations, and refinement projection: found bounded-below
  `properOpenInterchangeCoherence`, `properOpenComparison`, and strict-tower/pro-etale
  `pi`, `alpha`, `cbcClopenProjection`; read their signatures. They use different
  derived categories or only bounded-below inputs, and do not give this equality
  for the normalized unbounded small-etale comparison.
- grep of the item's blueprint id in upstream `WeilConjectures`: zero hits.
- rg of the proposed declaration names in `dag/lean_names_upstream.json`,
  `lean/Sheaf`, and upstream: zero hits before writing.

Source read: `literature/stacks-project/more-etale.tex`,
`lemma-shriek-proper-and-open` (0F7B), especially the exact representative
`g_! f'_* J = f_* g'_! J → f_* I` and case (b). The clopen-section proof
is the explicitly recorded extracted argument of the item's node. No statement
correction, disputed statement, new node, or dependency-record repair.

Validation: prescribed `scompile.py Q35 lem-asd-proper-open-refinement-adjoint-projection`
finished with exit code 0 for both the sandbox and final module name, with no
compiler errors or warnings. Every line of the Lean module is at most 100 characters.

## Second reading by Q35

Author's second reading (no sub-agent was started, as required by the dispatcher).
Opened the node and finished Lean module again. The coefficient, Noetherian,
properness, open-immersion, and commutativity binders match individually. Checked
that the comparison is the normalized dependency witness with `r = 𝟙 U` and that
its source identity comparison is inverted in the correct direction. Checked the
projection's first equation from `j₁* p* j₂! M` to `j₁* j₁! M`: inverse compositor,
inverse j₂ unit, j₁ unit. Checked zero on the complementary component, and that
this condition does not assert j₁ is closed in V₁. Checked the degreewise formula
has Q applied to the actual π chain map and binds all integer degrees through an
arbitrary cochain complex. The final transformation has source `Dj₂! ⋙ Dp*` and
target `Dj₁!`, with the counit of exact pullback/derived direct image. No input
projection, Cartesian assumption, or boundedness condition is substituted.
The existential outputs package the canonical component construction and its
unique localization characterization; they are not extra hypotheses. The only
postponed proof is the item's theorem. Independent review remains the maintainer's.
