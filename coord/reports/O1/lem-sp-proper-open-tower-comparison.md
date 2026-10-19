## Worker report

The module `Sheaf.Paper.ProperOpenTowerComparison` states
`AlgebraicGeometry.ProEtale.StrictTower.properOpenTowerComparison` with one `sorry`.
The other declarations are concrete compositions of existing canonical functors/maps,
or a dependent-pair specialization of the recorded etale-origin witness. No new DAG
node or dependency statement is introduced, and no statement is corrected.

Hypothesis-by-hypothesis correspondence:

- The commutative Noetherian coefficient ring is `A : Type (u+1)`, `[CommRing A]`,
  `[IsNoetherianRing A]`; the ideal is `I : Ideal A`.
- Finiteness of every positive quotient is
  `[∀ n : ℕ, Finite (A ⧸ I ^ (n+1))]`. The index `n` means positive level `n+1`;
  this is the published tower indexing and includes level 1.
- The four schemes are `U V W Z : Scheme.{u}`, each with `[IsNoetherian ...]`.
  Mathlib's class means locally Noetherian and quasi-compact, equivalently the
  specified finite affine cover. It does not assume separatedness of the schemes.
- The four named maps are exactly `k : U ⟶ V`, `r : U ⟶ W`, `p : V ⟶ Z`,
  `i : W ⟶ Z`. The equation `h : k ≫ p = r ≫ i` is commutativity.
  `[IsProper r] [IsProper p] [IsOpenImmersion k] [IsOpenImmersion i]` are all four
  morphism hypotheses. There is no cartesian-square binder. Quasi-compactness needed
  by the existing calculus is inferred from the Noetherian hypotheses, not added.
- The sites, coefficients, modules, towers and unbounded localization are the
  existing `coefficients`, `Modules`, `Towers`, and `Derived A T` of StrictTower.
  They use small pro-etale site objects in `u+1`, morphisms in `u`, and module
  values in `u+1`. There is no equality imposed on these site universes.
- `G`, `R`, `J`, `adj`, and `jAdj` are the recorded termwise inverse image, total
  right derived termwise direct image, exact open extension, and their adjunctions.
  `J` uses the universal-property-defined module left adjoint whose recorded source
  identifies it with localized extension presheaf followed by sheafification.
  A lift to an open is unique when it exists: its summand is the original module,
  and the empty sum is zero. Thus this is the presheaf prescribed by the item.
- `N : Derived A U` is an actual object of the derived category of strict towers.
  `w : ∀ n, properOpenQuotientOrigin A I U N n` retains the specified finite
  pro-etale bounded-below object, the recorded `EtaleOriginWitness` (including its
  bounded-below etale `L` and comparison iso), and its scalar-restriction iso to
  `(ev A U n).obj N` (the inverse direction of the displayed iso, with no loss
  of its specified data). This is precisely the displayed finite-origin witness;
  `properOpenScalarOrigin` just repackages it for the existing calculus, with ring
  exactly `A/I^(n+1)` and scalar map exactly `Ideal.Quotient.mk`. The discrete
  topology is fixed in that specialization. There are no transitions on the `L`s,
  common lower bound, completeness, cartesianness, or extra coefficient assumptions.

Clause-by-clause correspondence:

- The unique natural iso `λ : (J A k ⋙ R A p) ⋙ G A i ≅ R A r` has exactly the
  direction `G_i R_p J_k → R_r`. Its hom is fixed by equality to
  `properOpenRestrictionMap`; it is not an arbitrary natural isomorphism.
- That definition uses `S = pullback p i`, `b = pullback.fst p i`,
  `q = pullback.snd p i`, `s = squareLift k r p i h`. The existing
  `squareLift_clopen`, `squareLift_open`, `squareLift_closed` give precisely the
  induced open-and-closed immersion, even in noncartesian squares.
- The actual formula first applies the cartesian square mate `exchange` for
  `(b,q,p,i)`, then `properOpenRestrictedExtension` identifies `G_b J_k` with `J_s`
  using `jComp`, `jCongr`, and the inverse open unit. Next it applies `openToR s`,
  then `rComp s q`, then equality transport along `s ≫ q = r`. Hence it is the
  stipulated open restriction/clopen/direct-image-composition map, including its
  K-injective diagram-site interpretation described in the theorem's proof docstring.
- The implication with premise `IsPullback k r p i` explicitly asserts the
  cartesian normalization. Its right-hand side `properOpenCartesianRestrictionMap`
  is the original square mate, followed by the inverse open unit.
- `properOpenOpenAdjunct ... λ` is defined by the inverse of the actual whiskered
  `jAdj` Hom equivalence applied to `λ.inv`. It is a natural transformation
  `R_r ⋙ J_i ⟶ J_k ⋙ R_p` in the derived strict diagram categories.
- The asserted equality with the published `gamma ... h` takes place between whole
  natural transformations before evaluation. It is the result of the explicit
  clopen projection and adjunction triangle calculation in DAG proof step 4.
- The unit equation at every `M` inserts `(jAdj A i).unit.app (R_r M)`, followed by
  `G_i Γ_M` and `λ_M`, and asserts equality to identity. This types exactly the
  displayed `λ_Q ◦ G_i Γ_Q = 1` under the open unit identification.
- For every `N,w`, `IsIso ((properOpenOpenAdjunct ... λ).app N)` is the required
  isomorphism in `D(T_Z)`. The subsequent equation conjugates its n-th evaluation
  by the specified `finiteSource` and `finiteTarget`, giving exactly `HD.map` of
  the dependency's normalized `finiteGamma` at the retained `origin.L`. These
  comparisons retain scalar restriction, site transport, and derived evaluation
  mates. No assertion of faithfulness of evaluation is present.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.StrictConstantTowerOperations`:
  `AlgebraicGeometry.ProEtale.StrictTower.coefficients`, `Modules`, `Towers`,
  `Derived`, `G`, `R`, `adj`, `ev`, `rComp`. These expose the Mathlib constant sheaf,
  functor category and ordinary localization rather than copying those notions.
- `Sheaf.AlgebraicGeometry.StrictTowerOpenExtension`: `J`, `jAdj`, `jComp`, `jCongr`.
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows`: `squareLift`,
  `squareLift_clopen`, `openToR`, `jAdj_unit_isIso`, `exchange`, `gamma`.
- `Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport`:
  `ScalarEtaleOrigin`, `finiteRestriction`, `HD`.
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`: `finiteSource`,
  `finiteTarget`, `finiteGamma`, `gamma_isIso`, `gamma_evaluation`.
- `Sheaf.Paper.RingedEtaleOriginWitness` retains the recorded general/finite ringed
  origin interface; the finite witness used here is the same
  `AlgebraicGeometry.ProEtale.EtaleOriginWitness` publicly imported there from
  `Sheaf.Paper.EtaleOriginWitness`.
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`:
  `AlgebraicGeometry.Etale.properOpenInterchangeCoherence`, through `finiteGamma`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsNoetherian` and its quasi-compactness
  instances; `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`;
  `Mathlib.RingTheory.Ideal.Quotient.Defs`: `Ideal.Quotient.mk`.
- The recorded statement dependencies for general sites, constant sheaves,
  sheafification, inverse systems, K-injectivity, site comparison, schemes,
  fibre products, proper maps and open immersions are reused through these
  operations, not redeclared. Their source signatures/docstrings were inspected.
- Recorded proof modules are imported for diagram-site realization, localization,
  K-injective resolutions and preservation, total derived functors, and normalized
  direct-image composition. The mate/composite-adjunction and exact-derived-functor
  Mathlib APIs are publicly available through the tower modules.

The five already stated strict-tower construction/calculus nodes were added to
`stmt_deps`, because their actual recorded declarations occur in this statement.
There are no extra node files or restated dependency theorems.

Edge cases checked: zero coefficient ring, `I=⊤`, `I=0` when its quotients satisfy
finiteness, level 1, empty schemes/opens, identity maps, cartesian squares, and
noncartesian clopen sections. The constructions have no nonempty or nonzero binder;
empty components contribute the zero factor. No uniform cohomological bound appears.
The empty complementary component specializes to the explicit cartesian clause.
Arbitrary ambient schemes need not be separated. The coefficient universe is the
existing site's value universe; smaller coefficient rings may be lifted there.

Searches made on 2026-10-16:

- `msearch.py leanfinder`, query "Open adjunction normalization of proper pushforward
  extension by zero comparison on derived strict inverse systems of module sheaves":
  eight hits about underived SheafOfModules adjunctions/direct images; no exact match.
- `msearch.py loogle`, query `SheafOfModules.pushforward, SheafOfModules.pullback`:
  twelve pullback/adjunction/composition hits; no strict derived normalization theorem.
- `msearch.py grep`, query `properOpen|proper_open|strict.*tower`: 25 unrelated
  Mathlib scalar-tower hits; no match.
- `msearch.py leansearch`, query "Canonical open restriction isomorphism for proper
  direct image and extension by zero on derived inverse systems of sheaves": eight
  ordinary scheme/sheaf open-immersion restriction hits; no strict-tower comparison.
- `rg` in upstream `WeilConjectures` for `properOpen|proper_open|openRestrictionComparison`
  and the exact node id: no matches. `rg` in `lean/Sheaf` located the existing
  strict-tower calculus and ordinary open-Hom restriction comparisons, which were
  read and reused. None states the open-restriction normalization delivered here.

No STATEMENT-DISPUTED or statement fault was found. Sources read: local Stacks
`more-etale.tex`, Lemmas `lemma-shriek-proper-and-open` and
`lemma-shriek-proper-and-open-base-change`. These are the finite etale comparison;
the explicit strict-tower/open-adjunction enhancement is attributed to the agent,
just as the node's source requires.

Validation: `scompile.py N1 lem-sp-proper-open-tower-comparison` passed both its
sandbox check and the actual module check (7.4 s and 28.6 s respectively), with
no errors or warnings. The only postponed proof is `properOpenTowerComparison`.
`deliver2.py N1 lem-sp-proper-open-tower-comparison --no-push` printed
`OK (dry run)` for commit `6d73cada1d`: compilation and preflight passed except
for the independent second-reading section, which the tool explicitly reserves
for the second reader. Nothing was pushed.


## Second reading by N1

Independent second reading, 2026-10-16. I read the sandbox node and module, the
repository node and dependency records, the five strict-tower construction/calculus
modules, the retained origin declaration, and the source text. There is no repair
note for this item and no `statement_change`. The sandbox contains one item node and
one module; there are no new definition nodes or dependency modules to review.

The source was read first: `more-etale.tex`, Section "Preliminaries to derived lower
shriek via compactifications", `lemma-shriek-proper-and-open` (0F7B), assumes proper
vertical maps and separated locally quasi-finite horizontal maps, without a
cartesian-square hypothesis. Open immersions satisfy the horizontal hypotheses.
The displayed map has direction `i_! Rr_* → Rp_* k_!`. Finite rings are torsion;
the origins here are also bounded below, so their coefficient and boundedness
hypotheses satisfy the source. `lemma-shriek-proper-and-open-base-change` (0F7F)
uses the same maps and K-injective normalization. I also read
`sites-cohomology.tex`, the diagram-site discussion and
`lemma-derived-limit-is-ok` (0941): evaluation extracts a strict diagram's terms
and preserves K-injectives by its exact left adjoint. These tags do not themselves
state the strict pro-etale theorem: the node and Lean both explicitly attribute
that enhancement and its open-adjunction calculation to the agent. No hidden
Noetherian, characteristic, separated-ambient-scheme or cartesian hypothesis from
these source places has been omitted.

Object, hypothesis and conclusion checklist (each verdict is PASS):

1. Commutative Noetherian ring and ideal: section variables
   `(A : Type (u + 1)) [CommRing A]`, followed by `[IsNoetherianRing A]` and
   `(I : Ideal A)`. This is a ring, not a field or a complete adic ring.
2. Every positive quotient is finite: `[∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))]`.
   Reindexing sends Lean zero to paper level one and is a bijection with all
   positive levels; there is no missing level or added quotient condition.
3. Four Noetherian schemes: `{U V W Z : Scheme.{u}}` with all four
   `[IsNoetherian ...]` binders. I read Mathlib's `IsNoetherian` and
   `isNoetherian_iff_of_finite_affine_openCover`: this is precisely a finite
   affine cover by spectra of Noetherian rings. The class adds no separatedness.
4. Named square and its commutativity: `(k : U ⟶ V) (r : U ⟶ W)` and
   `(p : V ⟶ Z) (i : W ⟶ Z)`, with `(h : k ≫ p = r ≫ i)`. The four map
   properties are exactly `[IsOpenImmersion k] [IsOpenImmersion i]`
   `[IsProper r] [IsProper p]`. `IsPullback` is only the premise of the
   cartesian-normalization clause, never a hypothesis on the whole square.
   Quasi-compactness of the opens is inferred, not imposed: I checked
   `IsNoetherian.noetherianSpace` and `quasiCompact_of_noetherianSpace_source`.
5. Sites, coefficients and strict towers: `coefficients A T` is the actual
   constant commutative ring sheaf on `Scheme.ProEt.topology T`; `Modules A T`
   is its module-sheaf category; `Towers A T = ℕᵒᵖ ⥤ Modules A T`;
   `Derived A T = DerivedCategory (Towers A T)`. These are the recorded
   `def-cbc-strict-constant-tower-operations` declarations. In particular the
   derived category is formed AFTER strict towers; transitions are not just
   maps of separate derived objects.
6. Operations and adjunctions: I read `modulePullback`, `moduleDirectImage`,
   `towerPullback`, `towerDirectImage`, `G`, `R`, `adj`, and `ev`. `G` is exact
   termwise inverse image and `R` is the total right derived termwise direct
   image. `constantRingIso` preserves the constant-section coefficient map.
   `adj` is their induced adjunction, rather than an additional chosen map.
7. Open extension: the recorded `moduleJ`, `moduleJAdj`, `towerJ`, `J`, and
   `jAdj` in `StrictTowerOpenExtension` use the localized-site left-adjoint
   universal property. It determines the functor with its adjunction up to
   unique unit-preserving isomorphism, so its use of a left adjoint is allowed
   by the no-hollow-definition rule. The module's five-step proof explains why
   the localized presheaf is exactly sections when a lift to the open exists,
   and zero otherwise: there is at most one lift. Its exactness, tower extension
   and open unit are the recorded ones, not private replacement constructions.
8. Canonical restriction isomorphism: the existential is
   `lam : (J A k ⋙ R A p) ⋙ G A i ≅ R A r`, with
   `lam.hom = properOpenRestrictionMap A k r p i h`. I followed that definition
   factor by factor: `exchange` on `(pullback.fst p i, pullback.snd p i)`,
   `properOpenRestrictedExtension`, `openToR` on `squareLift`, `rComp`, and
   `eqToIso` along `pullback.lift_snd`. This is the source's restriction and
   clopen-component formula, not an unspecified isomorphism with those endpoints.
   `squareLift_clopen` and its two recorded instances supply the stipulated
   open-and-closed immersion; it need not be a cartesian lift isomorphism.
   `∃!` only expresses canonicity: equality to the fixed hom determines the iso.
9. Cartesian normalization: the implication
   `IsPullback k r p i → lam.hom = properOpenCartesianRestrictionMap ...`
   gives exactly the original square mate followed by the inverse open unit.
   I checked both this map and the general map's associator directions.
10. Actual open adjunct: `properOpenOpenAdjunct` is the inverse of the
    Hom equivalence of `(jAdj A i).whiskerRight (Derived A U)` applied to
    `lam.inv`. I checked Mathlib's `Adjunction.whiskerRight` signature. This
    produces `R A r ⋙ J A i ⟶ J A k ⋙ R A p` as a whole natural
    transformation in the derived strict-diagram category. It is independent
    of any input origin or subsequent evaluation.
11. Open-adjunction normalization: for every `M : Derived A U`, the equation
    inserts `(jAdj A i).unit.app ((R A r).obj M)`, then maps the adjunct by
    `G A i`, then applies `lam.hom.app M`, and obtains identity. This is the
    typed version of `λ G_i Γ = 1` under the open unit identification. The
    additional equality of the adjunct with the dependency's `gamma` records
    exactly the node's proof-step-4 identification, not a second comparison.
12. Input and specified origins: the theorem quantifies over every
    `(N : Derived A U)` and `(w : ∀ n, properOpenQuotientOrigin A I U N n)`.
    I unfolded the dependent pair: its coefficient ring is exactly
    `A ⧸ I ^ (n + 1)` with discrete topology, and it retains a bounded-below
    finite-coefficient `F`, the EXISTING `ProEtale.EtaleOriginWitness ... F`,
    and an isomorphism from its scalar restriction to `(ev A U n).obj N`.
    The witness retains its bounded-below etale `L` and `alpha`; taking the
    inverse of the displayed isomorphism gives the node's orientation.
    `properOpenScalarOrigin` merely repackages this data, with scalar map
    exactly `Ideal.Quotient.mk _`. There is no existential replacement of the
    specified `L`, transition on the origins, uniform bound or completeness.
13. Isomorphism on the input: `IsIso ((properOpenOpenAdjunct ... lam).app N)`
    is precisely invertibility in the target derived STRICT tower category.
14. Finite evaluation normalization: the final equation precomposes the
    evaluated adjunct by the recorded `finiteSource ... w` and postcomposes
    `HD.map ((finiteGamma ...).hom.app w.origin.L)` by `finiteTarget ... w`.
    I read those definitions: they retain the origin iso, exact scalar
    restriction, site comparison, open-extension comparison, and derived
    evaluation/direct-image mates with their specified directions. I opened
    `Etale.properOpenInterchangeCoherence` and its section/derived-unit
    normalization; `finiteGamma` selects that normalized witness. Thus the
    equation concerns the specified finite map, not merely isomorphic objects.
    It asserts no faithfulness of derived evaluation.

Universes and edge cases: the small pro-etale site retains object universe `u+1`
and morphism universe `u`; coefficients and module values lie in `u+1`, as in the
recorded dependencies. There is no equation identifying the site's two universes,
no arbitrary lower test universe, and no extra derived-category instance argument.
For any fixed coefficient and scheme sizes a common ambient universe may be chosen;
there is no fixed finite size bound. The literal index is the nonempty fixed
positive-natural tower, so an empty index set is not a case of this node. Empty
schemes and opens, the zero object, the zero ring, `I = ⊤`, and `I = 0` when its
quotients are finite have no excluded binder. No positive-characteristic,
characteristic-invertibility, nonzero or nonempty assumption appears. `n = 0`
correctly denotes the first positive level. Identity squares, cartesian squares,
and noncartesian clopen components are all included; the complement may be empty.
Different origins may have different lower bounds.

Independent searches on 2026-10-16, using words different from the first reader's:

- `msearch.py ... leanfinder`, "Derived open base change natural isomorphism and
  adjunction transpose for proper direct images of inverse systems of sheaves":
  eight ordinary sheaf adjunction/composition hits, no strict-diagram statement.
- `msearch.py ... loogle`, `CategoryTheory.Adjunction.whiskerRight`: five hits;
  the general functor-category adjunction was opened and is reused by the
  helper definition. It is not this proper/open comparison theorem.
- `msearch.py ... grep`, `derived.*(shriek|extension).*restriction|open.*adjunct|clopen.*comparison`:
  25 ordinary scheme/topological sheaf adjunction hits, no exact statement.
- Direct `rg` in Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf`
  for proper/open, restriction, clopen and tower comparisons. I opened
  `ProEtaleProperOpenComparison`, `ProperOpenComparisonIso`,
  `ProperOpenComparisonSiteNormalization`, and the etale unbounded interchange
  interface. They concern individual derived etale/pro-etale complexes or a
  refinement triangle, not unbounded derived strict constant-coefficient towers
  with independent specified quotient origins. The closest strict-tower calculus
  provides `gamma_isIso`/`gamma_evaluation`, but not this canonical restriction
  isomorphism and its open-adjunction identification. It is reused here.

Mismatch found and repaired: the module relied on transitive availability for
five recorded proof-dependency modules. I added explicit ordinary imports of
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
`Mathlib.CategoryTheory.Adjunction.Basic`,
`Mathlib.CategoryTheory.Adjunction.Mates`,
`Sheaf.AlgebraicGeometry.StrictTowerOpenExtension`, and
`Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`, retaining the proof
plan as required by the stage-2 import convention. I found no mathematical
statement mismatch. The theorem, helper data and node fields were left unchanged.
All six helpers contain real data; the sole theorem proof remains `by sorry`.
Every declaration has its source and blueprint docstring, and the theorem
carries all five proof steps. There is no local notation, private notion,
local instance, hidden statement `let`/`show`, or unbound variable/universe.
The node's `lean.statement` was checked byte-for-byte against the theorem's
signature before `:=`.

Second-reader validation: `scompile.py N1 lem-sp-proper-open-tower-comparison
lean/Sheaf/Paper/ProperOpenTowerComparison.lean` passed the sandbox check (3.5 s)
and the actual module check (21.4 s), with no errors or warnings. The verbatim
signature comparison and 100-column check also passed.
