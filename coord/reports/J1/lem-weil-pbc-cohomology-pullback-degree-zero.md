## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero` states the two clauses
of the item in four named theorems, each with `sorry`. It introduces no definition and does
not change the natural-language node, its dependencies, or its proof. The signatures use
only explicitly bound universes and variables.

Hypotheses and clauses:

- A scheme `T` is `T : Scheme.{u}`; an abelian étale sheaf is
  `G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`. The complexes are indexed by all
  of `ℤ`, not by `ℕ`, so arbitrary unbounded K-injective resolutions are included.
- The augmentation is `s : (CochainComplex.singleFunctor _ 0).obj G ⟶ I`, with
  `[QuasiIso s] [I.IsKInjective]`. These are exactly the two parts of a K-injective
  resolution. The recorded resolution abbreviation only accepts module-valued sheaves;
  its underlying recorded Mathlib notions `QuasiIso` and `CochainComplex.IsKInjective`
  apply directly to the abelian sheaf category, without making another definition.
- `G(T)` is `(Sheaf.Γ T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj G`. Its standard
  identification with evaluation at the terminal étale object is
  `Sheaf.ΓNatIsoSheafSections ... terminalIsTerminal`.
- Clause 1, well-definedness, is the existential cycle factor `z` in
  `exists_degreeZeroCohomology_cycles_iso`. The equation `z ≫ iCycles 0 = Γ.map ...`
  says its underlying section is precisely `s⁰(g)`; `singleObjXSelf.inv` identifies the
  degree-zero term of `G[0]` with `G`. Since `iCycles` is monic, this characterizes `z`
  uniquely. This explicitly records landing in cocycles rather than assuming it.
- Clause 1, the actual augmentation-to-cohomology map, is `z ≫ homologyπ 0`.
  Its target is `(((Sheaf.Γ ...).mapHomologicalComplex (.up ℤ)).obj I).homology 0`,
  exactly `H⁰(Γ(T,I))` from the dependency's K-injective recipe. `IsIso` expresses
  that this homomorphism is an isomorphism of abelian groups. No comparison group or
  arbitrary isomorphism is substituted for this canonical map.
- Clause 1, naturality, is `degreeZeroCohomology_resolution_naturality`. It quantifies
  over `G G'`, `φ`, both resolutions, a lift `a`, and
  `h : Homotopy (s ≫ a) ((singleFunctor _ 0).map φ ≫ s')`.
  The factors `z z'` are characterized by `hz hz'`, the same augmentation equations
  as above. The conclusion is `ε_s ≫ homologyMap (Γ.mapHomologicalComplex.map a) 0 =
  Γ.map φ ≫ ε_s'`. This is exactly `H⁰(φ) ∘ ε_s = ε_s' ∘ φ(T)`, written in diagram order.
  A chosen lift and its homotopy describe the map in the node; they are not an exact
  commuting-lift restriction (the homotopy may be nontrivial).
- Clause 1, compatibility between resolutions, is the same universal theorem with
  `G' = G` and `φ = 𝟙 G`. It holds for every comparison lift of the identity. Thus it
  uses the compatible comparison identification, not an arbitrary isomorphism supplied
  by `Nonempty.some`. Existence and independence of comparison lifts belong to the
  cited functoriality and resolution-independence nodes.
- Clause 2, schemes and morphism, is `{X Y : Scheme.{u}} (u : Y ⟶ X)` with `G` on `X`.
  In `degreeZeroCohomology_resolution_pullback`, `s` resolves `G` and
  `r : (upperStar ... u).mapHomologicalComplex.obj I ⟶ J` is the second resolution;
  `[QuasiIso r] [J.IsKInjective]` are exactly its conditions.
- The target augmentation is described by `hz'`: on sections it is
  `upperStar.map (singleObjXSelf.inv ≫ s.f 0) ≫ r.f 0`, namely the degree-zero component
  of the composite resolution `r ∘ u⁻¹s`, with the single-complex identification.
  Exactness of `upperStar` ensures this is a K-injective resolution, as the dependency
  specifies. Its cycle factor exists and is an isomorphism by the first theorem applied
  to that composite resolution.
- The pullback chain map in this theorem is written out, with no private copy:
  `NatTrans.mapHomologicalComplex` of the adjunction unit whiskered by global sections,
  then `Functor.associator`, then the existing `lowerStarCompGlobalSectionsIso`, followed
  by `Γ_Y.mapHomologicalComplex.map r`. Applying `homologyMap ... 0` is exactly the
  node's resolution-level definition of `u*`. The conclusion is
  `ε_X ≫ u* = globalSectionsUpperStarMap ... u G ≫ ε_Y`.
- The unit on sections `η_{u,G}(X)` is the existing `globalSectionsUpperStarMap`, whose
  full source definition evaluates `upperStarLowerStarAdjunction.unit.app G` at the
  terminal object and identifies its base change with the terminal object of `Y`.
  This incorporates `(u_* u⁻¹G)(X) = (u⁻¹G)(Y)` via the canonical terminal isomorphism.
- `cohomologyMap_zero_eq_globalSectionsUpperStarMap` also gives the same clause in the
  recorded upstream pullback encoding, using `cohomologyMap u G 0` and the inverses of
  `Sheaf.H.equiv₀`, with `ΓNatIsoSheafSections` to evaluate global sections. It holds for
  every global section `g`. This supplements, rather than replaces, the explicit
  resolution-level formula.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.CategoryTheory.Sites.Sheaf` and the small étale site:
  `CategoryTheory.Sheaf`, `Scheme.smallEtaleTopology`.
- `Sheaf.AlgebraicGeometry.KInjectiveResolutions`:
  `CochainComplex.IsKInjectiveResolution`, read in full. Its two primitive notions
  `QuasiIso` and `CochainComplex.IsKInjective` are used on abelian sheaves, as explained above.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `Etale.cohomology`, `Etale.rightDerivedGlobalSections`, read with signatures/docstrings.
  The theorem statements use precisely their resolution computation `H⁰(ΓI)`, rather
  than introduce a new spelling of either derived functor.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective`:
  `CochainComplex.IsKInjective.nonempty_homology_iso`, read with its full signature and
  proof/docstring. It gives abstract independence, while our naturality statement specifies
  the augmentation compatibility for every lift of the identity. This import also supplies
  the K-injective complex API.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `Etale.upperStar`, `Etale.lowerStar`, `Etale.upperStarLowerStarAdjunction`, used through
  the global-sections import, with their full definitions/signatures read.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`:
  `Etale.cohomologyMap`, used through the global-sections import.
- `lem-weil-pbc-cohomology-pullback-functorial` has neither `lean` nor `mathlib_match` in
  the supplied node. The present item's reference to it specifies `H⁰(φ)` via a chain lift;
  we state that exact formula using Mathlib's `Homotopy` and `homologyMap`, without an
  undefined function name or a new copy of the functoriality theorem. Its full statement
  was read. No notion necessary for the present signature is missing.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections`:
  `Etale.globalSectionsUpperStarMap`, `Etale.lowerStarCompGlobalSectionsIso`.
- `WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections` supplies the additive
  instance for `Sheaf.Γ`, needed for applying it to complexes.
- `Mathlib.Algebra.Homology.Single`: `HomologicalComplex.singleObjXSelf`.
  `Sheaf.H.equiv₀` and its naturality lemmas were read in
  `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.

Edge cases: zero sheaf, empty scheme, arbitrary negative terms in `I` and `J`, nontrivial
homotopies into degree `-1`, identity morphisms, and identity comparison maps are all allowed.
There is no finiteness, properness, étaleness, boundedness, characteristic, or nonemptiness
assumption. In particular the hypotheses do not require the resolution to vanish in negative
degrees. Scheme and coefficient universes follow the recorded small-site encoding.

Searches made:

- `msearch.py ... leanfinder "Degree zero etale cohomology pullback is the map on global
  sections"`: eight hits, mostly scheme module pullback and pullback-spectrum lemmas;
  no matching theorem.
- `msearch.py ... loogle "CategoryTheory.Sheaf.H.equiv₀"`: four hits, the degree-zero
  equivalence and its naturality and exact-sequence lemmas; no scheme pullback formula or
  arbitrary K-injective augmentation theorem.
- `msearch.py ... grep "equiv₀|homologyZeroIso" CategoryTheory/Sites`: five lines in
  `SheafCohomology/Basic.lean`, including `H.equiv₀`; no full match.
- `msearch.py ... leansearch "zeroth cohomology of a K injective sheaf resolution is global
  sections"`: unavailable, Internal Server Error; other search kinds were used.
- `rg` in Mathlib's homology and category directories for single/homology and termwise
  functor compatibility located `singleObjXSelf`, `singleObjHomologySelfIso`, and
  `singleMapHomologicalComplex`. These supply the canonical single-term identifications,
  not the theorem for K-injective resolutions after global sections.
- `rg "globalSectionsUpperStarMap" WeilConjectures` located its existing definition and
  identity/composition laws. `rg "equiv₀.*cohomologyMap|cohomologyMap.*equiv₀"` found
  no degree-zero pullback identification. Searching the item's exact id in the source
  repository found no declaration.
- `rg` across `lean/Sheaf` for degree-zero cohomology and the item id located other
  cohomology statements, but no duplicate of this node's statement.

Source checked directly: Stacks Tags [05TD](https://stacks.math.columbia.edu/tag/05TD) and
[01FA](https://stacks.math.columbia.edu/tag/01FA). The local Stacks checkout is absent, so
these source pages were read online. Tag 05TD gives the degree-zero map for a left exact
functor and the reduction to nonnegative resolutions; 01FA gives the functorial cohomology map.

No statement correction, new definition node, dependency module, or disputed statement.
The first compiler feedback required an explicit coefficient category in an evaluation map;
the second required qualifying `Functor.whiskerRight` and `Functor.whiskerLeft`.
All four declarations retain only `sorry` proofs. The second reader will supply their own
reading section and deliver the result.

## Second reading by J1

Independent reading on 2026-10-12 of the sandbox node and all four signatures, against
all nine statement-dependency nodes and their source declarations. Verdict: the delivery
states both clauses, including the canonical augmentation and arbitrary resolutions;
no mathematical or Lean change was needed. This section is the only changed content.

Source reading: the repository has no Stacks checkout. I fetched the upstream Stacks
`derived.tex` and `cohomology.tex` into the item's scratchpad and read
`lemma-left-exact-higher-derived`, the preceding higher-derived-functor definition,
`section-functoriality`, `equation-functorial`, and `remark-explain-arrow`. I also read
[05TD](https://stacks.math.columbia.edu/tag/05TD),
[05TC](https://stacks.math.columbia.edu/tag/05TC), and
[01FA](https://stacks.math.columbia.edu/tag/01FA).
05TD assumes additive functors between abelian categories, with the right derived functor
everywhere defined; its isomorphism clause assumes left exactness. For global sections
of abelian sheaves these are structural facts, not additional restrictions on schemes.
The cohomology source constructs the map for an arbitrary morphism of ringed spaces and
an f-map, using injective resolutions and the pushforward/global-sections identification.
The node expressly extends that construction to the small étale site and arbitrary
K-injective resolutions, with the comparison transport written in its proof. No proper,
Noetherian, finite-type, characteristic, or bounded-resolution assumption is implicit here.

Object/hypothesis/conclusion checklist (all verdicts PASS):

- Arbitrary scheme T: `(T : Scheme.{u})`. Mathlib's `Scheme` is the locally ringed
  space with local affine charts; its morphism type is the node's scheme morphism.
- Abelian étale sheaf G: `Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`.
  I read `Sheaf` as the full subcategory of sheaf presheaves, and `smallEtaleTopology`
  as the topology on schemes étale over T. No module-valued substitute is imposed.
- Resolution of G[0]: `I : CochainComplex ... ℤ`, augmentation
  `s : (CochainComplex.singleFunctor _ 0).obj G ⟶ I`, `[QuasiIso s]`,
  `[I.IsKInjective]`. I read the landed resolution module: its abbreviation is only
  for ModuleCat sheaves, but its two recorded primitive declarations apply here.
  Using those primitives directly is the same notion, without a private predicate.
- G(T): `(Sheaf.Γ ...).obj G`. I read `Sheaf.Γ` and `ΓNatIsoSheafSections`:
  this is global sections canonically identified with evaluation at the terminal
  étale object, rather than sections at a chosen nonterminal test scheme.
- H^0(T,G): `((Sheaf.Γ ...).mapHomologicalComplex (.up ℤ)).obj I |>.homology 0`.
  The recorded `rightDerivedGlobalSections` is the total right derived functor of Γ,
  and `cohomology` its composition with derived homology. The theorem uses exactly
  the node's computation on a K-injective resolution, without redefining cohomology.
- Well-definedness and the actual epsilon: `exists_degreeZeroCohomology_cycles_iso`
  gives `∃ z`, with `z ≫ iCycles 0 = Γ.map (singleObjXSelf.inv ≫ s.f 0)`.
  Thus epsilon is precisely `z ≫ homologyπ 0`; it is not an unspecified isomorphism.
  The inclusion of cycles is monic, so every factor satisfying this equation is the
  same map. `IsIso` of this composite gives the claimed abelian-group isomorphism.
- Naturality in G: `degreeZeroCohomology_resolution_naturality` binds G, G', φ,
  their resolutions, a comparison chain map a, and
  `Homotopy (s ≫ a) ((singleFunctor _ 0).map φ ≫ s')`.
  Its equality is epsilon_s followed by homology of Γ(a), equal to Γ(φ) followed
  by epsilon_s'. The cycle-factor hypotheses identify the maps rather than add
  restrictions on the objects: their factors exist by the first theorem.
- Compatibility between resolution choices: specialize that same universally
  quantified theorem to `G' = G`, `φ = 𝟙 G`. The result concerns every comparison
  lift of the identity, exactly the identifications in the node's functoriality
  statement. I read `IsKInjective.nonempty_homology_iso` and its signatures:
  it supplies abstract independence, while this delivery specifies augmentation
  compatibility, not an arbitrary choice from that existential isomorphism.
- Arbitrary pullback u:Y→X and G on X: `{X Y : Scheme.{u}} (u : Y ⟶ X)`;
  `upperStar`, `lowerStar`, and `upperStarLowerStarAdjunction` are the recorded
  inverse image, base-change direct image, and their adjunction. I opened their
  definitions. They carry no extra property of u.
- Second resolution: `r : upperStar.mapHomologicalComplex.obj I ⟶ J`,
  `[QuasiIso r] [J.IsKInjective]`; the equation hz' characterizes the augmentation
  `upperStar.map (singleObjXSelf.inv ≫ s.f 0) ≫ r.f 0`. This is precisely the
  composite resolution of u-inverse-image G specified in the node.
- Pullback equality: `degreeZeroCohomology_resolution_pullback` applies `homologyMap`
  to the chain map made from the adjunction unit, the functor associator,
  `lowerStarCompGlobalSectionsIso`, and Γ(r). Its conclusion is
  epsilon_X followed by u*, equal to `globalSectionsUpperStarMap ... u G`
  followed by epsilon_Y. I read both global-sections declarations in full:
  they identify pushforward sections at X with sections at Y by the terminal
  base-change isomorphism, so the right side is exactly η_u,G(X).
- The fourth theorem gives the same pullback clause for the recorded Ext encoding
  `cohomologyMap u G 0`, using `(Sheaf.H.equiv₀ ...).symm` and the canonical
  Γ-to-terminal-sections isomorphism. I read `cohomologyMap` and `H.equiv₀`:
  the latter is the additive Ext/Hom/constant-sheaf-adjunction equivalence.
  This supplementary form does not replace the resolution-level clauses.

Dependency freshness: the first worker's report says that the functoriality dependency
has no Lean record. On the base I read it now has
`Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial.cohomologyPullbackFunctorial`
(the declaration namespace is `AlgebraicGeometry.Etale`). I opened that module: it
states Ext-map naturality, composition, and identity. It does not introduce a notion
needed by our signatures; the node itself specifies H^0(φ) as homology of a lift.
Our homotopy-naturality formula is that specification at degree zero, not a private
replacement definition. No dependency module or new definition node is required.

Edge cases: the zero sheaf and empty scheme are permitted without nonemptiness binders.
There is no index-set binder to exclude an empty index set. Degree zero is explicitly
0 in ℤ; I, I', and J may have negative terms and be unbounded in both directions.
In particular homotopies into I' at degree -1 are allowed. Identity and zero sheaf maps,
identity scheme maps, and all characteristics are included. The single universe u is
explicitly bound; the coefficient category at u+1 follows the recorded small-site
encoding and imposes no finiteness or algebraic assumption on the groups. There is no
free variable, file-local instance/notation, or hidden let/show binder in any signature.

Independent searches:

- LeanFinder: `augmentation zeroth homology global sections K-injective comparison
  naturality` returned `InjectiveResolution.toRightDerivedZero'_comp_iCycles` and
  `toRightDerivedZero'_naturality`, plus ℕ-cochain degree-zero homology lemmas.
  I opened the RightDerived signatures: these are ordinary ℕ-indexed injective
  resolutions with a commuting lift, not arbitrary ℤ-indexed K-injective resolutions
  and homotopy-commuting lifts, and give no scheme pullback clause.
- Loogle: `CategoryTheory.Sheaf.H.mapFunctor` returned no hits (unknown identifier
  in that service). The upstream declaration is available locally and was read there.
- LeanSearch: `inverse image unit induces pullback on zeroth sheaf cohomology under
  global sections identification` was unavailable (Internal Server Error).
  This is recorded as unavailable, not as evidence of absence.
- Direct rg over Mathlib's sheaf-cohomology files, all WeilConjectures, and lean/Sheaf
  for `equiv₀`, `zero.*globalSections`, `globalSections.*zero`,
  `degreeZeroCohomology`, and the exact node id found Mathlib's equivalence and sheaf-map
  naturality, other module/pro-étale results, and no duplicate of the full statement.
  A focused read of the upstream cohomologyMap file found only general map naturality
  and topological invariance, not its compatibility with the degree-zero equivalence.

Standards: all four declarations have source/blueprint docstrings and the proof route:
cycle formation; homotopy boundaries; the left-exact bounded-below injective case;
transport to arbitrary K-injective resolutions; unit naturality for pullback. All proofs
are exactly `sorry`, with no definitions or axioms added. Imports supply the used maps,
additivity instance, K-injective API, and single-term identification. The node's
lean.statement matches the primary theorem signature verbatim. No statement correction,
new node, dependency module, or mathematical mismatch was found; the original Lean and
node were retained. Server compilation was clean (4.4 seconds, exit 0, no warnings).
