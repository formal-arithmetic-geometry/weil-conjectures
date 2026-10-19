## Worker report

Item: `det-base-field-cd-cochains`. Module:
`Sheaf.RepresentationTheory.BaseFieldContinuousCochains`.
The three theorem declarations state clauses (1), (2), and (3), respectively.
Their only proofs are `sorry`. All supporting abbreviations and predicates have
complete bodies. No other DAG node is stated or changed.

Sources read: the current blueprint main-20261015 files
`sec-six-functors-basics/sk-lem-base-field-cd/sk-lem-base-field-cd-cochains.md`
and its `.proof.md`; the item's full DAG statement and nine proof steps; all four
statement dependency records and the recorded source declarations; the recorded
integer-invariants, locally constant effaceability, and delta-universality proof
dependencies and their source modules. The recorded finite-ring continuous
cohomology definition was also inspected and deliberately not applied to integer
coefficients: it requires `[Finite A]`, which would exclude this item's scope.

Hypotheses and objects:

- `G : Type u`, `[Group G]`, `[TopologicalSpace G]`, `[IsTopologicalGroup G]`,
  `[CompactSpace G]`, `[T2Space G]`, `[TotallyDisconnectedSpace G]` render a
  profinite group. In a compact Hausdorff topological group, total
  disconnectedness is equivalent to having an open-normal neighborhood basis.
- `A : Type v`, `[Category.{w} A]`, `[Abelian A]`, and
  `E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G` present precisely the
  category in the node. This is the same equivalence-based presentation used
  by the recorded integer-cochain dependency. It imposes no finite scalar or
  finite coefficient condition and no extra structure on a representation.
  Open stabilizers and equivariant linear homomorphisms come from the recorded
  `Rep.DiscreteContinuousRep`; integer-linear maps are exactly additive maps.
  An equivalent presentation does not replace this category by a subcategory.
- `max u s` allows coefficient carriers at least as large as the group, with
  arbitrary larger carriers by varying `s`. Object and morphism universes of
  the equivalent presentation are independent and explicitly bound.
- The abbreviation `baseFieldIntegerInvariants G A E` is literally the
  composite `E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
  forget₂ (ModuleCat ℤ) AddCommGrpCat`. Thus its objects are the actual invariant
  subgroups and its arrows are restrictions of the original coefficient maps.
  `baseFieldDerivedInvariants` specializes Mathlib's `Functor.rightDerived`;
  it introduces neither another cohomology theory nor a resolution choice.
- `LocallyConstant (Fin n → G) (E.functor.obj M).obj.V` is precisely
  `Cont(G^n,M)` when the coefficient group has the discrete topology. Local
  constancy does not require putting any other topology on the coefficient.

Differential and coefficient maps:

- `HasBaseFieldCochainCoordinates G A E C e` records additive equivalences
  `e M n` from the degree `n` term of `C.obj M` to the stated cochains.
- Its first conjunct says that `C.map f` is pointwise `E.functor.map f`.
  This fixes coefficient functoriality, rather than assuming an arbitrary map.
- Its second conjunct has the action term
  `(E.functor.obj M).obj.ρ (g 0) (e M n x (fun k ↦ g k.succ))`.
  The sum has signs `(-1 : ℤ) ^ (k.val + 1)` and uses
  `Fin.contractNth k (· * ·) g`. The first `n` terms multiply adjacent entries
  and the last deletes the final entry, with sign `(-1)^(n+1)`. This is exactly
  the displayed differential for positive `n`. At `n = 0` the single contracted
  face gives minus the original zero-cochain, hence `g m - m`.
- The complex is `CochainComplex AddCommGrpCat ℕ`. Mathlib homology is kernel
  modulo the incoming image, including zero incoming image in degree zero.

Clause (1): `Rep.exists_baseFieldContinuousCochains_universal`.

- The conclusion provides `C`, `e`, and the coordinate predicate just described.
  Its existential `hI : EnoughInjectives A` and
  `hV : (baseFieldIntegerInvariants G A E).Additive` assert the intrinsic
  infrastructure needed to form derived invariants; neither is an added
  hypothesis of the theorem.
- `T : CohomologicalDeltaFunctor A AddCommGrpCat` and the equality
  `T.F = fun n ↦ C ⋙ HomologicalComplex.homologyFunctor ... n` identify the
  delta-functor's functors with cochain cohomology. `T.IsUniversal` is exactly
  the dependency's universal extension property, including uniqueness.
- `Nonempty (T.F 0 ≅ baseFieldIntegerInvariants G A E)` gives natural `H^0=M^G`.
- The second delta-functor `R` has `R.F n` equal to the actual right-derived
  invariant functor, using the asserted `hI` and `hV`. The morphisms
  `α : CohomologicalDeltaFunctor.Hom T R` and `β : ... Hom R T`, with both
  composites equal to the identity in every degree, give an isomorphism as
  delta-functors. Their `Hom.naturality` fields impose compatibility with every
  connecting map, and their components are natural transformations.

Clause (2): `Rep.baseFieldContinuousCochains_directedUnion`.

- `C`, `e`, and `hC` refer to a complex with the exact coordinates above; these
  are not extra mathematical assumptions about the coefficients. Clause (1)
  supplies such a complex, and its coordinates uniquely determine its maps and
  differential up to coordinate isomorphism. The theorem applies to every such
  presentation of that same complex.
- `I : Type t`, `[PartialOrder I]`, `[Nonempty I]`, and
  `[IsDirected I (· ≤ ·)]` are exactly an arbitrary small nonempty directed
  partially ordered index set. The index universe is independent.
- `D : I ⥤ A` and `c : Cocone D` present the inclusions of stable subgroups
  into their union. `hinj` says every leg is injective on the underlying group.
  `hunion` says every element at the vertex belongs to some stage. Cocone
  naturality says that all transitions commute with these inclusions; hence
  the stages identify with their actual image subgroups and transitions with
  inclusions. Conversely any union of the node's stable subgroups gives such
  a cocone. There is no arbitrary transition-map replacement.
- For every `n : ℕ`, the conclusion says the canonical cohomology cocone is a
  colimit: `Nonempty (IsColimit ((C ⋙ homologyFunctor ... n).mapCocone c))`.
  Given any chosen colimit, this is equivalent to saying its canonical map to
  the vertex is an isomorphism. The clause (1) natural comparison transports
  this very cocone to the cocone of `H^n(G,-)`, preserving its canonical maps.
  Expressing it as `IsColimit` avoids a size restriction from a separately
  chosen colimit object.

Clause (3): `Rep.baseFieldContinuousCochains_finiteQuotients`.

- `baseFieldTrivialOpenNormals G (E.functor.obj M)` is the subtype of
  `OpenNormalSubgroup G` whose every element fixes every coefficient element.
  It retains the node's whole-module triviality condition, not merely a
  pointwise stabilizer condition. Its order dual `ᵒᵈ` is reverse inclusion.
- `hlim : IsBaseFieldQuotientLimit G (E.functor.obj M)` renders the given
  inverse-limit identification without weakening it to an arbitrary quotient
  family. The predicate is `Nonempty (IsLimit (baseFieldQuotientCone G M))`,
  using Mathlib's limit universal property. `baseFieldQuotientDiagram` has
  objects the actual `G ⧸ N.val.toSubgroup` and arrows the actual
  `QuotientGroup.map` induced by the identity on `G`. The cone has vertex `G`
  and legs `QuotientGroup.mk'`. Thus its limiting property says that every
  compatible family of cosets has exactly one simultaneous lift in `G`. Since `G` is compact Hausdorff and these quotients
  are finite discrete spaces, that canonical bijection is a homeomorphism
  onto the closed compatible-tuple subspace, hence the topological group
  inverse-limit identification in the node. This is an equivalent encoding,
  not a correction of its hypothesis.
- `D` is the finite-quotient complex diagram on exactly this entire index
  type. `eN N n` identifies each term additively with the quotient cochains.
  The first displayed equation specifies its differential on tuples lifted
  from `G`. Quotient surjectivity specifies the differential on every tuple;
  whole-module triviality makes the action independent of the lifts.
- The next equation specifies `D.map f` pointwise as pullback along the
  quotient projection. For an arrow `N ⟶ N'` in the order dual, `N' ≤ N`;
  on tuples lifted from `G`, both evaluations use the same tuple in `G` and
  then the relevant quotient. This is exactly inflation from `G/N` to `G/N'`.
  The finite tuple quotient maps are surjective, so this equation uniquely
  fixes the transition map on all quotient tuples.
- `ι : D ⟶ (Functor.const _).obj (C.obj M)` is the inflation cocone. The third
  equation says each leg is the specified cochain pullback to `G`, fixing all
  legs uniquely. Naturality imposes compatibility with every transition.
- `Nonempty (IsColimit (Cocone.mk (C.obj M) ι))` is the asserted chain-level
  colimit. For every `n`, the final conjunct is `IsColimit` after applying
  `homologyFunctor ... n` to this same cocone, giving the cohomology colimit
  with precisely the induced inflation maps. Clause (1), also for the finite
  groups `G/N`, identifies these with the stated Galois cohomology colimits.

Dependency declarations used:

- `WeilConjectures.RepresentationTheory.DiscreteContinuousRep`:
  `Rep.DiscreteContinuousRep` (the actual integer representation category).
- `Mathlib.CategoryTheory.Abelian.RightDerived`:
  `CategoryTheory.Functor.rightDerived` (injective-resolution derived invariants).
- `WeilConjectures.CategoryTheory.DeltaFunctor`:
  `CategoryTheory.CohomologicalDeltaFunctor`, its `Hom` and `IsUniversal`.
- `Mathlib.CategoryTheory.Limits.HasLimits` and its cone imports:
  `CategoryTheory.Limits.Cocone`, `IsColimit`, and the canonical colimit universal
  property. `CategoryTheory.IsFiltered` is the filteredness convention; the
  explicit nonempty directed poset in clause (2) is its stated special case.
- `Mathlib.RepresentationTheory.Invariants`: `Rep.invariantsFunctor`.
- `Mathlib.Topology.Algebra.OpenSubgroup`: `OpenNormalSubgroup` and its normal
  subgroup instance; `QuotientGroup.mk'` and `QuotientGroup.map` from its imports.
- `Mathlib.Topology.LocallyConstant.Algebra` and `Mathlib.Data.Fin.Tuple.Basic`:
  `LocallyConstant` and `Fin.contractNth`.
- Proof imports: `Sheaf.RepresentationTheory.DiscreteIntegerInvariantsInfrastructure`
  (`Rep.discreteInteger_invariants_infrastructure`),
  `Sheaf.RepresentationTheory.LocallyConstantCochainsEffaceable`
  (`Rep.exists_locallyConstantCochains_effaceable`),
  `Sheaf.CategoryTheory.EffaceableDeltaFunctorUniversal`
  (`CategoryTheory.effaceable_deltaFunctor_isUniversal`),
  `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`
  (`CategoryTheory.Functor.exists_universal_rightDerived_deltaFunctor`), and
  `Mathlib.Algebra.Category.Grp.AB`
  (`instPreservesHomologyFunctorAddCommGrpCatColim`). The abelian-category
  definition is supplied by the already imported Mathlib abelian modules.
  No proof-dependency import was omitted to avoid a cycle.

Edge cases checked before and during drafting:

- Degree zero: `Fin 0 → G` is a singleton, the first differential is `g m - m`,
  and the natural `ℕ` complex has zero incoming boundaries.
- The zero coefficient group: every term and cohomology group is zero, and the
  triviality condition allows every open normal subgroup.
- The trivial group with arbitrary coefficients, including infinite `ℤ`:
  there is no finite coefficient hypothesis. The quotient family includes the
  whole group, and the limit hypothesis is meaningful.
- Directed unions: a singleton index is allowed; an empty index is excluded
  exactly as in the node. A group with no nonzero elements still has a zero
  element, so nonemptiness is genuinely needed to capture that element.
- Quotient inflation: `N = G` and `n = 0` are allowed. No properness of `N`,
  positive-degree restriction, finite coefficient condition, or extra common
  kernel hypothesis has been inserted.
- If no open normal subgroup acts trivially on all of `M`, the inverse-limit
  predicate cannot silently hold: its empty compatible family would force `G`
  to be trivial, in which case the whole group does act trivially. The node's
  conditional clause (3) is retained rather than asserted for every action.
- All universes and variables are explicitly bound, and `autoImplicit` is
  disabled. There are no file-local notations, private definitions, or local
  instances used to interpret an exported statement.

Searches actually run:

- `msearch.py leansearch`: "Continuous cohomology of discrete modules over a
  profinite group is the right derived functor of invariants". Eight hits,
  including continuous cohomology, its degree-zero comparison, homogeneous
  cochains, and abstract group cohomology. No match for all three clauses.
- `msearch.py leanfinder`: "Continuous cochains of discrete profinite group
  modules form a universal delta functor compute derived invariants and commute
  with directed unions and inflation from finite quotients". Eight hits, mainly
  the continuous cohomology construction and degree-zero result, plus condensed
  profinite solid objects. No exact match.
- `msearch.py loogle`: `continuousCohomology`. Twelve hits, including
  `continuousCohomology`, `ContinuousCohomology.map`, and its functoriality and
  zero-degree comparison. These use topological representations and do not
  state universality or the two filtered-colimit clauses.
- `msearch.py grep`: `continuousCohomology|continuous.*[Cc]ochain` under
  Mathlib `RepresentationTheory`. Fourteen hits in continuous-cohomology Basic,
  LowDegree, and Functoriality. No theorem matching this node.
- Direct `rg` of upstream `WeilConjectures` and project `lean/Sheaf` with
  `det-base-field-cd-cochains|continuousCohomology|continuous.*[Cc]ochain`,
  plus an exact node-id search of `dag/lean_names_upstream.json`. No upstream
  node-id match. Project hits include the existing cochain universal-comparison
  infrastructure, whose source signatures were inspected. The older
  `discreteContinuousCohomologyFunctor` is restricted to finite scalar rings;
  the integer-cochain existential construction does not include clauses (2)
  or (3). Neither can be recorded as an exact existing match for this item.
- Direct `rg` of all proposed declaration names in Mathlib, upstream
  `WeilConjectures`, and project `lean/Sheaf`: no collisions.

Validation: `scompile.py Q61 det-base-field-cd-cochains` compiled the final
module cleanly, including both the sandbox and library-path passes. The delivery
is checked with `deliver2.py Q61 det-base-field-cd-cochains --no-push`.

No statement correction or disputed statement. No new DAG nodes or dependency
repairs are needed: the helpers expose canonical specializations and coordinates
belonging to this node itself. Validation uses only the prescribed `scompile.py`
single-file wrapper. The second reader supplies the independent reading and delivers.

## Second reading by Q61

I independently read the node statement, its blueprint source and proof, the Lean
module, and every recorded statement dependency before this verdict. The source
place is the blueprint node `det-base-field-cd-cochains` (with the cited Stacks
Tags 010T, 04JP, 04JR, 04JF, and 00DB).

Step 1 list and Lean matching:

- The profinite group is `G : Type u` with `[Group G]`, `[TopologicalSpace G]`,
  `[IsTopologicalGroup G]`, `[CompactSpace G]`, `[T2Space G]`, and
  `[TotallyDisconnectedSpace G]`. This is the compact Hausdorff totally
  disconnected topological-group presentation of the source's profinite group;
  in this setting it has the open-normal neighborhood basis used by the proof.
  Verdict: exact scope, with no finiteness, characteristic, or connectedness
  assumption added.
- The discrete integer representation category is rendered by
  `E : A ≌ DiscreteContinuousRep.{0,u,max u s} ℤ G`, with
  `[Category.{w} A]` and `[Abelian A]`. `DiscreteContinuousRep` is the recorded
  dependency declaration, whose objects have open element stabilizers and whose
  arrows are equivariant integer-linear maps, hence exactly equivariant additive
  maps. The arbitrary equivalent abelian presentation does not restrict the
  coefficient category. Verdict: exact category up to the explicitly supplied
  equivalence, with all universes bound.
- The invariants functor is the abbreviation
  `baseFieldIntegerInvariants`, namely the actual invariant-subgroup functor
  followed by the underlying additive-group functor. Verdict: the same `M^G`.
- The derived functors are `baseFieldDerivedInvariants`, Mathlib's
  `Functor.rightDerived` with the stated `[EnoughInjectives A]` and additive
  invariants structure. Verdict: the node's right derived invariants, not a
  second cohomology definition.
- Cochains are represented by
  `e M n : (C.obj M).X n ≃+ LocallyConstant (Fin n → G) (E.functor.obj M).obj.V`.
  `HasBaseFieldCochainCoordinates` states both coefficient functoriality and
  the displayed inhomogeneous differential. Its action face is
  `ρ (g 0) (e ... (fun k => g k.succ))`; its interior and final faces are the
  `Fin.contractNth` sum with sign `(-1 : ℤ)^(k.val+1)`. At `n = 0` this is
  `g • m - m`, and homology has zero incoming image in degree zero. Verdict:
  every cochain and differential clause matches the node.
- Clause (1) is
  `exists_baseFieldContinuousCochains_universal`: it supplies `C`, `e`, the
  coordinate predicate, enough injectives and additive invariants as intrinsic
  infrastructure, a delta-functor `T` whose functors are the homologies, its
  `T.IsUniversal`, the natural degree-zero invariants isomorphism, a delta
  functor `R` whose functors are the actual right-derived invariants, and
  mutually inverse delta-functor morphisms `α, β`. Verdict: all universal,
  degree-zero, comparison, and naturality clauses are present.
- Clause (2) is
  `baseFieldContinuousCochains_directedUnion`. The independent nonempty
  directed poset `I : Type t`, diagram `D : I ⥤ A`, cocone `c`, injective legs
  `hinj`, and joint-surjectivity `hunion` render exactly a directed union of
  stable subgroups with inclusion transitions. The conclusion is
  `Nonempty (IsColimit ((C ⋙ homologyFunctor ... n).mapCocone c))` for every
  `n`; this is the canonical cohomology colimit, and clause (1) transports it
  to the node's derived-invariant formulation. Verdict: exact quantifiers and
  canonical maps; no arbitrary transition maps or empty index are admitted.
- Clause (3) is
  `baseFieldContinuousCochains_finiteQuotients`. The whole-module-trivial
  open-normal subtype, its order dual, and `IsBaseFieldQuotientLimit` encode
  precisely the node's quotient system and inverse-limit hypothesis. The
  quotient diagram uses the actual `G ⧸ N` objects and `QuotientGroup.map`; the
  cone uses `QuotientGroup.mk'`. The existential `D`, quotient coordinates
  `eN`, and `ι` equations specify the quotient differential, every inflation
  transition, and every cocone leg by pullback along quotient projections.
  The two `IsColimit` conclusions give the chain and all homology colimits.
  Verdict: the reverse-inclusion order, inflation direction, whole-module
  triviality, and all finite-quotient clauses match the node.

Edge cases checked: `n = 0` (singleton `G^0`, differential `g m - m`, zero
incoming image); zero coefficients; the trivial group with arbitrary integer
coefficients; singleton and arbitrary nonempty directed index sets; `N = G`;
empty or absent trivial-normal families under the conditional clause; and all
coefficient, group, category, and index universes. No edge case covered by the
node is excluded by the Lean binders.

Independent searches run during this second reading:

- LeanSearch: "Right derived invariants for profinite groups preserve directed
  unions of discrete modules" returned eight related results (the invariants
  adjunction, module direct limits, and condensed/profinite constructions), with
  no match for the three-clause assertion.
- LeanFinder: "Cohomology of discrete profinite group modules preserves filtered
  unions and inflation colimits" returned eight results, including topological
  continuous cohomology and condensed/profinite colimit constructions. None
  gives this theorem about arbitrary discrete integer representations.
- Loogle: `"continuousCohomology", "colimit"` returned no result.
- Direct `rg` searches of Mathlib representation theory, all upstream
  `WeilConjectures`, project `lean/Sheaf`, and `dag/lean_names_upstream.json`
  used `inflation`, `filtered.*cohomology`, `cohomology.*[Cc]olimit`,
  `continuousCohomology`, and all ten proposed declaration names. There is no
  declaration collision or existing theorem for these three clauses. Mathlib's
  continuous-cohomology definition has topological representation coefficients;
  the project's integer-cochain effaceability theorem supplies only part (1)'s
  infrastructure. Its exact signature was read, as were the integer-invariants
  infrastructure and the recorded delta-functor source (including Hom and
  IsUniversal).

The four statement dependencies and their recorded source declarations were
opened. `def-sp-left-exact-additive` has a Mathlib match rather than a project
Lean module; `Functor.rightDerived` is the matching injective-resolution
construction and is imported directly. No repair module or new definition node
is needed. The quotient-limit helper is a specialization of Mathlib's cone and
IsLimit notions; its data contains the actual quotient maps, not a choice of
maps. Compactness and the finite discrete quotients make the underlying Type
limit formulation equivalent to the source's profinite limit formulation.

No mismatch was found. The only editorial clarification is in this report: the
module uses the same explicit equivalent-category presentation already used by
its recorded integer-cochain dependencies, while the node states the category
intrinsically. The Lean file and node copy were otherwise left unchanged.

Second-reader validation: the prescribed `scompile.py` wrapper compiled the
sandbox and library-path module separately and cleanly (6.6 and 13.9 seconds).
Every theorem proof remains `sorry`; the data definitions are complete.
`lean.statement` was compared verbatim with the primary theorem signature,
and all exported helpers and sibling theorem names occur in `lean.declarations`.
