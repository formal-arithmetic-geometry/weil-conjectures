## Worker report

`Sheaf.AlgebraicGeometry.DmFiniteInertiaAffineRelation` states
`CategoryTheory.dm_finite_inertia_affine_relation`, with one `sorry` and no new
definitions. The natural-language statement is unchanged. Read the source paragraphs
in Stacks 0CL0, 0DU3/0DU4 (initial chart argument), 03XX, 04T4, 04WY and 050Q.
The current blueprint unit is `sec-six-functors-basics/sk-thm-sf-ctf-stability`;
this is a prerequisite in its direct-image argument, not the unit proposition.

Hypotheses and clauses:

- `{S : Scheme.{u}}` is arbitrary. `X : BasedCategory.{v, w} (Over S)` and
  `hX : IsDeligneMumfordModuliStack X` give the stack. The explicit independent
  universes u, v, w impose no equality on object/morphism universes. No field,
  Noetherian, quasi-compact or separated-base assumption is added.
- `hfinite : IsRepresentableFiniteModuliMap (moduliInertiaProjection X)` uses
  the actual vertical-automorphism inertia with conjugating arrows. Every scheme
  2-base change is a finite scheme, with projection compatibility.
- `V : Over S`, `[IsAffine V.left]`, the based functor a, representability ha,
  and `IsEtaleModuliMap a` render exactly the affine representable etale chart.
  No surjectivity hypothesis is present.
- `R : Over S` is a scheme. The equivalence E to `moduliTwoFiberProduct a a`
  identifies it with the isomorphism-triple relation; the two `ModuliTwoIso`
  comparisons identify both projections with the chosen S-maps s and t.
- e, i, c and the recorded `IsGroupoidScheme` give identity, inversion and
  composition on all scheme points. The quotient presentation additionally
  identifies original arrows with isomorphisms of chart objects and their
  composition with c. Thus this is the isomorphism-triple groupoid, without
  replacing it by an orbit relation or assuming a monomorphic relation map.
- Each projection has all five requested properties explicitly: `IsSeparated`,
  `Etale`, `Flat`, `LocallyOfFinitePresentation`, and
  `Scheme.Hom.IsLocallyQuasiFinite`. The last is the recorded Stacks predicate
  including local finite type. Separatedness means closed-immersion diagonal.
- The product in `Over S` is V times_S V. The pullback of `prod.lift s t`
  along `prod.lift (𝟙 V) (𝟙 V)` is exactly G; the `IsFinite` clause applies
  to its second projection G -> V, not to R -> V.
- For each `v₀ : V.left`, r has source
  `Over.mk (V.left.fromSpecResidueField v₀ ≫ V.hom)` and underlying scheme map
  `V.left.fromSpecResidueField v₀`. The canonical `Over.homMk ... rfl` exists
  and is unique, so universally quantifying this presentation neither restricts
  points nor adds an assumption. The source of the fibre E is the representable
  presheaf of the actual pullback G times_V Spec kappa(v₀). Its target is the
  inertia test by `((discreteModuliMap (yoneda.map r)).comp a)`.
  `IsSchemeModuliBaseChange E (pullback.snd ... r)` includes equivalence and
  the projection comparison: precisely representation of automorphisms of a(v₀)
  on every scheme over its residue field, not just rational automorphisms.
- `W : OpenModuliSubstack X` is strictly full and pullback stable, with open
  scheme tests. b factors a with `b.comp (fullModuliInclusion X W.property) = a`.
  The full-subcategory lift makes this equality possible without an extra
  strictification hypothesis.
- `SchemeGroupoidQuotientPresentation s t e i c W.category b` characterizes
  the fppf quotient: actual fppf stack descent, the vertical natural arrow
  isomorphism, bijection on original arrows, local lifting of every object and
  compatibility with c. W itself is a representative of [V/R]; no second
  stackification or arbitrary orbit bijection is chosen. Its full inclusion,
  with the displayed chart equality and arrow maps, is the canonical quotient
  functor. This states its identification with W up to the usual stack equivalence.
- `W.pointImage = Set.range (moduliSchemePointMap a)` is exactly the image of
  the ordinary scheme point space. `IsOpen W.pointImage` gives openness in the
  existing atlas topology; `IsDeligneMumfordModuliStack W.category` gives DM.
  `ModuliSchemeTest @IsOpenImmersion` of the same inclusion means representable
  open immersion, and `IsEtaleModuliMap` states its etaleness.

Dependency declarations read (module suffixes below are under
`Sheaf.AlgebraicGeometry` unless otherwise stated):

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `IsAffine`.
- `def-weil-size-convention` is a metatheoretic universe convention with no
  declaration; explicit universe levels render it.
- `StablePointedModuliGroupoids`: `discreteModuli`, `discreteModuliMap`,
  `ModuliTwoIso`, `moduliTwoFiberProduct`, `moduliTwoFiberFst`,
  `IsDeligneMumfordModuliStack`, `IsRepresentableByAlgebraicSpaces`,
  `HasSpaceBaseChange`, `SpaceMapIsEtale`. Read full definitions and docstrings.
- `AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`, `IsEtale`,
  publicly imported by the moduli-groupoid dependency and used by its chart tests.
- `GroupoidScheme`: `AlgebraicGeometry.IsGroupoidScheme`, all pointwise laws.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology`, used in the
  existing quotient presentation and imported through it.
- `Sheaf.CategoryTheory.GroupoidStackificationLocalDescription`:
  `CategoryTheory.Pseudofunctor.exists_groupoid_stackification_local_description`;
  its full signature/docstring were read, and it is imported for the proof plan.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale` (the recorded old name
  is a deprecated alias; this is the actual nondeprecated declaration).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `Scheme.Hom.IsLocallyQuasiFinite`, including the finite-type condition.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`,
  through `IsSeparated` in `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.fromSpecResidueField`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, also used in `Over S` for the relative product/fibres.

The only added statement dependencies are already landed definition nodes:
`def-sfb-moduli-inertia` (`ModuliInertia`, `moduliInertiaProjection`),
`def-sfb-finite-stack-scheme-tests` (`FiniteStackSchemeTests`,
`IsRepresentableFiniteModuliMap`), `def-sfb-dm-stack-morphism-properties`
(`DmStackMorphismProperties`, `ModuliSchemeTest` and point maps),
`def-sfb-open-moduli-substack` (`OpenModuliSubstack`, `OpenModuliSubstack`,
`fullModuliInclusion`, `moduliTwoFiberSnd`), and
`def-sfb-scheme-groupoid-quotient-presentation` (`SchemeGroupoidQuotientPresentation`,
`SchemeGroupoidQuotientPresentation`). Their records and definitions were read in
full. No new node or dependency repair is needed. The actual point-image and
scheme-point constructions are reused from the recorded proof modules
`StackTopologyOpenSubstacks` and `StackPointTopologyFlatLfpOpen`.

All proof dependencies with recorded modules are imported. Public imports include
those used in the statement. The remaining plain imports are
`EtaleSmoothAtlasFppfDescent`, `SeparatedEtaleSpaceScheme`,
`EtaleSpaceLocallyQuasiFinite`, `StackChartwiseSmoothEtaleCalculus`, and
`GroupoidStackificationLocalDescription`. Other proof nodes have no module recorded
and remain named step by step in the proof docstring; no theorem was proved here.

Edge cases: empty V gives empty R and W and vacuous residue fibres; empty X;
identity or open-immersion chart gives the trivial stabilizer; a finite etale chart
of BG permits nontrivial finite stabilizers (R is not forced mono); nonseparated S
is allowed; R need not be quasi-compact; arbitrary characteristic, nonreduced tests
and arbitrary residue fields are included. There is no algebraic-closure or
rational-point restriction on the fibre-representability clause.

Searches for the whole statement (none matched; component definitions were reused):

- `msearch.py leansearch`: “Affine etale chart of finite inertia Deligne Mumford
  stack separated self relation quotient open image”: 8 scheme etale/affine/separated
  hits, no stack theorem.
- `msearch.py leanfinder`: “An affine etale chart of a Deligne Mumford stack with
  finite inertia has a separated scheme self relation and its quotient is the open
  image”: 8 scheme etale/separated hits, no stack theorem.
- `msearch.py loogle`: `"AlgebraicStack", "IsSeparated"`: 0 hits.
- `msearch.py grep`: `finite.inertia|FiniteInertia|Deligne.Mumford`: 0 Mathlib hits.
- `rg` in `lean/WeilConjectures`: `finite.inertia|FiniteInertia|affine.relation`:
  only an unrelated ring-inertia comment; the item id has no match.
- `rg` in `lean/Sheaf/AlgebraicGeometry` and `CategoryTheory` for inertia,
  self-relation and open-substack names found the reused interfaces. Read
  `AffineEtaleRelationSeparatedQuasiFinite`: it assumes R already a scheme and
  its relation map mono, so misses nontrivial stabilizers. Read
  `FiniteFlatAffineGroupoidModuli`: it assumes finite locally free projections
  over a field and proves coarse properties; it is not this theorem.

Validation: scompile.py accepted the module against the live published server
library and current landed imports, without errors or unexpected warnings.
`autoImplicit false` is set; there is no file-local notation, private definition,
helper axiom or arbitrary chosen construction. No statement correction or dispute.

## Second reading by Q37

No independent worker was started: the dispatcher's brief forbids other agents;
the maintainer independently reviews the delivery. Self-check with node and module
open: both relation projections are pinned; G -> V is finite; the actual residue
fibre retains its projection; the fppf quotient presentation retains original
arrows and composition; and W's point space is the actual chart image. No mismatch
or statement change was found.
