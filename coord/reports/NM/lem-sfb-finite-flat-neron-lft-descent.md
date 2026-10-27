## Worker report

The item is stated by `AlgebraicGeometry.exists_neronLftModel_of_finite_faithfullyFlat`
in `Sheaf.AlgebraicGeometry.GroupScheme.FiniteFlatNeronLftDescent`. Its only proof is
`sorry`. The statement reuses Q92's shared predicate `AlgebraicGeometry.IsNeronLftModel`
from `Sheaf.AlgebraicGeometry.NeronLftModel`; this repair introduces no definition.
The original statement, proof, proof dependencies and all other original node fields
are retained; only `lean` and the additional definition dependency change.

I read BLR §10.1 Definition 1 and Proposition 4 in the primary-source scan,
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf,
printed pp.289–291, PDF pages 295–297, and the current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`.
The local BLR PDF is absent, as the original node already records. The source describes
smooth separated lft models with the Néron mapping property and descent to a smooth
closed subgroup. The more specific commutative finite-type setting of this item is
retained exactly. No modification to a blueprint unit is needed.

Hypothesis and conclusion correspondence:

- The domains D and D' are `(D D' : Type u) [CommRing D] [CommRing D']` and
  `[IsDedekindDomain D] [IsDedekindDomain D']`. Mathlib gives Noetherian,
  integrally closed domains of dimension at most one. `hD : ringKrullDim D = 1`
  and `hD' : ringKrullDim D' = 1` express the item's exact dimension-one convention.
- The ring inclusion is `algebraMap D D'` with `hinj : Function.Injective ...`.
  A specified ring map is equivalently specified by its algebra structure.
  `[Module.Finite D D']` is the required finite generation as a module, and
  `[Module.FaithfullyFlat D D']` is precisely the recorded faithfully flat notion.
- E and E' are the canonical `FractionRing D` and `FractionRing D'`. Their induced
  field embedding is `IsFractionRing.map (K := FractionRing D)
  (L := FractionRing D') hinj`. It is constructed by localization, not an arbitrary
  field map. Choosing the canonical fraction fields only fixes the meaning of Frac;
  the canonical fraction fields give the same objects used by the shared model predicate.
- S and S' are `Spec (.of D)` and `Spec (.of D')`, and their generic inclusions are
  `Spec.map (CommRingCat.ofHom (algebraMap D (FractionRing D)))` and its D' version.
- `G H : Grp (Over (Spec (.of (FractionRing D))))` are group schemes with the
  multiplication, identity, inverse and all group diagrams carried by `GrpObj`.
  `[IsCommMonObj G.X]` imposes commutativity of G. `[Smooth G.X.hom]` and
  `[IsSeparated G.X.hom]` impose smoothness and separatedness. Finite type is
  `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]` exactly as recorded by
  def-weil-finite-type-morphism.
- H is smooth through `[Smooth H.X.hom]`. The inclusion `i : H ⟶ G` is a
  homomorphism of the bundled group objects; `[IsClosedImmersion i.hom.hom.left]`
  asserts that its underlying scheme morphism is a closed immersion. Commutativity
  and separatedness of H follow from this inclusion and are not extra hypotheses.
- `((Over.pullback (Spec.map (CommRingCat.ofHom (IsFractionRing.map ...)))).mapGrp.obj G)`
  is G_E': the existing pullback functor acts on the actual group structure through
  `Functor.mapGrp`. `hmodel : ∃ N' e', IsNeronLftModel N' G_E' e'`
  is existence of the specified Néron lft-model over S'. It places no additional
  commutativity or quasi-compactness requirement on the given model.
- The conclusion `∃ N e, IsNeronLftModel N H e ∧ IsCommMonObj N.X`
  provides a group scheme N over S and its specified generic group isomorphism e.
  The shared predicate expresses smoothness, separatedness, and bijectivity of
  generic restriction for every smooth S-scheme. Smoothness implies lft. The
  commutativity conjunct is imposed on the integral model, exactly as requested.
- The hypothesis existentially quantifies the model N' over S' and its generic
  group isomorphism e' with the base-changed G. It imposes neither commutativity
  nor quasi-compactness on the supplied model; these would be extra hypotheses.
- Both generic isomorphisms are in `Grp (Over (Spec E))` (or the E' version).
  The restriction maps of the shared predicate concern all scheme morphisms of
  smooth test schemes, without imposing a group structure on the test schemes.
- The identity case is admitted by `H = G`, `i = 𝟙 G`; identity maps are closed
  immersions. The item asserts no separate additional construction in that case.

Dependency declarations read and used:

- def-sfb-neron-lft-model: `Sheaf.AlgebraicGeometry.NeronLftModel`,
  `AlgebraicGeometry.IsNeronLftModel`. Read the full current server source through
  `scompile.py --source`. It takes the model N, generic group V and specified
  generic group isomorphism e over a fraction field of the domain. Its data are
  smoothness, the closed-immersion condition on the diagonal, and bijectivity
  of generic restriction for every smooth test scheme in universe u.
- def-pc-scheme and def-weil-affine-spectrum: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec` and `Spec.map`.
- def-pc-base-change: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`,
  whose source explicitly identifies scheme base change with `Over.pullback`.
  `Scheme.Modules.moduleBaseChange` itself concerns modules and is not substituted
  for scheme base change. The removed duplicate supporting module had imported
  that convention; the revised item uses the canonical `Over.pullback` directly.
- def-sbc-smooth-morphisms: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `Smooth`.
  This is the current name; the deprecated `IsSmooth` alias is not used.
- def-weil-closed-immersion: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `IsClosedImmersion`. `IsSeparated` from Morphisms.Separated is exactly the
  closed-immersion condition on the diagonal, with no replacement definition.
- def-weil-finite-type-morphism: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `LocallyOfFiniteType`, and Morphisms.QuasiCompact, `QuasiCompact`.
- def-sc-group-scheme: `Mathlib.CategoryTheory.Monoidal.Grp`, `Grp`, `GrpObj`,
  `IsCommMonObj` and the group-object homomorphisms. I read the explanatory source
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` as well as the Mathlib
  signatures. `Mathlib.CategoryTheory.Monoidal.Cartesian.Over` supplies the
  monoidal pullback used by `Functor.mapGrp`.
- def-weil-finitely-generated-module: `Mathlib.RingTheory.Finiteness.Defs`,
  `Module.Finite`.
- def-weil-pbc-faithfully-flat-ring-map:
  `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`, `Module.FaithfullyFlat`.

Already stated proof inputs are imported non-publicly: AlgebraicSpaceFpqcSheaf,
EnlargedEtaleRingedSite, GroupScheme.HomomorphismFactorization, and
LfpSmoothFlatBaseChange. Smooth-flat and closed-immersion base change are available
from Mathlib. The three statement-only proof dependencies for Weil restriction,
generic subgroup closure and group smoothening have no Lean records in this read
snapshot, so there are no modules to import for them yet; their exact ids and role
remain in the proof docstring and the node. They are proof inputs, not missing
notions needed to type this statement.

Edge cases checked before writing:

- No finite-type or quasi-compactness requirement is placed on either model or
  on smooth test schemes; this allows the infinite-component lft models of tori.
- Empty and disconnected smooth test schemes are included: X is arbitrary in
  `Over (Spec D)`. There is no nonempty, affine, connected or finite-type binder.
- No perfectness, excellence, separability, characteristic-zero or unramified
  assumption is added. Inseparable fraction-field extensions are permitted.
- The trivial group and identity subgroup inclusion are permitted. An empty
  group scheme over a nonempty field is correctly excluded by its identity section.
- Dimension-zero domains (fields) are excluded precisely because the original
  item explicitly defines Dedekind domain to have dimension one, rather than
  because of a hidden Mathlib convention.
- Rings, their fraction fields, models and tests use one arbitrary common universe
  u; tests do not range in an independent smaller universe that could make the
  condition vacuous. All binders and the universe are explicit.
- Models have their own specified group structure and group isomorphism; a mere
  isomorphism of underlying schemes, an arbitrary comparison map, or arbitrary
  choice of a model was not inserted as a definition.

Searches made:

- `msearch.py ... leanfinder`: "Neron locally finite type models descend along
  finite faithfully flat extensions of Dedekind domains" returned eight general
  finite-type/smoothness facts, not Néron descent or a model definition.
- `msearch.py ... loogle '"Neron"'`: zero hits.
- `msearch.py ... leansearch`: "Definition of a Neron locally finite type model:
  smooth separated group scheme and bijection on Hom from every smooth scheme"
  returned eight general smoothness and local finite presentation/type facts.
- `msearch.py ... grep 'Neron|Néron|NeronModel'`, globally and under
  AlgebraicGeometry: zero hits. The original raw tool records remain in sandbox `searches.jsonl`; these
  initial searches predated Q92's reviewed shared definition.
- `rg -n 'Neron|Néron|neron' lean/WeilConjectures lean/Sheaf`: no hits, including
  no declaration carrying this item's id. The original source has no Néron API.
- DAG search for `Néron lft-model|NeronLft|Néron.*model` found sixteen statement
  nodes that explain the notion inline at the original search time. The return
  identifies the subsequently reviewed shared definition node owned by Q92.
  `tools/blueprint_refs.py search 'Néron'`: zero blueprint nodes. Ancestor lookup
  for this item gives None, matching its existing blueprint metadata.

## Repair of return H4/H12/H13

Returned head: 5aeaf671e92e. Q92's reviewed delivery c84990108 owns
`def-sfb-neron-lft-model`, with declaration `AlgebraicGeometry.IsNeronLftModel`
in `Sheaf.AlgebraicGeometry.NeronLftModel`.

The duplicate structure `AlgebraicGeometry.NeronLftModel` and its entire module
`Sheaf.AlgebraicGeometry.GroupScheme.NeronLftModel` have been removed from this
sandbox. The duplicate definition-node JSON copy has also been removed; this
repair does not overwrite Q92's node. The item's `stmt_deps` retains the shared
node id. The theorem now imports Q92's module, existentially quantifies N' and
its generic group isomorphism in the hypothesis, and existentially quantifies
N and its generic group isomorphism in the conclusion, with
`IsNeronLftModel N H e ∧ IsCommMonObj N.X`. This is a substantive interface
repair, not an unchanged re-push. All other mathematical hypotheses, the proof
plan and the original natural-language statement are retained.

The required shared module is now published. Its full live source was read with
`scompile.py --source Sheaf.AlgebraicGeometry.NeronLftModel`; its three explicit
arguments match the revised theorem. The delivery dry run compiled both the sandbox
and the library module and passed preflight on the current base. No duplicate node
or module is included in the repair. `set_option autoImplicit false` explicitly
checks that the declaration introduces no auto-bound variables.

No STATEMENT-DISPUTED finding or statement correction.

## Second reading by NM

This is the author's second pass, not an independent worker review; the dispatcher
prohibits other agents and the maintainer supplies the independent review. The
repair removes both duplicate files and uses the shared declaration requested in
the return. The theorem has existentially specified group isomorphisms in both
the hypothesis and conclusion, with commutativity asserted only on G and the
resulting integral model. The remaining hypothesis and edge-case correspondence
is unchanged from the review, which explicitly accepted it. The reviewed shared module is now available on the live base; the revised
theorem has passed the delivery dry run against it.

## Current validation status

2026-10-24 14:14 UTC: The required shared definition has landed. Read its full live source and its landed DAG record; `AlgebraicGeometry.IsNeronLftModel` has exactly the interface used here. The prescribed `scompile.py` compiled the final sandbox and library modules cleanly with no errors or warnings. The earlier successful dry run returned `OK (dry run): commit a2b0a5908e9 passes the preflight and compiles; nothing pushed`. A final dry run follows the report update and explicit `autoImplicit false` setting. The item signature is unchanged by that setting and remains synchronized with its Lean record. The duplicate definition module and node are absent.
