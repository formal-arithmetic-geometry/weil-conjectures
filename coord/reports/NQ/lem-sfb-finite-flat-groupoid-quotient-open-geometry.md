## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteFlatGroupoidQuotientOpenGeometry` states
`CategoryTheory.finiteFlatGroupoid_quotient_open_geometry`. Its only postponed proof is
that named theorem. The two real helper definitions `groupoidOpenChart` and
`groupoidOpenChartInclusion` package the existing open scheme and its inclusion in
`Over S`; neither chooses data from a theorem. There is no statement correction, dependency-module repair, or mathematical dispute.
The returned H2 dependency-ownership defect is repaired by the definition node described
below, recording two existing maps without introducing a new Lean definition.

Hypothesis and conclusion correspondence, checked with the node and module open:

- Arbitrary base scheme and size convention: `{S : Scheme.{u}}`, `{U R : Over S}`,
  and `Q : BasedCategory.{v, w} (Over S)`. All three universes are explicitly bound.
  No field, Noetherian, separated-base, characteristic, constant-rank, or nonempty
  hypothesis is imposed.
- The specified groupoid operations are `s t : R ⟶ U`, `e : U ⟶ R`, `i : R ⟶ R`,
  and `c : pullback s.left t.left ⟶ R.left`. The binder
  `hG : IsGroupoidScheme s.left t.left e.left i.left c` uses the recorded
  `def-a1-groupoid-scheme`. Endpoint maps in `Over S` make the operations over the
  stated base: the groupoid endpoint identities force the composition and inverse
  to respect the base, and the identity map is explicitly over it.
- Finite local freeness of BOTH projections is exactly
  `[s.left.IsFiniteLocallyFree] [t.left.IsFiniteLocallyFree]`, using the upstream
  class extending `IsFinite`, `Flat` and `LocallyOfFinitePresentation`.
- The quotient and its natural object map are `Q`, `p`, and
  `presentation : SchemeGroupoidQuotientPresentation s t e.left i.left c Q p`.
  This existing interface specifies the fppf stack, original arrow bijections,
  fppf local lifts and composition. Thus `Q` is the stackification `[U/R]` up to
  equivalence, with its actual natural map, not an arbitrary map to a DM stack.
  Its `Scheme.IsGroupoid` field gives the same groupoid laws as `hG`, in the
  existing presentation interface's equivalent formulation; it adds no condition.
- The DM hypothesis is exactly `hQ : IsDeligneMumfordModuliStack Q`.
- Scheme representability and the four asserted properties of `p` are one
  `ModuliSchemeTest (fun _ _ f ↦ Surjective f ∧ IsFinite f ∧ Flat f ∧
  LocallyOfFinitePresentation f) p`. For every scheme test this supplies a
  representing scheme, an equivalence with the actual 2-pullback, its projection
  comparison, and all four properties of that same scheme projection.
- The bijection is `∃ b : OpenModuliSubstack Q ≃ {V : U.left.Opens //
  s.left ⁻¹ᵁ V = t.left ⁻¹ᵁ V}`. This is a bijection of actual strictly full
  open substacks and actual invariant open subschemes, not just point subsets.
  `OpenModuliSubstack` is closed under all pullbacks and isomorphisms, and every
  scheme test of its full inclusion is represented by an open immersion.
- This bijection IS pullback along `p`: for every `W`, the first existential
  `a` is an equivalence from the representable open chart `(b W).val` to
  `moduliTwoFiberProduct p (fullModuliInclusion Q W.property)`, with
  `IsSchemeModuliBaseChange a (groupoidOpenChartInclusion U (b W).val)` identifying
  the projection with the actual open inclusion. This renders
  `U ×_Q W = V`, including the specified map to `U`.
- The map of the restricted presentation is `pV`. Its displayed `ModuliTwoIso`
  identifies `pV` followed by the full inclusion with the original map `p`
  precomposed by the actual inclusion `V → U`. Its `ModuliSchemeTest` asserts
  representability by schemes, surjectivity, finiteness, flatness and lfp again.
- `restrictedEtaleRelation s t (groupoidOpenChartInclusion U (b W).val)` is the
  EXISTING iterated pullback `V ×_U R ×_U V`. By its two pullback universal
  properties this is exactly `R ×_(U ×_S U) (V ×_S V)`, with the first and last
  endpoint maps `restrictedEtaleRelationSource/Target`. Those definitions have
  no etaleness assumptions despite their historical names.
- Both restricted projections are explicitly `.left.IsFiniteLocallyFree`.
- The final `Nonempty (SchemeGroupoidQuotientPresentation ... W.category pV)`
  says exactly `W ≃ [V/R_V]`, with the specified object map, original arrows,
  fppf stack and composition. The quantified restricted `eV`, `iV`, `cV` are
  normalized by their equations with `restrictedGroupoidMiddle` and
  `restrictedGroupoidComposableMap`. These equations specify the usual induced
  operations and prevent an unrelated groupoid structure from satisfying the
  assertion. They express the restriction in the node, rather than add a new
  mathematical conclusion. The original arrow two-isomorphism is natural and
  its bijection with all vertical arrows supplies the canonical restriction
  comparison; the object-map comparison is retained explicitly.
- Surjectivity of `|U| → |Q|` is `Function.Surjective (moduliPointMap p)`.
  The domain is the existing scheme-as-discrete-moduli point quotient, canonically
  the ordinary scheme points: a representative is a map from a field spectrum;
  the arrow relation identifies precisely field extensions over a fixed scheme
  point. This uses the existing point definition, without choosing an arbitrary
  function or bijection.
- The final implication starts with `IsAffine U.left`. Its conclusion is
  `HasProperModuliDiagonal (BasedCategory.ofFunctor (Q.p ⋙
  Over.map (AlgebraicGeometry.specULiftZIsTerminal.from S)))`.
  This is the SAME total category projected to schemes over `Spec(ULift ℤ)`.
  Thus the products in `HasProperModuliDiagonal` are over the integers, not over
  `S`. The predicate retains both scheme-test projections and asserts properness
  of the map to their product. For a DM stack a proper unramified space diagonal
  is finite and therefore scheme representable, so this scheme-test form is
  precisely the stated properness of the representable absolute diagonal.

The theorem docstring contains the node's complete nine-step proof plan, with the
individual DAG dependencies, including the order “descend affineness to obtain a
scheme, THEN descend finiteness”, fppf descent of invariant opens (not an incorrect
smooth-atlas shortcut), and the absolute properness triangle over the integers.
Every theorem proof in the delivered module is `sorry`.

Dependency declarations used (source signatures and docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`;
  the universe convention is implemented by the explicit universes above.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `IsFibredInGroupoids`,
  `ModuliTwoIso`, `moduliTwoFiberProduct`, `moduliTwoFiberFst`, `discreteModuli`,
  `discreteModuliMap`, and `IsDeligneMumfordModuliStack`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, its representability
  predicates, and its meaning in the DM and scheme-test definitions, through the
  recorded moduli modules. No second algebraic-space definition.
- `Sheaf.AlgebraicGeometry.GroupoidScheme`: `AlgebraicGeometry.IsGroupoidScheme`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology`, with its induced
  slice topology used by the recorded quotient presentation.
- `Sheaf.CategoryTheory.GroupoidStackificationLocalDescription`:
  `CategoryTheory.Pseudofunctor.exists_groupoid_stackification_local_description`,
  imported for the proof's fppf local-lift argument. The already landed
  scheme-quotient-presentation definition supplies the equivalent total-category
  interface for stating that quotient; a new pseudofunctor/total-category bridge
  or a second stackification is not introduced.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `.Flat`, `.FinitePresentation`,
  `.Proper`: respectively `IsFinite`, `Flat`, `LocallyOfFinitePresentation`,
  `IsProper`. These are exposed by the recorded morphism and moduli imports.
- `Sheaf.AlgebraicGeometry.SchemeGroupoidQuotientPresentation`:
  `SchemeGroupoidQuotientPresentation`, including its specified arrow map.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`: `OpenModuliSubstack`,
  `OpenModuliSubstack.category`, `fullModuliInclusion`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `ModuliSchemeTest`,
  `ModuliPoints`, `moduliPointMap`, with `IsSchemeModuliBaseChange` from
  `Sheaf.AlgebraicGeometry.ModuliChartNormalization`.
- `Sheaf.AlgebraicGeometry.ModuliStackProperties`: `HasProperModuliDiagonal`,
  valid for arbitrary base schemes; only its separate smooth-atlas definition
  is field-specific. `specULiftZIsTerminal` is Mathlib's integer spectrum.
- `Sheaf.AlgebraicGeometry.EtaleRelationRestrictionQuotient`:
  `restrictedEtaleRelation`, `restrictedEtaleRelationSource`,
  `restrictedEtaleRelationTarget`, owned by the already landed definition node
  `def-sfb-restricted-groupoid-relation`.
- `Sheaf.AlgebraicGeometry.FppfGroupoidRestrictionQuotient`:
  `restrictedGroupoidMiddle`, `restrictedGroupoidComposableMap`; only these
  real constructions are used, not its theorem with a covering hypothesis.

The item gains five already landed statement dependencies and one new definition owner for the interfaces in
its signature: `def-sfb-scheme-groupoid-quotient-presentation`,
`def-sfb-open-moduli-substack`, `def-sfb-dm-stack-morphism-properties`,
`def-sfb-moduli-stack-properties`, `def-sfb-restricted-groupoid-relation`, and
`def-sfb-restricted-groupoid-middle-maps`. This follows brief §5's permission
to add landed interfaces and new definition ownership. The theorem node
`lem-sfb-fppf-groupoid-restriction-quotient` is not cited in stmt_deps. No existing
node except the item is edited.
The additional statement dependencies do not depend back on this item.

All available proof-dependency modules are imported (plain imports): the local
stackification description, four-property fppf descent, fpqc finite descent,
fpqc open-subscheme descent, chartwise calculus, algebraic-stack fibre products,
and Mathlib relative gluing/properness. The other recorded general Mathlib leaves
are provided by these imports. The three proof nodes
`lem-sfb-flat-groupoid-algebraic-quotient`,
`lem-sfb-fppf-groupoid-stack-presentations`, and
`lem-sfb-representable-proper-fppf-target-test` have no Lean module on this base;
the docstring retains them in the proof plan. They are proof dependencies, not
missing notions required to type this statement, and are not restated here.

Edge cases checked before writing:

- Identity groupoid: `Q = U`, `p` is identity, every open is invariant; the
  correspondence and restricted presentations reduce to the usual open schemes.
- Empty object and arrow schemes, and empty/full invariant opens: no
  nonemptiness restriction, and the empty test scheme and empty covering sieves
  are admitted by the existing interfaces.
- A finite constant group in characteristic dividing its order: `BG` can still
  be DM, and the finite flat atlas need not be smooth or tame. No inversion of
  group order, smoothness of endpoints, or characteristic assumption is added.
- Nonreduced finite locally free relation and varying degrees: the full relation
  scheme is retained; no reducedness, fixed rank or etaleness is assumed.
- Nonseparated `S`: the last clause uses the absolute integer product, so it does
  not silently assert only relative separatedness over `S`. The affine hypothesis
  is imposed on `U`, exactly as in the node.

Searches for existing statements and notions:

- `msearch.py ... leanfinder "Finite locally free groupoid quotient stack has a
  finite flat surjective presentation and invariant opens correspond to open
  substacks"`: eight hits on scheme lfp, flat descent and universally open
  morphisms; no matching stack statement.
- `msearch.py ... loogle "AlgebraicGeometry.IsGroupoidScheme, IsFiniteLocallyFree"`:
  zero hits, unknown identifier `AlgebraicGeometry.IsGroupoidScheme` (a project
  definition, not a Mathlib declaration).
- `msearch.py ... grep "GroupoidScheme|OpenSubstack|quotientStack" AlgebraicGeometry`:
  zero Mathlib hits.
- `msearch.py ... leansearch "finite locally free groupoid quotient stack invariant
  open substack"`: eight hits on manifold groupoids and open-subgroup quotients;
  no algebraic-stack quotient statement.
- `rg` in `lean/WeilConjectures` for groupoids/fppf quotients and for this exact
  node id: no matching theorem; the invariant-neighbourhood results concern
  scheme groupoids, not open substacks.
- `rg` in `lean/Sheaf/AlgebraicGeometry` for quotient stacks, open substacks,
  groupoid schemes and absolute proper diagonals: found and reused all the
  interfaces above. `FiniteFlatAffineGroupoidModuli` is restricted to affine
  schemes over a field and states a different coarse-moduli theorem.
  `StackTopologyOpenSubstacks` concerns points of DM stacks; its proof invokes
  smooth-atlas invariant-open descent and cannot replace the present finite-flat
  presentation result. No existing theorem states all the present clauses.
- Checked `groupoidOpenChart` and `finiteFlatGroupoid_quotient_open_geometry` in
  both project roots: no existing declarations.

Sources read: the node, all twelve original statement dependencies and their
recorded declarations/docstrings; the additional landed interfaces above;
Stacks `stacks-more-morphisms.tex` lemma-well-nigh-affine (0DUM),
`stacks-properties.tex` lemma-substacks-presentation (0507), and
`stacks-morphisms.tex` lemma-properties-diagonal-from-presentation (0DTY);
the current blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/_section.md`. The item is a supporting lemma, not the unit's
own statement. Its historical alteration-subroute provenance is left intact.

Validation: every compile used the prescribed `scompile.py`. An initial public
import of `AlgebraicStackChangeBaseToIntegers` hit an overlay timeout; that import
was removed in favor of the existing proper-diagonal predicate on the explicit
composite projection, which is definitionally the same change of base. The server
confirmation then compiled the module cleanly (14.7 seconds); subsequent final
validation and delivery preflight are run on the exact delivered file.


## Returned delivery repair

H2 on immutable returned head `6d52852e716f`: the statement used only the two
plain helper definitions in `FppfGroupoidRestrictionQuotient`, but cited its theorem
node as their owner. The new definition node
`def-sfb-restricted-groupoid-middle-maps` now owns
`AlgebraicGeometry.AlgebraicSpace.restrictedGroupoidMiddle` and
`AlgebraicGeometry.AlgebraicSpace.restrictedGroupoidComposableMap`, with
`existing: true` on their current published module. The item replaces the erroneous
`lem-sfb-fppf-groupoid-restriction-quotient` statement dependency with this definition
node. The original Q59 node and its declaration list remain intact.

Compared the retained sandbox with current main: all original non-Lean fields agree;
main has no Lean record for the item. The delivery wrapper rebases this corrected packet
on current main. The Lean source, theorem signature, and all conclusions accepted by
the independent reviewer are byte-for-byte unchanged from the returned delivery.
The existing plain definitions have been reread: the middle map is the two successive
pullback projections; the composable-pair map is `pullback.map` with the middle map on
both factors and `q.left` on the base. The required squares are proved directly by the
pullback conditions, with no groupoid or covering hypothesis and no theorem choice.

## New nodes

`def-sfb-restricted-groupoid-middle-maps` records the two existing canonical maps from
the restricted relation and its composable pairs to the original relation and its
composable pairs. Source: Stacks `groupoids.tex`, Tag 02VB,
`lemma-restrict-groupoid` and its restriction diagram. The statement introduces
arbitrary `s,t,q` and the already recorded restricted relation and endpoint maps;
it imposes no groupoid, covering, monicity or etaleness assumption. `lean.statement`
is the verbatim main definition signature; `lean.declarations` names both existing
maps. There is no new Lean module and no duplicate definition. The new node depends
on `def-sfb-restricted-groupoid-relation`, not on the Q59 theorem. Its provenance
has the null ancestor returned by `blueprint_refs.py ancestor` and the item's via
chain prefixed by the item itself.

New-node searches (performed for this repair and recorded in its mathlib_searches):
LeanSearch query “restriction of a scheme groupoid middle projection and induced map
on composable pairs” returned scheme open-restriction lemmas and a manifold-groupoid
lemma; LeanFinder query “The restricted relation V times U R times U V has a middle
projection to R and a canonical map of composable pairs to the original composable
pairs” returned general relations and complex-shape projections. Neither matches.
Mathlib grep `restrictedGroupoidMiddle|restrictedGroupoidComposableMap` returned zero
hits. The exact same names in `lean/WeilConjectures` have no match. In `lean/Sheaf`
they are the two existing plain definitions in the Q59 module. DAG grep and an audit
of definition-node statements and lean records found no owning definition node;
only the Q59 theorem record lists the maps. `blueprint_refs.py search "restricted
groupoid"` returned zero blueprint matches. Thus existing:true ownership reuses the
exact published data and repairs the dependency without copying or replacing code.

The new node's small cases are unrestricted: empty schemes and empty restrictions
still have the same pullback projections; `q = identity` gives the original middle
coordinates; arbitrary q, including nonsurjective maps, does not need the covering
hypotheses of the Q59 theorem. The composable-pair map preserves the factor order:
the first/later arrow maps to the first/later arrow and likewise for the second.

Repair validation: rerun the prescribed single-file scompile.py on the unchanged
consumer and run deliver2.py --no-push, which also checks both existing definitions
in module-mode probes. Then redeliver through deliver2.py only.

## Second reading by NQ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
