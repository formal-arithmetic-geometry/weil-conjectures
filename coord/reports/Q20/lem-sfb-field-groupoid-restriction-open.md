## Worker report

The module `Sheaf.AlgebraicGeometry.FieldGroupoidRestrictionOpen` states
`AlgebraicGeometry.field_groupoid_restriction_open` with a `sorry` proof. It also
constructs the actual middle projection `AlgebraicGeometry.groupoidRestrictionMiddle`
by composing `pullback.fst` and `pullback.snd`. This is an auxiliary map of this
item, not a new independent notion; its data contains no postponed proof or choice.

Source read: `literature/stacks-project/groupoids.tex`, the section Restricting
groupoids and Tag 02VB (`lemma-restrict-groupoid`), and
`literature/stacks-project/more-groupoids.tex`, Tag 04LQ
(`lemma-restrict-groupoid-on-field`), including its diagram and proof. The latter
proves more properties, but this node asks only for open and surjective.

Hypotheses and objects, clause by clause:

- A field k is `(k : Type u) [Field k]`; V is literally `Spec (CommRingCat.of k)`.
- R and the two potentially different source/target maps are `{R : Scheme.{u}}`
  and `(s t : R ⟶ Spec (CommRingCat.of k))`.
- The original identity, inverse and composition are the explicit binders `e`,
  `i`, `c`; their types are V → R, R → R and `pullback s t → R` respectively.
  `(hG : IsGroupoidScheme s t e i c)` is exactly the recorded absolute groupoid
  predicate, without the additional relative equation s = t.
- Any field extension K/k is `(K : Type u) [Field K] [Algebra k K]`, with its
  specified ring map `algebraMap k K`. There is no algebraicity, finite-type,
  separability, perfection or finite-presentation hypothesis. The ambient universe
  u is arbitrary; fields originally of different sizes may both be placed in a
  common ambient universe. No quantifier over test schemes has a smaller
  independent universe that could make a condition vacuous.
- V_K is `Spec (CommRingCat.of K)`, and q is written in full throughout as
  `Spec.map (CommRingCat.ofHom (algebraMap k K))`.
- The restricted arrow scheme is literally
  `pullback (groupoidSaturationMap s t q) q`, where the imported definition expands
  `groupoidSaturationMap s t q` to `pullback.snd q t ≫ s`. It is thus
  `(V_K ×[V,t] R) ×[s,V] V_K`, with the node's factor order, rather than a
  base change that identifies the two possibly different maps s and t.
- The two fibre-product compatibility equations give the triple conditions
  `t(r) = q(u)` and `s(r) = q(v)` on every test scheme.

Conclusions, clause by clause:

- The restricted source is the existing `groupoidRestrictionSource s t q`,
  definitionally the last endpoint projection. The restricted target is the
  existing `groupoidRestrictionTarget s t q`, definitionally the first endpoint
  projection. These give exactly s_K(u,r,v) = v and t_K(u,r,v) = u.
- The existentially supplied maps eK, iK and cK have precisely the types of
  restricted identity, inverse and composition on this fixed arrow scheme.
  Their `IsGroupoidScheme` conjunct gives all groupoid laws, with the same
  source/target and composition orientation as the dependency.
- `eK ≫ groupoidRestrictionMiddle s t q = q ≫ e` gives the identity's middle
  component. The two unit source/target identities force both endpoints to be
  u, so this is exactly e_K(u) = (u,e(q(u)),u). Pullback uniqueness determines
  the morphism; it is not an arbitrary existential groupoid structure.
- `iK ≫ groupoidRestrictionMiddle s t q = groupoidRestrictionMiddle s t q ≫ i`
  gives the inverse's middle component. The inverse source/target laws exchange
  endpoints, hence i_K(u,r,v) = (v,i(r),u).
- The universal clause over every test scheme T and composable maps a,b states
  that the middle coordinate of `pullback.lift a b h ≫ cK` is composition of
  their two middle coordinates using c. Its proof argument hm just expresses
  their induced composability downstairs: from h, pullback compatibility gives
  `s(r) = q(v) = t(r')`. Thus hm always exists; quantifying over its proof is
  not an additional hypothesis on the original data or a vacuous condition.
  The composition source/target laws force the two outer endpoints, giving
  c_K((u,r,v),(v,r',w)) = (u,c(r,r'),w). This formula is for every T and hence is
  natural under precomposition; all operations are scheme morphisms.
- `Surjective (groupoidRestrictionMiddle s t q)` expresses surjectivity on
  underlying topological spaces, using Mathlib's scheme-morphism class.
- `IsOpenMap (groupoidRestrictionMiddle s t q)` is the literal open-image
  condition on the underlying map, with no quasi-compactness or finiteness added.

Dependency declarations read and used:

- `Field`, `Mathlib.Algebra.Field.Defs`, for `def-weil-field`.
- `Algebra` and `algebraMap`, `Mathlib.Algebra.Algebra.Defs`, for
  `def-pc-field-extension`.
- `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`, for `def-weil-affine-spectrum`.
- `AlgebraicGeometry.IsGroupoidScheme`,
  `Sheaf.AlgebraicGeometry.GroupoidScheme`, for `def-a1-groupoid-scheme`.
  Its complete structure and explicit pointwise laws were read.
- `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd` and
  `pullback.lift`, `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  for `def-pc-fibre-product`; existence for schemes is imported by GroupoidScheme.
- `AlgebraicGeometry.groupoidSaturationMap`, `groupoidRestrictionSource` and
  `groupoidRestrictionTarget`,
  `Sheaf.AlgebraicGeometry.CohenMacaulayGroupoidDoubleRestriction`. The already
  definition node `def-sfb-groupoid-restriction-projections` owns these existing
  plain definitions and is cited in stmt_deps. No theorem or Cohen-Macaulay
  hypothesis from that module is used. This repairs H2 of the returned delivery.
- For the proof plan, plain imports include
  `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen` and
  `Mathlib.AlgebraicGeometry.PullbackCarrier`. The first contains the recorded
  universally-open instance for an integral singleton target, the match of
  `lem-sc-scheme-over-field-universally-open`; the second contains
  `Surjective.instIsStableUnderBaseChangeScheme`, the recorded match of
  `lem-weil-pbc-surjective-base-change`. Their full instance signatures and
  surrounding source were read. These are proof imports, not new hypotheses.

Edge cases checked before drafting and on rereading: K = k; a trivial groupoid
on Spec k, whose restriction becomes the pair groupoid of Spec K over Spec k;
inseparable and transcendental extensions; different s and t; arbitrary
non-finite-type arrow schemes. The arrow scheme cannot be empty under the
original hypotheses, because the identity comes from a nonempty field spectrum.
The empty test scheme causes no difficulty: all displayed equations still make
sense. Both source and target conventions agree with the node and Tag 02VB.

Searches for an existing declaration (all msearch invocations used group Q20
and item lem-sfb-field-groupoid-restriction-open):

- LeanFinder: `Restriction of an absolute groupoid scheme along any field
  extension has an open surjective middle arrow projection`. Eight hits on
  joint surjectivity, open-cover gluing and affine-space surjectivity; none is
  a scheme-groupoid restriction result.
- LeanSearch: `Restriction of an absolute scheme groupoid along a field
  extension has open surjective projection to its original arrow scheme`.
  Eight hits, all on ordinary scheme restriction to opens, not this statement.
- Loogle: `IsGroupoidScheme, pullback, IsOpenMap`. No hits; IsGroupoidScheme is
  unknown to the Mathlib search service.
- msearch grep in Mathlib/AlgebraicGeometry:
  `GroupoidScheme|restrict.*[Gg]roupoid|[Gg]roupoid.*restrict`. No hits.
- rg of `lean/WeilConjectures` for the item id, GroupoidScheme and groupoid
  restriction found only an unrelated invariant-affine-neighbourhood docstring;
  no declaration matches this theorem. The prescribed item-id search likewise
  found no existing upstream declaration.
- rg of `lean/Sheaf` found the existing absolute IsGroupoidScheme definition,
  the three plain projection helpers reused above, a restriction in `Over S`
  for fppf quotient statements, and open invariant restrictions. The `Over S`
  helper uses the opposite endpoint order and a different carrier category;
  it does not replace the actual Scheme pullback projection here. None states
  arbitrary field restriction with the requested two topological conclusions.
- The recorded `def-sfb-restricted-groupoid-relation` was read: it owns the
  `Over S` relation in source-first order and supplies no operations. The present
  statement reuses the already existing plain Scheme projection helpers instead.
- Name checks in `dag/lean_names_upstream.json`, `lean/WeilConjectures`,
  `lean/Sheaf` and Mathlib found no declaration named groupoidRestrictionMiddle
  or field_groupoid_restriction_open.

No statement correction or disputed statement is needed. The repair adds the
definition ownership node def-sfb-groupoid-restriction-projections and cites it
in place of the theorem node in stmt_deps. The item changes only lean and stmt_deps. Compilation through scompile.py succeeds for both its sandbox
and final module-name checks. A parenthesis typo in the initial draft was repaired;
the final compile reports no errors or warnings.

## Second reading by Q20

I performed a separate second pass with the node statement, the imported
IsGroupoidScheme structure, the source/target helper definitions and this final
module open. This is a single dispatcher worker; no independent second agent
was started, as instructed. Independent review remains with the maintainer.

I checked the first endpoint is target and the last is source, that c(a,b) has
s(a) = t(b), that the original maps s and t are not identified, and that the
identity, inverse and composition middle formulas plus the groupoid laws force
all three coordinates in every displayed formula of the node. I also checked
that hm is derived from the pullback conditions and h for every composable pair,
so the universal clause does not lose any pair. The two topological conjuncts
refer to the defined middle projection, never an arbitrary map. Every field and
groupoid hypothesis above has its corresponding binder and no finiteness or
perfectness assumption appears. The new definition node owning the existing helper declarations is recorded in
stmt_deps; it depends only on schemes and fibre products, so no cycle arises. No mathematical mismatch was found;
only the initial syntax typo needed correction. Definitions have real data,
and the sole theorem proof remains `sorry` for stage 2.


## New nodes

`def-sfb-groupoid-restriction-projections` gives definition ownership to the
three existing plain Scheme definitions in
`Sheaf.AlgebraicGeometry.CohenMacaulayGroupoidDoubleRestriction`, with
`existing: true`. No new Lean module is added and no declaration is moved or
copied. For arbitrary schemes U,R,B and morphisms s,t,g, its first clause
W = B ×[g,U,t] R and h = s ∘ π_R is precisely
`groupoidSaturationMap s t g := pullback.snd g t ≫ s`. Its arrow scheme
R_B = W ×[h,U,g] B is the type of the other two declarations.
Its source b is `groupoidRestrictionSource s t g := pullback.snd h g`;
its target π_B ∘ a is
`groupoidRestrictionTarget s t g := pullback.fst h g ≫ pullback.fst g t`.
The fibre-product compatibility equations give g(u) = t(r) and s(r) = g(v),
with source v and target u on every test scheme. No groupoid law or finiteness
is a parameter of any declaration. Empty B or R and g = id give the same
canonical projections, so no edge case is excluded.

Source: Tag 02VB's defining diagram, read together with saturation h in
Tag 04MX. LeanSearch query "Scheme groupoid restriction projections from the
iterated fibre product, with source last endpoint and target first endpoint"
returned unrelated fibres, abstract groupoids and group objects. LeanFinder
query "Restriction of a scheme relation along a morphism by two pullbacks,
source last and target first, saturation map" returned pullback-cover
constructions. Mathlib grep for the three exact names returned zero hits.
Project grep found exactly the three existing definitions, and DAG grep found
only their listing in the theorem node lem-sfb-cm-groupoid-double-restriction.
Blueprint search "groupoid restriction projections" returned no matches.
These raw service results are recorded in the new node's mathlib_searches.
The existing def-sfb-restricted-groupoid-relation is the different source-first
Over S interface, not an owner of these Scheme declarations. The new node thus
adds ownership of existing definitions rather than a second definition.

## Returned delivery repair

H2 at immutable head `4fad425c2c87`: the previous stmt_deps incorrectly used
the theorem lem-sfb-cm-groupoid-double-restriction as owner of its plain helper
definitions. Added def-sfb-groupoid-restriction-projections with existing:true
on precisely groupoidSaturationMap, groupoidRestrictionSource and
groupoidRestrictionTarget in their original module. Replaced the theorem
id in the item's stmt_deps with this definition id. The original mathematical
statement, proof plan and Lean module are unchanged. Compared with current
main before repairing: the returned item differed only in lean and stmt_deps;
the repaired node is based on current main with exactly those authorized deltas.
The delivery wrapper refreshes and constructs the commit on the current base.

Repair second pass: read the new node beside all three full definition bodies
and confirmed parameter-by-parameter and projection-by-projection agreement.
The source/target order matches the consumer's node and Lean. The new node's
only dependencies are def-pc-scheme and def-pc-fibre-product, both cited in its
statement; no theorem dependency or theorem choice remains. It records the
existing declarations and has no Lean file, as requested. Main Lean SHA256
remains 059de91ac4b3d28265193fa86a48c10ddf01e481ede364bcef6ff041a9c9fba2.
