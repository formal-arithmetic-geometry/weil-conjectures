## Worker report

Stage 2, Q43, 2026-10-19. This delivery states `lem-per-set-local-system-calculus`
in `Sheaf.AlgebraicGeometry.SetLocalSystemCalculus`. The five theorems have `sorry`
proofs. The action structure and three slice-site helpers have actual data. The item
changes only in `lean`; there are no new nodes, dependency repairs or statement changes.

The previous worker's stale-assignment diagnosis confused stages: the ledger entry at
2026-10-19 00:19 records Q127's stage-1 split, not a Lean statement. The current item
has `lean: null`. I use its reviewed nine-step split, without splitting it again.

Clause-by-clause rendering:

- X is a scheme: `X : Scheme.{u}`. Noetherian means `[IsLocallyNoetherian X]`
  and `[CompactSpace X]`, precisely the recorded locally Noetherian and quasi-compact
  definitions. No connectedness, nonemptiness, separatedness or geometric point is added.
- Set sheaves on the small étale site are `Sheaf X.smallEtaleTopology (Type (u + 1))`.
  Local systems are exactly the dependency's `Scheme.IsIndFiniteEtaleSheaf`, with its
  filtered colimit of actual finite étale representables, not a new predicate.
- Finite local systems are represented by objects of `X.FiniteEtale`, included in
  `X.Etale` by `ObjectProperty.ι _`, then represented by
  `X.smallEtaleTopology.uliftYoneda.{u + 1}`. `Scheme.FiniteEtale` is the existing
  full subcategory of finite objects of the étale site: objects are finite étale schemes
  and arrows are all base-scheme maps, the notion of the recorded generic Over interface.
- Clause (1), filtered union: `indFiniteEtale_filtered_union` gives a small filtered I,
  finite étale diagram D, and a natural transformation ι to the constant diagram at F.
  Each `ι.app i` is an ambient `Mono`, and `Cocone.mk F ι` is an ambient colimit.
  Thus its images are actual finite local-system subsheaves with filtered union F.
  The clause does not merely give another filtered presentation with noninjective legs.
- All small ambient colimits: `indFiniteEtale_colimit` quantifies over every small
  diagram D and every ambient colimit cocone c. If every D(i) is a local system, c.pt is.
  Ambient set sheaves already have these colimits; no additional existence hypothesis on
  the category is assumed. Using an arbitrary universal cocone avoids choosing a second
  colimit object. The full subcategory therefore has the same colimits.
- Finite ambient limits: `indFiniteEtale_finite_limit` makes the analogous assertion
  for every `FinCategory I` and ambient limiting cone. This includes the empty diagram.
- Clause (2), q and Y: `q : Y ⟶ X`, `[IsFinite q] [Etale q]`, with the same two
  Noetherian hypotheses on Y. Surjectivity and monomorphy are not assumed.
- The sheaf h_Y is `X.smallEtaleTopology.uliftYoneda.obj (Etale.mk q)`.
  `indFiniteEtale_total_space` supplies an equivalence ξ from set sheaves on Y to
  `Over h_Y`, whose forward direction is the specified total space over h_Y.
- The forward section equivalences ε identify its sections at U with
  `Σ a : U ⟶ Etale.mk q, E.obj.obj (op (localSystemLift q a))`.
  These arrows are exactly `Hom_X(U,Y)`; `localSystemLift` is the same scheme U with
  structural arrow a.left to Y. Étale cancellation supplies its étaleness through the
  existing site morphism instance. The first ε equation identifies the structural map to
  h_Y with the label a (unwrapping only Mathlib's universe lift).
- The second ε equation states restriction along b:V→U sends `(a,t)` to
  `(b ≫ a, E.map (localSystemLiftMap q b a).op t)`. The helper has underlying map b.left,
  with its actual commuting triangle. Thus the sigma presheaf has exactly the node's
  restrictions. Its being naturally isomorphic to the underlying presheaf of the sheaf
  `(ξ.functor.obj E).left` says precisely that this presheaf is already a sheaf. There is
  no sheafification substituted for the explicit formula. The third ε equation specifies
  the effect on every sheaf map, retaining the label and applying that map to t.
- The inverse section equivalences β identify `ξ.inverse.obj F` at V=(U,a) with the
  subtype of sections t of F on the composite U→Y→X satisfying `p(t)=a`.
  `localSystemLabel q V` is the actual arrow a in the X-site. The following equations
  give restriction in V and naturality for every arrow of `Over h_Y`. Thus the inverse
  is the fibre functor on objects and maps, rather than an arbitrary objectwise bijection.
- G is an arbitrary group sheaf `Sheaf X.smallEtaleTopology GrpCat`. The helper
  `LocalSystemSheafAction` records sectionwise multiplication, the identity and product
  action laws, and naturality under restrictions. It is a sectionwise interface for this
  clause, not an extra assumption on G or a postponed data construction.
- The subtype of actions on F explicitly requires `p(g • t)=p(t)`. The equivalence α
  identifies exactly these actions with actions of G restricted to Y on `ξ.inverse.obj F`.
  Restriction is `Etale.localizationRestriction GrpCat q inferInstance`, the group-valued
  restriction along the same site functor as for set sheaves. The α equation says β carries
  the fibre action to the original action on t, unchanged in the ambient group G(U).
  Restriction is the specified inverse image along étale q. Naturality of β in F implies
  that the correspondence also respects equivariant maps: the same equation on underlying
  t tests equivariance on both sides. No commutativity, torsion or local-system condition
  is imposed on the group sheaf.
- Preservation by q inverse-image is `indFiniteEtale_pullback`, using the published
  `Scheme.etaleSetPullback q`. Preservation by q_! is the fourth conjunction in
  `indFiniteEtale_total_space`, concerning the underlying sheaf of ξ.functor.obj E.

The existential ξ, ε and β occur in a theorem, not in a definition selecting an unknown
object. Their formulas fix both functors on sections, restrictions and morphisms. There is
no arbitrary map substituted for the canonical total-space construction.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom category.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, `Scheme.Etale`.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone`, `IsColimit`, `Cone`, `IsLimit`;
  `Mathlib.CategoryTheory.Filtered.Basic`: `IsFiltered`.
- `Sheaf.AlgebraicGeometry.IndFiniteEtaleLocalSystem`: `Scheme.IsIndFiniteEtaleSheaf`.
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`:
  `Scheme.FiniteEtale`, the existing finite-étale specialization of the category in
  def-weil-pbc-finite-etale-category's Mathlib match.
- `WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`:
  `AlgebraicGeometry.etaleSetInverseImageCompositionUnits`, read via `scompile.py --source`.
- `WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction`:
  `AlgebraicGeometry.etaleSetInverseImageRestriction`, also read via the source wrapper;
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.localizationRestriction`. The abelian/mono-only lower-shriek
  interface there is not used for set-valued total spaces or general finite étale q.

All already recorded modules of proof dependencies are imported, with proof-only imports
not public. The unrecorded set-monodromy proof dependency has no module to import. The
five theorem docstrings give the relevant parts of the reviewed nine-step proof.
The source was read directly with `pdftotext`, PDF pages 307–309, printed pages 301–303:
ILO XVII 7.2.1–7.2.4 and 7.2.6.

Edge cases checked: empty X (the empty covering forces the unique sheaf), empty Y and
empty fibres (empty sigma), nonsurjective finite étale q, empty colimit and empty finite
limit, infinite stalks, noncommutative and nontorsion group sheaves, disconnected Noetherian
bases, and nonmonic arrows in the original filtered presentations. Only the union theorem
requires the replacement presentation to have monic cocone legs. The index universe is
u+1, as in the existing local-system definition, and admits arbitrary small set diagrams.
All variables and universes are explicitly bound and `autoImplicit` is false.

Searches actually made (preserved by msearch.py in searches.jsonl):

- LeanFinder: `Ind finite etale sheaves of sets closed under colimits finite limits and
  slice equivalence finite etale morphism`: eight hits, giving the site and general finite
  presheaves/condensed infrastructure, no statement of this node.
- Loogle: `Sheaf, Over` returned an unknown-identifier diagnostic, not evidence of absence.
  Repaired query `CategoryTheory.Sheaf` succeeded with twelve results: the sheaf category,
  terminal sheaves, ordinary section sheaves, Yoneda and hom interfaces, no total-space
  equivalence or ind-finite étale calculus.
- LeanSearch: `An equivalence of sheaves on a slice site and sheaves over a representable
  sheaf`: eight results, including sheaf equivalences for dense subsites and equivalent
  sites, not the required over-representable equivalence with sigma and fibre formulas.
- msearch grep: `IndFiniteEtale|localSystem|local_system`, scoped to AlgebraicGeometry:
  no Mathlib hits. Direct rg of Mathlib Sites for totalSpace/sheafOver/overEquiv and
  over-equivalence terms found over-site topology and unrelated section sheaves, not this
  theorem. Direct rg of source WeilConjectures and shared lean/Sheaf found the existing
  local-system definition and downstream consumers, but no declaration for this item.
  Direct rg for this exact blueprint id found the downstream torsor docstring only.
- Direct source searches for action interfaces found ordinary fixed external-group
  `CategoryTheory.Action` and monoidal category actions, not this varying group-sheaf
  section interface. The in-module action structure is part of the action clause and
  consists entirely of actual operation data and their laws.

Compilation: the complete delivered module compiles through `scompile.py Q43
lem-per-set-local-system-calculus <module>` with no errors or warnings (last full pass
4.8 seconds). The earlier scratch probes exposed only deliberately queried nonexistent
names; those probes are outside lean/ and are not delivered. No global build or direct
compilation was run. No statement dispute remains.

## Second reading by Q43

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
