## Worker report

The module `Sheaf.AlgebraicGeometry.FineLogStructureEtaleDescent` states
`AlgebraicGeometry.fineLogStructureEtaleDescent`, with `sorry` as its entire proof.
It proves nothing. Four supporting definitions present the actual local restrictions,
normalized overlap datum, and prescribed identifications. None contains postponed data
or a postponed proof. The node copy changes only `lean`; no statement correction,
new node, or dependency repair is needed.

Source read: ILO Exposé VI 1.1 (printed p. 69, PDF p. 75), and Exposé VIII 3.3.4(ii),
3.3.8 (printed pp. 107--108, PDF pp. 113--114). VI defines fine/fs via étale-local
charts and makes locally Noetherian the standing assumption. VIII invokes descent
from strict étale charts. The arbitrary monoid-sheaf morphism clause is ordinary
sheaf-map gluing (Stacks 04TQ), exactly as the node and its proof specify.

Hypotheses and clauses, in order:

- The base is `{T : Scheme.{u}} [IsLocallyNoetherian T]`. The covering members are
  `U : I → T.Etale`, so each structure map is étale. `hcov` says every point of `T`
  lies in the image of some `(U a).hom`, precisely joint surjectivity. `I : Type v`
  is arbitrary; no nonempty, finite, affine, separated, or global-chart assumption
  has been introduced. An étale scheme over a locally Noetherian base is locally
  Noetherian, so no additional local hypothesis is required.
- The first conjunct quantifies over `D : EtaleLogStructure.CoverDatum U`.
  `D.localLog a` is the recorded log structure on `(U a).left`; its monoid sheaf,
  structure map, and log-unit axiom are inherited from `EtaleLogStructure`.
- The fine hypothesis is expanded without defining a competing notion: at every
  geometric point there exists a pointed étale neighbourhood `W`, a commutative
  monoid `P`, and a section homomorphism `β` with `Monoid.FG P`, injective canonical
  map to `Algebra.GrothendieckGroup P`, and `(D.localLog a).IsChart W β`.
  This is finite generation plus integrality, with no saturation assumption.
- `CoverDatum.transition a b W f g` is a multiplicative equivalence of the local
  section monoids for every common étale test object `W` and arrows to `U a,U b`.
  By the fibre-product universal property these are all objects over their double
  overlap. `naturality` requires commutation with restriction along every test
  morphism `h`. Thus these components give exactly an isomorphism of monoid
  sheaves on the double overlap, rather than unrelated sectionwise bijections.
- `CoverDatum.alpha` equates their images under the actual local structure maps
  to `Γ(W.left, ⊤)`. `diagonal` requires the identity for identical arrows `f,f`:
  this is restriction to the diagonal, including repeated indices, and does not
  impose identity on the entire self-intersection. `cocycle` states
  `transition_ab.trans transition_bc = transition_ac` on all triple test diagrams.
- The conclusion supplies `M : EtaleLogStructure T` and the same expanded fine
  chart condition for `M`. `e : CoverIdentification D M` supplies natural
  isomorphisms of its restrictions with the specified local structures.
  `e.alpha` gives structure-map compatibility. `e.transition` states that the
  second identification is the first followed by the prescribed transition,
  so the original labelled datum is induced.
- The saturation clause is the implication
  `(∀ a, (D.localLog a).IsFineSaturated) → M.IsFineSaturated`, using the existing
  fs definition. It refers to this same descended `M`.
- Identification-preserving uniqueness quantifies over a second `N`, its
  `CoverIdentification D N`, and its expanded fine hypothesis. It asserts
  `∃! h : M.monoidSheaf.obj ≅ N.monoidSheaf.obj` with
  `h.hom ≫ N.alpha = M.alpha` and
  `Functor.whiskerLeft (Over.forget (U a)).op h.hom ≫ (f.iso a).hom = (e.iso a).hom`.
  This is unique isomorphism compatible with the fixed identifications, not
  uniqueness of unlabelled log structures or equality of their underlying data.
- The second conjunct quantifies over arbitrary
  `A B : Sheaf T.smallEtaleTopology CommMonCat.{u}` and structural natural
  transformations `α,β` into the multiplicative étale structure presheaf.
  No log, fine, unit-reflection, or saturation condition is imposed on `A,B`.
- Each local homomorphism `f a` is a natural transformation from
  `(A.over (U a)).obj` to `(B.over (U a)).obj`. The first hypothesis is exactly
  local compatibility with `α,β`, evaluated on every localized test object.
  The second equates local components on every common double-overlap test object.
- The conclusion `∃! h : A.obj ⟶ B.obj` requires `h ≫ β = α` and equality of
  every restriction `Functor.whiskerLeft (Over.forget (U a)).op h = f a`.
  This includes arbitrary inverse-image monoid sheaves equipped with a composite
  structure map: those are among the quantified sheaves and maps, and no
  additional log condition on them is needed.

The sectionwise overlap presentation changes no objects: for two arrows to cover
members, being a common test object is equivalent to being an object over their
fibre product. For three arrows it is the corresponding triple fibre product.
The diagonal condition evaluates the actual diagonal, and naturality imposes all
morphisms of these localized sites. `Scheme.Etale.overToEtale` supplies the
canonical identification with the small étale site of each member. Both
structure presheaves evaluate to the same ring of actual regular functions, with
the same restriction maps; no chosen ring map or extra transport assumption occurs.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`:
  `AlgebraicGeometry.EtaleLogStructure`, its inherited `monoidSheaf` and `alpha`,
  `EtaleLogStructure.IsChart`, `EtaleLogStructure.IsFineSaturated`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`,
  `Scheme.Etale`, and the joint-surjectivity characterization
  `Scheme.ofArrows_mem_smallEtaleTopology_iff` (the cover is expanded pointwise).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and its universal property, explaining the
  equivalent common-test-object representation of overlaps.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` imports the
  localized-site declarations recorded for `def-pur-localized-ringed-site`;
  the declaration used here is `CategoryTheory.Sheaf.over`, defined in
  `Mathlib.CategoryTheory.Sites.Over`. Module restriction is not needed.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`:
  `Scheme.Etale.overToEtale`, and its recorded equivalence `overEquiv`:
  the first functor is evaluated directly for all local section objects and maps.
- `Sheaf.CategoryTheory.SetSheafCoverDescent`:
  `CategoryTheory.setSheafCoverDescent`, imported as a proof dependency.
- `def-weil-size-convention` is the metatheoretic convention, not a declaration
  to duplicate or import. Schemes, local monoids, section sets, fields, and charts
  use the shared explicit universe `u`; the index has arbitrary explicit `v`.
  There is no additional equality imposed on category object and morphism universes.

Edge cases checked before writing and again against the compiled signature:

- Empty cover: `hcov` then forces the empty base, for which the first assertion
  and arbitrary-map uniqueness have their usual empty-site meaning. No
  `[Nonempty I]` prevents this case.
- Identity cover: the datum induces its original log structure, and compatible
  isomorphism uniqueness is relative to the specified identification.
- Repeated indices and nontrivial self-overlaps: `diagonal` only fixes `f=f`;
  off-diagonal transition maps may carry the nontrivial descent information.
  The cocycle explicitly includes all repeated indices and all triples of arrows.
- Trivial log structure, unit charts, and noninjective structure maps: no
  injectivity is imposed on `alpha` or on chart maps; integrality is solely the
  injectivity of the monoid's map to its group completion.
- Fine nonsaturated monoids are permitted. Saturation is a conditional conclusion,
  not a hidden strengthening of the initial fine hypothesis.
- Arbitrary monoid sheaves in the moreover clause, including ones that fail
  the log-unit axiom, are accepted without any additional hypothesis.
- All characteristics, nonaffine and nonseparated schemes, arbitrary index
  universes, and empty overlap schemes are retained.

Searches for an existing statement or a competing helper (all via the prescribed
`msearch.py Q139 lem-trf-fine-log-structure-etale-descent` or read-only `rg`):

- LeanFinder: `Fine log structures and morphisms of monoid sheaves descend along
  etale covering families`. Eight hits: étale composition/cancellation, ordinary
  scheme gluing, the étale site, and affine limit results. None states this theorem.
- Loogle: `LogStructure, SheafOfMonoids`. Zero hits; `LogStructure` unknown.
- Mathlib grep: `LogStructure|LogScheme|SheafOfMonoids|fine.*monoid` in
  `AlgebraicGeometry`. Two affine monoid scheme comments; no log descent theorem.
- LeanSearch: `Fine log structures and arbitrary monoid sheaf morphisms descend
  along etale covers`. Eight ordinary étale-site and flat descent hits; no match.
- Read-only grep/rg in `WeilConjectures` for the item id and
  `fine.log|FineLog|LogStructure|log.structure`: no item declaration or log descent.
- Read-only `rg` in `lean/Sheaf`: the existing log structure and fs chart
  definitions and the fine-stalk spreading theorem were found and read. The
  spreading theorem expands fineness in precisely the same form used here;
  it does not state descent. No exact existing statement was found.
- Exact proposed full names were searched in Mathlib, upstream, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: no collisions. Other namespaces have unrelated
  `coverSections` declarations; none uses `AlgebraicGeometry.EtaleLogStructure`.
- `tools/blueprint_refs.py search fine-log` found no separately named definition;
  DAG text search found the already recorded log definitions and their consumers.
  No standalone fine predicate is introduced: the existing chart predicate is
  used directly, as in the landed fine-stalk spreading statement.

Validation: the prescribed `scompile.py` compiled both its sandbox check and the
actual module path cleanly, in 2.5 s and 3.2 s. The first run reported only two
unqualified whiskering names; qualifying them as `Functor.whiskerLeft` fixed both.
The final file has explicitly bound universes and variables, no local notation
or instances, and no warning. Its only postponed proof is the named main theorem,
whose docstring includes all seven steps of the DAG proof and its source nodes.

No statement is disputed. No DAG fault was identified. Independent review is
performed by the maintainer under the direct-delivery brief.

## Second reading by Q139

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
