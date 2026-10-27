## Worker report

The theorem module `Sheaf.AlgebraicGeometry.ZariskiTorsorCategoricalCoarseDescent`
states `AlgebraicGeometry.SchemeAction.zariski_torsor_categorical_coarse_descent`.
The node statement and its accepted proof are unchanged. Its only added statement
dependency is the new Zariski torsor definition node below. All theorem proofs are
`sorry`; definition data are explicit. No statement dispute or dependency repair.

Hypotheses, matched individually:

- The field is `(k : Type u) [Field k]`.
- Schemes and morphisms over k are `Over (Spec (.of k))`; G, J and Q are arbitrary
  objects, with `[GrpObj G]` for the internal multiplication, unit and inverse laws,
  and `[ModObj G J]` for the specified left action.
- The presentation category is `zariskiTorsorGroupoid G J`. Its objects are existing
  fppf scheme torsor pairs satisfying the additional open-neighbourhood equivariant
  product condition `IsZariskiTrivial`. This is equivalent to the node's Zariski
  open-cover condition: choose the neighbourhood for each point. Conversely any
  covering provides one at each point. Zariski triviality implies the inherited
  fppf condition, since Zariski covers are fppf; this adds no restriction.
- The arbitrary category F retains independent object and morphism universes w,v;
  `hF : IsFibredInGroupoids F` is the recorded lift/cartesian-arrow definition.
- The functor e is based, and `he : e.toFunctor.IsEquivalence` states equivalence.
  For fibred groupoids, every arrow is cartesian, so this is exactly a cartesian
  equivalence, without an additional cartesian condition on e.
- `q : J ⟶ Q` is a k-map. `hq` is equality after action and second projection on
  the actual scheme product over k, as required; not just geometric invariance.
- `hcat` quantifies over every recorded `AlgebraicSpace (Spec (.of k))`. Maps are
  natural transformations out of the actual Yoneda representables. An invariant
  f has a unique b with `yoneda.map q ≫ b = f`. Together with hq this is exactly
  the bijection from maps out of Q to invariant maps out of J.
- `hgeom` quantifies over every algebraically closed field Ω of the size convention
  and every structure map `a : Spec Ω ⟶ Spec k`. Surjectivity and the equivalence
  `x ≫ q = y ≫ q ↔ ∃ g, g • x = y` say precisely that q induces a bijection on
  the orbit set. A structure map is equivalent to a field extension here; no
  algebraicity or finite-extension assumption is imposed.

Conclusions, matched individually:

- An existential based functor pi has target `discreteModuli (yoneda.obj Q)`.
- The first conjunction says its section, after pullback by the torsor projection,
  is `yoneda.map (u ≫ q)`. The `eqToHom ((e.w_obj X).trans (pi.w_obj X).symm)`
  just identifies the two base schemes supplied by the based-functor equalities;
  it is the identity after putting X in its fibre. No arbitrary map is introduced.
- The next conjunction says any other based functor satisfying that very same
  pullback formula equals pi. Uniqueness is of the map, not merely of a choice
  satisfying additional coarse properties.
- For every B the equivalence R is between maps F→B and the subtype of invariant
  maps J→B. Its iff clause specifies restriction: transfer A to a based functor AP
  on the presented torsor category and restrict AP along `zariskiQuotientAtlas`.
  Thus R is the required restriction correspondence, not an arbitrary bijection.
  AP can be chosen since precomposition by e is bijective for a discrete target;
  all choices agree. Equality of maps into the discrete fibred groupoid is literal.
- The equation for every b says R sends `pi.comp (discreteModuliMap b)` to
  `yoneda.map q ≫ b`, giving exactly the required precomposition compatibility.
- On every geometric fibre the map induced by e on skeletons is bijective. The
  equivalence c identifies the torsor fibre skeleton with Mathlib's actual orbit
  quotient. Its normalization sends the specified trivial pair P_x to `[x]`.
  Composing with the e-bijection therefore gives precisely the presentation's
  identification of F(Ω)/isomorphism with J(Ω)/G(Ω).
- The following implication identifies the pi-image of every class over `[x]`
  with the class of the actual representable point `x ≫ q`. Together with hgeom
  this is the specified geometric bijection, not an unrelated class bijection.
- `IsCoarseModuliScheme F Q pi` is the exact recorded definition: universal
  bijectivity for every algebraic-space target and geometric-fibre skeleton
  bijectivity. There is no projectivity, finite type, algebraicity or existence
  assertion about q, and no such assumptions.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field` (line 180).
- Mathlib.AlgebraicGeometry.Scheme: `Scheme`, `Scheme.Hom` (lines 42, 74).
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`, `fst`,
  `snd`, `lift` (lines 95, 111, 115, 128). `IsPullback` expresses the same
  scheme-fibre-product property without choosing an additional isomorphism.
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed` (line 62). The dependency
  also records AlgebraicClosure, but no chosen algebraic closure is needed:
  the node quantifies over arbitrary algebraically closed extensions.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicSpace` (fppf sheaves with
  representable diagonal and surjective etale scheme atlas), and its underlying
  presheaf `.obj.obj`.
- Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids: `IsFibredInGroupoids`,
  `discreteModuli`, `discreteModuliMap`, `moduliFiberMap`, `IsCoarseModuliScheme`.
  The stable-curve-specific structures are not substituted for arbitrary F.
- Sheaf.AlgebraicGeometry.SchemeActionTorsorGroupoids: `TorsorObject`, `TorsorHom`,
  `torsorGroupoid`, `ActionObject`, `trivialObject`, `trivialTorsorFunctor`.
- Sheaf.AlgebraicGeometry.AffineActionQuotientStack: the GENERIC helper declarations
  `schemeToActionGroupoid` and `quotientAtlas`; their full signatures work over an
  arbitrary S with arbitrary G,J. No affine, smooth or finite-type hypothesis from
  the separately defined affine-action quotient is used.
- Mathlib.CategoryTheory.Monoidal.Cartesian.Grp/Mod: `GrpObj`, `ModObj`, their
  group and action structures on scheme-test Hom sets.
- Proof imports include Sheaf.CategoryTheory.SiteCoveringAxioms and
  Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite (`schemeSpace`). Zariski-to-fppf
  is `Scheme.zariskiPrecoverage_le_fppfPrecoverage` in Mathlib's Fpqc, and Yoneda
  is `yonedaEquiv` in Mathlib.CategoryTheory.Yoneda; both are already public through
  the statement imports. No proof-dependency import cycle is introduced.

Sources read: Stacks examples-stacks.tex section-group-quotient-stacks (04UV),
including the object/arrows description and inverse-right-translation trivial
functor; groupoids-quotients.tex lemma-invariant (048F) and definition-categorical
(048J). The latest blueprint unit sk-thm-sf-ctf-stability/_section.md was checked;
this item is an auxiliary node, not a unit statement. The accepted node's eight
proof steps are transcribed step by step in the theorem docstring.

Edge cases checked before finalizing:

- Empty base T: IsZariskiTrivial is vacuous and the fppf sheaf empty-cover condition
  gives the unique target section. No nonempty hypothesis is present.
- Empty J and its torsor category: nonempty torsor bases cannot map their nonempty
  product charts to J; the categorical and geometric hypotheses impose precisely
  the corresponding empty-quotient condition.
- Trivial G: torsor pairs reduce locally and globally to maps to J; the formulas
  give the ordinary Yoneda correspondence and orbit equality.
- Nontrivial/nonreduced/nonflat group schemes: no smoothness, reducedness,
  finite-presentation or flatness hypothesis is used. The torsor notion here is
  explicitly local product triviality, exactly as stipulated in the node.
- Over any field Ω, Spec Ω has a single nonempty open; a Zariski torsor therefore
  has a section. Triviality does not rely on a false assertion about all fppf
  torsors. Automorphisms remain in the fibre groupoids until taking skeletons.
- All fields and schemes use u, matching the dependency's size convention;
  the arbitrary F category has independent universes v,w. The group action on
  points is the actual internal-action-induced MulAction.

Searches actually run (msearch.py Q85/item; logs in sandbox searches.jsonl):

- LeanFinder: “Maps from Zariski locally trivial scheme torsors with equivariant
  maps to J to algebraic spaces correspond to invariant morphisms from J”:
  eight hits on affine-space Hom equivalences and scheme gluing, no exact match.
- Loogle: `AlgebraicGeometry.Scheme, CategoryTheory.BasedFunctor`: zero hits.
- LeanSearch: “Zariski locally trivial group scheme torsor equivariant maps quotient
  groupoid”: eight hits, including abstract orbit quotient and unrelated topological
  trivializations, no scheme torsor presentation definition or theorem.
- Mathlib grep `ZariskiTorsor|zariskiTorsor|categorical.*coarse|CoarseModuli`:
  zero hits. `IsLocallyTrivial|TorsorObject` in AlgebraicGeometry: zero hits.
- Project rg of actions/torsors found the existing fppf SchemeAction framework;
  used it. The right-torsor Zariski predicate in SplitSolvableTorsorDefinitions
  assumes represented finitely presented right torsors and is not this notion.
- Exact item id and intended names in WeilConjectures and Sheaf: no definition or
  theorem match (only unrelated units torsor imports). Upstream name JSON searched.
- DAG search for Zariski/torsor found specialized units, right solvable and other
  torsor statements, not this groupoid. `blueprint_refs.py search 'Zariski locally
  trivial torsor'` returned zero blueprint nodes. Ancestor command returned None,
  matching the item's current blueprint.from.node; this is retained in the new node.

Validation: scompile.py compiled each delivered module in dependency order, as
separate module-mode files. Both are clean; only expected sorry declarations
remain. No lake build or direct repository mutation was run.

## New nodes

`def-sfb-zariski-torsor-groupoid` owns module
`Sheaf.AlgebraicGeometry.ZariskiTorsorGroupoid`. It defines the local open product
predicate, the full subcategory and base projection, its canonical trivial-torsor
atlas and its trivial fibre objects. It reuses all existing group actions, scheme
torsors, arrows and trivial product data; the new restriction is absent from the
existing DAG/Mathlib/project as checked above. Its source is Stacks 04UV restricted
to the precise Zariski triviality specified in the item. The named postponed theorem
`trivialObject_isZariskiTrivial` has its full law stated in this node and its proof
in its docstring: use the whole base and identity product chart. No data are chosen
from a mere existence theorem, and no definition contains sorry.

The definition node cites the existing affine-action quotient node solely for
its generic schemeToActionGroupoid/quotientAtlas helpers; their arbitrary-base
signatures were read in full. The new category is a full subcategory rather than
a duplicate of the existing torsor category.

## Second reading by Q85

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
