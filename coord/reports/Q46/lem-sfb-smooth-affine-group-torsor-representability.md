## Worker report

Delivered module: `Sheaf.AlgebraicGeometry.SmoothAffineGroupTorsorRepresentability`.
The only declaration is the theorem
`AlgebraicGeometry.smooth_affine_group_torsor_representability`, with proof `sorry`.
No statement correction, new definition, dependency replacement, or disputed statement.
All notions are existing Mathlib constructions; the sheaf-action and local-equivariance
hypotheses are written explicitly rather than introducing a second torsor definition.

Hypothesis and clause correspondence:

- A field k: `(k : Type u) [Field k]`. An arbitrary k-scheme S:
  `(S : Scheme.{u}) (_s : S ⟶ Spec (.of k))`. Its structure map is deliberately
  unrestricted; neither reducedness nor Noetherianity nor any characteristic is assumed.
- The S-group scheme: `(G : Over S) [GrpObj G]`. This is the internal group object
  with S-morphism multiplication, unit, inverse and their diagram identities.
  Mathlib's Cartesian monoidal structure on `Over S` uses precisely the scheme
  pullbacks, not absolute products. In particular `(G ⊗ P).left` is
  `pullback G.hom P.hom`.
- Affine and smooth: `[IsAffineHom G.hom] [Smooth G.hom]`.
  Finite presentation: `[LocallyOfFinitePresentation G.hom]` together with
  affineness, which supplies quasi-compactness and separatedness (hence
  quasi-separatedness). These are exactly finite presentation; Mathlib's
  finite-presentation morphism module uses its three component properties.
- A sheaf of sets on the big fppf slice site:
  `F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))`.
- The given left action is `act T : (T ⟶ G) → F(T) → F(T)` for every S-scheme T.
  `one_act` and `mul_act` are its unit and associativity laws. `map_act` is
  compatibility with every S-morphism of test schemes, so this is a sheaf
  action by h_G, not merely unrelated sectionwise group actions.
- Existence of an fppf covering family is the existential `locally_trivial`
  over `I`, `U`, `f`, with `Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage S`.
  There is no nonempty or finite restriction on I.
- For each cover member, the natural isomorphism `e` is from F restricted
  along `(Over.map (f i)).op` to h_G restricted along that same functor.
  The latter is canonically the functor h_(G ×_S U_i): a U_i-map into the
  fibre product is exactly an S-map from the same test scheme into G.
  The following equality says e takes `act g x` to the product of g and e(x)
  using `lift g ... ≫ μ[G]`, namely left translation, for every test scheme.
- `uliftYoneda.{u + 1}` is the existing Yoneda presheaf followed by ULift;
  `.down` is its canonical bijection to actual morphisms. This puts points
  in the sheaf's universe without any smallness or representability assumption.
- The conclusion provides `(P : Over S)` and a natural isomorphism
  `e : F.obj ≅ uliftYoneda.{u + 1}.obj P`. Since F is a sheaf and this
  is an isomorphism of presheaves, this is exactly F ≅ h_P as sheaves.
- The four geometric clauses are respectively `IsAffineHom P.hom`,
  `Smooth P.hom`, `Surjective P.hom`, and `UniversallyOpen P.hom`.
  The last is Mathlib's openness after every scheme base change.
- The represented action is `(a : ModObj G P)`, an S-morphism G ×_S P → P
  with the unit and associativity laws. The final universal equality on T,g,x
  identifies its induced action with the INPUT action through e. Thus the
  action is not an unrelated existential scheme action.
- `IsIso (lift a.smul (snd G P))` is precisely the S-map (g,p) ↦ (gp,p)
  from G ×_S P to P ×_S P being an isomorphism. Isomorphisms in `Over S`
  are exactly the scheme isomorphisms over S.
- Schemes have universe u, site objects and sheaf values use u+1, and covering
  indices range over `Type (u + 1)`, as in the existing family-descent interface.
  Smaller families and sheaves can be lifted canonically. All universes and
  variables are explicitly bound; `autoImplicit` is disabled.

Dependency declarations read and reused:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs, the commutative field class.
- def-pc-scheme: `AlgebraicGeometry.Scheme` and its morphisms,
  Mathlib.AlgebraicGeometry.Scheme.
- pqf-def-affine-morphism: `AlgebraicGeometry.IsAffineHom`,
  Mathlib.AlgebraicGeometry.Morphisms.Affine, affine preimages of affine opens.
- def-sbc-smooth-morphisms: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth, affine-locally smooth ring maps.
- def-sbc-locally-finite-presentation: `AlgebraicGeometry.LocallyOfFinitePresentation`,
  Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation.
- def-pc-fppf-site: `Scheme.fppfPrecoverage`, `Scheme.fppfTopology`,
  Mathlib.AlgebraicGeometry.Sites.Fpqc, and `GrothendieckTopology.over` from
  Mathlib.CategoryTheory.Sites.Over. No private topology is defined.
- def-weil-size-convention is a metatheoretic convention, rendered by universe u
  and u+1 and the explicit site/sheaf/index universes.
- def-pc-fibre-product: `CategoryTheory.Limits.pullback`, its projections and lift,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback. The canonical
  Cartesian monoidal Over structure identifies these with tensor, fst/snd/lift.
- Other existing notions are `GrpObj`, `ModObj`, `uliftYoneda`, `Spec`,
  `Surjective`, and `UniversallyOpen`; none is redefined.

The module imports all recorded non-Mathlib proof-dependency modules:
`SchemeCoverDescentDatum`, `AffineFpqcDescent`, `FppfFamilyCoproductDescentEncoding`,
`FpqcAffineDescent`, and `SmoothFiber`, along with the Mathlib gluing/coproduct
modules. The proof-only dependency `lem-sfb-space-smooth-surjective-fppf-locality`
has no Lean record or Mathlib match in the current DAG, so it has no module to
import; its intended use is preserved in the theorem's complete six-step proof
docstring. It is not needed to type this statement. The full node proof is
rendered there, including the same-scheme descent clause and inverse gluing.

Edge cases checked before writing: empty S and empty covers are permitted;
the sheaf axiom at the empty object is retained. The trivial group is allowed
without a dimension, nontriviality or connectedness hypothesis. Arbitrary
nonreduced test schemes occur in every naturality/equivariance quantifier.
Noncommutative groups are allowed: the chosen action is left translation and
its local torsor inverse is (x,y) ↦ (xy⁻¹,y). Surjectivity is geometric, not
nonemptiness of F(T) for every T, so nonsplit torsors are included.

Searches (2026-10-24 UTC):

- msearch.py leanfinder, query "An fppf sheaf torsor under a smooth affine group
  scheme is represented by an affine smooth scheme": 8 results, affine spaces,
  affine scheme instances and affine-transition-limit helpers; no match.
- msearch.py loogle, query `"Torsor", "Scheme"`: 0 hits.
- msearch.py grep, query `torsor|IsTorsor`, subdirectory AlgebraicGeometry:
  0 hits in Mathlib's algebraic geometry.
- rg of `torsor|Torsor|GroupScheme|GroupObj|MulAction.*yoneda|Presheaf.*Action`
  in lean/WeilConjectures and lean/Sheaf found many torsor-related results.
  Read upstream CategoryTheory/Sites/Torsor.lean: its torsors are for abelian
  sheaves, so do not cover arbitrary smooth affine groups. Read
  SchemeActionTorsorGroupoids.lean: its objects are already schemes and cannot
  supply representability of an input sheaf. Read SplitTorusTorsorFrameGeometry:
  specialized to represented split-torus torsors and does not state this result.
- Searched group schemes and action notions in the DAG; `def-sc-group-scheme`
  records Mathlib GrpObj. Read its defining signature and upstream GroupScheme/Defs
  documentation, and Mathlib Cartesian/Grp and Cartesian/Mod. Reused them directly.
- `rg -n 'lem-sfb-smooth-affine-group-torsor-representability' lean/WeilConjectures`:
  no existing declaration for the item. `blueprint_refs.py search
  'fppf group sheaf action'`: 0 blueprint nodes.
- Read the local Stacks source groupoids.tex, remark-fun-with-torsors (049C):
  affine groups give an affirmative answer to representability by affine descent.
  This agrees with the given statement and its proof route.

Validation: prescribed scompile.py compiled both the sandbox and actual library
module names successfully (1.8 s and 1.5 s in the successful run). A first typeclass
elaboration issue on local multiplication was repaired by using the canonical
internal multiplication `lift g h ≫ μ[G]`, avoiding an opaque-functor Hom inference.
No compiler warnings remain except the permitted sorry warning. No project build
or direct Git command was run and all worker writes are in the assigned sandbox.

## Second reading by Q46

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
