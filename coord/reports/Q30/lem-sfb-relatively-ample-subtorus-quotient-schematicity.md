## Worker report

The delivery states `AlgebraicGeometry.relatively_ample_subtorus_quotient_schematicity`
in `Sheaf.AlgebraicGeometry.RelativelyAmpleSubtorusQuotientSchematicity`. Its only
proof is `by sorry`. The supporting module `Sheaf.AlgebraicGeometry.RelativeTorus`
has two actual definitions and no postponed data or proofs.

The inherited BLOCKED ending was a stage-1 handoff error. I read the current node,
queue entry (stage 2), and brief-stage2 section 0. The node is split and reviewed by
Q05, has no Lean record, and has no released repair note. The accepted split and
its ten proof steps are preserved. The current blueprint unit
`sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` was read: this item is
a supporting lemma, not the unit statement. `blueprint_refs.py ancestor` reports
that the inherited ancestor is null; the new definition preserves this value and
extends the inherited via chain, without inventing an ancestor.

Hypotheses and clauses, matched against the node:

- The base scheme is `S : Scheme.{u}`. `[IsLocallyNoetherian S]` supplies local
  Noetherianness. `hS` says every stalk is a domain and integrally closed, exactly
  normality of the scheme. This imposes neither integrality nor connectedness on S.
- The group is `G : Over S` with `[CommGrpObj G]`, the actual relative commutative
  group object of the node. Its structure map is `G.hom`.
- Smoothness and separatedness are `[Smooth G.hom]` and `[IsSeparated G.hom]`.
  Finite presentation is `[LocallyOfFinitePresentation G.hom]` together with
  `[QuasiCompact G.hom]`; separatedness supplies quasi-separatedness. This is the
  finite-presentation convention of the cited node, not just local presentation.
- `[GeometricallyConnected G.hom]` states that every field-valued base change is
  connected. It is equivalent to connected geometric fibres; this includes
  nonemptiness of those fibres, already guaranteed by the identity section.
- `hample` supplies a possibly empty `I : Type u`, opens `W`, coverage of every
  base point, and `IsAffineOpen (W i)`. On each inverse-image open
  `(G.hom ⁻¹ᵁ W i).toScheme`, it supplies `L` with `hL : L.IsInvertible` and
  `@Scheme.Modules.IsAmple ... L hL`. The inverse-image open is the canonical
  open-subscheme model of `G ×_S W_i`; no pullback line from S is required.
- `T : Over S`, `[GrpObj T]`, `i : T ⟶ G`, `[IsMonHom i]`, and
  `[IsClosedImmersion i.left]` express the specified closed subgroup over S.
- `hT : IsRelativeTorus T` is the stated fppf-local split-torus condition over
  arbitrary S. It allows rank zero and locally varying finite rank. The source's
  existing field-only multiplicative group is not imposed on S.
- `F : AlgebraicSpace S` is an fppf sheaf with representable diagonal and etale
  surjective atlas, using the dependency's actual category. `p` has source the
  Yoneda presheaf of G and target the presheaf underlying F.
- The coequalizer displayed in `eta` is taken in presheaves of sets of the
  projection `(g,t) ↦ g` and right translation `(g,t) ↦ g i(t)`. Presheaf colimits
  are pointwise, so it is exactly `U ↦ G(U)/T(U)`. `hp` makes the supplied p the
  coset projection followed by eta. For every fppf set sheaf Z, `hF` requires
  precomposition with eta to be bijective. This is precisely the universal
  property of sheafification from def-weil-pbc-sheafification. It fixes the actual
  quotient and map, rather than assuming a torsor theorem or replacing them by
  an unconstrained morphism. It requires no extra sheafification-existence instance
  or equality of universes. All presheaves have the same value universe as F.
- The conclusion supplies `H : Over S`, an actual `CommGrpObj H`, and the
  representing isomorphism `e : yoneda.obj H ≅ F.obj.obj`.
- `q : G ⟶ H` satisfies `yoneda.map q ≫ e.hom = p`; the quotient map on the
  representing scheme is the specified p. `IsMonHom q` makes its multiplication
  the multiplication of local lifts in G. Since p is the sheafification of the
  coset projection, sections have fppf local lifts, and this property determines
  the group law uniquely. No preassigned alternate group law on F is assumed.
- `Smooth H.hom`, `IsSeparated H.hom`, `LocallyOfFinitePresentation H.hom`,
  `QuasiCompact H.hom`, and `QuasiSeparated H.hom` are exactly the required smooth,
  separated, finitely presented structure morphism. `IsAffineHom q.left` is the
  required affineness of the original p under the representing identification.
- No semiabelian-fibre, maximality, generic-fibre, constant-rank, quasi-compact-base,
  or field hypothesis has been added. There is no statement correction.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  together with `IsDomain`, on the local rings. The node's general normal-ring
  inline predicate specializes on these already-local rings to normal domains.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`; the convention node gives the
  quasi-compact/quasi-separated finite-presentation convention and adds no object.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, through the existing
  `GeometricallyConnected` in `Mathlib.AlgebraicGeometry.Geometrically.Connected`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple` (the exact absolute condition).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `AlgebraicGeometry.StandardGroupSchemes.multiplicative` and its group instance
  were read. They require a field and therefore do not supply the arbitrary-base
  notion. The missing relative notion is supplied by the new definition below,
  using the units functor, not by redefining the field-based multiplicative group.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`; `Mathlib.CategoryTheory.Sites.Over` supplies its slice.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`,
  `toSheafify`, `sheafificationAdjunction`; their universal property is written
  explicitly in `hF`, as in the existing quotient-presentation interface.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace` and
  `AlgebraicSpace.IsAlgebraicSpace`, including the actual underlying sheaf.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` and
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: the recorded
  canonical scheme-base-change convention, `pullback`, and its two projections.
  Restrictions to base opens use their canonical inverse-image-open model.
- Group objects, homomorphisms and relative group products use Mathlib's
  `CommGrpObj`, `GrpObj`, `IsMonHom`, `CartesianMonoidalCategory.fst`, `snd`,
  `lift`, and `MonObj.mul`. The new notion uses `yonedaGrpObj`, `Over.map`,
  `CommMonCat.units` and finite categorical products.

The recorded modules of stated proof dependencies are ordinary proof imports,
including FreeFlatGroupSpaceQuotient, StackChartwiseSmoothEtaleCalculus,
AlgebraicSpaceFourPropertyFppfDescent, SmoothConnectedGenericGeometry, AmplePullback,
FpqcClosedImmersionDescent, AmpleFiniteSetAffine, the relative descent datum,
InvariantAffineNeighbourhoods, InvariantAffineDescentGluing and the representability
criterion. Dependencies without declarations cannot yet be imported; they remain
named in the full proof docstring and in the unchanged DAG proof.

Edge cases checked before writing:

- Empty S: the covering index may be empty; there is no global nonemptiness
  hypothesis. Group objects over the empty scheme and the quotient still make
  sense, and all stalk and fibre hypotheses are vacuous in the intended way.
- Rank zero: `Fin 0` gives the empty product, the trivial group. Quotienting by
  the identity subgroup recovers G; p is an isomorphism and hence affine.
- T = G when G is a torus: the quotient is the base with its trivial group law;
  its structure morphism is the identity, and p is affine.
- Disconnected or non-quasi-compact S: neither is excluded, and local ranks may
  vary. The affine covering is not required finite. Its index shares the scheme
  universe, rather than a smaller independent universe.
- Arbitrary characteristic, and nonreduced test schemes: no reducedness, field
  hypothesis or characteristic assumption is placed on tests. The splitting is
  an isomorphism of group-valued functors on all schemes, not just field points.
- The distinction between presheaf cosets and their fppf sheafification is kept
  by eta and its universal property. An algebraic-space quotient is an input;
  schematicity is a conclusion.

Searches actually run through msearch.py (the sandbox log contains their exact
queries, results and digests):

1. LeanFinder: `The fppf quotient of a relatively ample smooth commutative group
   scheme by a subtorus is a scheme and the quotient map is affine`: eight hits
   concerning affine spaces and affine transition limits, no quotient theorem.
2. Loogle: `GrpObj, AlgebraicGeometry.Scheme`: zero hits, unknown GrpObj identifier
   in the service. This is not evidence that Mathlib lacks group objects; the
   local Cartesian group-object source was read directly and reused.
3. Mathlib grep: `subtorus|Subtorus|IsTorus|torus quotient`, AlgebraicGeometry:
   no hits.
4. LeanSearch: `The quotient of a relatively ample smooth group scheme by a
   closed subtorus is represented by a smooth separated group scheme`: eight
   hits about abstract group and representation quotients, no scheme theorem.
5. The three relative-torus queries are recorded verbatim in the new node:
   LeanSearch and LeanFinder return only topological tori, generic pullbacks,
   affine spaces and elementary units identities; Mathlib grep finds no torus
   predicate. These do not define the needed fppf-local notion.
6. Local rg searches of `lean/WeilConjectures`, `lean/Sheaf`, Mathlib,
   `dag/lean_names_upstream.json`, and DAG definition nodes for torus, IsTorus,
   splitTorus, group objects, coset and quotient interfaces. No item declaration
   or relative-torus definition exists. The item-id search in WeilConjectures
   has no hit. `ToriMultiplicativeType.IsTorus` and StandardGroupSchemes are
   field-only. `IsFppfGroupQuotient` requires a scheme quotient already and so
   cannot serve as the present algebraic-space-quotient hypothesis; its
   coequalizer/sheafification universal-property pattern is reused inline.
7. `blueprint_refs.py search 'relative torus'`: zero matches; `search 'torus'`
   checks the wider imported blueprint too. The new notion is not an existing
   blueprint definition. The ancestor command reports the inherited null
   ancestor; this is recorded rather than silently replaced.

No mathematical statement dispute was found. Source limitation: the node's
Raynaud PDF is marked WANTED and is absent from the read clone. I do not claim
to have read it. This delivery follows the accepted independently formulated
statement and ten-step proof, unchanged. I read Stacks `groupoids.tex`, Example
example-multiplicative-group (Tag 022U), whose arbitrary-base functor of points
is exactly the units functor used by the new definition.

Validation: scompile.py compiled both modules separately, in dependency order,
with module headers, explicit universes and auto-implicits disabled. Each sandbox
and final module check passed without errors or warnings (about 2 and 4 seconds
respectively). A first compiler probe exposed a missing direct forgetful functor
from CommRingCat to MonCat; the definition now uses the existing CommMonCat.units
route, and both files compile cleanly. The dry-run and push results follow below.

## New nodes

`def-sfb-relative-torus` records the missing arbitrary-base torus notion. Its
module defines `relativeSplitTorusFunctor` as the finite product of the functor
of units of global regular functions, and `IsRelativeTorus` as existence of an
fppf covering and group-functor splitting isomorphisms of finite ranks. This
states the item's own torus convention using the arbitrary-base description of
G_m in Stacks Tag 022U, rather than changing its hypotheses to field bases.
Its searches are the actual logged LeanSearch, LeanFinder and Mathlib grep
queries described above. The field-only def-sfb-tori-multiplicative-type and
def-sc-gm-ga do not give this notion. The new definition is cited by the item;
all definition data are explicit compositions, products and a Prop-valued
existential, with no chosen model from an unproved existence assertion.

## Second reading by Q30

The dispatcher explicitly forbids starting other agents; no independent second
worker was started, and this section records my own second pass, leaving the
independent review to the maintainer as the assignment specifies.

With the node and final files open, I rechecked every binder and conclusion:
S is only normal locally Noetherian, not integral; finite presentation includes
quasi-compactness; geometric connectedness is retained; the affine cover and
ample invertible module concern G over each base open, not the base itself;
the subgroup inclusion is the specified closed group homomorphism; and the
new torus predicate preserves arbitrary bases, finite local ranks and rank zero.
The quotient hypothesis uses the actual orbit coequalizer and its sheafification
universal property, including the projection equation hp. The conclusion's e
represents the same F, its equation fixes q as p, and IsMonHom q specifies the
induced group law. Smoothness, separatedness, finite presentation and affineness
are all present. The ordinary input QS hypothesis would be redundant with
separatedness, so it is correctly not added; the conclusion spells out all three
finite-presentation components. All original node fields except lean and the
added definition dependency are preserved. The new definition has the required
field layout, source, searches, own module and real data. No mismatch or change
was needed on this second pass.

Delivery validation: the first dry run required the live schema's `import_flags`
key on the new node. Added `import_flags: []`; no Lean or mathematical statement
changed. The next deliver2.py --no-push passed preflight and compiled both modules,
printing `OK (dry run)` for commit 5ee28730f19. The packet is now submitted through
the authorized deliver2.py wrapper.
