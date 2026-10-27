## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleSchemeLineMorphismGluing` states
`AlgebraicGeometry.Scheme.Modules.existsUnique_etaleSchemeLineMorphism` with one
`sorry`, and supplies two explicit helpers for its canonical comparison equations.
No statement correction, new node, dependency repair, or disputed statement is needed.
The node copy changes only `lean`.

Sources read: Stacks `descent.tex`, Tag 023Q,
`lemma-fpqc-universal-effective-epimorphisms` (the scheme-map sheaf condition),
and Tag 023T, `proposition-fpqc-descent-quasi-coherent` (especially fullness and
faithfulness); `spaces-descent.tex`, Tag 04W8, the proposition of the same name.
These give descent for arbitrary fpqc families, hence for the stipulated etale
families after the topology-comparison proof dependency. The theorem postpones
exactly the node's five-step argument, reproduced in its docstring with the named
proof dependencies.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Schemes S, X, Y | `{S X Y : Scheme.{u}}` |
| Maps X to S and Y to S | `(a : X ⟶ S) (d : Y ⟶ S)` |
| Invertible modules L on X and M on Y | `(L : X.Modules) (M : Y.Modules) [IsInvertible L] [IsInvertible M]` |
| Arbitrary indexed etale covering | `{I : Type v} (U : I → S.Etale)`; each `U i` includes its scheme, structural map, and etaleness |
| Joint surjectivity | `hcover : ∀ x : S, ∃ (i : I) (z : (U i).left), (U i).hom z = x` |
| X_i and Y_i | `Limits.pullback a (U i).hom` and `Limits.pullback d (U i).hom` |
| Projections to X and Y | `pullback.fst a (U i).hom` and `pullback.fst d (U i).hom` |
| L_i and M_i | The `tensorPullback` objects along these first projections, in the type of `μ` |
| Scheme maps b_i | Binder `b`, with precisely the two base-changed schemes as source and target |
| Each b_i is over U_i | `hover`, equality of its composite with the second projection and the second projection of X_i |
| Module maps b_i* M_i to L_i | Binder `μ`, an arbitrary module homomorphism of those exact objects |
| Scheme maps agree on overlaps | The existential equality `hb` inside `hcompat`, for every test pair `r,s` with `hp` (same X component) |
| Module maps agree under canonical identifications | The equation in `hcompat`, using `lineHomPullToTest`, `tensorPullbackCompositionIso`, and equality transports `eqToHom` |
| Global S-morphism b and module map μ | The sigma witness `B`; `B.1.val` is its scheme map, `B.1.property` is the equation over S, and `B.2` is the module map |
| Every base change is the given local pair | The first conjunct, `∀ i, IsLineHomBaseChange ... B.1.val (b i) ... B.2 (μ i)` |
| Uniqueness of the pair | The second conjunct: every sigma witness `B'` satisfying the same base-change equations equals `B` |
| If all b_i and μ_i are isomorphisms, so are b and μ | The final implication from `∀ i, IsIso (b i) ∧ IsIso (μ i)` to `IsIso B.1.val ∧ IsIso B.2` |

The overlap formula is the original condition, with its identifications expanded,
not an additional descent hypothesis. Write p_i and q_i for the first projections
and f_i = b_i followed by q_i. The local map is first expressed as
ν_i : f_i* M → p_i* L by the recorded composition isomorphism followed by μ_i.
`lineHomPullToTest r f_i p_i M L ν_i` is explicitly
C(r,f_i) followed by r*(ν_i) followed by C(r,p_i) inverse, so its source and target
are `(r ≫ f_i)* M` and `(r ≫ p_i)* L`. The equality transports in `hcompat`
identify those sources using hb and those targets using hp.

The scheme X_i ×_X X_j is canonically X ×_S (U_i ×_S U_j). Every pair r,s in
`hcompat` factors uniquely through X_i ×_X X_j, by hp. Consequently ordinary
compatibility on that overlap gives every displayed test equation by pulling
back, naturality, and associativity of the composition comparisons. Conversely,
take T = X_i ×_X X_j and its two projections to recover the overlap equation.
Etale base components are already fixed by `hover`. Equality of the Y components
hb is therefore equivalent to equality of the base-changed b_i over U_i ×_S U_j.
The test scheme has the same universe u as X, so this includes the actual overlap
and is not a vacuous test over a smaller universe.

`IsLineHomBaseChange` expands base-change agreement without constructing or
choosing another scheme map. Its hb fixes the Y component; the U_i component is
fixed by the over equations. Its module equation is
C(p_i,b) followed by p_i*(μ) = transport(hb) followed by C(b_i,q_i) followed by μ_i.
Thus it is precisely equality of the local map with the canonical base change.
Both helpers belong to the canonical-map interface of this node; they introduce
no alternative definition of schemes, invertibility, modules, or pullback.
Their data are explicit composites, with no postponed proof or arbitrary choice.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (Zariski local triviality of
  rank one). The same module supplies the proof dependency `IsInvertible.pullback`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.Etale`,
  `Scheme.smallEtaleTopology`, and `ofArrows_mem_smallEtaleTopology_iff` identify
  the cover binder and pointwise surjectivity with the recorded small-site cover.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, and the
  universal property. Scheme pullbacks exist by the imported scheme API.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: public access to
  the existing tensor formula `Scheme.Modules.tensorPullback`; the recorded
  section-normalized adjunction, identity and composition comparisons were read.
  No new pullback functor is defined.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`:
  `exists_tensorPullbackAdjunction`, whose sectionwise unit is 1 tensor m.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso`:
  `tensorPullbackCompositionIso`, the canonical conjugate of pushforward
  composition under the recorded tensor adjunctions. This is the comparison
  used in both helpers and every overlap equation.

The stated proof modules are imported without `public`:
`Sheaf.AlgebraicGeometry.FpqcFinerThanEtale` (the recorded
`Scheme.fpqcCover_of_smallEtaleCover`),
`WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionAssociativity`
(`tensorPullbackCompositionIso_associativity`), and
`WeilConjectures.AlgebraicGeometry.Descent` (`bijective_toDescentData_map`,
full faithfulness). The Mathlib proof dependencies are imported via
`Mathlib.AlgebraicGeometry.Sites.Fpqc` (subcanonicity of fpqcTopology) and
`Mathlib.CategoryTheory.Sites.Precoverage` (base change of covers).
The invertible-pullback proof dependency shares the public invertible-module
module. No proof import closes a cycle.

Edge cases checked before writing:

- I may be empty. Then `hcover` forces S to be empty, and the given structure
  maps force X and Y to be empty. There is a unique scheme map and a unique
  module map; the vacuous local isomorphism condition correctly gives both
  global isomorphisms. There is no Nonempty assumption on I or on any scheme.
- The identity cover and repeated/empty charts are permitted. Canonical
  composition comparisons and equality transport give their ordinary equations;
  no chosen trivialization or scalar normalization is added.
- μ_i may be zero or noninvertible; existence and uniqueness have no IsIso
  hypothesis. The extra conclusion is only conditional on all local maps being
  isomorphisms. Invertibility of L and M does not make every module map invertible.
- Infinite covers and index types in arbitrary universe v are included; no
  indexed limit, finiteness, quasi-compactness, separatedness or field hypothesis
  is added. Test schemes have universe u, including the actual fibre products.
- Pair uniqueness uses a dependent sigma, so it compares the module maps after
  equality of their underlying scheme maps; over-equation proofs are irrelevant.

Searches actually run for this item:

- `msearch.py ... leanfinder "Compatible morphisms of schemes and homomorphisms
  between line bundles glue uniquely on an etale covering"`: eight hits, including
  `Scheme.Cover.glueMorphisms`, `Cover.hom_ext` and ordinary scheme gluing. None
  states joint etale descent of scheme and module homomorphisms.
- `msearch.py ... loogle 'AlgebraicGeometry.Scheme, "descent"'`: zero hits.
- `msearch.py ... grep '(lineMorphism|LineHom|etale.*gluing|tensorPullbackHomAlong)'
  AlgebraicGeometry`: zero hits.
- `msearch.py ... leansearch "Etale descent of morphisms of schemes with
  invertible modules"`: eight hits, including `Scheme.Etale`, etale topologies,
  and algebra etale base change; no exact match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the node id and
  `lineMorphism|LineHom|tensorPullbackHomAlong|etale.*[Gg]lu`: no implementation of
  this node. Read the relevant hits in `PolarizedSchemeEtaleDescent.lean`, which
  supply isomorphism comparisons for descent data, not this arbitrary-map
  theorem. `EtaleFramedLineEffectiveGluing.lean` concerns gluing frames on a fixed
  scheme, and the SpaceLinePresentation modules concern other objects.
- `grep -rn` for the node id in `lean/WeilConjectures`: no hits.
- `rg` for the three proposed declaration names across Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no hits.

Validation: the required `scompile.py Q31 ...` compiled this complete module
against the current server sources in 1.9 seconds, with no errors or warnings
(the project's expected sorry warning is suppressed by its standard options).
The wrapper's local attempt reported no free disk space, then its normal server
confirmation succeeded; no tool or live source was modified. The first probe
caught an unqualified `pullback` resolving to `Scheme.Modules.pullback` inside
its namespace; the scheme-object expressions now use `Limits.pullback`.
The final record contains the theorem signature verbatim, and each universe and
variable is explicitly bound. Only the theorem body is `sorry`.

## Second reading by Q31

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
