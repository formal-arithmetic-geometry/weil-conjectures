## Worker report

The item states Milne, Algebraic Groups (2017), Proposition 17.61(a), printed
p.372, with the all-algebra centralizer condition of Proposition 1.92,
pp.33--34. The source PDF pages 384 and 45--46 were read directly, as was the
current blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/
sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3). This extracted
lemma supports the inherited alteration/moduli/PGL/reductive-centre chain;
it is not itself a unit statement.

The previous BLOCKED ending concerned stage 1. The current standing brief,
section 0, explicitly authorizes stating an accepted split in stage 2. The
live queue lists this item at stage 2, the node has a reviewed split and no
Lean record, and there is no released repair note for it. The accepted
statement and split are preserved verbatim. Only lean and the permitted
additions to stmt_deps change.

Main declaration:
`AlgebraicGeometry.ReductiveTorusCentralizer.reductive_torus_self_centralizer`
in `Sheaf.AlgebraicGeometry.ReductiveTorusSelfCentralizer`.
Its proof is exactly `sorry`. Its docstring contains the four proof steps of
the DAG: the closed factorization locus construction and its universal point,
smoothness/connectedness and Borel containment over the algebraic closure,
Chevalley's intersection formula killing the unipotent radical, and descent
of defining ideals by injectivity of scalar extension of vector spaces.

Clause-by-clause comparison:

- The field is `{k : Type u} [Field k]`. The closure is the existing
  `AlgebraicClosure k`; a second arbitrary closure datum is unnecessary.
- `T G : Grp (Over (Spec (.of k)))` supplies the two k-group schemes with
  their actual multiplication, identity, and inverse diagrams. `i : T ⟶ G`
  is a group-scheme homomorphism. `hi : IsClosedSubgroupScheme i.hom.hom`
  is precisely the stipulated closed subgroup inclusion.
- Affineness and finite type of G are the first conjunct
  `SolvableGroupStructure.IsAlgebraic G` of `hG : IsReductive G`:
  `IsAffine G.X.left`, `LocallyOfFiniteType G.X.hom`, and
  `QuasiCompact G.X.hom`. The ambient convention for T is explicitly
  `hT : SolvableGroupStructure.IsAlgebraic T`.
- Smoothness is `Smooth G.X.hom` inside IsReductive. Geometric connectedness
  is `ConnectedSpace` of the underlying scheme of
  `(MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj G`.
  It entails connectedness over k; no perfectness or characteristic
  hypothesis is imposed.
- Reductivity's absence of a nontrivial smooth connected normal unipotent
  subgroup is the universal quantifier over U and its closed normal inclusion
  j into that very scalar extension of G. `ConnectedSpace U.X.left` and
  `SolvableGroupStructure.IsUnipotent U` impose connectedness and smooth
  faithful-matrix unipotence. The latter existing predicate includes the
  smooth structure map and a closed faithful GL_n representation with
  `(r(x)-1)^N = 0`, `0 < N`, over every algebraically closed extension.
  `Nonempty (U ≅ Grp.trivial _)` means the subgroup is trivial as a group
  scheme, not merely on geometric points. Affine finite type of U is the
  ambient closed-subgroup convention in the node.
- `ht : MultiplicativeType.IsTorus T` uses the existing finite-product
  definition: after algebraic closure it is a split torus of rank n : ℕ.
- Geometric maximality is `hmax : IsMaximalTorus (...baseChange.map i)`.
  The definition requires the closed torus inclusion and says that whenever
  it factors through another closed torus subgroup, the factoring group
  homomorphism is an isomorphism. Thus there is no strictly larger torus
  subgroup. It does not assert that T contains every torus in G (which
  would incorrectly say largest rather than maximal).
- The commutative k-algebra A is universally quantified as
  `(A : Type u) [CommRing A] [Algebra k A]`. `centralizerPoints i A` is a
  concrete set of morphisms `StandardGroupSchemes.affine k A ⟶ G.X`.
- For every commutative k-algebra B and algebra map `f : A →ₐ[k] B`, the
  predicate tests every `t : affine k B ⟶ T.X` and requires
  `Commute (StandardGroupSchemes.map k f ≫ g) (t ≫ i.hom.hom)`.
  Such f is exactly an A-algebra structure compatible with k. Thus this
  quantification is the node's all-A'-algebras condition; it includes
  noninjective maps and the zero algebra and does not require reducedness.
- The conclusion is the set equality between those points and
  `Set.range (fun t : affine k A ⟶ T.X ↦ t ≫ i.hom.hom)` for every A.
  Since hi makes this map injective, T represents this subfunctor via the
  specified closed inclusion. Both sides have the inherited restriction
  maps given by precomposition, so equality on every algebra is precisely
  equality of subfunctors, not only a bijection on field points. There is
  no additional representability assumption and no unspecified centralizer
  scheme chosen from an existence theorem.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj` and its
  bundled `Grp` (over-category group schemes).
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsSubgroupScheme`, `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `affine`, `map`,
  `multiplicative`, `multiplicativeGroup`, with the Laurent Hopf law.
- Newly cited landed node def-sfb-tori-multiplicative-type:
  `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`,
  `MultiplicativeType.baseChange`, `splitTorus`, `IsTorus`.
- Newly cited landed node def-sfb-solvable-group-structure:
  `Sheaf.AlgebraicGeometry.SolvableGroupStructure`,
  `SolvableGroupStructure.IsAlgebraic`, `IsUnipotent`.
- The further newly cited definition node and its declarations are listed
  below. There is no repaired dependency module or private replacement.

Available proof modules are plain imports: pullbacks, closed immersions,
properness, the upstream proper/smooth pullback theorem, the upstream
smooth-geometrically-reduced instance, and ideal-sheaf subschemes. The
three extracted geometric input nodes and constant-source factorization
locus have no recorded Lean modules yet, so none is invented or imported.
The affine-morphism correspondence node likewise has no recorded module.
Statement dependency imports are public and each file uses module mode
with `@[expose] public section` and `set_option autoImplicit false`.

Edge cases checked before writing: rank zero is allowed by n : ℕ in the
recorded torus definition; G = T and the trivial group satisfy the intended
reading; a nonmaximal torus such as the identity in GL_2 fails hmax;
G_a × G_m fails reductivity because of its normal G_a; the diagonal torus
in GL_2 has the expected self-centralizer. No smoothness of arbitrary
centralizers is assumed. Positive characteristic and imperfect k are
allowed. Test algebras include dual numbers and other nonreduced algebras,
noninjective algebra maps, and the zero ring. All test algebras use the
same object universe u as k and the schemes, matching the existing
small-algebra functor-of-points convention and avoiding a smaller independent
universe that could make the quantifiers vacuous. No infinite rank restriction
or arbitrary-map replacement of scalar extension occurs.

Searches performed with the prescribed msearch.py wrapper (recorded in
searches.jsonl):

- LeanFinder: “The scheme theoretic centralizer of a geometrically maximal
  torus in a reductive algebraic group scheme equals that torus” returned
  eight Lie/abstract-group results, including Cartan self-normalization;
  no algebraic-group-scheme theorem.
- Loogle: `IsReductive, IsTorus, centralizer` returned no hits, with unknown
  identifier IsReductive.
- grep in Mathlib/AlgebraicGeometry:
  `centralizer.*torus|torus.*centralizer|[Rr]eductive|[Uu]nipotent`
  returned zero hits.
- LeanSearch: “The scheme theoretic centralizer of a maximal torus in a
  reductive group is the torus” returned eight abstract-group results,
  including Subgroup.centralizer; no exact match.
- LeanSearch: “Reductive algebraic group maximal torus scheme theoretic
  centralizer definitions” returned eight abstract-group/subalgebra results.
- LeanFinder: “A reductive algebraic group is smooth geometrically connected
  and has no nontrivial smooth connected normal unipotent subgroup after
  algebraic closure” returned eight Lie-algebra results; no exact definition.
- Full Mathlib grep:
  `IsReductive|IsMaximalTorus|centralizerPoints|def.*[Rr]eductive`
  returned zero hits.
- rg of both project source roots for IsReductive, IsTorus, maximal tori,
  centralizers and unipotence found and reused ToriMultiplicativeType and
  SolvableGroupStructure. The upstream matrix-centralizer equations are
  for closed subgroups of GL_n, not the general functor or this theorem.
  Searching the item id in WeilConjectures found no existing statement.
- DAG search found no definition node for reductivity/maximality/centralizer
  points; theorem nodes using these words do not supply the definitions.
  `tools/blueprint_refs.py search reductive` found zero blueprint nodes;
  `... search centralizer` found three unrelated affine/Lie geometry nodes.
  `... ancestor` returned None, agreeing with the item's recorded ancestor.

Both delivered modules compiled separately in dependency order through
scompile.py against the published live build. No errors or warnings remain
other than the permitted theorem sorry warning (the wrapper suppressed it).
No statement correction or STATEMENT-DISPUTED issue was needed.

## New nodes

`def-sfb-reductive-torus-centralizer-terminology` supplies the previously
missing reductivity predicate, maximal-torus predicate, and explicit
all-algebra centralizer set. Its source is Milne's Chapter 17 convention,
Proposition 17.61(a), and Proposition 1.92. It reuses the existing torus,
scalar-extension, affine finite-type, and smooth-matrix-unipotence notions;
it does not redefine any of them. The three new declarations have real
Prop/Set bodies, with no postponed data or auxiliary theorem. LeanSearch,
LeanFinder, Mathlib grep, both source-tree searches, DAG searches, and the
blueprint search above found no existing definition of these missing notions.
The item cites this new node and the two existing terminology nodes. The
new node cites all the definition nodes it uses, carries the inherited null
blueprint ancestor and via chain, and records the actual searches as returned.

## Second reading by Q23

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
