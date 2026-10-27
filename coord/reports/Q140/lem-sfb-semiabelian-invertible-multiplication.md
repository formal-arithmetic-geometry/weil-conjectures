## Worker report

The module `Sheaf.AlgebraicGeometry.SemiabelianInvertibleMultiplication` states
`AlgebraicGeometry.AlgebraicSpace.semiabelian_invertible_multiplication`, with its
proof postponed by `sorry`. The only helper is the real pointwise power natural
transformation `commutativeGroupPresheafMultiplication`. It belongs to this node's
canonical multiplication construction (brief §1, missing helpers), is listed in
`lean.declarations`, and has no postponed data or auxiliary theorem. Its naturality
field is the existing group-homomorphism `map_pow` identity.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- Group algebraic space over k: `G : AlgebraicSpace (Spec (.of k))`, using precisely
  the recorded full subcategory of fppf sheaves with representable diagonal and an
  étale surjective scheme atlas. `F : (Over (Spec (.of k)))ᵒᵖ ⥤ CommGrpCat.{u}` and
  `e : F ⋙ forget CommGrpCat ≅ G.obj.obj` specify its natural commutative group law.
  This is data for the stated group object, rather than a scheme hypothesis or an
  arbitrary endomorphism. Transport along e gives the functorial operations on G.
- Smooth: `hsmooth : MapIsLocally (@Smooth) (groupSpaceProjection G)`, the existing
  compatible étale-chart predicate. Separated: `hsep : MapIsSeparated ...`, whose
  definition says that the relative diagonal is represented by closed immersions.
  Finite type: `hfinite : MapIsFiniteType ...`, the existing quasi-compactness plus
  locally-finite-type chart predicate. No integrality condition from
  `IsSmoothIntegralGroupSpace` is imposed.
- Split torus of finite rank: `t : ℕ` and `MultiplicativeType.splitTorus k t`.
  Its recorded construction is the iterated product of the canonical Laurent
  multiplicative group, starting with the trivial group at rank zero. Thus it is
  exactly G_m^t, with G_m(U) = Γ(U,O_U)^×, not a constant group of k-points.
  Giving this torus directly as the kernel is the same as giving T together with
  its displayed isomorphism to G_m^t; it does not restrict the extension.
- Abelian quotient: `A : Grp (Over (Spec (.of k))) [IsAbelianVariety A.X]` supplies
  the given scheme group law and the recorded proper, smooth, connected predicate.
- Extension homomorphisms: `i` and `q` are natural transformations valued in
  `GrpCat`, from the represented torus to F and from F to the represented A.
  `yonedaGrp.obj` uses the actual group-scheme operations, so these are group
  homomorphisms on all scheme-valued points, not arbitrary maps of sets.
- Exactness at the left/middle: `hkernel : IsPullback ...` is the square with top
  i, left the torus structure map, right q, bottom the unit of A. It identifies the
  whole sheaf kernel, including its injective inclusion, by the universal property.
  The square is in presheaves; fppf sheaves are closed under these limits, so this
  is precisely the sheaf-kernel square. No extra monomorphism assumption is needed.
- Quotient exactness: `hlift : Presheaf.IsLocallySurjective
  (Scheme.fppfTopology.over (Spec (.of k))) ...` says that each section of A lifts
  to F locally for the given fppf topology. The generating fppf families are exactly
  jointly surjective flat locally finitely presented scheme morphisms. The target
  represented sheaf and F (via e) are already fppf sheaves.
- Positive integer: `n : ℕ`, `hn : 0 < n`. Invertible in k: `hunit : IsUnit (n : k)`.
  This includes every positive n in characteristic zero, and exactly the integers
  prime to the characteristic in positive characteristic.
- Multiplication [n]_G: `e.inv ≫ commutativeGroupPresheafMultiplication F n ≫ e.hom`.
  Its middle component is exactly x ↦ x^n; multiplicative notation here renders
  the node's sum of n identities. No unspecified comparison map is introduced.
- All four conclusions, including the explicit scheme-test clause, are expressed
  simultaneously by `IsRepresentableWith (fun _ _ p ↦ IsFinite p.left ∧
  Etale p.left ∧ Surjective p.left)` applied to that multiplication map. Unfolding
  it quantifies over every `U : Over (Spec (.of k))` and `a : yoneda.obj U ⟶ G.obj.obj`,
  hence by Yoneda over every y in G(U). It supplies a scheme over U and an actual
  `IsPullback` square representing exactly U ×_[y,G,n] G. The projection p is
  finite, étale and surjective. `IsFinite` extends `IsAffineHom` with finite ring
  maps on affine sections, i.e. coordinate algebras finite as modules. `Etale` is
  the recorded scheme étale predicate. There is no constant-rank, nonemptiness or
  scheme-source assumption.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (the algebraically closed
  clause of def-weil-algebraic-closure's Mathlib match).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, and the existing scheme-test/atlas predicates.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`, `Scheme.fppfTopology`;
  `Mathlib.CategoryTheory.Sites.Over`: `GrothendieckTopology.over`.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`: `IsAbelianVariety`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`, with affine-ring-map definition.
- `Sheaf.AlgebraicGeometry.RegularGroupSpace`: `groupSpaceProjection`. Its definition
  is the unique natural map to the represented base; no group-law choice is hidden.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsSeparated`, `MapIsFiniteType` (read their full definitions).
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: `MultiplicativeType.splitTorus`;
  its factor `StandardGroupSchemes.multiplicative` and Laurent Hopf group law were read.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: `yonedaGrp`, `yonedaGrpObj`,
  `GrpObj.Hom.group`, and `GrpObj.Hom.commGroup`; these preserve the represented laws.
- `Mathlib.CategoryTheory.Sites.LocallySurjective`: `Presheaf.IsLocallySurjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.

The three already-landed definition nodes for the structure map, chart properties
and split torus were appended to stmt_deps under the existing-landed-node rule.
The original six statement dependencies are retained, and the natural-language
statement, proof and proof_deps are unchanged. No new notion node or dependency
repair is needed.

Plain proof imports supply AdjoinRoot's monic quotient basis, StandardEtalePair's
standard étale algebra, finite and étale permanence, universal-injectivity base
change, `isIsogeny_npow_id`, `etale_npow_id`, and
`fppfLocalRepresentationsFullyFaithful`. The finite-étale fppf descent proof node
has no Lean record in the read clone, so it has no module to import. It is not a
statement prerequisite. All six proof steps, including the local root equations,
the torsor translation, overlap cocycle and descended scheme projection, are in
the theorem docstring. Transitive public imports provide the scheme fibre product,
fppf topology and covering-base-change APIs.

Sources opened: Milne Algebraic Groups PDF, printed p.152 (8.21), pp.233–234
(12.9(b)). These give the stated abelian and diagonalizable inputs; as the node
explicitly says, the semiabelian algebraic-space consequence is its supplied
local-trivialization and descent argument, not a theorem quoted verbatim from
Milne. The source text and the six node proof steps agree with this formulation.

Edge cases checked before writing: t=0 is the trivial torus, so abelian varieties
are included; A=the trivial abelian variety leaves the split-torus case; n=1 gives
the identity, n=0 is excluded exactly by hn; positive characteristic dividing n is
excluded exactly by hunit; no dimension or characteristic-zero restriction occurs.
Empty U is admitted by the universal scheme-test quantifier (its representing
pullback is empty and its projection is still surjective). Non-affine and
nonreduced U are included; the group/kernel hypotheses are functorial on all
schemes, not only fields. One explicit universe u is shared by k, schemes,
sections, and test schemes, as in the recorded algebraic-space API. There are no
auto-bound implicit variables (`set_option autoImplicit false`).

Searches actually run:

- msearch leanfinder: "Multiplication by an invertible positive integer on a
  semiabelian algebraic space is representable finite etale surjective". Eight
  hits concerned étale morphism permanence, standard étale algebras and affine
  space surjectivity; none stated this theorem or its canonical map.
- msearch loogle: `"AlgebraicGeometry", "npow"`. Zero hits.
- msearch grep: `semi.?abelian|[Ii]sogeny|AbelianVariety`, subdirectory AlgebraicGeometry.
  Zero Mathlib hits.
- msearch leansearch: "Multiplication by an invertible integer on a semiabelian
  group is finite etale and surjective". Eight abstract-group scalar-multiplication
  hits (including exists_zsmul_surjective and nsmulCoprime), none a geometric match.
- rg of `lean/WeilConjectures` for semiabelian/semi_abelian, and for the item id:
  no declaration of this statement. rg of its AlgebraicGeometry subtree found no
  semiabelian definition. The abelian-variety multiplication statements were read
  and are proof inputs, not statements about algebraic-space extensions.
- rg of `lean/Sheaf` for semiabelian, AlgebraicSpace, IsRepresentableWith and group
  structures found the existing chart/group/split-torus interfaces used above.
  `HasSemiabelianGeometricFibres` is about geometric fibres of a scheme group,
  and therefore cannot replace an algebraic-space extension. No duplicate was made.
- Exact-name rg across Mathlib, WeilConjectures and Sheaf found neither new name.
- `python3 tools/blueprint_refs.py search semiabelian`: zero blueprint nodes.
  Definition-node searches of dag/nodes found the already-used split-torus and
  group-space records; no independent new definition was required.

Validation: scompile.py compiled the module both as a sandbox module and under its
final library name cleanly (4.0 s and 2.2 s). The first compile diagnosed ambiguity
between monoidal and functor whiskering; qualifying `Functor.whiskerRight` repaired
it without changing the statement. All variables and universes are explicit.
No mathematical statement fault or STATEMENT-DISPUTED issue was found.

## Second reading by Q140

This is a separate self-reading pass, not an independent agent review: the explicit
dispatcher instruction forbids starting another agent. The maintainer's independent
review remains necessary. I reopened the node, the final module and the definitions
of IsRepresentableWith, MapIsLocally, MapIsSeparated, MapIsFiniteType, splitTorus,
yonedaGrp and IsLocallySurjective. I checked the matching described above against
the actual types: hkernel's four arrows form precisely the kernel square; its
upper-left and lower-left represented presheaves reduce definitionally to the
underlying yonedaGrp presheaves. The quotient arrow is a group homomorphism and
hlift tests every section. The transported power is conjugated in the correct
direction, from G through e.inv to F and back by e.hom. The conclusion's property
is on the SAME representing projection for all three properties. The smoothness,
separatedness and finite-type binders add no integrality/properness condition on G.
No mismatch was found, and no theorem or definition was weakened. I confirmed the
node's recorded signature is the exact final theorem text before `:=`, and the
module has only the helper construction and this node's sorried theorem.
