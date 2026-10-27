## Worker report

The delivery states `AlgebraicGeometry.semiabelian_hom_finite_free` in
`Sheaf.AlgebraicGeometry.SemiabelianHomFiniteFree`, with its proof exactly `sorry`.
Its new definition module is `Sheaf.AlgebraicGeometry.SemiabelianGroupSpace`.
There are no definition-data placeholders and no statement correction.

Clause-by-clause reading of the item and its Lean:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- A commutative group algebraic space is represented by a functor
  `(Over (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u}` whose underlying set presheaf
  satisfies the existing `AlgebraicSpace.IsAlgebraicSpace` predicate and the
  fppf sheaf condition. This encodes precisely functorial group operations;
  natural transformations into `AddCommGrpCat` are the group homomorphisms.
  The category of such functors has the pointwise preadditive Hom structure.
- `hG : IsSemiabelianGroupSpace G` and `hH : IsSemiabelianGroupSpace H`
  impose the item's entire semiabelian condition on the two spaces.
  The predicate uses the existing algebraic-space definition, not schemes
  in place of spaces. It does not assume that G or H is representable.
- Separatedness is `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)`
  on the actual presheaf diagonal. Thus every scheme base change of the
  diagonal is represented by a closed immersion.
- Smoothness and finite type are expressed by existence of a representable
  etale surjective scheme atlas U with `Smooth U.hom`,
  `LocallyOfFiniteType U.hom`, and `QuasiCompact U.hom`. This is the usual
  atlas criterion: smoothness descends etale locally; a finite-type space
  has a quasi-compact etale atlas of finite type over the field (take a finite
  collection of affine etale charts), and conversely such an atlas detects
  finite type. There is no extra global affine-atlas assumption.
- The split torus is the already recorded `relativeSplitTorusFunctor` at
  `Spec k` and `r : ℕ`; its components are exactly tuples of units in global
  sections, including the terminal group when r=0. No second torus is defined.
  The arrow i is into the multiplicative notation for G's additive group.
- The quotient is `commutativeGroupSchemeAdditivePoints A`, for
  `A : Over (Spec k)`, `[GrpObj A]`, `[IsAbelianVariety A]`. The quantified
  `IsCommMonObj A` is automatic for abelian varieties, as the imported
  `IsAbelianVariety.isCommMonObj` proves. It retains the actual given group law.
- Exactness is pointwise injectivity of i and the equivalence
  `q_U(g)=0 ↔ ∃ t, i_U(t)=Multiplicative.ofAdd g` on every test scheme U.
  Consequently i identifies T with the entire sheaf kernel. The zero composite
  follows by taking any t; no separate untyped or arbitrary kernel is used.
  `Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec k))`
  for the underlying q is exactly local lifting of sections on fppf covers.
- Hom is literally `G ⟶ H`. The first conclusion is a finite integer basis,
  `∃ n : ℕ, Nonempty (Module.Basis (Fin n) ℤ (G ⟶ H))`.
  A finite basis is the requested finite-rank freeness using Mathlib's basis
  notion, rather than an unrelated free abstract group of rational points.
- End is Mathlib's `End G`. Its canonical `Ring` instance is already constructed
  in `CategoryTheory.Preadditive.Basic`; it has the same pointwise addition.
  Its finite integer basis is the second conclusion. The remaining clauses
  specify `f * g = g ≫ f` (f after g), and `(1 : End G) = 𝟙 G`.
  Associativity, both distributive laws and the unital ring axioms are carried
  by this actual Ring instance, not by an arbitrary ring on another carrier.

Dependency declarations read and used:

- `Field` in Mathlib.Algebra.Field.Defs; `IsAlgClosed` in
  Mathlib.FieldTheory.IsAlgClosed.Basic. The algebraic-closure dependency's
  mathlib_match explicitly gives `IsAlgClosed` for this predicate.
- `AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace`,
  `.IsRepresentableWith`, `.IsEtale`, `.IsSurjective` in
  Sheaf.AlgebraicGeometry.AlgebraicSpace. Its full signatures and scheme-test
  pullback definition were read; the predicate is applied directly.
- `AlgebraicGeometry.Scheme.fppfTopology` and `.fppfPrecoverage` in
  Mathlib.AlgebraicGeometry.Sites.Fpqc, with the slice topology
  `GrothendieckTopology.over`. The precoverage is jointly surjective, flat,
  locally finitely presented families.
- `AlgebraicGeometry.IsAbelianVariety` in
  WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs, and its automatic
  commutativity in `.Basic`: proper, smooth and connected, with GrpObj separate.
- `Module.Free` and `Module.Basis` in Mathlib.LinearAlgebra.FreeModule.Basic;
  the finite-index basis states exactly the requested finite-rank case.
- New definition node def-sfb-semiabelian-group-space, as described below.
  This reuses `relativeSplitTorusFunctor` owned by def-sfb-relative-torus in
  Sheaf.AlgebraicGeometry.RelativeTorus. Its actual product-of-units definition
  and the node statement were read.

Proof dependencies: the available abelian Hom module
Sheaf.AlgebraicGeometry.AbelianVariety.HomFiniteFree is a plain proof import;
its full subgroup, Hom, theorem signature and proof docstring were read.
Mathlib.LinearAlgebra.FreeModule.PID provides `Submodule.basisOfPid` from the
subgroup-freeness dependency's mathlib_match. The algebraic-space module is
public via the definition module. The torus-abelian vanishing and split-torus
matrix nodes currently have neither a Lean record nor a mathlib_match, so no
module import is possible for them; their intended uses remain in the full
four-step proof docstring. They are proof prerequisites, not notions required
to type this statement. No downstream theorem is needed to define any object.

Sources checked: local Milne AV I Theorem 10.15 (printed pp.49–50) states finite
freeness of abelian Hom; Milne Algebraic Groups Theorem 12.9 (pp.233–234) gives
the torus character description, and Section 8(e), p.151, gives the
anti-affine-to-affine vanishing. Deligne's primary Numdam PDF was opened at
https://numdam.org/item/AST_1985__127__131_0.pdf: Section 1.1 explicitly defines
semiabelian group algebraic spaces and notes representability over a field.
The Hom proof follows the node's agent-derived filtration argument, rather
than attributing the entire semiabelian assertion to Milne AV 10.15.

Edge cases: r=0 is the empty product, not excluded; zero abelian quotient and
pure torus are allowed; zero torus gives an abelian variety; G=0 gives the
zero End ring and 1=0=id, and n=0 permits the empty basis. Neither the field
characteristic nor positive dimension is restricted. The same universe u is
used for schemes, fields and section values, matching the recorded
algebraic-space interface. The group has an identity section so no empty
nontrivial group space is accidentally admitted. Hom includes the zero map.

Searches actually run through msearch.py:

- LeanFinder: “Homomorphisms of semiabelian group algebraic spaces form a free
  abelian group of finite rank”: eight hits, chiefly Module.Free.addMonoidHom
  and Module.Finite.addMonoidHom; these concern abstract underlying groups and
  assume finite generation already, so are not this result.
- Loogle: `"Semiabelian", "Hom"`: zero hits.
- Mathlib grep: `Semiabelian|SemiAbelian|semiabelian|semiAbelian` in
  AlgebraicGeometry: zero hits.
- LeanSearch: “Semiabelian algebraic space as a smooth separated finite type
  fppf sheaf of commutative groups extension of abelian variety by split torus”:
  eight hits including smooth manifold sheaves and AddGroupExtension; no match.
- LeanFinder: “Semiabelian group algebraic space exact fppf extension split
  torus abelian variety”: eight hits about cotangent exact sequences and
  general exactness; no definition of this notion.
- Mathlib grep: `IsSemiabelian|SemiabelianGroupSpace|semiabelian|SemiAbelian`
  in AlgebraicGeometry: zero hits.
- Project rg on lean/WeilConjectures and lean/Sheaf: no semiabelian notion in
  WeilConjectures; Sheaf has HasSemiabelianGeometricFibres for group schemes,
  plus its consumers, not the algebraic-space predicate needed here.
  The exact item-id grep in WeilConjectures returned no match.
- DAG search of definition nodes, and `blueprint_refs.py search semiabelian`:
  no group-algebraic-space definition, zero blueprint matches. The old
  IsSemiabelian hit in lem-sfb-cubical-ample-norm-reflection is only a search
  query. Existing RelativeTorus and ToriMultiplicativeType were opened; the
  former's units functor is reused directly. `blueprint_refs.py ancestor`
  returns None for this supporting item, matching its inherited from record.

Validation: both delivery modules compiled separately through scompile.py,
including their dependency order and module-mode imports, with no errors or
unexpected warnings. All universes and variables are explicitly bound and
`autoImplicit` is false. No local instances, private definitions, or local
notation are used. The theorem proof is exactly sorry. The only intermediate
compile fault, an unqualified whiskerRight name, was fixed to
Functor.whiskerRight before the clean compile. The delivery dry run passed preflight and compilation;
the final packet also normalizes the new node’s TeX to single backslashes.

## New nodes

`def-sfb-semiabelian-group-space` registers the actual group-algebraic-space
predicate needed by the item's opening definition, and its helper
`commutativeGroupSchemeAdditivePoints`. Source: Deligne Section 1.1, p.131,
over an algebraically closed field, with the split units functor from
Milne Section 12 and Stacks 022U. The node explicitly spells out the atlas,
closed diagonal, exact kernel and fppf local surjectivity. The three search
kinds and project/DAG/blueprint searches above are recorded in its
mathlib_searches with their actual logged outputs. Existing notions are used:
this neither redefines algebraic spaces nor creates another split torus.
The helper constructs point groups and restriction maps from Yoneda's actual
scheme morphisms. All data are fully defined. The item cites this new node.
The distinction from HasSemiabelianGeometricFibres is essential: that
predicate accepts schemes with group structures and concerns geometric base
changes, whereas this definition concerns algebraic spaces over k themselves.

## Second reading by Q119

A separate agent was not started, as the dispatch brief expressly forbids it.
I reopened the item, the new node, and both source modules for a second pass.
This is a self-check, not a claim of independent review; the maintainer's
independent review remains the delivery review.

The second pass checked k, G, H and both complete semiabelian hypotheses
against the definition, the pointwise Hom addition against the functor-category
Preadditive instance, and both finite-basis conclusions and the multiplication
and unit against Mathlib's actual End Ring instance. It found a potential
one-definition-per-notion fault in the first draft: a separately written
finite product of units. I removed that declaration and now use the existing
relativeSplitTorusFunctor directly, only converting G to multiplicative notation
in the inclusion's target. The pointwise image/kernel clause now explicitly
uses Multiplicative.ofAdd to identify those two notations. Both files were
recompiled after this change. No mathematical hypothesis, clause, edge case
or object has been changed from the item; no STATEMENT-DISPUTED remains.
