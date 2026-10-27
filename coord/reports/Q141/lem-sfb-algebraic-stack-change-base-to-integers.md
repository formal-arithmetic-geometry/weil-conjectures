## Worker report

Item: `lem-sfb-algebraic-stack-change-base-to-integers`, group Q141, stage 2.

The module `Sheaf.AlgebraicGeometry.AlgebraicStackChangeBaseToIntegers` states
`CategoryTheory.algebraicStack_changeBase_toIntegers`. It supplies concrete auxiliary
constructions belonging to the change-of-base operation introduced in this node.
There is one postponed theorem, with the node's eight-step natural-language proof in
its docstring. Every auxiliary definition has actual data; no object is chosen from
an uncharacterized existence theorem. The original statement and dependencies are
unchanged. There are no new nodes, dependency repairs, or statement disputes.

Clause-by-clause correspondence:

- A scheme S with no hypothesis: `(S : AlgebraicGeometry.Scheme.{u})`. There is no
  quasi-compactness, quasi-separatedness, finiteness or separation assumption on S.
- Size convention: explicit universes `u v₁ w₁ v₂ w₂ v₃ w₃ v₄ w₄` and
  `set_option autoImplicit false`. The schemes lie in `Scheme.{u}`; total categories
  retain independent object and morphism universes. The arbitrary test universes
  `v₄,w₄` are preserved in both quasi-compact-morphism predicates.
- Integers and structure morphism: `Spec (.of (ULift.{u} ℤ))` and
  `AlgebraicGeometry.specULiftZIsTerminal.from S`. The lift places the same integer
  ring in the scheme universe; it adds no arithmetic or geometric restriction.
- A category over Sch/S: `BasedCategory (Over S)`. The predicates imported from
  the dependency modules include the fibred-groupoid and étale-stack conditions;
  an algebraic-stack hypothesis is `IsAlgebraicModuliStack F`.
- The same total category regarded over the integers: `moduliChangeBase g F` is
  exactly `BasedCategory.ofFunctor (F.p ⋙ Over.map g)`. Its objects, arrows and
  category structure are the original ones. Its projection sends T → S to the
  same scheme with map T → S → Spec Z.
- Its map to S: `moduliChangeBaseProjection g F` has underlying functor exactly
  `F.p`, targeting the represented S modeled by `Over S` with projection
  `Over.map g`. This is the model of h_S explicitly used by Stacks 04X5/04WV
  and by the node, rather than a new scheme representation predicate.
- Clause (1), algebraicity: the first conjunction gives
  `IsAlgebraicModuliStack F → IsAlgebraicModuliStack (moduliChangeBase g F)`.
- Clause (1), every given atlas: for every U and given
  `a : BasedFunctor (discreteModuli (yoneda.obj U)) F`, the hypothesis
  `IsSmoothModuliAtlas F U a` yields a smooth atlas b with precisely the same
  scheme U, now `((Over.map g).obj U)`. `moduliChangeBaseScheme g U` sends each
  represented scheme map to the identical scheme map viewed over Spec Z.
  The `ModuliTwoIso` identifies b after this canonical identification with
  `moduliChangeBaseMap g a`. Thus b represents the given atlas, rather than
  an unrelated smooth cover.
- Clause (2), objects of pairs and the inverse construction: for any G over
  Spec Z and `q : G.obj ⥤ Over S`, the equation `q ⋙ Over.map g = G.p` means
  q is precisely a morphism to h_S over Spec Z. The second conjunction asserts
  algebraicity of G iff that of `BasedCategory.ofFunctor q`. Both constructions
  keep the same total category. The recovered projection is q, and forgetting
  it again recovers G.p by the displayed equality. Together with the forward
  construction this is essential surjectivity on pairs and the inverse on objects.
- Clause (2), morphisms and 2-morphisms: `moduliChangeBasePairHom g F G` is the full
  subcategory of absolute based functors with equation `f.toFunctor ⋙ G.p = F.p`.
  The third conjunction gives an equivalence of this category with
  `BasedFunctor F G`, fixing the underlying functors and natural transformations.
  Its natural transformations are automatically over S: their images over Spec Z
  are identities and `Over.map g` is faithful on arrows. For fibred groupoids,
  such vertical natural transformations are invertible, so these are precisely
  the node's 2-isomorphisms. The normalizations identify the maps with the actual
  forgetting operation and hence retain identity, composition and whiskering.
- Clause (2), 2-fibre products: the fourth conjunction takes arbitrary algebraic
  F, G, H and maps f, g. It gives a based equivalence from
  `moduliChangeBase g₀ (moduliTwoFiberProduct f g)` to the absolute 2-fibre product
  of the two changed maps. Equality on the underlying comma objects and `HEq` on
  comma arrows specify the canonical triple-and-arrow comparison; both projections
  are thereby the original projections. This asserts pullbacks over H, without
  identifying products over S with products over Spec Z.
- Clause (3), objects: the fifth conjunction is exactly
  `IsQuasiCompactModuli F ↔ IsQuasiCompactModuli (moduliChangeBase g₀ F)`
  for algebraic F.
- Clause (3), morphisms: the last conjunction, for arbitrary f between algebraic
  F and G, states separately the iff for
  `IsQuasiCompactAlgebraicModuliMap` and the iff for
  `IsQuasiSeparatedAlgebraicModuliMap`. These are the dependency's actual predicates,
  including all quasi-compact algebraic-stack tests and the representability plus
  qcqs algebraic-space projections in the relative-diagonal test.
- Final product convention: `moduliProductOverIntegers F G` is the iso-comma
  product of the projections to Sch/Spec Z. Its objects are (x,y,φ) with φ an
  isomorphism of their absolute base schemes. This models the absolute fibre product
  of fibred groupoids over the base category, with its canonical projection. In
  particular, different S-structures on a common absolute base are retained.
- Final absolute-diagonal convention: `moduliDiagonalOverIntegers F` sends an
  object to (x,x,id), and an arrow to (a,a). Its domain is F viewed over Spec Z
  and its codomain is the preceding absolute product, so it is the absolute
  diagonal specified in the node, with no restriction on the diagonal of S.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, `Spec.map`. The size-convention node is metatheoretic
  and supplies no declaration; universe binders implement it.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `IsFibredInGroupoids`,
  `IsModuliStack`, `ModuliTwoIso`, `discreteModuli`, `moduliTwoFiberProduct`,
  `HasSpaceBaseChange`, `HasAlgebraicSpaceDiagonal`. Their full definitions were
  read, including actual projections in algebraic-space presentations.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`,
  `IsSmoothModuliAtlas`, `SpaceMapIsSmooth`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsEtale`, `IsSurjective`, `IsAlgebraicSpace`.
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`: `IsQuasiCompactModuli`,
  `IsQuasiCompactAlgebraicModuliMap`, `IsQuasiSeparatedAlgebraicModuliMap`.
- The canonical category machinery is Mathlib `BasedCategory.ofFunctor`,
  `BasedFunctor`, `BasedNatTrans`, `Over.map`, `CostructuredArrow`, `Comma`,
  and `ObjectProperty.FullSubcategory`; their relevant signatures were read.
- `Mathlib.AlgebraicGeometry.Limits`: `specULiftZIsTerminal`.
- Stated proof dependencies are imported: `SpaceChangeBase` (the existing
  `AlgebraicSpace.exists_spaceChangeBase`) and Mathlib's pullback module, along
  with the statement dependencies. `lem-sfb-etale-stack-localization` has no Lean
  record yet, so there is no module to import for that proof-only dependency.

Sources read: `literature/stacks-project/algebraic.tex`, section-change-base-scheme,
lemma-category-of-spaces-over-smaller-base-scheme and definition-viewed-as (04X5,
04X6); `stacks.tex`, section-localize, constructions A/B and lemma-localize-stacks;
`stacks-morphisms.tex`, lemma-compose-after-separated (050M). These identify the
represented S with Sch/S over Sch/Spec Z and use the unchanged total category.

Edge cases checked before stating:

- Empty base S and empty stacks: no nonempty premise; atlas predicates permit empty
  schemes. All constructions still use their literal categories and projections.
- Non-quasi-separated or non-separated S: the proof uses the equalizer scheme
  E = T ×_(S ×_Z S) S, with no open/closed condition; the absolute product retains
  distinct S-maps. No relative product is silently substituted for it.
- A map to Spec Z has its forced integer structure; the universe lift includes all
  scheme universes, all characteristics, and rings with nilpotents.
- Automorphisms and nontrivial stabilizers are retained in BasedCategory, the comma
  comparison, and the categories of based functors; no set of isomorphism classes
  replaces a groupoid.
- Pullbacks over an arbitrary algebraic H, including identity arrows, are included.
  Canonical comparison normalizations retain both factors and the isomorphism.
- Quasi-compact and quasi-separated are separate clauses: neither is assumed on
  the base, and no finite-type or DM condition appears.

Searches (2026-10-24, prescribed msearch wrapper with Q141 and this item):

1. LeanFinder: "Algebraic stacks over a scheme as algebraic stacks over integers
   preserving atlases and quasi compact quasi separated morphisms". Eight hits,
   including Scheme.Etale, Scheme, AffineScheme and scheme quasi-compactness.
   None states an algebraic-stack change-of-base theorem.
2. Loogle: "CategoryTheory.BasedCategory, CategoryTheory.Over.map". Zero hits.
3. LeanSearch: "Algebraic stacks equivalence over a base scheme and over integers".
   Eight hits concerning affine schemes, ring localization and scheme topology;
   no algebraic-stack result.
4. Mathlib grep: "AlgebraicStack|algebraicStack|BasedCategory". Five BasedCategory
   hits identifying the canonical based-category machinery, no algebraic-stack
   theorem. This machinery is reused.
5. `rg` in `lean/WeilConjectures` for change-base variants and this item's id:
   unrelated derived/scheme base-change modules; no stack theorem or item match.
6. `rg` in `lean/Sheaf` for change-base variants and stack modules: the already
   landed SpaceChangeBase theorem concerns algebraic spaces only. Existing stack
   modules supply the imported predicates but no matching operation or theorem.
7. Exact-name `rg` across Mathlib, WeilConjectures and Sheaf for all new declaration
   names gave no matches. `dag/lean_names_upstream.json` has no matching stack
   change-of-base declaration. No released repair note exists for this item.

Validation: the prescribed scompile.py successfully compiled both sandbox and
library forms of the module. All universes and variables are explicit; no #check
commands remain. The delivery dry run and final push are performed after this report.

## Second reading by Q141

Author's second reading, not an independent agent review (the dispatcher explicitly
prohibits starting other agents). Reopened the node and complete final module.

Matched the initial S, structure map, and same-total-category operation to the exact
`F.p ⋙ Over.map g` construction. Checked that the map to S is F.p itself and that
its model of the represented S is precisely the slice model stated in the source.
Read the first conjunction against clause (1): it quantifies over the given atlas,
retains the identical source scheme, and its 2-isomorphism forces the resulting
absolute atlas to be that atlas after the canonical represented-scheme identification.

Read the next two conjunctions against clause (2): the q equation is exactly a map
of pairs, not a free functor; the inverse algebraicity test and forward construction
cover all pairs. The Hom-category equivalence fixes actual functors and actual
natural transformations. Its full-subcategory morphisms have the right compatibility
because Over.map is faithful on arrows; no additional 2-morphisms are introduced.
The fourth conjunction retains all three algebraic stacks, both maps, actual comma
objects and arrows, hence both projections of the 2-pullback.

Read the last two conjunctions against clause (3): all three equivalences appear
(object qc, map qc, map qs), and the map-qc test universes agree verbatim. Checked
the final two convention sentences against the concrete absolute-product and
absolute-diagonal definitions, especially when S has nontrivial relative diagonal.
The absolute product allows different S-structures and the diagonal is (x,x,id).

The second reading added explicit public imports of every recorded statement
module and the stated proof-only pullback import. It found no mathematical
statement mismatch; the node's statement, stmt_deps and proof remain unchanged.
