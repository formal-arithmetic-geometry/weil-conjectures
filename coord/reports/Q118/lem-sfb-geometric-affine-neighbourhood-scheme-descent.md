## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricAffineNeighbourhoodSchemeDescent` states
`AlgebraicGeometry.AlgebraicSpace.isRepresentable_of_geometric_affine_neighbourhoods`.
Its sole theorem has proof `sorry`; no definitions, instances, helper theorems or new nodes
are introduced. The node's statement, dependency lists and proof are unchanged.

Read sources: `literature/stacks-project/spaces-over-fields.tex`, Tag 0B88,
`lemma-scheme-over-algebraic-closure-enough-affines`, including its proof;
`literature/stacks-project/decent-spaces.tex`, Tag 088J,
`lemma-locally-separated-decent`, including the locally separated hypothesis and proof.
The node specializes decency to local separatedness, using composition with the scheme map
Spec k → Spec Z. Its existing expanded proof handles inseparability directly. The complete
11-step node proof and the dependency IDs are included in the theorem docstring.

Clause-by-clause translation:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| k is a field | `(k : Type u) [Field k]` |
| Ω is an algebraic closure of k | `(Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]` |
| X is an algebraic space over Spec k | `X : AlgebraicSpace (Spec (CommRingCat.of k))` |
| Every étale scheme chart is locally of finite type over k | `hlft : ∀ (U : Over (Spec (CommRingCat.of k))) (a : yoneda.obj U ⟶ X.obj.obj), IsEtale a → LocallyOfFiniteType U.hom` |
| The relative diagonal is representable by immersions | `hlsep : IsRepresentableWith (fun _ _ p ↦ IsImmersion p.left) (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj))` |
| Y is an Ω-scheme | `Y : Over (Spec (CommRingCat.of Ω))` |
| Y represents the sheaf base change X_Ω | `hY : Nonempty (yoneda.obj Y ≅ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))).op ⋙ X.obj.obj)` |
| Every n ≥ 0 and list of Ω-morphisms Spec Ω → Y | `haff : ∀ (n : ℕ) (y : Fin n → (Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶ Y)), ...` |
| A single affine open V contains all members of the list | `∃ V : Y.left.Opens, IsAffineOpen V ∧ ∀ i : Fin n, ∃ z : Spec (CommRingCat.of Ω) ⟶ V.toScheme, z ≫ V.ι = (y i).left` |
| X is represented by a k-scheme | `∃ Z : Over (Spec (CommRingCat.of k)), Nonempty (yoneda.obj Z ≅ X.obj.obj)` |
| No group structure or quasi-compactness is assumed | Neither occurs in the binders; local finite type is not replaced by finite type |

Why these are the same objects:

* The diagonal is the product diagonal in presheaves on `Over (Spec k)`, hence the relative
  diagonal over Spec k, rather than an absolute diagonal.
* On an Ω-test scheme `T`, the right side of the representing isomorphism evaluates as
  `X(T → Spec Ω → Spec k)`. A map over Ω from T into the fibre product is exactly this
  section. This is the canonical base-change sheaf, not a chosen arbitrary comparison map.
  For a representable X it is represented by the usual scheme pullback, by its universal
  property. The library already uses this literal restriction encoding in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFpqcValuativeDescent`; no duplicate construction
  is introduced. The recorded fibre-product dependency is imported publicly.
* `Over.mk (𝟙 (Spec Ω)) ⟶ Y` requires the rational points to be Ω-morphisms. An underlying
  factor z through V is automatically over Ω for the induced map `V.ι ≫ Y.hom`, since
  `(y i)` is an over morphism and `z ≫ V.ι = (y i).left`. Thus the factorization clause has
  exactly the required Ω-linear meaning.
* Both representing isomorphisms are between full functors of points and are natural in
  all test schemes. Merely choosing unrelated pointwise bijections would not suffice.

Dependency declarations read and reused:

* `Field`, `Mathlib.Algebra.Field.Defs`: the field class (available through the public
  algebraic-closure import).
* `IsAlgClosure`, `IsAlgClosed`, `Mathlib.FieldTheory.IsAlgClosed.Basic`: algebraic,
  algebraically closed extension, with its specified `Algebra k Ω` structure. The node's
  alternative canonical choice `AlgebraicClosure`, in
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`, was also read; Ω remains arbitrary.
* `AlgebraicGeometry.AlgebraicSpace`, `IsRepresentableWith`, `IsEtale`,
  `Sheaf.AlgebraicGeometry.AlgebraicSpace`: the existing full subcategory of fppf sheaves,
  representability on all scheme tests, and étaleness on all such tests. The source module
  and full predicate signatures and docstrings were read.
* `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: finite type of local affine ring maps;
  the structure morphism is `U.hom`.
* `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, and
  `AlgebraicGeometry.IsImmersion`, `Mathlib.AlgebraicGeometry.Morphisms.Immersion`:
  the immersion clause of the recorded dependency is its `mathlib_match` alternative.
  `IsImmersion.isImmersion_iff_exists` identifies it with a closed immersion followed by
  an open immersion, exactly the node's immersion notion.
* `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: read the universal property;
  representation of X_Ω is encoded on Ω-tests instead of choosing an auxiliary scheme
  to represent an a priori nonrepresentable X.
* `AlgebraicGeometry.Spec`, `Spec.map`, `Mathlib.AlgebraicGeometry.Scheme`: the spectra
  and contravariant map for `algebraMap k Ω`.
* `AlgebraicGeometry.IsOpenImmersion`, `Mathlib.AlgebraicGeometry.OpenImmersion`,
  and `Scheme.Opens.toScheme`, `Scheme.Opens.ι`, `Mathlib.AlgebraicGeometry.Restrict`:
  V is an actual open subscheme, with its canonical inclusion. `IsAffineOpen`,
  `Mathlib.AlgebraicGeometry.AffineScheme`, means that open subscheme is affine.
* `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`,
  `etaleCover_pullback`, `etale_fibreProduct_isScheme`,
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`: full declarations and
  docstrings read, and the recorded module imported publicly as required.
* `CategoryTheory.Over.map`, `Mathlib.CategoryTheory.Comma.Over.Basic`: composition of
  a test scheme's structure morphism with the specified field-extension spectrum map.

All currently stated proof dependencies are imported with ordinary `import`, including
Mathlib matches, and their IDs remain in the theorem's proof docstring. Unstated proof
lemmas remain future proof work; none is needed as a new notion in this statement.

Edge cases checked before writing and again after compilation:

* `n = 0` is included and imposes only existence of an affine open; the empty open is
  affine, as Spec of the zero ring. No nonempty index or nonempty open is required.
* Empty X and empty Y are admitted: empty schemes represent the base change and the
  conclusion, and no rational-point list of positive length exists for empty Y.
* Repeated points are admitted. All finite sets can be enumerated, so the list formulation
  has the same finite-neighbourhood property as the source.
* Positive characteristic and inseparable algebraic extensions are admitted. No perfection,
  separability, reducedness, Galois or finiteness hypothesis is imposed on k or Ω.
* Infinite disjoint unions of affine k-schemes are admitted: the theorem has no global
  quasi-compactness premise. Local separatedness is not strengthened to separatedness.
* One explicitly bound universe u is the scheme/site universe of the recorded algebraic-space
  framework; fields and their spectra live in that universe. The index is `Fin n`, not an
  additional arbitrarily small universe. `set_option autoImplicit false` is explicit.

Searches actually run:

1. `msearch.py ... leanfinder "An algebraic space over a field is a scheme if after base
   change to an algebraic closure every finite set of rational points lies in an affine
   open"`: eight hits, including `IsAffine`, `AffineScheme`, `Scheme.IsQuasiAffine` and
   unrelated affine/finite morphism declarations; no matching descent theorem.
2. `msearch.py ... loogle "AlgebraicGeometry.AlgebraicSpace, IsAffineOpen, IsImmersion"`:
   zero hits, unknown identifier `AlgebraicGeometry.AlgebraicSpace` in Loogle's index.
3. `msearch.py ... grep "AlgebraicSpace|enough_affines|scheme_over_algebraic_closure"
   AlgebraicGeometry`: zero hits in Mathlib.
4. `msearch.py ... leansearch "An algebraic space locally of finite type over a field is a
   scheme if its geometric base change is a scheme with affine neighbourhoods of finite
   sets of rational points"`: eight generic scheme/local-finite-type hits, no exact theorem.
5. `rg` on `lean/WeilConjectures` and `lean/Sheaf` for the node ID and
   `geometricAffineNeighbourhood|isRepresentable_of_geometric|isScheme_of_geometric|geometric_affine|enough_affines`:
   no existing declaration. Broader searches located the existing algebraic-space
   representability, diagonal, chart and change-of-base interfaces used above.
6. `rg` on Mathlib for the same declaration-name patterns: no match. Direct source searches
   located `Over.map`, `IsAlgClosure`, `IsImmersion.isImmersion_iff_exists`, `IsAffineOpen`
   and the canonical open inclusion; these notions are reused, not redefined.

Validation: `scompile.py Q118 lem-sfb-geometric-affine-neighbourhood-scheme-descent
<module path>` completed successfully for both the sandbox and actual library module
checks (13.1 s and 7.4 s). No errors or unexpected warnings. Delivery preflight follows.

No statement correction, dependency repair, new notion, or STATEMENT-DISPUTED issue.

## Second reading by Q118

Final self-check, not a claim of independent review: the dispatcher explicitly forbids
starting other agents and assigns the independent reading to the maintainer. Reopened
the node and the generated Lean module and checked every row of the translation above.
In particular checked that hY is over Ω, that the product diagonal is over k, that the
finite points are over Ω rather than arbitrary scheme morphisms, and that factorization
through V automatically respects Ω. The conclusion is an actual natural representing
isomorphism over k. The node record's statement is extracted verbatim from the Lean
signature, and only the node's `lean` field changes. No mismatches found; no statement
change or additional dependency was needed.
