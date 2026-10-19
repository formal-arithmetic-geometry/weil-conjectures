## Worker report

The item is stated in `lean/Sheaf/AlgebraicGeometry/ReducedAlgebraicNormalizationFieldChange.lean`, declaration `AlgebraicGeometry.reduced_algebraic_normalization_field_change`. Its proof is exactly `sorry`. A new definition module `ReducedNormalization.lean` constructs the componentwise normalization with actual data, reusing the recorded integral-scheme normalization, and supplies one named, sorry-only integralness theorem needed to type that construction. No node statement was corrected.

Hypothesis and clause correspondence:

- A field k is `{k : Type u} [Field k]`. The scheme over k is `(X : Scheme.{u}) (q : X ⟶ Spec (.of k))`. This explicit structure map is used throughout the field-change clauses.
- Reduced is `[IsReduced X]`. Finite type is `[LocallyOfFiniteType q] [QuasiCompact q]`, precisely the conjunction in the recorded definition.
- The definition of X^ν is `Scheme.reducedNormalization X`: the coproduct indexed by `irreducibleComponents X` of `(X.reducedNormalizationComponent Z).normalization`. The component is the subscheme cut out by the radical vanishing ideal of Z, hence has the reduced induced structure. `Scheme.fromReducedNormalization X` is `Sigma.desc` of the component normalization maps followed by the closed inclusions. No integrality assumption is imposed on X itself. The finiteness of the component set follows from finite type over k, rather than being an extra hypothesis.
- Finite and surjective are the first two conjuncts, `IsFinite X.fromReducedNormalization` and `Surjective X.fromReducedNormalization`.
- The normal locus is an open `N : X.Opens` characterized point by point by `x ∈ N ↔ IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)`. Its density is `Dense (N : Set X)`, and the isomorphism on its inverse image is `IsIso (X.fromReducedNormalization ∣_ N)`. In particular, N is the whole normal locus, rather than an unspecified dense normal open.
- For every open `W : X.Opens`, the next conjunct gives the unique isomorphism from `W.toScheme.reducedNormalization` to `(X.fromReducedNormalization ⁻¹ᵁ W).toScheme` whose composite with the restricted normalization map is `W.toScheme.fromReducedNormalization`. This says the inverse-image map is canonically the normalization of W, over W.
- For every `(K : Type u) [Field K] [Algebra k K]`, assuming `Algebra.IsSeparableExtension k K`, the next conjunct gives the unique comparison isomorphism from the normalization of `pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))` to `pullback (X.fromReducedNormalization ≫ q) (Spec.map (CommRingCat.ofHom (algebraMap k K)))`. These are exactly `(X_K)^ν` and `X^ν ×_k K`. The two equations specify compatibility with both projections, hence that the comparison is over X_K.
- The final conjunct repeats the same comparison for arbitrary extensions K/k under `IsAlgClosed k`, without assuming separability, algebraicity, or finite generation of K/k.
- The unique-isomorphism descriptions express the word “canonically”: on the dense open where normalization is an isomorphism the map is forced, and equality extends because the source is reduced and the target is separated over the base. They avoid choosing unspecified comparison maps as new data. Both displayed projection equations are needed to express being over X_K, rather than merely over X or K separately.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`; `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, with `QuasiCompact` from `Morphisms.QuasiCompact`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`: `AlgebraicGeometry.Scheme.normalization`, `fromNormalization`, plus its recorded finiteness and surjectivity statements for the proof plan. These apply only to integral schemes, so are used separately on the components.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`, `isClosed_of_mem_irreducibleComponents`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`; `Morphisms.Integral`: `IsIntegralHom`; `Morphisms.UnderlyingMap`: `Surjective`.
- `Sheaf.AlgebraicGeometry.BaseChangeConventions`: the recorded scheme base change is `CategoryTheory.Limits.pullback`, with `pullback.fst` and `pullback.snd`. Its module is publicly imported; its module-sheaf base change functor is not substituted for scheme base change.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`; `Mathlib.Algebra.Ring.Defs`: `IsDomain`. Their conjunction is the recorded normal-domain notion.
- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.Algebra.Algebra.Defs`: `Algebra`, with `algebraMap` defining the field embedding.
- `Sheaf.FieldTheory.SeparableExtension`: `Algebra.IsSeparableExtension`, whose full body quantifies over all intermediate fields F with `F.FG` and demands `IsSeparablyGenerated k F`. It includes transcendental extensions.
- Additional actual construction primitives: `Scheme.IdealSheafData.vanishingIdeal`, `.subscheme`, `.subschemeι`, and scheme coproducts `Sigma.desc`, already in Mathlib. No alternate integral normalization or base-change definition is introduced.

All stated proof dependency modules are imported, directly or through a public statement dependency. `lem-weil-pbc-normal-algebra-separable-scalar-extension` has no Lean record yet, so has no module to import; its role is explicitly retained in the theorem docstring. This is a future proof dependency and is not needed to type the statement.

Edge cases checked mathematically: X empty gives the empty coproduct, empty dense normal locus, and identity comparisons of empty schemes. W empty is allowed. Zero-dimensional reduced schemes and multiple intersecting components are allowed; X is not required to be irreducible, separated, smooth, or a curve. Components may split after separable field change: no correspondence of individual component index sets is assumed. Arbitrarily transcendental separable extensions and all characteristics are covered by the recorded separability predicate. An arbitrary algebraically closed k is allowed. All fields and schemes share an explicit universe u; this is the standard scheme universe, with no independently smaller test universe.

Searches performed (2026-10-15):

- `msearch.py ... leanfinder` query “Normalization of a reduced finite type scheme is finite surjective and commutes with separable field extension”: 8 relative-normalization hits; no complete match.
- `msearch.py ... loogle` query `AlgebraicGeometry.Scheme.normalization, AlgebraicGeometry.Scheme.Hom.normalizationPullback`: 0 hits; unknown upstream identifier `AlgebraicGeometry.Scheme.normalization`. The upstream file was opened directly instead.
- `msearch.py ... grep` query `normalizationPullback|normalLocus|reducedNormalization`, subdirectory AlgebraicGeometry: 7 hits in Mathlib Normalization and ZariskisMainTheorem. Read the comparison and smooth-base-change instance; relative normalization does not provide this absolute componentwise statement for arbitrary separable extensions.
- `msearch.py ... leansearch` query “The normalization of a scheme is the disjoint union of the normalizations of its reduced irreducible components”: service unavailable, Internal Server Error.
- `msearch.py ... leanfinder` query “Disjoint union of normalizations of reduced irreducible components of a scheme”: 8 hits, relative normalization and integral/reduced equivalence, no definition of the componentwise coproduct.
- `rg` in Mathlib, `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, and `lean/Sheaf` for reduced normalization, normal locus, and normalization/separability/component patterns: no complete statement or componentwise absolute normalization definition. `ReducedCurveNormalization.lean` constructs existence witnesses for a curve modification, not a named general normalization object; its component construction was inspected and the actual Mathlib vanishing-ideal construction reused. The exact item id is absent upstream.
- Exact proposed declaration names were searched in Mathlib, upstream, `lean/Sheaf`, and `dag/lean_names_upstream.json`: none exist.
- DAG grep and `tools/blueprint_refs.py search normalization`: integral normalization and curve-modification nodes exist, but none defines this general componentwise normalization. `tools/blueprint_refs.py ancestor` identifies `lemma-weil-pbc-normalization-exact-sequence`.

Source checked locally: Varieties Tags 0BXR/0C3N give the geometry and separable comparison. Morphisms 0CDV identifies normalization with the union of normalized components; the reduced component structure is the vanishing-ideal structure. No STATEMENT-DISPUTED flag or mathematical node fault was found.

Validation: both delivered modules compiled individually, in dependency order, using `scompile.py` on the server (nice 19, two threads, 60 seconds per file); both were clean. No local compiler was used. The required delivery dry run is recorded below after execution.

## New nodes

`def-weil-pbc-reduced-normalization` defines, for a scheme X, the reduced induced integral component schemes, their disjoint union of function-field normalizations, and its canonical map to X. Source: Morphisms Tag 0CDV and Schemes Tag 01J3. DAG, LeanSearch, LeanFinder, Loogle, Mathlib/source/project grep searches above found no existing node or declaration for the whole construction. The integral scheme normalization is reused, not copied. The component integralness proof required by the construction is a separate named theorem `Scheme.isIntegral_reducedNormalizationComponent`, with source and complete proof in its docstring and this matching definition node. All definition data is explicit: vanishing-ideal subschemes, the existing normalization, and the coproduct and its induced map.

The first dry run found that the signature reader omits the `noncomputable` modifier from `lean.statement`; the definition record was adjusted accordingly. The independent second-reading section is intentionally left for the next worker.

## Second reading by NG

Independent second reader, 2026-10-15. I opened the item JSON, both delivered modules,
the new definition JSON, the recorded dependency signatures and their implementations,
and the local Stacks sources. No mathematical or Lean mismatch was found. No statement,
definition, signature, or node record was changed in this reading; this section is the
only repair/addition.

Object/hypothesis/conclusion checklist, in the order of the node:

1. Field k: `{k : Type u} [Field k]`. Scheme X with its k-structure:
   `(X : Scheme.{u}) (q : X ⟶ Spec (.of k))`. Verdict: exact. The explicit q is
   appropriate because the statement base-changes that same structure morphism.
2. Reduced X: `[IsReduced X]`; finite type over k: `[LocallyOfFiniteType q]
   [QuasiCompact q]`. Verdict: exact conjunction from def-weil-finite-type-morphism;
   no integrality, separatedness, perfectness, or extra finiteness is assumed.
3. Reduced irreducible components and their normalizations: `irreducibleComponents X`,
   `X.reducedNormalizationComponent Z`, and the existing integral-scheme
   `.normalization`. `reducedNormalizationComponent` is the subscheme of
   `IdealSheafData.vanishingIdeal` of the closed component. Verdict: exact reduced
   induced structure, not an arbitrary subscheme or an integral hypothesis on X.
   `Scheme.reducedNormalization` is their actual coproduct; the canonical map is
   `Sigma.desc` of `.fromNormalization ≫ .subschemeι`. Finitely many components
   follows from finite type over a field; it is not an additional hypothesis.
4. Finite and surjective ν: `IsFinite X.fromReducedNormalization ∧
   Surjective X.fromReducedNormalization`. Verdict: both required properties of
   the same componentwise map, using the recorded scheme-morphism classes.
5. Normal locus: `∃ N : X.Opens` with, for every x, membership equivalent to
   `IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)`.
   Verdict: exactly all normal points, not just a smaller normal open. `Dense
   (N : Set X)` supplies density and `IsIso (X.fromReducedNormalization ∣_ N)`
   supplies the required isomorphism over N.
6. Every open subscheme: `∀ W : X.Opens`, the unique isomorphism from
   `W.toScheme.reducedNormalization` to `(X.fromReducedNormalization ⁻¹ᵁ W).toScheme`
   has composite with `X.fromReducedNormalization ∣_ W` equal to
   `W.toScheme.fromReducedNormalization`. Verdict: precisely normalization of W
   over W. The inverse orientation describes the same canonical identification.
   Uniqueness follows from the dense isomorphism locus and reducedness, since
   the target is finite, hence separated, over W.
7. Separable extension: `∀ (K : Type u) [Field K] [Algebra k K],
   Algebra.IsSeparableExtension k K → ...`. Verdict: no algebraicity or finite
   generation assumed. I read `IsSeparableExtension`: it quantifies over every
   `F : IntermediateField k K` with `F.FG`, requiring `IsSeparablyGenerated k F`.
   I also read that latter definition: a transcendence basis with separable
   algebraic remainder, as required by the dependency node.
8. Field-change comparison: the source is the reduced normalization of
   `pullback q (Spec.map (CommRingCat.ofHom (algebraMap k K)))`; the target is
   `pullback (X.fromReducedNormalization ≫ q) (Spec.map ...)`. Verdict: exactly
   `(X_K)^ν` and `X^ν ×_k K`. The first equation identifies the composite to X
   with the normalization map followed by the X-projection; the second identifies
   the composite to Spec K. Together they say the isomorphism is over X_K.
   `∃! e` captures the canonical comparison: any two such maps agree over the
   dense normal open and hence everywhere (reduced source, separated target).
9. Algebraically closed base: `IsAlgClosed k → ∀ (K : Type u) [Field K]
   [Algebra k K], ...`, with the identical comparison equations. Verdict: every
   extension is covered, without a separability premise in this last clause.

Source and dependency review: varieties.tex, lemma-normalization-locally-algebraic
(Tag 0BXR), explicitly assumes only a field and a locally algebraic scheme; the
node takes the stated finite-type reduced case. lemma-normalization-and-change-of-fields
(Tag 0C3N) gives precisely the separable comparison and its orientation. The node
intentionally does not ask for the additional inseparable universal-homeomorphism
conclusion. morphisms.tex, lemma-normalization-in-terms-of-components (0CDV),
identifies the coproduct with normalization when quasi-compact opens have finitely
many components; our finite-type X satisfies this. schemes.tex,
lemma-reduced-closed-subscheme (01J3), constructs the reduced closed structure by
its radical vanishing ideal. I read Mathlib's vanishingIdeal, subscheme and
subschemeι implementations, and the upstream integral normalization and
fromNormalization definitions: the new construction genuinely uses those objects.
The general new definition makes sense for any scheme; it does not claim the
0CDV normalization properties without that lemma's local-finiteness assumption.
I checked the dependency records against IsReduced, irreducibleComponents,
LocallyOfFiniteType/QuasiCompact, IsFinite/Surjective, IsDomain/IsIntegrallyClosed,
Field/Algebra, and BaseChangeConventions. None is substituted by another notion.

New-node review (H12): def-weil-pbc-reduced-normalization has exactly the required
new-definition fields, cites its four building notions, belongs to the item's
chapter/unit, and is cited by the item. It introduces the missing componentwise
object, not another copy of integral normalization. Its integralness helper has a
named sorry-only theorem with a complete proof: radical quotients are reduced,
the underlying component is irreducible and nonempty, so the scheme is integral.
This proof supplies only a property of already constructed data. No definition
contains sorry or selects unspecified data from an existence theorem. There are
no extra dependency modules and no statement correction requiring citer verdicts.

Edge cases: empty X yields no irreducible components and the empty coproduct;
N and W can be empty, and density in the empty space is valid. Zero-dimensional
schemes and multiple/intersecting components are included. A zero coordinate
ring represents an empty affine chart, not an excluded Field instance. The
component predicate excludes empty components, not the empty scheme. Components
may split after extension: the statement compares entire schemes and never
assumes their component indices agree. All characteristics and transcendental
separable extensions are included; the algebraically closed clause allows
arbitrarily transcendental extensions. `u` is explicitly bound and common to
fields and schemes, as in the fixed-universe Scheme category; no smaller,
independent test universe can make the field-change premise vacuous. There is no
n-parameter or positive-dimension assumption.

Independent searches (2026-10-15): msearch LeanFinder query “absolute normalization
reduced scheme finite type normal locus separable scalar extension” returned eight
relative-normalization hits, no full match. LeanFinder query “coproduct of integral
closures of irreducible components of a reduced scheme” returned relative
normalization and integral/reduced equivalences, no componentwise construction.
Loogle `AlgebraicGeometry.Scheme.Hom.normalizationPullback` returned seven hits;
I opened Mathlib Normalization.lean at its definition and smooth-base-change
instance. These concern relative normalization of a morphism, and do not supply
the present absolute componentwise object or arbitrary separable comparison.
Independent rg searches of Mathlib/AlgebraicGeometry, upstream WeilConjectures,
and project lean/Sheaf for `normalization.*[Cc]omponent`,
`[Cc]omponent.*normalization`, `normalization.*separ`, and `normal.*locus` found
only integral normalization, relative dense-open normalization, curve-existence
statements and separate normal-locus algebra tools. I opened the relative
NormalizationDenseOpen module and the curve module: neither defines this object
or states this lemma. DAG searches for disjoint-union/componentwise normalization
found statements using that description, not an existing definition node.
The first worker's LeanSearch service failure is retained rather than treated as
positive evidence of absence. No existing declaration was found to replace the
new node or item module.

Conventions and validation: every delivered declaration has its source and
blueprint docstring; the main docstring follows all eight node proof steps.
All theorem proofs are sorry-only; all definition bodies are real constructions.
There is no file-local notation, private object, local instance, hidden let in a
statement, or unbound variable/universe. I independently ran scompile.py on both
delivered sibling files in dependency order: clean, 1.3 s and 1.7 s respectively,
nice 19, two threads, 60 seconds per file. No local compilation or global build.
