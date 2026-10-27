## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.HomogeneousQuotient` states
`AlgebraicGeometry.exists_homogeneousQuotient`, with its sole proof `sorry`.
There are no new definitions, dependency repairs, or statement changes. The item node
is copied with only `lean` changed. All variables and the universe `u` are explicitly
bound; `autoImplicit` is disabled. The module docstring cites the source and the
statement docstring supplies all twelve steps of the recorded natural-language proof.

### Source and correspondence

I read Milne, Algebraic Groups (2017), printed pp.104–105 (PDF pp.116–117):
Definition 5.20, Proposition 5.24, Proposition 5.25, Theorem 5.28 and its following
sentence. Definition 5.20 gives coset fibres and faithfully-flat local lifts on
algebras; affine-locality gives the stated version for arbitrary test schemes.
The node asks only for the quotient scheme and projection, not separate action or
base-point data. No action or group structure on the quotient is added to Lean.

Each hypothesis and conclusion clause is rendered as follows:

| Node clause | Lean rendering |
| --- | --- |
| Field k | `(k : Type u) [Field k]` |
| k-group schemes G and L | `(G L : Over (Spec (.of k))) [GrpObj G] [GrpObj L]` |
| G separated over k | `[IsSeparated G.hom]` |
| G finite type over k | `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]` |
| Closed subgroup j : L ↪ G | `(j : L ⟶ G) [IsClosedSubgroupScheme j]`; the recorded class extends `IsSubgroupScheme`, hence `IsMonHom`, and includes `IsClosedImmersion j.left` |
| No normality, smoothness or affineness hypotheses | None of these predicates occurs among the binders |
| A k-scheme X and a k-morphism p : G → X | `∃ (X : Over (Spec (.of k))) (p : G ⟶ X)` |
| X separated and finite type over k | `IsSeparated X.hom ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom` |
| p flat and surjective | `Flat p.left ∧ Surjective p.left` |
| p of finite presentation, in the node's expanded sense | `LocallyOfFinitePresentation p.left ∧ QuasiCompact p.left ∧ QuasiSeparated p.left` |
| Every k-scheme T and every pair of G(T)-points | `∀ (T : Over (Spec (.of k))) (a b : T ⟶ G)` |
| p_T(a) = p_T(b) | `a ≫ p = b ≫ p` |
| a⁻¹b belongs to j_T(L(T)) | `a⁻¹ * b ∈ Set.range (fun l : T ⟶ L ↦ l ≫ j)` |
| The coset-fibre equivalence | `↔`, relating exactly the preceding two expressions |
| Every x ∈ X(T) | `∀ (T : Over (Spec (.of k))) (x : T ⟶ X)` |
| Some family of test schemes over T | `∃ (I : Type u) (T' : I → Over (Spec (.of k))) (f : ∀ i, T' i ⟶ T)` |
| The family is an fpqc covering | `Presieve.ofArrows (fun i ↦ (T' i).left) (fun i ↦ (f i).left) ∈ Scheme.fpqcPrecoverage T.left` |
| Each restricted point belongs to the image | `∀ i, ∃ g : T' i ⟶ G, g ≫ p = f i ≫ x` |

The group operation and inverse on `T ⟶ G` are Mathlib's internal-group-object
functor-of-points operations, exposed by `open scoped CategoryTheory.MonObj`.
Composition with j gives the subgroup's actual image, rather than an unrelated subgroup.
The covering predicate is on the underlying schemes; its arrows are k-morphisms because
they are arrows in `Over (Spec (.of k))`. A singleton cover suffices for the existence
clause (base change of p), so an index in `Type u` loses no case.

### Recorded dependency declarations used

- `def-weil-field`: Mathlib `Field`, read in `Mathlib.Algebra.Field.Defs`.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` from
  `Mathlib.CategoryTheory.Monoidal.Grp`; the pointwise group structure and over-category
  specialization are also exposed by the upstream group-scheme module.
- `def-sc-group-scheme-subgroup`:
  `AlgebraicGeometry.IsClosedSubgroupScheme`, `IsSubgroupScheme` and their parent
  `CategoryTheory.IsMonHom`, from
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`. I read the full class definitions
  and their docstrings (including injectivity on algebra-valued points).
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`; this is the field of the
  imported closed-subgroup class, not an independently redefined predicate.
- `def-weil-proper-morphism`: its separatedness component
  `AlgebraicGeometry.IsSeparated`, defined in `Mathlib.AlgebraicGeometry.Morphisms.Separated`
  and imported through the recorded `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
  No properness hypothesis is used.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, through
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`.
- `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `def-weil-quasi-separated-morphism`: `AlgebraicGeometry.QuasiSeparated`,
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `def-weil-pbc-fpqc-covering`: `AlgebraicGeometry.Scheme.fpqcPrecoverage`,
  `Mathlib.AlgebraicGeometry.Sites.Fpqc`.

All currently recorded proof-dependency modules are ordinary (non-public) imports,
except fpqc coverings, which are already a public statement dependency. The Mathlib
match `LocallyOfFinitePresentation.iff_locallyOfFiniteType` is imported from
`Mathlib.AlgebraicGeometry.Noetherian`. Proof dependencies without recorded declarations
are explained in the proof docstring and do not require unstated notions in the signature:
`lem-sfb-finite-extension-open-exhaustion`,
`lem-sfb-homogeneous-scheme-finite-set-affine`,
`lem-sfb-representable-lft-fppf-source-descent`,
`lem-sfb-space-closed-immersion-fppf-descent`, `lem-sfb-space-qcqs-permanence`,
`lem-sfb-space-quasicompact-fppf-local`, and
`lem-sfb-stack-point-topology-flat-lfp-open`.

### Edge cases checked before writing

- L is the identity subgroup: p can be the identity of G; the fibre condition becomes
  a = b iff a⁻¹b = 1.
- L = G: X can be Spec k; every a⁻¹b is in the image, and the unit gives local lifts.
- Non-normal subgroups: the conclusion imposes no group structure on X or homomorphism
  property on p; its cosets are right cosets (`a⁻¹b`), as required.
- Nonreduced subgroups, such as α_p ⊆ G_a: no smoothness or reducedness is assumed,
  and points range over schemes, so nilpotent test algebras remain visible.
- Non-affine G, including abelian varieties, is not excluded.
- The empty test scheme is allowed, as are non-affine and non-quasi-compact test
  schemes. The covering condition has exactly Mathlib's fpqc meaning, and no
  `Nonempty I` restriction has been added. G itself cannot be empty because it is a
  group object over the nonempty Spec k.
- Arbitrary characteristic and the trivial group are allowed. The common universe
  is the standard universe of schemes over k; the statement is polymorphic in u.

### Searches

The prescribed wrapper `msearch.py Q12 lem-sfb-algebraic-group-homogeneous-quotient`
was used for:

1. `leanfinder`: “A finite type separated group scheme over a field modulo any closed
   subgroup is a separated finite type scheme with flat surjective finitely presented
   quotient and fpqc local lifts”. Eight hits, on finite morphisms, separated schemes,
   and abstract Galois-category quotients; no matching group-scheme quotient theorem.
2. `loogle`: `GrpObj, IsClosedSubgroupScheme`. Zero hits; the service reports the
   unqualified `GrpObj` identifier unknown. Direct source searches resolve its actual
   definition and the recorded subgroup interface.
3. `grep`: `homogeneous|quotient|Quotient` in `AlgebraicGeometry/Group`. Zero hits.
4. Direct `rg` in both `lean/WeilConjectures/AlgebraicGeometry` and
   `lean/Sheaf/AlgebraicGeometry` for homogeneous spaces, homogeneous quotients, and
   closed-subgroup quotients. Existing `AffineNormalQuotientGeometry` is restricted to
   normal subgroups of affine groups, and `SolvableHomogeneousProperSubschemes` assumes
   its quotient scheme. Neither states this theorem. Other hits concern graded rings.
5. Direct `rg` for the item id in `lean/WeilConjectures`: no result. Direct `rg` for
   `exists_homogeneousQuotient` in the group-scheme directories: no existing declaration.

No STATEMENT-DISPUTED issue or node fault was found.

### Validation

`scompile.py Q12 lem-sfb-algebraic-group-homogeneous-quotient` compiled the delivered
file in both sandbox mode and its actual library module path, cleanly (5.5 s and 7.7 s).
All compiles use the prescribed wrapper and the live published library.

## Second reading by Q12

This is the author's second reading, not an independent review; the dispatcher brief
assigns the independent review to the maintainer. I reopened the node and final module
and matched each binder and each conjunction using the table above. In particular:
G's finite type includes quasi-compactness; X is only a scheme over k; all five
properties of p are explicit; the equality is equality of k-morphisms; the right-coset
orientation is a⁻¹b; T is an arbitrary over-scheme rather than an affine spectrum; the
local-lift clause supplies actual covering arrows and an actual lift on each member.
The subgroup condition is precisely the recorded upstream class and no normality,
smoothness, affineness, or extra finiteness is assumed. The final signature has no
`let`, hidden arbitrary maps, copied notions, or auto-bound variables. No mismatch
was found and no correction was needed.
