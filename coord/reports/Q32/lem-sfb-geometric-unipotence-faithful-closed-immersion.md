## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.FaithfulClosedImmersion` states
`AlgebraicGeometry.isClosedImmersion_of_faithful_affineGroupHom`. Its sole theorem has
proof `sorry`; it introduces no definitions or helper theorems. The source read is
Milne, Algebraic Groups (2017), Corollary 3.35 and Theorem 3.34, printed p.75. The
corollary uses trivial scheme-theoretic kernel and its proof explicitly uses injectivity
on all k-algebra points, as in the node. The docstring records all five DAG proof steps,
including the fpqc-covering check and descent of the inverse.

Clause-by-clause correspondence:

- A field k: `{k : Type u} [Field k]`.
- Group schemes G,H over k: `(G H : Over (Spec (.of k))) [GrpObj G] [GrpObj H]`.
  These are the recorded group objects in the slice category, so all structure maps
  and the morphism below are over the same base field.
- Affineness of each group: `[IsAffine G.left] [IsAffine H.left]`.
- Finite type over k: `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, and the same
  two classes for H, exactly the finite-type dependency's recorded conjunction.
- A group homomorphism: `(f : G ⟶ H) [IsMonHom f]`. IsMonHom expresses compatibility
  with multiplication and identity, with inverse compatibility automatic for groups.
- Every commutative k-algebra R: `∀ (R : Type u) [CommRing R] [Algebra k R]`.
- G(R) is Hom over k from Spec R to G: the domain of the injectivity function is
  `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ G`.
- The map f_R is postcomposition: `fun x ... ↦ x ≫ f`. Its codomain is the same
  slice Hom into H. `Function.Injective` renders the stated hypothesis exactly.
- Conclusion: `IsClosedImmersion f.left` on the underlying scheme morphism.
- No smoothness, connectedness, reducedness, characteristic or perfectness assumptions
  occur. No node statement correction or disputed claim is needed.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs (the dependency def-weil-field).
- `CategoryTheory.GrpObj`, Mathlib.CategoryTheory.Monoidal.Grp (the recorded module
  for def-sc-group-scheme), with `CategoryTheory.IsMonHom` from
  Mathlib.CategoryTheory.Monoidal.Mon. Their scheme specialization and slice conventions
  are documented in the publicly imported WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `AlgebraicGeometry.LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType;
  `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `AlgebraicGeometry.IsClosedImmersion`, Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion.

The stated proof dependency `lem-sfb-affine-homomorphism-flat-image` is imported privately
from Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage. Its full declaration
and proof docstring were read. The other proof dependencies are Mathlib notions/results:
Spec and pullbacks; Module.FaithfullyFlat; Flat.SpecMap_iff;
PrimeSpectrum.comap_surjective_of_faithfullyFlat; isAffineHom_of_isAffine;
isAffineHom_isStableUnderBaseChange; isAffine_of_isAffineHom;
Scheme.fpqcPrecoverage and the subcanonical fpqc topology. Their defining Mathlib proof
modules are imported privately (the spectrum and closed-immersion definitions are already
public statement imports). No unstated project proof dependency is imported.

Edge cases checked: arbitrary characteristic and imperfect fields remain allowed;
nonreduced groups and test algebras remain allowed. In particular, restricting tests to
fields would lose infinitesimal kernels, and is deliberately not done. The trivial group
and identity morphisms satisfy the statement. The zero k-algebra is included by CommRing
without Nontrivial, so the empty test spectrum is permitted. An empty group scheme over a
field cannot carry its required identity section; this is intrinsic to GrpObj rather than
an extra hypothesis. The common universe u is the existing scheme/group-scheme API's
universe and contains k and the coordinate algebras needed to test the universal points;
it has no independent smaller test-algebra universe.

Searches (2026-10-24):

- msearch LeanFinder: “A homomorphism of affine finite type group schemes over a field
  injective on every commutative algebra points is a closed immersion”. Eight results
  were ordinary closed-immersion criteria, none the affine-group statement.
- msearch Loogle: `"IsClosedImmersion", "IsMonHom"`. Zero results.
- msearch LeanSearch: “An injective homomorphism of affine algebraic group schemes on
  all algebra valued points is a closed immersion”. Eight closed-immersion criteria;
  no exact statement.
- msearch grep in AlgebraicGeometry:
  `(faithful|injective|[Mm]ono).*[Cc]losed[Ii]mmersion|[Cc]losed[Ii]mmersion.*(faithful|injective|[Mm]ono)`.
  Eleven hits: finite/proper monomorphism criteria and a criterion for an already closed
  immersion to be an isomorphism. None supplies the affine-group assertion.
- rg of lean/WeilConjectures and lean/Sheaf with that same pattern: the relevant overlap
  is AlgebraicGeometry.isClosedImmersion_of_injective_algebraPoints in
  Sheaf.AlgebraicGeometry.GroupScheme.MonomorphismClosedImmersion. Its full signature
  and docstring were read locally and checked against the current server source.
  It states the result for separated finite-type groups, without the affine hypotheses.
  A module-mode scratch example compiled the application to affine groups: separation
  is inferred by isAffineHom_of_isAffine and IsSeparated.of_isAffineHom. It is a more
  general theorem on different input objects, so this delivery retains the exact affine
  node statement instead of recording that stronger signature as verbatim equality.
  No new definition duplicates any existing notion.
- rg by this item's exact ID in lean/WeilConjectures returned no declaration. Searches
  for the chosen new declaration name in Mathlib, WeilConjectures, Sheaf and the upstream
  name index returned no collision.

Validation uses scompile.py only. The first version compiled cleanly, and the final
version adds the complete five-step proof docstring and private proof imports. The
scratch specialization also compiled cleanly. Dry-run and delivery validate the final file.

## Second reading by Q32

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
