## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility` states
`AlgebraicGeometry.Etale.isBoundedConstructible_rightDerivedLowerStar_of_finiteType_over_field`.
Its sole theorem has proof `sorry`; no definition or auxiliary theorem is introduced.
The node is unchanged except for its Lean record.

Hypotheses and conclusion, clause by clause:

- A field k: `(k : Type u) [Field k]`.
- Finite-type k-schemes X and Y: `{X Y : Scheme.{u}}`, structure maps
  `aX : X ⟶ Spec (.of k)` and `aY : Y ⟶ Spec (.of k)`, each with
  `LocallyOfFiniteType` and `QuasiCompact`. These two properties are precisely finite type.
- A morphism of k-schemes: `(f : X ⟶ Y) (hf : f ≫ aY = aX)`.
  This is the usual meaning of a morphism between schemes over k, as in the upstream
  theorem for this same blueprint node. It does not assume separatedness.
- A finite commutative coefficient ring: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  Commutativity follows the cited coefficient conventions, and allows the zero ring.
- An integer annihilating A and invertible in k: `(N : ℕ)` and
  `hA : IsSmoothBaseChangeCoefficients N A (Spec (.of k))`.
  The recorded predicate expands to positivity, finiteness, `(N : A) = 0`, and
  `IsUnit (N : Γ(Spec (.of k), ⊤))`. Global sections of Spec k give k, so this is
  invertibility in k. An invertible integer is nonzero, and its positive absolute
  value gives this natural-number formulation. Finiteness repeats the instance
  needed to form the recorded bounded-constructibility predicate, not an extra condition.
- Input D^b_c: `(K : DerivedCategoryModule A X)` and
  `hK : DerivedCategory.isBoundedConstructible A X K`.
- Rf_* takes values in D^b_c(Y,A):
  `DerivedCategory.isBoundedConstructible A Y
    ((rightDerivedLowerStar (ModuleCat.{u + 1} A) f).obj K)`.
  The ambient `rightDerivedLowerStar` is the existing total right derived functor on
  ordinary unbounded derived categories; preservation of the full-subcategory predicate
  is exactly its restriction to the displayed bounded constructible categories.
  There is no perfectness or finite Tor-amplitude condition and no separatedness condition.

Recorded dependencies used:

- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible` (all cohomology
  sheaves constructible, with an ordered finite cohomological interval), and its
  full subcategory `BoundedConstructibleDerivedCategory`.
- `Sheaf.AlgebraicGeometry.DerivedCategories` and upstream
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, the ordinary derived category of
  `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)`.
- `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`:
  `AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients`.
- The scheme-conventions dependency introduces no declaration. Its recorded Mathlib
  notions `AlgebraicGeometry.Scheme`, `LocallyOfFiniteType`, `QuasiCompact` are used.
- The direct-image proof dependency records `AlgebraicGeometry.Etale.lowerStar` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`; its existing ordinary
  derived functor is `AlgebraicGeometry.Etale.rightDerivedLowerStar` in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`.

All recorded proof-dependency modules are imported without `public`; statement modules
are public imports (bounded constructibility and ordinary derived categories are
publicly imported by SmoothBaseChangeCoefficients). The proof-only nodes
`lem-weil-pbc-dplus-injective-representative`, `lem-wf-affine-noetherian-components`,
and `lem-weil-derived-direct-image-composition` currently have no recorded Lean module,
so there is no such module to import. They are retained in the proof docstring and DAG.
No new nodes, interface repairs or statement corrections are needed.

Edge cases checked: the empty source and empty target are allowed; the zero complex is
allowed; the zero coefficient ring is allowed, including N = 1; arbitrary positive
characteristic is allowed when N is invertible. No affine-intersection or separatedness
hypothesis is introduced. Bounds belong to each complex rather than a uniform bound over
all complexes. Universe u is explicit; schemes and k use u and coefficient modules use
u+1, exactly as the recorded ambient derived category requires. No independent small
universe makes a quantified hypothesis vacuous.

Searches (2026-10-15):

- msearch LeanFinder, “Derived direct image preserves bounded constructible etale
  complexes for morphisms of finite type schemes over a field”: eight hits, including
  `Scheme.Hom.isConstructible_image`; these concern constructible subsets, not complexes.
- msearch Loogle, `DerivedCategory, FiniteType`: zero hits, unknown identifier FiniteType.
- msearch grep, `boundedConstructible|isBoundedConstructible`, Mathlib AlgebraicGeometry:
  zero hits.
- msearch LeanSearch, “Derived direct image preserves bounded constructible complexes on
  etale sites of finite type schemes over a field”: service unavailable, Internal Server
  Error; no mathematical verdict inferred from this unavailable search.
- rg of project and upstream for boundedConstructible/isBoundedConstructible and
  finite-type constructibility, and grep of upstream for this blueprint id: upstream
  `boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType` in
  `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage` has the same geometric
  hypotheses but uses upstream `DerivedCategory.boundedConstructible`, whose sheaf
  predicate differs from the recorded `IsConstructibleEtaleModuleSheaf`. Its full
  signature and docstring were read. Thus it is not an exact existing declaration for
  this node's recorded definitions. The same distinction is expressly recorded in
  def-weil-pbc-constructible-complexes and its module. The proper/open siblings use the
  required predicate and cover only their respective special cases.
- rg for the proposed declaration name in lean/Sheaf and upstream: no existing match.

Validation: server scompile.py compiled both the sandbox module and its library-form
module cleanly (1.8 s and 2.0 s respectively); no warnings. The dry run below verifies
the final packet too. No STATEMENT-DISPUTED or node fault found.


## Second reading by NO

I read the node and its five proof steps independently against the source
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/thm-dg-finite-type-constructibility.md`,
then compared the full Lean signature. This item's source is the blueprint Markdown,
not a Stacks tag; the surrounding section adds no standing geometric hypotheses.
I also read the four statement-dependency nodes and their recorded interfaces, and
opened the coefficient-conventions source to resolve the word "ring".

Object/hypothesis/conclusion checklist (all verdicts: exact):

- Field k: `(k : Type u) [Field k]`. No characteristic restriction is added.
- Schemes X and Y over k: `{X Y : Scheme.{u}}`,
  `(aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))`.
  These are actual scheme structure maps, not topological spaces or affine schemes.
- Both are finite type: `[LocallyOfFiniteType aX] [QuasiCompact aX]` and
  `[LocallyOfFiniteType aY] [QuasiCompact aY]`. I read the Mathlib definitions in
  Morphisms/FiniteType and Morphisms/QuasiCompact; their conjunction is precisely
  the finite-type convention of def-weil-pbc-scheme-conventions. No separatedness,
  extra Noetherian instance, dimension bound or affine hypothesis occurs.
- Morphism of k-schemes: `(f : X ⟶ Y) (hf : f ≫ aY = aX)`. The compatibility
  equation expresses the base structure, without constraining f further.
- Finite coefficient ring A: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  The cited sbc-def-coefficient-conventions source explicitly says commutative,
  so CommRing does not strengthen the intended ring convention.
- An annihilating integer invertible in k: `(N : ℕ)` and
  `(hA : IsSmoothBaseChangeCoefficients N A (Spec (.of k)))`.
  I unfolded the recorded definition: `0 < N ∧ Finite A ∧ (N : A) = 0 ∧
  IsUnit (N : Γ(Spec (.of k), ⊤))`. This is annihilation and invertibility in k;
  the latter is equivalent through the canonical global-sections isomorphism.
  Any invertible integer has positive absolute value, giving exactly this natural
  witness. Repeated finiteness is a required interface instance, no new condition.
- Arbitrary input in D^b_c(X,A): `(K : DerivedCategoryModule A X)` and
  `(hK : DerivedCategory.isBoundedConstructible A X K)`. I read
  BoundedConstructibleComplexes and DerivedCategories and the upstream
  Derived/Coefficients definition: the ambient category is the ordinary unbounded
  derived category of etale ModuleCat A sheaves; the predicate means every
  cohomology sheaf is IsConstructibleEtaleModuleSheaf and vanishes outside some
  ordered integer interval. There is no finite Tor-amplitude hypothesis.
- Output in D^b_c(Y,A): `DerivedCategory.isBoundedConstructible A Y
  ((rightDerivedLowerStar (ModuleCat.{u + 1} A) f).obj K)`.
  I read rightDerivedLowerStar in Derived/UpperLowerStarCoherence: it is the total
  right derived functor of etale lowerStar on ordinary unbounded categories,
  for arbitrary f. Preservation of the full-subcategory predicate expresses
  exactly the asserted restriction of that functor. Bounds may depend on K.
- Nonseparated f: there is no IsSeparated or compactification instance on f.
  The docstring retains all five node proof steps, including finite Cech rows,
  bounded-below reindexing, finite filtration and the constructible abutments.

Edge cases: empty X and empty Y are not excluded by any binder (a morphism to
empty Y forces empty X); the empty cover/intersection argument is explicitly
handled in the proof docstring. K = 0, the zero coefficient ring, and N = 1
remain allowed. N = 0 is excluded precisely because it cannot be invertible
in a field. Positive characteristic is allowed exactly when it does not divide
N. No index set occurs in the signature. Universe u is explicit throughout;
A and its modules live in u+1 as required by the recorded small-etale derived
category. A finite coefficient ring can always be represented there. No
independent lower test-object universe or unbound universe occurs.

Independent searches, with different wording from the author's:

- msearch LeanFinder: "etale higher pushforward finite field constructible
  cohomology sheaves": eight hits on etale morphisms and ordinary module
  pushforward; no derived constructibility statement.
- msearch Loogle: `Sheaf, DerivedCategory`: unknown identifier Sheaf, no hits;
  this did not establish nonexistence.
- msearch LeanSearch: "higher direct image of constructible etale module sheaves
  has finite cohomological range": service unavailable (Internal Server Error).
- rg in Mathlib AlgebraicGeometry and CategoryTheory for isBoundedConstructible,
  boundedConstructible, constructible pushforward and derived constructibility:
  no match. Independent rg in lean/Sheaf and upstream found only the open/proper
  special cases for this project's predicate, and the upstream general theorem
  boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType.
  I opened that theorem and followed its predicate to
  CategoryTheory/DerivedCategory/Constructible and ConstructibleSheaf/Defs.
  It uses Scheme.IsConstructibleSheaf and its finite-locally-constant interface,
  whereas the recorded dependency here uses IsConstructibleEtaleModuleSheaf
  with finite constant module values. They are not definitionally the same;
  identifying them requires a comparison theorem. The dependency node explicitly
  records this distinction. Thus the upstream declaration is not an exact
  existing declaration for the requested recorded predicate.

No mismatch was found; I retained the Lean module and node signature unchanged.
There are no new nodes, dependency repairs or statement_change to audit. The
only delivery change from this reading is this report section. The signature
was compared verbatim with lean.statement, including every binder. No hollow
definition, private copy, file-local notation or proof beyond sorry is present.
