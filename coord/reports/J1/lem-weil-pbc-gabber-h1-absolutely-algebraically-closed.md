## Worker report

The module `Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing` states
`AlgebraicGeometry.Etale.isZero_constant_cohomology_one_of_isIntegrallyClosed`, with
only `sorry` as its proof. No new definition, dependency module, or statement
correction is required.

Hypotheses and conclusion, matched clause by clause:

- A commutative normal domain R is `(R : Type u) [CommRing R] [IsDomain R]
  [IsIntegrallyClosed R]`. This uses the normal-domain clause of
  def-weil-pbc-normal-ring, rather than the general normal-ring localization clause.
- Its field of fractions is separably closed: `[IsSepClosed (FractionRing R)]`.
  The canonical fraction field removes the need to choose a separately named K.
- X is Spec R: the codomain of i is `Spec (CommRingCat.of R)`; no extra X or
  identification is needed.
- An arbitrary closed subscheme is `(Z : Scheme.{u})
  (i : Z ⟶ Spec (CommRingCat.of R)) [IsClosedImmersion i]`.
- Every finite abelian group is `(M : Type (u + 1)) [AddCommGroup M] [Finite M]`.
  This is the coefficient universe used by the recorded cohomology functor on
  Scheme.{u}; every finite abelian group admits a representative there.
- Its constant sheaf on Z_et is
  `(constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)`.
- The sheaf is placed in degree zero by
  `DerivedCategory.singleFunctor (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) 0`.
  Its H^1 is the value of `cohomology AddCommGrpCat.{u + 1} Z 1` on this object.
- Vanishing is `IsZero` of this AddCommGrpCat object. This means the cohomology
  group is trivial, exactly the zero-group conclusion (and is not IsZero on a
  bare Type).

Dependency declarations read and used:

- def-weil-pbc-normal-ring: `IsDomain` (Mathlib.Algebra.Ring.Defs) and
  `IsIntegrallyClosed` (Mathlib.RingTheory.IntegralClosure.IntegrallyClosed).
- def-pc-separably-closed: `IsSepClosed` (Mathlib.FieldTheory.IsSepClosed).
- def-weil-affine-spectrum: `AlgebraicGeometry.Spec` (Mathlib.AlgebraicGeometry.Scheme).
- def-weil-closed-immersion: `AlgebraicGeometry.IsClosedImmersion`
  (Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion).
- def-weil-pbc-constant-sheaf: `CategoryTheory.constantSheaf`
  (Mathlib.CategoryTheory.Sites.ConstantSheaf).
- def-weil-pbc-etale-cohomology: `AlgebraicGeometry.Etale.cohomology`
  (WeilConjectures.SixFunctors.Etale.Derived.LowerShriek), defined as
  `rightDerivedGlobalSections A X ⋙ DerivedCategory.homologyFunctor A i`.
  Its docstring explicitly identifies its value on a sheaf in degree zero with
  étale sheaf cohomology. No alternate Sheaf.H encoding is introduced.

Edge cases: Z may be empty, disconnected, nonreduced, or all of Spec R; no
nonemptiness, connectedness, or reducedness is imposed on it. M may be the trivial
group, and its order may be divisible by the residue characteristics. There is no
invertibility-of-order hypothesis. R may be a field and need not be Noetherian.
The zero ring is excluded exactly by the source's domain hypothesis. The degree
is precisely one, not an arbitrary degree or a positivity premise. Universes are
explicit; there are no auto-bound variables or file-local definitions/instances.

Source checked: the local Stacks TeX file is not present on this machine, so I
opened https://stacks.math.columbia.edu/tag/09ZB. Its statement is normal integral
affine X with separably closed function field, closed Z, and finite abelian M.
The Spec R form in the node is exactly its affine form. The theorem docstring
carries all three proof steps: H^1–torsor correspondence (03AJ), representation
by a finite étale surjection (03RV), and the section from 09ZA trivializing it.

Searches for an existing statement (actual msearch queries are also recorded in
searches.jsonl):

- LeanFinder: "First etale cohomology of a finite constant abelian sheaf on a
  closed subscheme of the spectrum of a normal domain with separably closed
  fraction field vanishes". Eight hits concern cotangent H1 and étale loci;
  none concern sheaf cohomology or this result.
- LeanSearch: "Etale cohomology H1 constant finite abelian group normal domain
  separably closed fraction field". Service unavailable (Internal Server Error).
- Loogle: `IsSepClosed, IsIntegrallyClosed`. Zero hits.
- msearch grep: `gabber|separably.closed.*cohomology|cohomology.*separably.closed`.
  Only three bibliography references to Gabber in t-structure files; no match.
- rg in WeilConjectures for `gabber`, `absolutely.algebraically.closed`,
  `IsSepClosed`, and the item's id: general Gabber effacement/comparison results
  and unrelated separably closed field facts, no statement of this lemma.
- rg in lean/Sheaf for Gabber/absolutely-algebraically-closed/H1 patterns and
  cohomology usages: no existing matching theorem.
- The chosen full declaration name was searched in Mathlib, WeilConjectures,
  lean/Sheaf, and dag/lean_names_upstream.json: no collision.

No STATEMENT-DISPUTED issue or node fault found.

Validation: scompile.py compiled the 50-line module on the server in 2.8 seconds
with exit code 0 and no warnings. deliver2.py --no-push printed OK: compilation
and preflight pass, except for the second-reading section reserved for the next
worker. Nothing was pushed.

## Second reading by J1

I independently reread the node statement and the Lean signature. The objects and clauses match item by item:

- The normal domain hypothesis is rendered by `(R : Type u) [CommRing R] [IsDomain R]
  [IsIntegrallyClosed R]`; this is exactly the normal-domain branch of
  `def-weil-pbc-normal-ring`, with no Noetherian or finiteness assumption.
- Separably closed fraction field is the instance `[IsSepClosed (FractionRing R)]`, using the
  canonical fraction field required by `def-pc-separably-closed`.
- `X = Spec R` is rendered directly as the codomain `Spec (CommRingCat.of R)` of
  `i : Z ⟶ ...`; `Z` is an arbitrary `Scheme.{u}` and `[IsClosedImmersion i]` is exactly
  the closed-subscheme hypothesis.
- The quantifier over finite abelian groups is `(M : Type (u + 1)) [AddCommGroup M] [Finite M]`.
  The coefficient universe is forced by the small-etale sheaf category and includes the zero
  group and all finite groups represented at that universe.
- The constant sheaf clause is exactly
  `(constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)`.
- Degree zero placement is the explicit `DerivedCategory.singleFunctor ... 0`; the conclusion is
  `IsZero` of the object obtained by applying `cohomology ... 1`, hence vanishing of precisely
  H^1. No extra degree, positivity premise, or stronger vanishing clause is present.

I checked the edge cases: `Z` may be empty, disconnected, nonreduced, or equal to the whole
spectrum; `M` may be the zero group; no invertibility, characteristic, connectedness, or
Noetherian hypothesis is added. The domain assumption excludes the zero ring as in the source.
The explicit universe relation `Z : Scheme.{u}` and `M : Type (u+1)` leaves no unbound universe
or auto-implicit variable.

I reopened the recorded dependency declarations. `IsDomain` and `IsIntegrallyClosed` give the
normal-domain notion, `IsSepClosed` gives the separably closed fraction field, `Spec` and
`IsClosedImmersion` give the affine spectrum and closed immersion, `constantSheaf` gives the
constant sheaf, and `AlgebraicGeometry.Etale.cohomology` gives the derived etale cohomology
functor. Searches in Mathlib, WeilConjectures, and `lean/Sheaf` found no existing declaration
of this statement; the worker's LeanFinder, LeanSearch, Loogle, and grep searches agree.

No mismatch was found, so no source or node change was necessary. The module compiles with only
the permitted `sorry` warning, and its node `lean.statement` remains verbatim identical to the
signature.
