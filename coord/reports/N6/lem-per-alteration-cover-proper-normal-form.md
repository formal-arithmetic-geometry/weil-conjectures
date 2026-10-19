## Worker report

The module `Sheaf.AlgebraicGeometry.AlterationCoverProperNormalForm` states
`AlgebraicGeometry.PrimeToEllAlteration.alteration_cover_proper_normal_form`.
Its sole theorem has proof `sorry`; no definitions or additional nodes are introduced.
The original natural statement and dependencies are unchanged.

Source checked directly: ILO, Travaux de Gabber, Exposé II, Theorem 3.2.1,
printed pp. 29–30, and Corollary 2.2.4, printed p. 27. The PDF was read using
pdftotext in the sandbox. The theorem gives the proper-surjection normal form;
finite affine-open refinement gives separated finite-type étale charts, preserving
complete decomposition and their maps to the original members. The source also
allows ell = 1, but this node explicitly fixes a prime, so that separate case is
not asserted here. The complete eleven-step DAG proof is included in the docstring.

Hypothesis and conclusion correspondence:

- Integral scheme X: `(X : Scheme.{u}) [IsIntegral X]`.
- Noetherian X, meaning a finite affine cover by Noetherian rings:
  `[IsNoetherian X]`. Mathlib's class is locally Noetherian plus compact; its
  `isNoetherian_iff_of_finite_iSup_eq_top` identifies this with the node's wording.
- Quasi-excellent affine coordinate rings:
  `hX : ∀ U : X.affineOpens, IsQuasiExcellent Γ(X, U.1)`.
  This uses the recorded dependency's quasi-excellent predicate, not its stronger
  excellent predicate.
- Prime ell: `(ell : ℕ) [Fact ell.Prime]`.
- Invertible on X: `hinv : ∀ x : X, IsUnit (ell : X.presheaf.stalk x)`.
- Finite family in alt/X: `{B : Type w} [Finite B] (T : B → Alt X)`.
  Each `T b` includes its finite-type structure morphism to X and the exact
  reduced, generically finite, maximally dominant conditions of the dependency.
- Covering of X: `hcover` supplies an object `base` with
  `base.obj = Over.mk (𝟙 X)` and arrows `q` satisfying `IsCoveringFamily ell T q`.
  This is the same identity-object interface used in the landed
  `alteration_cover_standard_refinement`; the underlying maps to X are
  `(T b).obj.hom`. It adds no choice of a different target scheme or topology.
- Integral Noetherian Y: existential `(Y : Scheme.{u}) (_ : IsIntegral Y)` and
  conclusion `IsNoetherian Y`. The existential integrality instance makes the
  generic point and function field available in the subsequent signature.
- Proper surjective Y → X: `(f : Y ⟶ X)`, `IsProper f ∧ Surjective f`.
- Finite prime-to-ell function field extension: the generic-point equation
  `f (genericPoint Y) = genericPoint X` and
  `(f.stalkMap (genericPoint Y)).hom.Finite`, followed by `Nat.Coprime` of the
  explicit `Module.finrank` with ell. The scalar module structure is exactly
  the algebra supplied by that stalk map, not an unrelated algebra structure.
  Its source is the stalk of X at the image of Y's generic point, identified by
  the preceding equation with X's generic stalk; its target is `Y.functionField`,
  definitionally the stalk of Y at its generic point. Thus these are exactly
  the local rings specified by the node. The generic-point equation expresses
  the induced function-field extension and also follows from proper surjectivity
  between integral schemes, so it introduces no extra mathematical restriction.
- Finite family: existential `(n : ℕ) (V : Fin n → Scheme.{u})` and maps
  `v : ∀ i, V i ⟶ Y`. Every finite family can be reindexed this way.
- Separated, étale and finite type: for each i,
  `IsSeparated (v i) ∧ Etale (v i) ∧ LocallyOfFiniteType (v i) ∧ QuasiCompact (v i)`.
- Complete decomposition: `∀ y : Y, ∃ (i : Fin n) (z : V i),
  v i z = y ∧ IsIso ((v i).residueFieldMap z)`.
  This is the pointwise clause of the recorded
  `IsCompletelyDecomposedEtaleFamily`, expressed for schemes instead of bundled
  alt/X objects, as in the landed standard-refinement theorem. No competing
  predicate is defined. IsIso concerns the induced residue-field homomorphism,
  hence expresses the specified same-residue-field lift.
- Factorizations: `(b : Fin n → B)` and maps
  `a : ∀ i, V i ⟶ (T (b i)).obj.left`, with
  `a i ≫ (T (b i)).obj.hom = v i ≫ f` for every i.
- All schemes finite type over X: `LocallyOfFiniteType f ∧ QuasiCompact f`,
  the analogous conditions for `v i ≫ f`, and the conditions already included
  in each `T b : Alt X`. X over itself is finite type automatically.
- The V_i need not be integral: no integrality, normality, connectedness, or
  nonemptiness condition on V_i is imposed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; its scheme-level
  finite-affine-cover encoding is `AlgebraicGeometry.IsNoetherian` from
  `Mathlib.AlgebraicGeometry.Noetherian`.
- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent` (the relevant declaration
  among those listed in def-exc-excellent-ring).
- `Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology`:
  `AlgebraicGeometry.PrimeToEllAlteration.Alt`, `topology`, `IsCoveringFamily`,
  and the pointwise meaning of `IsCompletelyDecomposedEtaleFamily`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`
  and `IsSeparated` (the latter defined in Morphisms.Separated).
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`.
- `Mathlib.AlgebraicGeometry.FunctionField`: `Scheme.functionField`, the generic
  stalk itself, with its integral-scheme field instance.

Imports also include the recorded modules of all currently stated proof dependencies.
The finite-normal-generator-tree and simultaneous-field-sections nodes have no Lean
record yet, so there is no module to import for them. They are proof prerequisites,
not missing notions required for this statement. No import cycle was found by compilation.

Edge cases checked before writing: X cannot be empty because integrality includes
nonemptiness; Y is similarly nonempty. B is allowed to be empty in the signature,
but then hcover would assert an impossible empty cover of this nonempty base. n = 0
is not artificially excluded: complete decomposition itself rules it out for the
nonempty Y. Empty V_i are allowed. Degree one and the identity cover are allowed.
Infinite generic degree is excluded explicitly by RingHom.Finite, independently of
finrank's default value. Ell = 2 is allowed; ell = 0 or 1 is excluded precisely by
primality. Invertibility excludes residue characteristic ell. Generic fields can
have inseparable finite extensions; no separability condition was added to f.
The finite input index lives in arbitrary universe w; output schemes live in the
same universe u as X, as do the schemes in Alt X. No extraneous universe equality
or test-object size restriction is imposed.

Searches made with the prescribed msearch.py wrapper:

- LeanFinder: "An alteration covering of an integral quasi excellent scheme is
  refined by a proper prime to ell alteration followed by a completely decomposed
  etale cover". Eight hits: QuasiCompactCover, quasiCompactCover, ordinary scheme
  Cover, transition-limit covers and cover reindexing; none is this normal form.
- LeanSearch: "prime to ell alteration covering proper surjection completely
  decomposed etale refinement". Eight hits on étale algebras, ordinary étale
  topology, and scheme covers; none gives this alteration-cover theorem.
- Loogle: "AlgebraicGeometry.IsProper, AlgebraicGeometry.Etale". No hits.
- Mathlib grep: "alteration|completelyDecomposed|completely.decomposed" restricted
  to AlgebraicGeometry. No hits.
- Direct rg in upstream WeilConjectures and side lean/Sheaf for alteration-cover
  normal-form wording and the exact node id: found the existing standard-refinement
  and uniformization statements and proof references, not this theorem.
- Exact name/id search in dag/lean_names_upstream.json and upstream WeilConjectures:
  no existing declaration. Read the related standard-refinement module in full
  to reuse the existing hcover encoding rather than introduce an identity object.

No STATEMENT-DISPUTED finding or node correction. Compilation via scompile.py
succeeded for both the sandbox form and the library module name, without errors
or non-sorry warnings (2.4 s and 2.7 s respectively).

## Second reading by N6

The dispatcher explicitly forbids starting another agent, so this is a second
self-reading, not a claim of independent worker review. The maintainer's independent
review remains the delivery review. Reopened the node and complete Lean file and
matched every hypothesis and clause as listed above. In particular checked: the
input is the identity object of alt/X; quasi-excellent is not excellent; generic
degree uses f's actual stalk map; finite degree is explicit; the residue-field map
is the induced map and must be an isomorphism; the factorization is an equality
over X; both finiteness clauses of finite type are present; and there is no
integrality assumption on V_i. No mismatch was found, and no changes were needed.
