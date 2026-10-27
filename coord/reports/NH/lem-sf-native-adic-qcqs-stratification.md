## Worker report

Existing declaration attachment; no Lean module is added and no statement is changed.
The exact declaration is
`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.isAdicStratifiedLisseSheaf`
in `WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero`, lines 132–134.
I read its docstring, signature, section variables, and proof through line 198,
including `exists_isAffineOpen` at lines 112–125. The recorded signature is copied
verbatim from `theorem` to immediately before `:=`. Its surrounding context is
`universe u` and `variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}`.
No repair note for this item is present in `coord/repair-notes/`.

Clause-by-clause correspondence:

- Prime ℓ and Ω = algebraic closure of Qℓ: `{l : ℕ} [Fact l.Prime]`;
  the coefficient construction uses `PadicAlgCl l` with its existing topology.
- Arbitrary scheme X and the coefficient sheaf on X itself:
  `{X : Scheme.{u}}`, `adicConstantSheaf l X`, and `{F : AdicSheaf l X}`.
  `AdicSheaf` in `WeilConjectures.SixFunctors.ProEtale.Adic.Module` is
  `Mod (Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l))
  (adicConstantSheaf l X)`. It introduces no geometric fibre or Weil action.
- Locally finite continuous coefficients on the whole underlying space:
  `PadicAlgCl.locallyFiniteFunctions` in
  `WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheaf`, lines 74–111,
  is the subalgebra of `C(T, PadicAlgCl l)` whose defining condition is
  `∀ x, ∃ U ∈ 𝓝 x, FiniteDimensional ℚ_[l] (Submodule.span ℚ_[l] (f '' U))`.
  `adicFunctionsPresheaf` takes `T` to be the underlying space of the entire
  scheme; `adicConstantSheaf` restricts this presheaf to `Scheme.ProEt.topology X`.
  The ULift in its values only implements the site's universe convention.
- The canonical pullback in the node is `adicUpperStar l f`, not an arbitrary
  inverse-image operation. In `Adic.UpperStar`, `adicConstantSheafToLowerStar`
  is precomposition by `pullback.fst`; it uses `locallyFiniteFunctionsComp`.
  `Adic.Module.adicUpperStar` is the induced module inverse image (`modLeft`)
  along precisely this coefficient map. The adjoint coefficient map is an
  isomorphism (`upperStarAdicConstantSheafHom`); transporting the inverse-image
  module along it is the extension of scalars in the node's tensor formula.
- The lisse condition is the framework's `IsAdicLisseSheaf` in `Adic.Constructible`,
  lines 81–87: a covering `R ∈ Scheme.proetalePrecoverage X` and, for EACH member
  `f : V ⟶ X`, `∃ n : ℕ, Nonempty ((f)^*ᵃ[l].obj F ≅
  ⨁ fun _ : Fin n ↦ AdicSheaf.unit l V)`. The existential rank is inside the
  covering-member quantifier and is a natural number including zero.
- Constructibility is `(hF : IsAdicConstructibleSheaf F)`. Its definition at
  `Adic.Constructible:145–149` is `∀ x : X, ∃ (W : Scheme.{u}) (j : W ⟶ X),
  IsOpenImmersion j ∧ x ∈ Set.range j.base ∧
  IsAdicStratifiedLisseSheaf ((j)^*ᵃ[l].obj F)`. Thus it is precisely the
  stated local finite partition condition, using the same canonical pullback.
- Quasi-compactness is `[CompactSpace X]`, the declaration recorded by
  `def-weil-pbc-quasi-compact-scheme` in `Mathlib.Topology.Defs.Filter`.
  This class assumes compactness of the whole space and no separation axiom.
- Quasi-separatedness is `[QuasiSeparatedSpace X]`. The dependency's
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` defines
  `AlgebraicGeometry.QuasiSeparated f` by quasi-compactness of its diagonal.
  Its `quasiSeparated_iff_quasiSeparatedSpace` identifies the scheme condition
  for the map to Spec Z with exactly this topological typeclass.
- The global finite stratification is the conclusion
  `IsAdicStratifiedLisseSheaf F`. Unfolding it (Adic.Constructible:119–125)
  gives `∃ (ι : Type) (_ : Finite ι) (Z : ι → Scheme.{u})
  (i : (k : ι) → Z k ⟶ X)`, followed by all the clauses below.
- Locally closed subschemes: `∀ k, IsImmersion (i k)` supplies actual scheme
  immersions, whose images are locally closed.
- Constructible strata: `∀ k, Topology.IsConstructible (Set.range (i k).base)`.
- Pairwise disjoint covering of the WHOLE scheme:
  `∀ x : X, ∃! k, x ∈ Set.range (i k).base`. Unique membership is equivalent
  to coverage plus pairwise disjointness, including empty strata.
- Lisse restrictions on every stratum:
  `∀ k, IsAdicLisseSheaf ((i k)^*ᵃ[l].obj F)`.
- This is exactly the dependency notion
  `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification` in
  `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`, together with
  the explicitly required constructibility and lissity. I read its full
  structure: `n`, subsets indexed by `Fin n`, local closedness, union equal
  to univ, pairwise disjointness, domain schemes, immersions and their ranges.
  Enumerating the finite type ι by `Fin n` gives these fields; conversely
  that structure yields the same existential partition. The existing theorem
  uses the framework's already-recorded predicate, so no duplicate definition
  or dependency interface repair is needed.

Dependencies read and used: the framework record in
`def-sf-native-weil-derived-framework` lists `AdicSheaf`, `adicConstantSheaf`,
`PadicAlgCl.locallyFiniteFunctions`, `IsAdicLisseSheaf`,
`IsAdicStratifiedLisseSheaf` and `IsAdicConstructibleSheaf`; their owning
modules and exact meanings are given above. Its public entry module is
`WeilConjectures.WeilSheaf.LowerShriek` with primary declaration
`AlgebraicGeometry.WeilComplex.derivedLowerShriek`; I also read its signature,
the recorded Weil-category/object-property and upper/lower-star declarations
in `WeilSheaf.Category` and `WeilSheaf.LowerStar`, and extension-by-zero and
compact-support declarations in `WeilSheaf.OpenImmersion` and `LowerShriek`.
Those finite-field and geometric-fibre constructions are not hypotheses of
this item: the node explicitly applies only their underlying adic framework
on arbitrary X. The other three statement dependencies are the exact
CompactSpace, QuasiSeparated, and finite locally closed stratification
interfaces detailed above. No dependency copy or new node is supplied.

Edge cases checked against the unfolded definitions: empty X permits ι = Empty
(and hence n = 0), with all covering and restriction clauses vacuous. Rank zero
is `Fin 0`; `IsAdicLisseSheaf.of_isZero` in the existing module confirms this
case. Different covering members can have different ranks. Empty strata are
allowed. Nonreduced, non-Noetherian and nonseparated qcqs schemes are retained;
no finite-type, characteristic, base-field or nonemptiness binder appears in
the theorem. The scheme universe u is arbitrary; a finite partition always
has a small finite index type, so `ι : Type` excludes no finite partition.

Searches performed using `msearch.py NH lem-sf-native-adic-qcqs-stratification`:

- `leanfinder`: “A constructible adic sheaf on a quasi compact quasi separated
  scheme admits a finite constructible stratification with lisse restrictions”.
  Eight hits: quasi-compact section-vanishing and affine cover results,
  locally constructible subsets and constructible images; no adic-sheaf match.
- `loogle`: `"IsAdicConstructibleSheaf", "IsAdicStratifiedLisseSheaf"`:
  OK, zero hits.
- `grep` (Mathlib): `IsAdicStratifiedLisseSheaf|isAdicStratifiedLisseSheaf|stratified.*[Ll]isse`:
  OK, zero hits.
- `leansearch`: “constructible adic sheaf on quasi compact quasi separated
  scheme admits finite stratification by constructible locally closed
  subschemes with lisse restrictions”: UNAVAILABLE, service rate limit
  (60 per minute); no verdict inferred from this unavailable search.
- `rg` on `lean/WeilConjectures/SixFunctors/ProEtale/Adic` for
  `IsAdicStratifiedLisseSheaf|isAdicStratifiedLisseSheaf` finds the exact
  theorem in `ExtensionByZero.lean:132`, as well as the definitions and
  other preservation results. The node-id search in `lean/WeilConjectures`
  and theorem-name search in `dag/lean_names_upstream.json` find no hits.
- `rg` on `lean/Sheaf` for the same theorem/predicate names finds uses in
  `Sheaf.AlgebraicGeometry.AdicClosedImmersionFiniteness`, not a second
  declaration of this global-stratification theorem.

No statement fault or STATEMENT-DISPUTED issue was found. The existing theorem
has a proof; this attachment adds no theorem, proof, axiom or sorry. Successful
compilation of its import and full declaration is checked by deliver2.py's
module-mode ExistingChecks probe through scompile.py, before server preflight.

Validation: `deliver2.py NH lem-sf-native-adic-qcqs-stratification --no-push`
returned `OK (dry run): commit 52a7a2bcbdd passes the preflight and compiles;
nothing pushed`. The server module-mode probe successfully imported the recorded
module and checked the full declaration; there were no compiler errors or warnings.
The sandbox JSON comparison confirms that only `lean` differs from the base node.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
