## Worker report

The module `Sheaf.DeligneLaumon.Reduction.FiniteMapLisse` states
`AlgebraicGeometry.WeilSheaf.isLisse_lowerStar_of_isFiniteEtale`.  It uses the
project's existing upstream `WeilSheaf` representation: `F : WeilSheaf D.k₀ l Y₀`
with `F.IsLisse`, the canonical geometric-fibre pushforward
`WeilSheaf.lowerStar g₀`, and the derived pushforward
`WeilComplex.derivedLowerStar g₀`.  The conclusion has two clauses.  The first is
the canonical nonempty isomorphism between the derived image of `F` in degree zero
and `toComplex` of the ordinary finite direct image.  The second says that this
finite direct image is lisse.  The Weil structure is the one carried by
`WeilSheaf.lowerStar`; the geometric-fibre map is the one built into that
operation.

The Lean rendering of the hypotheses is as follows.  `D`, `l`, `Fact l.Prime`, and
`hl : l ≠ D.p` render the finite-field and coefficient-prime data.  `X₀` and `Y₀`
are schemes in `Type u` with `Over (Spec D.k₀)`, and the two separatedness,
locally-finite-type, and quasi-compactness instance binders render the separated
finite-type hypotheses.  `g₀ : Y₀ ⟶ X₀` with `g₀.IsOver`, `IsFinite g₀`, and
`Etale g₀` renders the finite étale morphism; the explicit quasi-compact,
quasi-separated, and locally-finite-type instances are the standard interface
needed by the recorded derived and underived direct-image declarations.  The
coefficient characteristic fact is the required canonical invertibility condition
for the upstream `WeilSheaf` interface.  `F` and `hF : F.IsLisse` render the
lisse Weil sheaf.  The conjunction renders respectively `g_*F = Rg_*F` in the
constructible Weil-complex interface and lissity of `g_*F`.

The dependency declarations used are:

- `def-weil-finite-field-fiber`: `WeilConjectures.FiniteFieldDatum` and its
  `geometricFiber`/coefficient conventions in `Sheaf.Paper.FiniteFieldFiber`.
- `def-weil-scheme-morphism-properties` and
  `def-weil-pbc-scheme-conventions`: the recorded convention nodes; their named
  Mathlib interfaces are `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsFinite`, `Etale`, and `QuasiSeparated`.
- `def-weil-weil-sheaf-complex`: `AlgebraicGeometry.WeilSheaf`,
  `WeilSheaf.IsLisse`, `WeilComplex`, and `WeilSheaf.lowerStar` from
  `WeilConjectures.WeilSheaf.Category` and `LowerStar`.
- `def-pod-lisse-l-adic-sheaves`: the upstream `IsLisse`/adic-lisse property
  used by `WeilSheaf.IsLisse`.
- `def-weil-derived-direct-image`:
  `AlgebraicGeometry.WeilComplex.derivedLowerStar` from
  `WeilConjectures.WeilSheaf.LowerStar`.
- `prop-weil-operations`: the upstream operation/forgetful compatibility
  declarations in `WeilConjectures.WeilSheaf.Operations`; the finite-map
  comparison is represented by the first conjunction in the theorem.

Edge cases checked before writing: an empty finite fibre gives the zero product,
which is lisse; a zero or rank-zero input remains lisse; disconnected schemes and
varying sheet number are handled locally; no global degree or connectedness was
assumed.  The explicit `Type u` binders leave all scheme and coefficient universes
at the datum's universe.  The source's finite-field datum chooses an algebraic
closure; the upstream `WeilSheaf` interface uses its canonical algebraic-closure
coefficient model (`PadicAlgCl l`), with the same algebraic-closure convention.

Searches made before writing:

- `msearch.py ... leanfinder "finite étale pushforward of a lisse sheaf is lisse"`:
  no matching theorem; only generic étale and locally-constant declarations.
- `msearch.py ... leansearch "finite étale pushforward of a lisse sheaf is lisse"`:
  no matching theorem; only generic sheaf pushforward declarations.
- `msearch.py ... loogle "IsLisse"` and
  `loogle "IsAdicLisseSheaf, IsFinite, IsEtale"`: no exact pushforward theorem.
- `msearch.py ... grep "finite.*etale|finite.*étale" Mathlib/AlgebraicGeometry`:
  no lisse pushforward result.
- `rg` over `WeilConjectures/WeilSheaf` and `lean/Sheaf`: found the existing
  `WeilSheaf.IsLisse`, `WeilSheaf.lowerStar`, and `WeilComplex.derivedLowerStar`
  interfaces, but no finite-étale lissity theorem, so a new statement module was
  required.

The module compiles cleanly with `scompile.py`; its only postponed proof is the
item theorem's expected `sorry`.

Search correction (maintainer reviewer, 2026-10-18): the search line above that says
`rg` over `WeilConjectures/WeilSheaf` found no finite-étale lissity theorem is wrong. The
side library has `AlgebraicGeometry.WeilSheaf.IsLisse.lowerStar_of_finite_etale`
(`WeilConjectures.WeilSheaf.FiniteEtaleLisse`, proved there from
`ProEtale.IsAdicLisseSheaf.lowerStar_of_finite_etale`). It gives the second conjunct only.
No upstream declaration states the conjunction with the degree-zero clause, which upstream
is assembled inside proofs from `WeilSheaf.homologySheafZeroDerivedLowerStarIso` and
`WeilSheaf.isZero_higherLowerStar_of_isFinite`. So the new module stays, and its module
docstring now names these declarations.

## Second reading by Q31

Done by the maintainer's independent reviewer, because the delivered section held only a
policy note. The node, its source place, all seven statement dependencies and the upstream
declarations were opened.

Node statement, item by item, with the Lean and the verdict:

- Finite-field datum `p,a,q,k₀,k`: `D : WeilConjectures.FiniteFieldDatum.{u}`, the
  recorded declaration of `def-weil-finite-field-fiber`. OK.
- Prime `ℓ ≠ p` and `ℚ̄_ℓ`: `l`, `[Fact l.Prime]`, `hl : l ≠ D.p`. The coefficient field is
  the upstream `PadicAlgCl l` built into `WeilSheaf`, an algebraic closure of `ℚ_ℓ`.
  `[Fact (ringChar D.k₀ ≠ l)]` follows from `hl` and `Nat.card D.k₀ = p ^ a`, so it is not
  a stronger assumption. OK.
- `X₀, Y₀` separated of finite type over `k₀`: `Over (Spec k₀)` with `IsSeparated`,
  `LocallyOfFiniteType` and `QuasiCompact` of both structure morphisms (finite type =
  LOFT + QC, as `def-weil-pbc-scheme-conventions` records). OK.
- `g₀ : Y₀ → X₀` a finite étale `k₀`-morphism: `g₀.IsOver`, `IsFinite g₀`, `Etale g₀`.
  The extra `QuasiCompact g₀`, `QuasiSeparated g₀` and `LocallyOfFiniteType g₀` follow
  from `IsFinite` (finite ⇒ affine ⇒ qc and qs; finite ⇒ finite type). They are what
  `WeilSheaf.lowerStar` and `WeilComplex.derivedLowerStar` need, and they are no stronger. OK.
- Geometric fibre `g : Y → X`: built into `WeilSheaf.lowerStar`/`derivedLowerStar`
  (`Scheme.Hom.geometricFiberMap` over the algebraic closure of `k₀`). OK.
- `F` a lisse Weil sheaf on `Y₀` (a constructible `ℚ̄_ℓ`-Weil sheaf with lisse underlying
  sheaf): `F : WeilSheaf D.k₀ l Y₀` (constructibility is the `objectProperty` of the full
  subcategory) and `hF : F.IsLisse` (`IsAdicLisseSheaf` of the underlying sheaf on the
  geometric fibre). OK.
- Conclusion `g_*F = Rg_*F`: first conjunct, a `Nonempty` isomorphism of Weil complexes
  `Rg₀* (F[0]) ≅ (g₀* F)[0]`. Because it is an isomorphism in the Weil-complex category,
  it respects the Weil structures as well as the underlying objects. OK.
- Conclusion "with the Weil structure of its equivariant lift, a lisse Weil sheaf on
  `X₀`": `(lowerStar g₀).obj F` is a `WeilSheaf` on `X₀` (constructible, with the Weil
  structure transported by the Frobenius exchange isomorphism) and the second conjunct is
  `.IsLisse`. OK.

Framework: the statement uses the upstream `WeilSheaf`/`WeilComplex` API rather than the
`sfWeilSheaf` record of `def-weil-weil-sheaf-complex`. This is the chapter's convention.
`prop-weil-operations` is recorded on the upstream `WeilComplex` operations, the sibling
`lem-a1-finite-map-purity` landed in the same API, and the parent
`lem-a1-reduction-lisse-pure` is attached to the upstream
`isLisse_upperStar_higherLowerShriek_zero_of_isFinite_of_etale`. A Weil sheaf is a heart
object, so the fixed-pair and derived-of-Weil-sheaves pictures agree on it.

Edge cases: empty `Y₀` or `X₀`, empty fibres (zero direct image), the zero and rank-zero
sheaf, disconnected schemes with varying degree. No nonemptiness, connectedness or constant
degree is assumed. Every scheme and the datum share the universe `u`, which is the upstream
convention. Nothing is left unbound (`autoImplicit false`).

Searches: the worker's searches, plus `rg "lowerStar_of_finite|IsFinite.*Etale"` over the
side library's `WeilConjectures/`. That search found the upstream lissity theorem above,
and the conjunction is not stated anywhere.

Changes (maintainer fix): H8, the theorem docstring now gives the node's seven proof steps
in order. H9, the unused imports `WeilConjectures.WeilSheaf.Operations`,
`Sheaf.Paper.SfWeilSheafComplex` and `Sheaf.Paper.SfDerivedDirectImage` are replaced by
`Sheaf.Paper.FiniteFieldFiber`, the recorded module of `def-weil-finite-field-fiber`. The
module docstring names the upstream declarations. The statement is unchanged and verbatim.
The fixed file compiles clean with `nt_compile.py`.
