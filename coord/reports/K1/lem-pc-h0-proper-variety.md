## Worker report

The module `Sheaf.AlgebraicGeometry.GlobalSectionsProperVariety` states both clauses of
`lem-pc-h0-proper-variety`.

Clause (1) binds a field `k`, a scheme `X` with `X.Over (Spec (.of k))`, properness,
and `Scheme.Hom.IsVariety`. Its conclusion is finiteness of
`Scheme.globalSectionsRingHom k (X := X)` together with `IsField Γ(X, ⊤)`.
Clause (2) binds the same field and scheme, properness, and
`GeometricallyIntegral`; `Scheme.GlobalSectionsBijective k X` is the existing
notion that the structure map is bijective, i.e. `H^0(X, O_X) = k` as k-algebras.

Dependencies used: `Sheaf.AlgebraicGeometry.Variety`,
`AlgebraicGeometry.Scheme.Hom.IsVariety`, Mathlib's
`AlgebraicGeometry.GeometricallyIntegral` and `IsProper`, and the source notion
`AlgebraicGeometry.Scheme.GlobalSectionsBijective`.

Edge cases checked: `Spec k` and `P^1_k` give `k`; `Spec L` gives a finite field
extension in clause (1) and need not satisfy clause (2); `P^1_C` over `R` shows
geometric integrality is necessary. No extra connectedness or algebraic-closure
hypothesis was added.

Searches: LeanFinder and Loogle queries for global sections of proper varieties;
grep of Mathlib found `finite_appTop_of_universallyClosed` and
`isField_of_universallyClosed`; grep of `WeilConjectures` found
`GlobalSectionsBijective.of_geometricallyIntegral`, but no exact combined theorem.

No `STATEMENT-DISPUTED` issue or node fault.

## Second reading by K1

The node introduces a field `k` (`{k : Type u} [Field k]`) and a `k`-scheme
`X` (`{X : Scheme.{u}} [X.Over (Spec (.of k))]`). Properness is
`[IsProper (X ↘ Spec (.of k))]` in both clauses. The Stacks source, Varieties
Tag 04L2 clauses (1) and (4), and Tag 0BUG clause (8), assumes a field and a
proper scheme; it adds no characteristic or algebraic closure condition.

Clause (1) assumes `Scheme.Hom.IsVariety (X ↘ Spec (.of k))`, the dependency
`def-pc-curve`'s integral, separated, finite-type variety. Its two conclusions
are `(Scheme.globalSectionsRingHom k (X := X)).Finite`, meaning finite as a
`k`-module, and `IsField Γ(X, ⊤)`. Together these say finite field extension.
The module's theorem carries exactly these binders and conclusions.

Clause (2) assumes `GeometricallyIntegral (X ↘ Spec (.of k))`, matching the
geometrically integral component of `def-pc-geometrically-irreducible`. Its
conclusion `Scheme.GlobalSectionsBijective k X` says the structure map
`k → Γ(X, ⊤)` is bijective, hence an isomorphism of `k`-algebras. The source
library already states exactly this as
`AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_geometricallyIntegral`
in `WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective`, with the same
properness and geometric-integrality binders. The two-clause node's record
requires both declarations in one module, so the theorem remains here.

`IsVariety` implies nonemptiness through integrality, and geometric integrality
also excludes the empty scheme. Thus neither clause accidentally asserts a
field structure for the zero ring of an empty scheme. `Spec k` and projective
space give `k`; `Spec L` for a nontrivial finite extension gives the allowed
finite field in clause (1). Characteristic zero and positive characteristic,
dimension zero, and every universe `u` are covered; there is no index set.

Independent searches: LeanFinder for "proper integral scheme finite field
global sections" returned Mathlib's separate `finite_appTop_of_universallyClosed`
and `isField_of_universallyClosed`; Loogle for `GlobalSectionsBijective`
returned no hit because that project name is outside its Mathlib index.
`rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf` found the exact source
theorem for clause (2), but no single declaration of the node's two clauses.
The source theorem has an unfinished proof and matches clause (2), but no
single existing declaration matches the entire two-clause node. I expanded
both theorem docstrings to carry the node's proof steps and cited dependencies.
A trial record listing the external theorem failed the stage-2 preflight,
which requires declarations to be defined in the delivered module; the local
clause (2) statement was restored.

## Earlier second reading (a previous round; superseded)

The node and module were reread clause by clause. The proper-scheme, variety, and
geometric-integrality hypotheses match exactly; clause (1) has precisely the finite
extension and field conclusions, while clause (2) has precisely the k-algebra
global-sections equality. No mismatch was found.

## Review fix (R-hpv0830)

Clause (2) was written again as `globalSections_bijective_of_isProper_of_geometricallyIntegral`
although the source states it verbatim, with the same binders, as
`AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_geometricallyIntegral` (H4). The local
theorem is removed and the record is mixed (allowed since the 2026-10-11 preflight change):
`declarations` names the module's clause (1) theorem and the source's clause (2) theorem. The
unused imports `Mathlib.AlgebraicGeometry.Geometrically.Integral` and
`WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective` are replaced by
`WeilConjectures.AlgebraicGeometry.Cohomology.Defs` (which defines `globalSectionsRingHom`).
Clause (1) is unchanged: proper and `Scheme.Hom.IsVariety` (def-pc-curve's record) give
`(Scheme.globalSectionsRingHom k (X := X)).Finite ∧ IsField Γ(X, ⊤)`.
