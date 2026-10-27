## Worker report

The module `Sheaf.AlgebraicGeometry.AlgClosedAffineNormalProjectiveBoundary` states
`AlgebraicGeometry.exists_algClosed_affine_normal_projective_boundary`, with `sorry` as
its sole proof. No definitions, new nodes, dependency repairs or statement corrections.
Only the item's `lean` field changes. All eight original proof steps, including their
node citations, appear in the theorem docstring.

Hypothesis and clause correspondence:

- Algebraically closed field k: `(k : Type u) [Field k] [IsAlgClosed k]`.
- A k-scheme X: `(X : Scheme.{u}) (f : X ⟶ Spec (.of k))`. The explicit structure map
  is needed for the base changes and the compatibility of j with the k-structures.
- Smooth, geometrically integral, affine, finite type: `[Smooth f]`,
  `[GeometricallyIntegral f]`, `[IsAffine X]`, and the pair
  `[LocallyOfFiniteType f] [QuasiCompact f]`. These are exactly the recorded interfaces.
- C and its k-structure: existential `C` and `p`; finite type is
  `LocallyOfFiniteType p ∧ QuasiCompact p`.
- A closed embedding into finite-dimensional projective space over k: `IsHProjective p`.
  Its recorded definition is the finite-coordinate projective-space factorization.
  C is nonempty by geometric integrality, so its coordinate type cannot be empty;
  identifying it with `Fin (n+1)` gives precisely the stated P^n_k embedding.
- Dense open immersion over k: `j ≫ p = f ∧ IsOpenImmersion j ∧ DenseRange j`.
- Geometric integrality of C: `GeometricallyIntegral p`.
- For EVERY F/k, geometric normality and the 'in particular' assertions: the first
  `∀ (F : Type u) [Field F] [Algebra k F]` uses exactly
  `pullback p (Spec.map (CommRingCat.ofHom (algebraMap k F)))`. It asserts `IsIntegral`,
  `∀ x, IsDomain (…presheaf.stalk x) ∧ IsIntegrallyClosed (…presheaf.stalk x)`,
  `IsNoetherian`, and properness of `pullback.snd`. Normality is the node's own inline
  stalk condition, not field-theoretic `Normal`. Mathlib `IsNoetherian` means locally
  Noetherian plus compact and is equivalent to the requested finite affine cover by
  spectra of Noetherian rings (`isNoetherian_iff_of_finite_iSup_eq_top`).
- Finiteness and possible absence of boundary primes: `∃ (r : ℕ) (B : Fin r →
  C.IdealSheafData)`. No positivity binder on r.
- Reduced boundary subschemes and geometric integrality: `IsReduced (B i).subscheme`
  and `GeometricallyIntegral ((B i).subschemeι ≫ p)`. `IdealSheafData` gives real
  closed subschemes, and its support is the image of its closed immersion.
- Exactly the codimension-one irreducible components of the boundary: the first
  `Set.range … = {T | …}`. Here `Z ∈ irreducibleComponents {x : C // x ∉ Set.range j}`
  gives an actual maximal irreducible component of the complement, and
  `Subtype.val '' Z = T` puts it in C. `∃ η, IsGenericPoint η T ∧
  ringKrullDim (C.presheaf.stalk η) = 1` is exactly the stated codimension convention.
  `Function.Injective` on supports rules out repetitions.
- Boundary primes after every F/k: the second universal quantifier. The actual
  scheme-theoretic base changes are `(B i).comap (pullback.fst p …)`, whose subschemes
  are canonically isomorphic to the relevant fibre products by `IdealSheafData.comapIso`.
  Their reducedness is explicit; no extra reduction erases nilpotents. Their supports
  are injective and their range equals exactly the codimension-one components of
  `{x : C_F // p_F x ∉ Set.range j}`. This is exactly `C_F ∖ j_F(X_F)` because the
  base change of an open subscheme is its inverse-image open. The generic-point and
  stalk dimension condition is imposed on C_F. Together with reducedness, equality
  of supports identifies the reduced induced closed subschemes, by the existing
  reduced-induced-closed-subscheme uniqueness theorem. This asserts equality as
  embedded reduced subschemes, not just a count or a choice of abstract schemes.

The theorem is universe-polymorphic in u. Fields tested have the same universe as
k and the schemes, exactly as the existing geometric-integrality and normality interfaces;
there is no independent potentially smaller test universe. No finiteness, algebraicity,
separability, characteristic or algebraic-closedness condition is placed on F.
`set_option autoImplicit false` enforces explicit variable binding.

Dependency declarations read and reused (the normal-ring convention is intentionally inline):

- `def-weil-field`: `Field` in `Mathlib.Algebra.Field.Defs`.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.
- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback` and `CategoryTheory.Limits.pullback.fst`, `CategoryTheory.Limits.pullback.snd`.
- `def-pc-geometrically-irreducible`: `Mathlib.AlgebraicGeometry.Geometrically.Integral`, `AlgebraicGeometry.GeometricallyIntegral` and `AlgebraicGeometry.GeometricallyIrreducible`, `AlgebraicGeometry.GeometricallyReduced`.
- `def-weil-algebraic-closure`: `IsAlgClosed` in `Mathlib.FieldTheory.IsAlgClosed.Basic`, the algebraically closed clause of its recorded mathlib_match; no algebraic-closure object is needed.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth` and `AlgebraicGeometry.SmoothOfRelativeDimension`, `AlgebraicGeometry.Etale`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map`.
- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, `AlgebraicGeometry.IsHProjective`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper` and `AlgebraicGeometry.IsSeparated`, `AlgebraicGeometry.UniversallyClosed`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`.
- `def-weil-pbc-normal-ring`: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, `IsIntegrallyClosed` and `IsDomain`, `Localization.AtPrime`.

Further existing APIs: `Scheme.IdealSheafData` and `support` in
`Mathlib.AlgebraicGeometry.IdealSheaf.Basic`, `subscheme`/`subschemeι` in `.Subscheme`,
`comap`/`comapIso` in `.Functorial`; `IsGenericPoint`, `irreducibleComponents`,
`ringKrullDim`; no replacement definition. The reduced-induced interface is
`WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`,
`AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`.
All proof dependencies with recorded modules are imported plainly unless already
public statement imports. The smooth-normal-ascent proof node has no recorded module
or match and is not invented here; it is not needed to type the statement.

Edge cases checked before writing: Spec k has C = Spec k and r = 0; A^n in P^n
has its geometrically integral hyperplane boundary for n > 0; G_m in P^1 has two
separate boundary points that remain separate over every extension. The empty scheme
is excluded by the given geometric-integrality hypothesis (not by an added binder).
Zero-dimensional integral smooth affine input has empty boundary. Empty r gives empty
ranges, so the last equality says there are no boundary primes after extension.
Higher-codimension boundary components are filtered by the exact stalk-dimension test,
not silently counted. Positive characteristic and transcendental extensions are allowed.
The identity extension F = k is included in both universal clauses.

Source read: local `literature/stacks-project/varieties.tex`, labels
lemma-normalize-projective (0GK4), lemma-geometrically-normal-at-point (038N),
lemma-perfect-reduced (020I), lemma-separably-closed-irreducible (020J);
`morphisms.tex`, lemma-H-quasi-projective-open-H-projective (01WA);
`algebra.tex`, lemma-dimension-preserved-field-extension (00P3).
The item is an assembled auxiliary statement, not a blueprint unit's own statement.
No statement fault or STATEMENT-DISPUTED claim.

Searches actually run through msearch.py with group Q151 and this item:

- leanfinder: "A smooth affine geometrically integral scheme over an algebraically closed
  field admits a normal projective compactification whose codimension one boundary
  components remain geometrically integral"; eight hits, mainly Mathlib normalization
  and IsIntegral declarations; none gives the compactification and boundary assertion.
- loogle: `AlgebraicGeometry.IsIntegral, "compactification"`; zero hits.
- grep: `normal.*projective|boundary.*component|geometricallyNormal`, restricted to
  Mathlib AlgebraicGeometry; zero hits.
- leansearch: "normal projective compactification smooth affine variety boundary
  components field extension"; eight hits, mainly field-extension Normal and
  compactSpace_of_isAffine; none matches.
- rg on `lean/WeilConjectures` and `lean/Sheaf`: item id, normal-projective compactification
  and boundary-prime patterns; only the existing affine projective compactification
  theorem is relevant, and it lacks normality and the boundary clause. Broader
  geometric-normality searches find normalization and curve inputs, not this assertion.
- rg on the pinned Mathlib IdealSheaf sources found the existing `comap` construction
  and its `comapIso`; these are used instead of creating another base-change notion.

## Second reading by Q151

Performed a second clause-by-clause self-check with the node and final module open;
no independent agent was started, as the dispatcher explicitly prohibits that. The
maintainer's independent delivery review is still required. In this reading I checked
that range equality plus injectivity gives a list without omissions or repetitions;
that the `IsGenericPoint` is in the ambient C (respectively C_F), so its stalk is the
one whose dimension the node specifies; and that boundary components are components
of the complement, not components of C itself. I checked that `comap` is the actual
scheme-theoretic base change and that reducedness is asserted before identifying
reduced closed structures by their support. I also checked both appearances of F = k,
the empty-list case, the k-linearity of j, and the proper projection's direction.
The compiler required explicit `: Scheme.{u}` annotations on pullbacks coerced to
point types; these annotations fix elaboration without changing the mathematical
statement. One overlong line was split; no node statement or dependencies changed.

## Validation

Compilation uses only the prescribed `scompile.py`, in module mode with the real
library module path and sandbox module path. Final compile and delivery preflight
results are recorded below.

Final `scompile.py` passed both sandbox and library module modes cleanly (1.8 s each),
with no errors or warnings. `deliver2.py --no-push` printed
`OK (dry run): commit 281b68a0083 passes the preflight and compiles; nothing pushed`.
