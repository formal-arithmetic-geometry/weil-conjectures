## Worker report

The module defines `AlgebraicGeometry.IsPerfectClosedImmersion` in
`lean/Sheaf/AlgebraicGeometry/PerfectClosedImmersion.lean`.

The Lean rendering of the statement is:

- `Z` and `Y` are schemes: `{Z Y : Scheme.{u}}`.
- `i : Z ⟶ Y` is the given morphism.
- `[IsClosedImmersion i]` is the closed-immersion hypothesis.
- `∀ x : Y, ∃ U : Y.Opens, x ∈ U` gives an affine open covering point by point.
- `IsAffineOpen U` renders that every covering open is affine.
- `I : Ideal (Γ(Y, U))` is the affine ideal.
- `Nonempty (Scheme.Opens.toScheme (i ⁻¹ᵁ U) ≅ Spec (CommRingCat.of
  ((Γ(Y, U) : Type u) ⧸ I)))` renders the quotient description of the inverse image.
- `P : ProjectiveResolution (ModuleCat.of (Γ(Y, U) : Type u)
  ((Γ(Y, U) : Type u) ⧸ I))` is a projective resolution of the quotient module.
- `∀ n, Module.Finite ... (P.complex.X n)` and `∀ n, Module.Projective ...
  (P.complex.X n)` render finite projective terms.
- `∃ N : ℕ, ∀ n, N ≤ n → IsZero (P.complex.X n)` renders boundedness.

Dependencies used are Mathlib declarations `AlgebraicGeometry.Scheme`,
`AlgebraicGeometry.IsClosedImmersion`, `AlgebraicGeometry.IsAffineOpen`,
`Module.Projective`, and `CategoryTheory.ProjectiveResolution`. The dependency
nodes `def-pc-scheme`, `def-weil-closed-immersion`, `def-weil-affine-spectrum`,
and `def-weil-pbc-projective-module` all record these Mathlib notions.

Edge cases checked: the pointwise cover is vacuous for an empty target; the unit
ideal gives an empty quotient scheme; the zero ideal gives the identity quotient;
and `N = 0` permits a length-zero bounded resolution. No statement fault or
`STATEMENT-DISPUTED` applies.

Searches made:

- LeanFinder query `surjective algebra map perfect morphism finite projective
  resolution quotient`: unrelated smoothness/cotangent declarations only.
- Loogle query `IsPerfectMorphism IsClosedImmersion`: zero hits; unknown
  `IsPerfectMorphism`.
- Mathlib grep for `perfect morphism ring map pseudo coherent finite tor dimension`:
  zero hits.
- Source grep for `perfect closed immersion`, `PerfectClosed`, and
  `IsPerfectClosed`: no matching declaration.

## Second reading by C1

I compared the node with the module and the Stacks source, Tags 0687, 0686,
and 068Y. Tag 0686 assumes a locally finite type morphism for its general
criterion. For a closed immersion with the node's finite resolution of `A/I`,
that finiteness follows locally: the first two finite projective terms give a
finite presentation of the quotient and hence a finitely generated ideal.

- The schemes `Z`, `Y` and map `i : Z ⟶ Y` are exactly `{Z Y : Scheme.{u}}`
  and `(i : Z ⟶ Y)`. `def-pc-scheme` records Mathlib's `Scheme` and `Scheme.Hom`.
- The closed immersion hypothesis is `[IsClosedImmersion i]`, Mathlib's closed
  embedding with surjective stalk maps, as recorded by
  `def-weil-closed-immersion`. No field, Noetherian, or separated assumption
  has been added.
- The affine covering is `∀ x : Y, ∃ U : Y.Opens, x ∈ U ∧ IsAffineOpen U`.
  The open is selected for each point, which is equivalent to an affine open
  covering. `IsAffineOpen` means `U.toScheme` is affine. The ring `A` is
  `Γ(Y, U)`, and `IsAffineOpen.isoSpec` identifies `U` with its spectrum.
- The ideal is `I : Ideal (Γ(Y, U))`. The quotient presentation is an
  isomorphism `e : (i ⁻¹ᵁ U).toScheme ≅ Spec (CommRingCat.of (A ⧸ I))`
  **together with** `i ∣_ U ≫ U.toSpecΓ = e.hom ≫ Spec.map
  (CommRingCat.ofHom (Ideal.Quotient.mk I))`. This last equality makes the
  isomorphism one over `U` and renders the node's assertion that the immersion
  is induced by the quotient map, using `def-weil-affine-spectrum`'s `Spec`.
- The module `A/I` has `P : ProjectiveResolution (ModuleCat.of A (A ⧸ I))`.
  This supplies the augmented exact resolution, rather than an arbitrary
  complex. For every term, `Module.Finite A (P.complex.X n)` and
  `Module.Projective A (P.complex.X n)` give finite projectivity; the latter
  is the declaration recorded by `def-weil-pbc-projective-module`.
  `∃ N : ℕ, ∀ n, N ≤ n → IsZero (P.complex.X n)` gives a finite upper bound.
  The finite-free refinement is the node's parenthetical equivalent form,
  not an additional condition.

The previous module had only `Nonempty` of the source-scheme isomorphism.
That did not relate the isomorphism to `i ∣_ U` and was weaker than the node's
quotient description. I replaced it by an isomorphism witness plus the
commuting equation and imported `Mathlib.AlgebraicGeometry.Restrict` for the
restricted morphism. The declaration's signature, and hence `lean.statement`
in the node record, remains verbatim unchanged.

Edge cases: if `Y` is empty, the pointwise covering condition is vacuous.
The unit ideal permits the zero quotient and empty inverse-image scheme;
the zero ideal permits the identity quotient. `N = 0` is allowed and says
all terms of a resolution are zero, as appropriate for the zero module;
nonzero length-zero resolutions use `N = 1`. There is no characteristic or
Noetherian restriction. The universe `u` is arbitrary and is bound explicitly.

Independent search: LeanFinder query `closed immersion finite tor dimension
perfect quotient module` returned no matching perfect-immersion definition;
Loogle queries `IsPerfectMorphism IsClosedImmersion` and `perfect closed
immersion finite projective quotient` had no matching declaration. Source and
Mathlib `rg` searches for `IsPerfectClosedImmersion`, `perfect morphism`,
`perfect ring map`, `pseudo-coherent`, and `Tor dimension` found no duplicate
in the relevant algebraic-geometry or ring-theory modules. I also opened
Mathlib's `IsClosedImmersion.Spec_iff`: it requires precisely the quotient
map equation added here. Compilation after the repair exited 0 without
diagnostics.

