## Worker report

Item: lem-per-generically-finite-proper-near-dimension-one. The module
`Sheaf.AlgebraicGeometry.Morphisms.GenericallyFiniteProperNearDimensionOne` states
`AlgebraicGeometry.exists_isFinite_morphismRestrict_of_generic_algebraic_of_local_dim_le_one`.
Its only theorem has proof `sorry`; there are no new definitions or helper theorems.
The source is Stacks Project, varieties.tex, Lemma finite-in-codim-1 (Tag 0AB7),
condition (1), read locally at lines 3267–3297 together with the preceding Tag 0AB6.
The node agrees with this source; no correction or disputed statement is needed.

Hypothesis and conclusion correspondence:

- Schemes Y and X, with their morphism f:Y→X: `{Y X : Scheme.{u}} (f : Y ⟶ X)`.
  The explicit universe `u` is arbitrary; Mathlib's category of schemes uses a common
  universe, as do the dependency declarations. No finite-type-over-a-field structure
  is imposed.
- Properness: `[IsProper f]`. This is separated, universally closed, locally finite
  type; universal closedness supplies quasi-compactness, hence finite type as in
  the dependency node's definition.
- The target point: `(x : X)`.
- The local ring is Noetherian: `[IsNoetherianRing (X.presheaf.stalk x)]`.
  This is the actual structure-sheaf stalk, with no condition at other points.
- Local Krull dimension at most one: `(hdim : ringKrullDim (X.presheaf.stalk x) ≤ 1)`.
  `ringKrullDim` takes values in `WithBot ℕ∞`, retaining dimension zero and the
  extended values of the definition.
- Every irreducible component and every generic point of it:
  `∀ (Z : Set Y), Z ∈ irreducibleComponents Y → ∀ (η : Y), IsGenericPoint η Z → ...`.
  Components need not be finite in number, and Y need not be irreducible or reduced.
  `IsGenericPoint` is precisely `closure {η} = Z`.
- Algebraicity of the induced extension κ(fη)⊂κ(η):
  `@Algebra.IsAlgebraic (X.residueField (f η)) (Y.residueField η) _ _
  (f.residueFieldMap η).hom.toAlgebra`.
  The algebra structure is the canonical map induced on residue fields by f's
  stalk map, not an independently chosen algebra structure. Expanding
  `Algebra.IsAlgebraic` and `IsAlgebraic` gives, for every element, a nonzero
  polynomial over κ(fη) whose evaluation at that element is zero. No separability,
  fixed degree, or independent finite-dimensionality hypothesis is imposed.
- An open neighbourhood V of x: `∃ V : X.Opens, x ∈ V ∧ ...`.
- Its induced restriction is finite: `IsFinite (f ∣_ V)`. Mathlib's
  `morphismRestrict` has source `(f ⁻¹ᵁ V).toScheme` and target `V.toScheme`, so
  this is exactly f⁻¹(V)→V, rather than the composite to X.

Statement dependency declarations used, with source signatures and docstrings read:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom`.
- def-weil-proper-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`.
- def-weil-pbc-noetherian-ring: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`.
- def-weil-pbc-krull-dimension-ring: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`.
- def-sc-generic-point: `Mathlib.Topology.Sober`, `IsGenericPoint`.
- def-weil-irreducible-components: `Mathlib.Topology.Irreducible`,
  `irreducibleComponents`, as specified by its mathlib_match; this Mathlib leaf
  needs no new lean record.
- def-weil-residue-field: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField`, `AlgebraicGeometry.Scheme.Hom.residueFieldMap`.
- def-weil-finite-integral-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite` (the node's integral alternative is not used here).
- Algebraicity uses the existing `Algebra.IsAlgebraic` and `IsAlgebraic` from
  `Mathlib.RingTheory.Algebraic.Defs`; these directly render the node's explanatory
  nonzero-polynomial clause, without introducing a private predicate.

Recorded proof dependency modules are imported without `public`:
`Mathlib.AlgebraicGeometry.Fiber`, `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
`Mathlib.AlgebraicGeometry.ZariskisMainTheorem`,
`Sheaf.AlgebraicGeometry.QuasiFiniteAtPointIsolated`, and
`Sheaf.AlgebraicGeometry.ProperBasic`. Proper base change is already present in
`Mathlib.AlgebraicGeometry.Morphisms.Proper`; affine spectra and compactness are
available through these imports. The proof prerequisite
lem-per-generically-finite-quasifinite-over-dimension-one has no recorded Lean
module on the read base, so there is no import to add for it. It is not needed to
state this item. Its use is retained in the complete five-step proof docstring;
no dependency is restated and no downstream module is edited.

Edge cases checked before writing:

- Empty Y: generic algebraicity is vacuous, and the empty restricted morphism is
  finite. No nonemptiness binder excludes this case.
- Empty fibre at x: allowed; the singleton-cover argument uses an empty subcover.
- Empty X: a point x cannot be supplied, so the universal statement is vacuous.
- Dimension zero: allowed by `≤ 1`, including a field local ring. The zero ring
  itself cannot be a scheme's local ring at an actual point, but the dimension
  encoding does not artificially exclude extended Krull dimensions.
- Reducible/nonreduced schemes and components not dominating X are allowed; the
  residue source is κ(fη), not the function field of X.
- Purely inseparable algebraic extensions are allowed; no separability binder.
- A positive-dimensional projective space over a field fails generic
  algebraicity, so properness over a dimension-zero base is not misread as finite.
- The blow-up of a surface at a closed point demonstrates why the local
  dimension bound cannot be omitted. No global dimension bound is imposed.

Searches (2026-10-18 UTC), via the prescribed msearch.py wrapper unless noted:

- LeanFinder: "A proper generically finite morphism is finite near a point whose
  local ring is Noetherian of dimension at most one". Eight hits: IsProper,
  IsFinite, LocallyOfFiniteType, LocallyQuasiFinite, stalk finite type, and
  finite_appTop_of_universallyClosed. No exact theorem.
- Loogle: `AlgebraicGeometry.IsProper, AlgebraicGeometry.IsFinite`. Nine hits;
  notably proper plus locally quasi-finite implies finite, and
  `exists_isFinite_morphismRestrict_of_finite_preimage_singleton` (Tag 02UP).
  The latter assumes a finite fibre, not this node's generic algebraicity.
- LeanSearch: "Proper generically finite morphism finite in codimension one".
  Eight hits, all on finite/proper morphisms or finite image hypotheses; no match.
- Mathlib grep: `0AB7|finite.*codim|genericallyFinite` in AlgebraicGeometry.
  Zero hits from the wrapper.
- Source repository rg: `genericallyFinite|finite.*codim|0AB7|` followed by the
  item id (the final alternative was the literal item id, not empty).
  Only flat quasi-finite codimension-preservation comments matched. A separate
  `grep -rn` for the literal item id returned no matches.
- Side library rg with those same patterns: ProperBirationalCurveFinite and
  ProperBirationalNormalCurveIso cite Tag 0AB7 but require curves/birationality;
  their source statements do not give this general theorem. Other hits concern
  etale neighbourhoods and purity, not generic algebraicity.
- Additional rg on residue-field algebra structures and stalk dimensions in
  lean/Sheaf/AlgebraicGeometry and lean/Sheaf/Paper found the established
  `.hom.toAlgebra` convention and the explicit `@Algebra.IsAlgebraic` application
  in StrictLocalAlgebraicResidueModels.lean. The new theorem name has no match
  in upstream source or dag/lean_names_upstream.json.

Validation: scompile.py compiled both the sandbox module and its library-path
form successfully (2.1 s and 2.5 s), with no errors or warnings. All variables
and the universe are explicitly bound. Node copy changes only the lean field;
JSON uses indent 1, Unicode characters, and a final newline.

## Second reading by Q97

Author's self-check under the dispatched direct-delivery protocol; independent
review is the maintainer's, and no additional agent was started. Reopened the node,
the Stacks source and the completed Lean file. Checked the order of schemes and
residue fields: Y is the domain, X the target, and the canonical map goes from
X.residueField (f η) to Y.residueField η. Checked that every component and every
point generic for it is quantified, rather than just a chosen component or a
chosen global generic point. Checked that the Noetherian binder is at x only,
that the inequality is at most one rather than exactly one, and that V contains
x. Read the full morphismRestrict signature to verify the target is V rather than
X. Read Algebra.IsAlgebraic and IsAlgebraic to check that the canonical algebra
structure renders exactly the nonzero-polynomial clause. No extra normality,
reducedness, global Noetherian, dominance, or finite-type-over-a-field hypothesis
appears. All five proof steps from the node appear in the theorem docstring.
No mismatch found and no statement correction made.
