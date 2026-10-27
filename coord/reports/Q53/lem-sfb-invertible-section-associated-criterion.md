## Worker report

The module `Sheaf.AlgebraicGeometry.InvertibleSectionAssociatedCriterion` states
`AlgebraicGeometry.Scheme.Modules.nonvanishing_associatedPoints_iff_affine_mul_injective`.
It has one theorem, with proof `sorry`, and introduces no definitions. The source
was read at `literature/stacks-project/divisors.tex`, definition-regular-section
(line 2778), Tag 01WZ (line 2787), and Tag 0AYL (line 2925).
The unchanged node is the affine-frame formulation of that criterion.

Hypothesis and clause correspondence:

- A scheme `X` is `{X : Scheme.{u}}`; `u` is explicitly declared.
- Locally Noetherian is `[IsLocallyNoetherian X]`, with no global Noetherian or
  quasi-compact assumption.
- An invertible module is `(L : X.Modules) [L.IsInvertible]` using the recorded
  upstream class, whose `exists_isoUnit` says precisely local rank-one freeness.
- A global section is `(s : Γ(L, ⊤))`.
- Condition (i) is `∀ x : X, x ∈ AlgebraicGeometry.associatedPoints X →
  x ∈ nonvanishingLocus L s`. The first set is the recorded stalkwise associated-prime
  definition. The second set is defined by the germ lying outside
  `IsLocalRing.maximalIdeal (X.presheaf.stalk x) • ⊤` in the stalk module.
  Nonmembership is exactly a nonzero image in the quotient `Lₓ / 𝔪ₓ Lₓ`, so
  it renders the specified residue-field fibre, rather than merely a nonzero germ.
- Equivalence of the two conditions is `↔`.
- Every affine open is `∀ (U : X.Opens), IsAffineOpen U → ...`. Its coefficient
  ring is `Γ(X, U)`, canonically the ring `A` in `U = Spec A`.
- Every trivialization is quantified as
  `∀ (e : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)), ...`.
  Mathlib's `over` is actual restriction to the over-site of `U`, equivalent to
  the open subscheme module category. An isomorphism with the unit is exactly a
  sheaf frame, not an arbitrary choice of a section or an unrelated linear map.
- The restriction of the given section is
  `L.presheaf.map (homOfLE le_top).op s`.
- Its coefficient `a` relative to the frame `e⁻¹(1)` is
  `sectionsLinearEquivOfOverIsoUnit e le_rfl` applied to that restriction.
  This existing upstream equivalence reads the component of `e.hom` over `U`;
  it is `Γ(X,U)`-linear with inverse the component of `e.inv`.
- The map `b ↦ ab` and its injectivity are rendered by
  `Function.Injective (fun b : Γ(X, U) ↦ ... * b)`.
- “Condition (ii) is the regular-section condition” identifies the condition just
  written; it is not a third independent assertion. The declaration docstring
  gives the sectionwise-kernel/sheaf-uniqueness argument identifying it with
  injectivity of `𝒪_X → L` in the source.
- There is no nonemptiness, reducedness, irreducibility, or quasi-compactness binder.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `Sheaf.AlgebraicGeometry.AssociatedPoints`: `AlgebraicGeometry.associatedPoints`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`; the residue field is literally the local-ring
  quotient. The formula uses the equivalent maximal-ideal-submodule condition.
- `WeilConjectures.AlgebraicGeometry.Ample`: `Scheme.Modules.nonvanishingLocus`.
  Its owning landed node `def-weil-pbc-ample-invertible-module` is added to
  `stmt_deps`, as the standing nonvanishing-locus convention requires.
  No ampleness hypothesis is used or introduced.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf` (publicly imported
  through `Modules.Invertible`): `Scheme.Modules.sectionsLinearEquivOfOverIsoUnit`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.over` and `overFunctor`, through the above imports.

The stated proof dependencies are imported without `public` when they are not
already statement dependencies: affine schemes/stalk localization and the affine
basis; localization at a prime; Noetherian rings; the associated-prime zerodivisor
criterion; `Module.exists_annihilator_eq_of_localization_atPrime` from
`Sheaf.RingTheory.AssociatedLocalizationFg`; and the general module-sheaf category
from `Sheaf.CategoryTheory.RingedSiteModules`. No dependency interface repair is needed.
The theorem docstring records all six proof steps of the DAG node.

Edge cases checked mathematically before writing:

- Empty scheme: no associated points. Its only affine open has zero section ring,
  and every self-map of that singleton is injective. Both conditions are true.
- `Spec k`: the sole associated point tests precisely whether the scalar is
  nonzero; multiplication over the field is injective precisely then.
- `Spec k[ε]/(ε²)`, with section `ε`: the sole associated point has zero fibre
  value, and multiplication kills the nonzero element `ε`; both sides fail.
- `Spec k[x,y]/(x²,xy)`, with section `y`: the embedded associated prime `(x,y)`
  must be tested; its fibre value is zero and multiplication kills `x`.
  Thus using associated points, rather than only generic points, is necessary.
- A nontrivial invertible sheaf needs only local frames. Universal quantification
  over affine frames imposes no global trivialization or finite-cover assumption.
  Changing a frame multiplies the coefficient by a unit and preserves injectivity.

Searches performed (2026-10-24; the prescribed `msearch.py` wrapper was used):

- LeanFinder: “A section of an invertible sheaf on a locally Noetherian scheme is
  regular if and only if nonzero at every associated point”. Eight hits, concerning
  residue evaluation and basic opens; no matching scheme/invertible-section criterion.
- LeanSearch: “A section of a line bundle is regular if and only if nonvanishing
  at all associated points on a locally Noetherian scheme”. Eight hits, including
  `IsRegular`, `isRegular_iff_mem_nonZeroDivisors`, and tilde-section facts;
  no matching statement.
- Loogle: `"associatedPrimes", "nonZeroDivisors"`. One hit:
  `biUnion_associatedPrimes_eq_compl_nonZeroDivisors`, the ring-theoretic proof
  input, not this sheaf statement.
- Mathlib grep through msearch: `regularSection|RegularSection|associatedPoints|regular_section`
  in `AlgebraicGeometry`: zero hits.
- `rg` in the project's `lean/WeilConjectures` and `lean/Sheaf` for
  `regularSection|RegularSection|regular_section` found unrelated regular sections
  of constant sheaves and higher-rank purity material; no matching declaration.
  Searches for `associatedPoints` and `nonvanishingLocus` found the definitions
  reused above. A search for both notions together gave a different fibre-assassin
  theorem. A name search in both source roots and `dag/lean_names_upstream.json`
  found no collision for the new declaration.
- `grep -rn 'lem-sfb-invertible-section-associated-criterion' lean/WeilConjectures`
  gave no hits.
- The related DAG statements `lem-pc-nonzero-section-integral-cartier` and
  `lem-sbc-affine-section-associated-stalk` were read. The first assumes an
  integral scheme and constructs a Cartier ideal; the second detects unequal
  module sections at an associated stalk. Neither states this criterion.

No statement correction, disputed statement, new node, or dependency module.
The first server compilation passed for both sandbox and library module modes.

## Second reading by Q53

A fresh second pass by the assigned worker compared the node and the completed
file, including the full signatures of `associatedPoints`, `nonvanishingLocus`,
`IsInvertible`, `SheafOfModules.over`, and `sectionsLinearEquivOfOverIsoUnit`.
No independent worker was started, in accordance with the dispatcher brief;
the maintainer supplies the independent delivery review.

The binders match scheme/local Noetherianity/invertibility/global section exactly.
The left side tests a nonzero fibre value at every associated point, including
embedded points. The right side quantifies all affine opens and all actual sheaf
trivializations and multiplies by the coordinate of the restriction of the same
section. The equivalence has the same direction and content as clauses (i)/(ii).
The empty scheme remains admitted. Neither a global frame nor a nonzero section
is assumed. The added landed dependency only supplies the standard nonvanishing
locus; it does not add an ampleness hypothesis. During this pass, the proof
explanation of the fibre calculation was made explicit in both cases `a ∉ p`
and `a ∈ p`; the Lean signature needed no change.
