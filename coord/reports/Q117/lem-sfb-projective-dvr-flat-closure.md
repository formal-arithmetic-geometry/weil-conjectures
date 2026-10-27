## Worker report

Module: `Sheaf.AlgebraicGeometry.ProjectiveDvrFlatClosure`.
Main declaration:
`AlgebraicGeometry.ProjectiveDvrFlatClosure.exists_unique_projective_dvr_flat_closure`.
The only theorem has proof `sorry`. The two helper definitions have real data:
`genericChartMap` is the restriction ring map of the given generic closed subscheme;
`quotientScalarMap` is the structural R-action on the actual affine quotient, composed
from `Scheme.ΓSpecIso`, the structural map on global sections, restriction, and the
quotient map. They belong to this node's contraction/quotient construction and introduce
no separate notion. Both are listed in `lean.declarations`.

Source read: Grothendieck, Bourbaki Expose 221, Lemma 3.7 and its kernel proof,
printed pp.264--265 (PDF pages 16--17), at
https://www.numdam.org/article/SB_1960-1961__6__249_0.pdf . The lemma concerns the unique
flat extension of a generic quasi-coherent quotient. Its structure-sheaf specialization
is the closed-subscheme statement here. Theorem 3.2 supplies the projective context;
the accepted node's step 7 and recorded locality theorem supply the constant polynomial.
The current blueprint unit was read at
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`.
This item is a created tool in that unit, not the unit statement itself. No correction
of the node or its dependencies was needed. No new nodes or dependency modules.

Hypothesis and clause correspondence:

- Any DVR R: `(R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`.
  The Mathlib class is precisely a local PID which is not a field. Any fraction field:
  `(K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]`.
- n >= 0: `(n : ℕ)` includes n = 0. E is an arbitrary `Scheme.{u}` and
  `i : E ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R))`, `[IsClosedImmersion i]`
  is exactly the specified embedding. The structure map f throughout the formula is
  `i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of R)) ↘ Spec (.of R))`.
- E_K: `pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))`.
  The arbitrary generic closed subscheme is `I_K : E_K.IdealSheafData`.
  Mathlib ideal sheaf data classify closed subschemes retaining the embedding.
- Existence: `∃ I : E.IdealSheafData`. The scheme is `I.subscheme` and its
  closed immersion is `I.subschemeι`; these are Mathlib's real gluing construction.
- Flat: the first `Flat (I.subschemeι ≫ f)` conjunct.
  Finitely presented: `LocallyOfFinitePresentation`, `QuasiCompact`, and
  `QuasiSeparated` of that same map. This is the recorded definition's comparison
  clause, not merely local finite presentation.
- The prescribed generic restriction as a closed subscheme:
  `I.comap (pullback.fst f h) = I_K`, where h is Spec K -> Spec R.
  `IdealSheafData.comap` is the ideal of the actual pullback closed immersion;
  equality retains the inclusion in E_K, not just the abstract generic scheme.
- Uniqueness: every `J : E.IdealSheafData` satisfying flatness, the three finite
  presentation conditions, and that same generic ideal equality satisfies `J = I`.
  This is uniqueness among exactly the closed extensions named in the statement.
- Every affine chart Spec C: `∀ U : E.affineOpens`, C = `Γ(E, U)`.
  `I.ideal U = RingHom.ker (genericChartMap f h I_K U)`. The displayed map is
  restriction `C -> Γ(Z_K, g⁻¹ U)`, for g the generic immersion followed by projection.
  On affine charts its codomain is `(C tensor_R K)/J_K`, so the kernel condition
  says exactly `c tensor 1 ∈ J_K`. There is no assumption that C embeds into C_K.
- Compatibility with every localization: `∀ T : Submonoid Γ(E, U)`, the extension
  of `I.ideal U` along `C -> Localization T` equals the kernel of `IsLocalization.map`
  of the same restriction ring map, with its codomain localized at the image of T.
  Thus the formula also handles multiplicative subsets whose image contains zero.
  This expresses contraction of `T⁻¹ J_K`, including arbitrary, not just principal,
  localizations. The localized quotient is `(T⁻¹ C_K)/(T⁻¹ J_K)`.
- Gluing: for every inclusion of affine opens `h : U ≤ V`, the next conjunct
  gives the equality after applying `E.presheaf.map (homOfLE h).op` to the ideal on V.
  Together with the actual `IdealSheafData` and its `subscheme` gluing, this specifies
  restriction on overlaps and the canonical cocycle, using the existing sheaf maps.
- R-torsion-free quotient: for each chart, `∀ r : R, r ≠ 0 → Function.Injective`
  of `fun x : Γ(E,U) ⧸ I.ideal U ↦ quotientScalarMap f I U r * x`.
  Flat quotient: the accompanying `(quotientScalarMap f I U).Flat` uses the same
  R-module structure and actual quotient ring.
- The common Hilbert polynomial: `∃ P : NumericalHilbertPolynomial` with
  `HasProjectiveFibreHilbertPolynomial f i (Over.mk h) I_K P.val` first identifies
  it as the polynomial of the given generic closed subscheme. For every
  `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]` and every geometric point
  `s : Spec Ω ⟶ Spec R`, `HasProjectiveFibreHilbertPolynomial f i (Over.mk s)`
  of the pulled-back I has that same `P.val`. The exact recorded definition uses
  eventual Euler characteristics of twists pulled back along the fixed embedding.
  All test fields are in the scheme universe u, including algebraic closures of
  residue fields; there is no independent lower test universe or excluded characteristic.
- Empty subschemes: there is no `Nonempty`, reducedness, or positive polynomial
  hypothesis. `I_K = ⊤` and `I = ⊤` give zero quotients and the zero polynomial.
  No flatness of E/R, excellence, or external base map appears anywhere in the binders.

Dependency declarations read and used:

- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd`, in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`;
  the universal property and scheme instances support the actual fibre product.
- `def-sfb-projective-fibre-hilbert-polynomial`:
  `AlgebraicGeometry.NumericalHilbertPolynomial` and
  `AlgebraicGeometry.HasProjectiveFibreHilbertPolynomial`, in
  `Sheaf.AlgebraicGeometry.ProjectiveFibreHilbertPolynomial` (full file read).
- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`, lines 55--60.
- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`, lines 116--120 and 180.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, lines 42--46.
- `def-kun-projective`: `AlgebraicGeometry.IsHProjective`,
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, lines 31--41.
  The statement gives the embedding itself; this class is used by proof step 4.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`, lines 469--480.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`, lines 35--45 and its stalk criterion 106.
- `def-sbc-locally-finite-presentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, lines 41--50;
  finite presentation also includes the recorded qcqs conditions.

For closed subschemes, the existing Mathlib `IdealSheafData.ideal`, `.comap`,
`.subscheme`, `.subschemeι`, and `Scheme.Hom.ker` were read in
`IdealSheaf.Basic`, `IdealSheaf.Functorial`, `IdealSheaf.Subscheme`. The latter's
`comapIso` explicitly identifies the comap scheme with the pullback.
No copied private closed-subscheme or Hilbert-polynomial definition was introduced.
All already stated proof dependencies are imported; Mathlib leaves use their recorded
files (the closed-proper leaf imports `ZariskisMainTheorem`). The full source and proof
of the recorded `flat_projective_hilbert_polynomial_locality` were read, including its
field-extension and empty-fibre clauses; its module is imported for stage 3.

Edge cases checked mathematically before drafting: n = 0; E empty; empty Z_K;
E supported on the special fibre (E_K empty, forcing empty flat extension); an ambient
chart with R-torsion, such as the relation pi*x = 0 (C -> C_K need not be injective);
nonreduced generic closed subschemes such as x^2 = 0; nonexcellent DVRs; mixed and equal
characteristic. The contraction kills vertical torsion and its quotient embeds in a
K-algebra in each case. Localization at a subset containing zero produces the zero ring
on both sides. No binder discards any of these cases.

Searches actually run on 2026-10-24 via msearch.py, Q117 / this item:

- leanfinder: `Over a DVR a generic projective closed subscheme has a unique flat closure defined by contraction of ideals`:
  8 hits, headed by `AlgebraicGeometry.Proj.valuativeCriterion_existence`, with
  projective-spectrum vanishing ideals and `Flat.generalizingMap`. These extend points
  or describe topological vanishing, not this closed-subscheme extension theorem.
- loogle: `"IsDiscreteValuationRing", "Flat"`: 0 hits.
- grep: `schematicClosure|closure.*flat|flat.*closure`, Mathlib AlgebraicGeometry: 0 hits.
- leansearch: `A generic closed subscheme of a projective scheme over a DVR has a unique flat closure`:
  8 hits, `Flat.flat_appLE`, `Flat`, `IdealSheafData.subscheme`, base-change and
  composition flatness. None contains the existence/uniqueness statement.
- Local rg on `lean/WeilConjectures` and `lean/Sheaf` for
  `schematicClosure|flat.*closure|closure.*flat|projective_dvr|dvr_flat_closure` found
  only unrelated homological closure and specialized component/subgroup results.
  `DvrFlatGenericSubgroupClosure.lean` was read: it requires a group scheme and a
  generic subgroup, hence cannot state this arbitrary generic closed-subscheme result.
- `grep -rn` of this item's id in `lean/WeilConjectures`, and `rg` in
  `dag/lean_names_upstream.json`: no match.

Server validation: scompile.py compiles both sandbox and library module successfully
(3.3 and 3.1 seconds). The initial diagnostic repairs were adding the public
`IsAlgClosed.Basic` import and making each projective projection's base explicit.
There are no Lean errors or non-sorry warnings. `autoImplicit` and
`relaxedAutoImplicit` are both false. Every delivered Lean line is at most 100 columns.

## Second reading by Q117

This is the author's second reading under the dispatcher brief (no other agents started);
the maintainer provides the independent review. I reopened the original JSON statement
and the completed Lean file and matched each clause above. I checked that the uniqueness
competitor is required to be flat and finitely presented with the same generic ideal;
it is not required to satisfy the kernel formula or polynomial conclusion, which would
weaken uniqueness. I checked that generic equality is an equality of pulled-back ideals,
that the localized map localizes the image multiplicative subset, and that scalar
multiplication is formed from the specified Spec R structure rather than an arbitrary
action. The quotient's ring-map flatness is the requested R-module flatness. Finally,
P is first constrained by the original I_K and then by every geometric point, using
exactly the existing fibre polynomial definition and fixed i; no arbitrary polarization
or abstract isomorphism replaces the one in the node. The empty case is included without
special hypotheses. No mathematical mismatch or node correction was found. Compiler
repairs only addressed import visibility and explicit projection bases.
