## Worker report

The new module `Sheaf.RingTheory.CompletedInvertibleKummerMonoidExtension` states
`Algebra.completedInvertibleKummerMonoidExtension_model`. Its single proof is `sorry`.
It adds no definition and changes only the item's `lean` record. The complete nine-step
natural-language proof from the node is included in the theorem docstring.

Source checked: ILO, Exposé VI 2.1–2.3, printed pp. 71–73, especially the completed
chart formulas on p. 73 (PDF page 79), available at
[arXiv:1207.3648](https://arxiv.org/pdf/1207.3648).
The source treats strict local charts; arbitrary residue fields, faces, and twists are
explicitly the algebraic refinement of this DAG node, rather than a verbatim quotation.
The current blueprint unit `literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/
sk-p-dl-a1-perverse/_section.md` was read. This item is an auxiliary local-algebra
statement, not the unit's own Fourier-transform assertion.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Nonzero Noetherian local commutative ring A | `(A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]`; `IsLocalRing` extends `Nontrivial`, so a separate nonzeroness instance was removed after the compiler identified the overlap. |
| Fine saturated R and Q | Independently sized `R : Type v`, `Q : Type w`, each with `CommMonoid`, and `_hR`, `_hQ : AlgebraicGeometry.IsFineSaturatedMonoid ...`. Multiplicative notation expresses the same monoids. |
| Injective h | `h : R →* Q`, `_hinj : Function.Injective h`. |
| Every q has a positive multiple in h(R) | `_hkummer : ∀ q : Q, ∃ (d : ℕ) (_ : 0 < d) (r : R), h r = q ^ d`. Powers are additive multiples in multiplicative notation. |
| Injective group completion map | `_hgp` is injectivity of `GrothendieckGroup.lift ((GrothendieckGroup.of (M := Q)).comp h)`, the actual induced group map. |
| Finite cokernel | `Finite (GrothendieckGroup Q ⧸ (...).range)`, using the group-homomorphism subgroup range. |
| Positive annihilator N invertible in A | `(N : ℕ)`, `_hN : 0 < N`, `_hkill : ∀ q : GrothendieckGroup Q, q ^ N ∈ (...).range`, `_hunit : IsUnit (N : A)`. |
| Chart alpha | `α : R →* A`. |
| G and S = R_G / G^gp | `chartSharpMonoid α` is `Additive (Associates (Localization ((IsUnit.submonoid A).comap α)))`. For these integral monoids this is exactly the canonical fraction localization and quotient by its units, already recorded by `def-per-formal-monoid-extension-data`. |
| Chosen a and unit character epsilon | `a : Multiplicative (chartSharpMonoid α) →* A` and `ε : GrothendieckGroup R →* Aˣ`. |
| Equality on every r in R_G | `_hα` quantifies over the full localization, equating `localizedUnitChart α r` to the character evaluated via `unitChartGroupMap` times a at `Associates.mk r`. It is not restricted to elements of R. |
| C = A tensor over Z[R] Z[Q] | `monoidChartTensor α h`, the actual canonical Mathlib tensor construction with the chart-induced algebra structures. |
| Arbitrary prime q contracting to m_A | `(q : Ideal (monoidChartTensor α h)) [q.IsPrime]` and `_hq : Ideal.comap (monoidChartTensorBase α h) q = IsLocalRing.maximalIdeal A`. |
| B, F, T and J | B is `Localization.AtPrime q`; `localizedTensorMonomial α h q` is its canonical Q-chart; its unit inverse image gives F and `chartSharpMonoid` gives T; `localizedTensorBoundary α h q` is precisely the span of images of Q outside F. |
| Both cases for any finite number n, including zero | A conjunction of two implications, one for each existence-of-presentation hypothesis; each existential `(n : ℕ)` includes zero. Thus neither case is assumed without proving its conclusion and neither characteristic case is dropped. |
| Equal-characteristic completed presentation over k = A/m | `CompletedLocalModel (IsLocalRing.ResidueField A) (chartSharpMonoid α) n ≃+* AdicCompletion (IsLocalRing.maximalIdeal A) A`. The model is the completion of k[S][t] at the stipulated ideal. |
| Compatibility with a(u) in case (a) | The equality for every `s : chartSharpMonoid α` sends the canonical completed monomial to `algebraMap A _ (a (Multiplicative.ofAdd s))`. |
| Cohen coefficient ring V of residue field k | Existential V with `CommRing`, `IsLocalRing`, `p : ℕ`, `IsCohenRing p V`, and `Nonempty (IsLocalRing.ResidueField V ≃+* IsLocalRing.ResidueField A)`. `IsCohenRing` supplies primality, DVR, uniformizer and completeness. |
| Mixed presentation and theta congruent to p modulo nonzero S-monomials and t | `θ : CompletedLocalModel V ... n`, `θ - p ∈ completedLocalModelBoundaryIdeal V ... n`, and a ring equivalence of its quotient by `Ideal.span {θ}` to the maximal-ideal completion of A. This boundary ideal includes the variables, not the coefficient maximal ideal. |
| Compatibility with a(u) in case (b) | The analogous equation for every s passes its canonical monomial through `Ideal.Quotient.mk (Ideal.span {θ})` and the specified equivalence. |
| Nonzero complete regular Noetherian local D and residue kappa(q) | In both cases the conclusion is the already recorded `HasExtendedFormalMonoidModel`: it existentially supplies D with `CommRing`, `Nontrivial`, `IsRegularLocalRing`, maximal-ideal completeness and residue equivalence to `IsLocalRing.ResidueField (Localization.AtPrime q)`, definitionally `q.ResidueField`. Regular local includes Noetherian and local. |
| D[[T]] and the isomorphism of pairs in case (a) | The false branch supplies the equivalence from the maximal-ideal completion of B to `CompletedLocalModel D T 0`, the stipulated completion of D[T] with a zero-variable polynomial wrapper, and `IsAdicPairEquiv` with the actual extended J and nonzero-T ideal. |
| Mixed quotient and reduced eta in m_D minus m_D squared | The true branch supplies eta, the quotient by `Ideal.span {η}`, and a D-algebra equivalence from the nonzero-T stratum to D, with the two explicit membership/nonmembership conditions on eta's reduction. The algebra condition fixes constants and therefore the canonical reduction. |
| Indicated ideals and continuity | `IsAdicPairEquiv` asserts equality of the image ideal with the target ideal, plus continuity of the equivalence and its inverse for the extended defining-ideal adic topologies. In the mixed case both ideals are mapped into the hypersurface quotient. |

Dependency declarations actually used:

- `Sheaf.RingTheory.FormalMonoidExtensionModel`: `Algebra.monoidChartTensor`,
  `monoidChartTensorBase`, `chartSharpMonoid`, `localizedUnitChart`, `unitChartGroupMap`,
  `localizedTensorMonomial`, `localizedTensorBoundary`,
  `AddMonoidAlgebra.IsAdicPairEquiv`, `HasExtendedFormalMonoidModel`.
  All nine recorded helpers were read in full, with their docstrings and real bodies.
- Its public import `Sheaf.RingTheory.LogRegularSaturationNormality`:
  `AddMonoidAlgebra.localModelBoundaryIdeal`, `localModelCompletionIdeal`,
  `CompletedLocalModel`, `completedLocalModelBoundaryIdeal`, all read in full.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup` imports
  `Sheaf.AlgebraicGeometry.LogRegularPair`, whose `AlgebraicGeometry.IsFineSaturatedMonoid`
  gives finite generation, canonical-group-completion injectivity, and saturation.
  The full definition was read. The log-blowup declaration of the broader dependency
  node is not the ring-theoretic notion used here.
- Mathlib: `IsNoetherianRing` (`RingTheory.Noetherian.Defs`), `AdicCompletion` and
  `IsAdicComplete` (`RingTheory.AdicCompletion.Basic` and `Algebra`),
  `TensorProduct` (`LinearAlgebra.TensorProduct.Defs`, with its universal-property
  declarations in `Basic`), `Localization.AtPrime` (`RingTheory.Localization.AtPrime.Basic`),
  `Ideal.ResidueField` (`RingTheory.LocalRing.ResidueField.Ideal`),
  `IsRegularLocalRing` (`RingTheory.RegularLocalRing.Defs`). Their definitions and
  relevant signatures/docstrings were read. The scheme clause of
  `Sheaf.AlgebraicGeometry.IsRegularScheme` is irrelevant here: the dependency's
  `mathlib_match` gives exactly its regular-local-ring clause.
- `WeilConjectures.RingTheory.CohenRing`: `IsCohenRing`, full definition read.

All published available proof dependencies are imported plainly: finite-type
Noetherianity (`Mathlib.RingTheory.FiniteType`), finite-completion factor idempotent,
local-completion quotient, power-series field/Cohen regular completeness,
adic-completion Noetherianity, fs face sharpening, and formal monoid implicit
elimination. Statement imports are public.
Two proof-only records name retired, unavailable source modules:
`Sheaf.RingTheory.FiniteEtaleFormalMonoidCoefficientLift` and
`Sheaf.RingTheory.TameKummerGroupAlgebraCompletion`. Their records explicitly note
withdrawal on 2026-10-20. `scompile.py --source` confirms each is unavailable.
They are omitted from imports, and remain referenced by their DAG IDs in the
complete proof docstring. No statement construction depends on either declaration;
there is no missing statement dependency to repair. The implicit-elimination module
is available under its recorded module path, now attached to the sfb node.

Edge cases checked: n=0 gives no variables; trivial T gives zero boundary and retains
the regular coefficient ring (or its parameter quotient); R or Q may be groups and
may have torsion units; arbitrary faces are obtained from units in the actual prime
localization, not assumed trivial; N=1 and h an isomorphism are admitted; N=0 is
excluded exactly by the positive-integer hypothesis; residue fields need not be
algebraically or separably closed; the mixed congruence permits linear t terms;
theta_0=p mod (t) still has nonzero p cotangent component; no equality between u,v,w
is imposed. The zero ring is excluded by the local-ring class as required.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leansearch "Kummer extension monoid algebra completion regular local ring"`:
  eight unrelated hits including `MonoidAlgebra.isLocalHom_algebraMap`, uniform-space
  completion algebras and the field Kummer extension parser; no match.
- `msearch.py ... leanfinder "Completion of an invertible Kummer monoid extension has a formal monoid ring local model over a complete regular local coefficient ring"`:
  eight hits about BDeRhamPlus, Laurent series and Weierstrass preparation; no match.
- `msearch.py ... loogle "AdicCompletion, MonoidAlgebra"`: zero hits.
- `msearch.py ... grep "Kummer|formalMonoidExtension|HasExtendedFormalMonoidModel" RingTheory`:
  five unrelated Kummer references in AdjoinRoot, roots of unity, and Dedekind-domain files.
- `rg -n 'formalMonoidExtension|completed.*[Kk]ummer|lem-per-completed-invertible-kummer-monoid-extension' lean/Sheaf lean/WeilConjectures`:
  the group-isomorphism theorem `Algebra.formalMonoidExtension_model` is the sole
  nearby model theorem; its hypothesis requires a bijective group map, so it does
  not state this node's general finite-cokernel theorem. Its helper definitions
  supply exactly the needed canonical objects and are reused.
- `rg -n 'Kummer|kummer' lean/Sheaf/RingTheory lean/WeilConjectures/RingTheory`:
  normalization-boundary, finite-Kummer-level, and unrelated field-algebra results;
  no existing completed Kummer monoid extension theorem.
- Direct item-id search in `lean/WeilConjectures`: no hit.

No statement correction, new node or disputed statement is needed. The initially
redundant `Nontrivial A` instance was removed after the compiler's overlap warning;
its mathematical condition is supplied by `IsLocalRing A`.

## Second reading by Q130

As instructed by the dispatcher, no other agent was started. This is the worker's
second reading of the node and finished file; independent review is the maintainer's.
I reread the complete theorem signature against the original node, then unfolded
`HasExtendedFormalMonoidModel`, `IsAdicPairEquiv`, `CompletedLocalModel` and the
chart helpers. The table above records each hypothesis and clause. Particular
checks: the quotient is by the range of the induced group map (not by the monoid
range); the character is evaluated on all fractions; no extension of epsilon to
Q's group completion is assumed; both cases have monomial compatibility; the mixed
congruence ideal includes t variables while the output boundary uses zero variables;
the output residue field is the selected prime's residue field; both directions of
continuity and equality of the actual J-ideal are retained. The only change from
this rereading/compile was deleting the redundant nontriviality instance. No mathematical
mismatch or unresolved fault was found.
