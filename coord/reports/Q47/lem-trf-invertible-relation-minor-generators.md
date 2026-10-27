## Worker report

The module `Sheaf.RingTheory.InvertibleRelationMinorGenerators` states
`LinearMap.invertible_relation_minor_generators`, with its sole proof `sorry`.
There are no new definitions or dependency repairs. The node is unchanged except
for its `lean` record. Its three-step constructive proof is in the theorem docstring;
this is the node's explicitly agent-written refinement of Stacks 07ZC, using 07DQ
and 01HV, rather than a claim that the Stacks proof itself uses elimination.

Hypothesis and clause correspondence:

- A commutative ring and an A-module are the bundled `A : CommRingCat.{u}` and
  `M : ModuleCat.{u} A`. The arbitrary universe `u` is a common universe for the
  ring and module, as in the recorded Mathlib tilde interface. There is no field,
  domain, Noetherian, nonzero-ring, or finite-presentation hypothesis.
- The nonnegative integers are `(a b : ℕ)`. The finite free direct sum is rendered
  by `Fin (a + b) → A`, with standard vectors `Pi.single j 1`.
  The specified surjection is `π` with `hπ : Function.Surjective π`.
- The block matrix is `(C : Matrix (Fin a) (Fin a) A)` and
  `(D : Matrix (Fin a) (Fin b) A)`; `hrel` says exactly
  `∀ k, π (Fin.append (C k) (D k)) = 0`, so every concatenated row is in its kernel.
  No generating assumption on those relations or finite generation of the kernel
  occurs.
- The determinant δ is `C.det`, and the adjugate is the existing `C.adjugate`.
  The cofactor convention is fixed by
  `Matrix.adjugate_fin_succ_eq_det_submatrix`: entry (i,j) deletes row j and column i
  and has sign `(-1)^(j+i)`, equal to the stated sign `(-1)^(i+j)`. Switching the
  paper's one-based indices to Fin's zero-based indices changes the exponent by 2,
  so the sign is identical. Size zero uses Mathlib's empty adjugate.
- The ring A_δ is `Localization.Away C.det`, the module M_δ is
  `LocalizedModule (Submonoid.powers C.det) M`, and m/1 is
  `LocalizedModule.mkLinearMap (Submonoid.powers C.det) M m`.
  `Fin.castAdd b i` indexes the first a generators and `Fin.natAdd a j` the last b.
- The first conjunct, for every `i : Fin a`, is precisely the component equation
  `δ x_i + ∑ k, ∑ j, (adj(C) i k * D k j) • y_j = 0`.
- The second conjunct expresses the same `x_i` as the negative of the inverse δ
  acting on that double sum. `IsLocalization.Away.invSelf C.det` is the inverse
  in the localized ring, rather than a field inverse or an assumed extra datum.
- The third conjunct is
  `Submodule.span (Localization.Away C.det) (Set.range ...) = ⊤`, using exactly
  the localized last b generators, with no newly chosen generating family.
- For the sheaf clause, `tilde M` is the recorded associated sheaf on `Spec A`.
  `(tilde M).over (PrimeSpectrum.basicOpen C.det)` is its restriction to the slice
  site of opens contained in D(δ). Mathlib's `Scheme.Modules.overEquiv` and
  `overFunctorEquiv` identify this with the usual restriction to that open scheme.
  The existential `s` is only the packaging of the specified canonical sections
  as compatible families. For every index j and every open V of that slice,
  `(s j).val V = tilde.toOpen M V.unop.left (π (Pi.single ... 1))` fixes the section
  to the restriction of τ(m_(a+j)). It does not allow arbitrary replacement sections.
  `ULift.{u} (Fin b)` is the same finite family in the universe required by the free
  sheaf API. `Epi (...freeHomEquiv.symm s)` is exactly the `epi` field of the recorded
  `SheafOfModules.GeneratingSections`, hence the requested sheaf-surjectivity/local
  lifting statement; it imposes no sectionwise surjectivity on arbitrary opens.

Dependency declarations read and used:

- `def-weil-matrix`: `Mathlib.LinearAlgebra.Matrix.Defs`, `Matrix`.
- `def-weil-ring-localization-away`:
  `Mathlib.GroupTheory.MonoidLocalization.Away`, `Localization.Away`, with the ring
  structure and inverse from `Mathlib.RingTheory.Localization.Away.Basic`,
  `IsLocalization.Away.invSelf`.
- `def-weil-pbc-module-localization`:
  `Mathlib.Algebra.Module.LocalizedModule.Basic`, `LocalizedModule` and
  `LocalizedModule.mkLinearMap`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec`, used through `tilde M` and its principal open.
- `lem-weil-pbc-spec-module-tilde-sections`:
  `Mathlib.AlgebraicGeometry.Modules.Tilde`, `AlgebraicGeometry.tilde`,
  `AlgebraicGeometry.tilde.toOpen`, `AlgebraicGeometry.tilde.toOpen_res`, and the
  instance localizing `toOpen` on basic opens. The latter two provide the proof plan.
- `def-weil-pbc-generating-sections`:
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`,
  `SheafOfModules.GeneratingSections`, expressed by its fixed-family `Epi` clause
  via `SheafOfModules.freeHomEquiv`.
- `def-weil-pbc-matrix-determinant`:
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`, `Matrix.det`.
- The proof leaf `lem-weil-pbc-matrix-adjugate-identity` is a Mathlib node without
  a `lean` record: its `mathlib_match` is used directly,
  `Mathlib.LinearAlgebra.Matrix.Adjugate`, `Matrix.adjugate_mul` and
  `Matrix.mul_adjugate`, with `Matrix.adjugate_fin_succ_eq_det_submatrix` fixing the
  cofactor convention. This module is public because the signature uses adjugate.
  The four imports publicly expose all statement dependencies; none needs repair.

Edge cases checked before writing:

- a = 0: det of the empty matrix is 1, both component identities are vacuous, and
  the original b generators span; the sheaf clause remains the original generation.
- b = 0: the double sums vanish and the span of the empty family is bottom, so its
  equality with top states exactly that M_δ is zero. The corresponding empty-family
  sheaf epimorphism says the restricted sheaf is zero.
- a = b = 0: surjectivity from the zero module forces M = 0.
- δ = 0, or a nilpotent δ: the localized ring and module are zero and D(δ) is empty;
  the formulas, span assertion and sheaf assertion all still hold.
- The zero ring is admitted by `CommRingCat`. There is no nontriviality assumption.
- One-by-one example: C = (c), D = (d) gives c x + d y = 0 and
  x = -c^(-1)d y, confirming orientation and sign. Over Z/6 with relation
  2m_1 - 2m_2 = 0, localizing at 2 gives m_1 = m_2 as required.

Searches actually run:

- msearch leanfinder: "Invertible relation minor eliminates fixed module generators
  after localization and generates the associated sheaf on a principal open".
  Eight hits on tilde fractions and local-generator data, including
  `ModuleCat.Tilde.const`, `ModuleCat.Tilde.exists_const` and
  `SheafOfModules.LocalGeneratorsData.I`; no exact result.
- msearch loogle: "Matrix.adjugate, Matrix.det, Submodule.span". Zero hits.
- msearch grep in Mathlib/RingTheory: "adjugate|relation.*minor|minor.*relation".
  Four polynomial resultant adjugate hits, none asserting the item.
- msearch leansearch: "Relations with an invertible determinant eliminate fixed
  generators after localization and generate the associated sheaf on the principal
  open". Eight hits on structure-sheaf localizations and principal-open immersions,
  including `StructureSheaf.basicOpenIso`; no exact result.
- Direct rg in both `lean/WeilConjectures` and `lean/Sheaf` for relation/minor and
  adjugate/generator terminology, and the required node-id grep in WeilConjectures:
  no existing declaration of this statement. Related
  `Sheaf.RingTheory.AffinePrincipalFittingGenerators` was opened and concerns a
  local ring and a quotient by Fitting torsion, a different assertion.
- Searched `dag/lean_names_upstream.json` for the item and proposed declaration:
  no match.

No statement dispute, correction, missing notion, or dependency interface fault
was found. The first server scompile run passed both sandbox and library-context
checks (2.4 s and 2.5 s); subsequent delivery checks compile the final file again.
The only postponed theorem is the named item theorem; there is no data `sorry`.

## Second reading by Q47

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
