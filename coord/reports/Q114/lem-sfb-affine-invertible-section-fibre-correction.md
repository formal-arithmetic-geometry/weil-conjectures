## Worker report

The module `Sheaf.AlgebraicGeometry.AffineInvertibleSectionFibreCorrection` states
`AlgebraicGeometry.Scheme.Modules.exists_affine_invertible_section_fibre_correction`.
Its only theorem proof is `sorry`. There are no new definitions, new nodes, dependency
repairs, or statement corrections. The item's original mathematical statement and
proof remain unchanged. Its `stmt_deps` gains the already landed
`def-weil-pbc-module-residue-fiber`, whose recorded canonical constructions are used
in the signature (brief-stage2 §5 permits adding landed statement dependencies).

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The affine scheme X is `(X : Scheme.{u}) [IsAffine X]`; `u` is explicit and unrestricted.
- The invertible O_X-module L is `(L : X.Modules) [L.IsInvertible]`. This is the recorded
  Zariski local rank-one definition; no additional finiteness or freeness hypothesis
  is imposed on L or its global sections.
- The arbitrary subset F and point z are `(F : Set X) (z : X)`. F has no finiteness,
  closedness, or nonemptiness hypothesis, and z need not be closed.
- The two global sections are `(s : Γ(L, ⊤)) (f : Γ(X, ⊤))`.
- The module residue value s(y) is `residueValue s y trivial`. The already recorded
  construction is `1 ⊗ germ(s)` in `κ(y) ⊗ L_y`. This is canonically the value in
  `L_y / m_y L_y`: Mathlib's `TensorProduct.quotTensorEquivQuotSMul`, specialized to
  `IsLocalRing.maximalIdeal (X.presheaf.stalk y)`, sends `1 ⊗ germ(s)` to the quotient
  class by `quotTensorEquivQuotSMul_mk_one_tmul`. Thus zero, nonzero, and equality of
  residue values in the theorem express exactly those in the node's quotient model.
  No basis, trivialization, or arbitrary identification is chosen in the signature.
- Scalar residue values f(y) are `X.Γevaluation y f`, the germ followed by the actual
  residue map into `X.residueField y`.
- `hs : residueValue s z trivial = 0` is precisely s(z) = 0.
- `hf : X.Γevaluation z f ≠ 0` is precisely f(z) ≠ 0.
- `hF : ∀ x ∈ F, X.Γevaluation x f = 0` is precisely vanishing of f at every x in F.
- The witness `(∃ t : Γ(L, ⊤), ...)` is a global section of the same L.
- The new section v is written explicitly as `s + f • t`; the action is the existing
  global O_X(X)-module structure on Γ(L, X). No extra witness equation is needed.
- The first conclusion `residueValue (s + f • t) z trivial ≠ 0` is v(z) ≠ 0.
- The second conclusion `∀ x ∈ F, residueValue (s + f • t) x trivial =
  residueValue s x trivial` is v(x) = s(x) for every x in F. It asserts equality only
  of residue values, as required, rather than equality of germs or restrictions.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffine`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, with its full local-triviality field.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.residue`,
  `Scheme.evaluation`, `Scheme.Γevaluation`, and the recorded `Scheme.Hom.residueFieldMap`.
- `WeilConjectures.AlgebraicGeometry.Modules.ResidueFiber`:
  `Scheme.Modules.residueFiber` and `Scheme.Modules.residueValue`.
- Proof imports: `Sheaf.AlgebraicGeometry.CoherentFiniteType`, exposing the recorded
  `Scheme.Modules.IsQuasiCoherentFiniteType` and the existing quasi-coherence/finite-type
  predicates; `WeilConjectures.AlgebraicGeometry.AffineFiniteTypeGeneratingSections`,
  `Scheme.Modules.affine_finiteType_generatingSections`;
  `WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre`,
  `Scheme.Modules.invertible_generating_sections_fibre_criterion`.

Source read: `literature/stacks-project/properties.tex`, Tag 0F20,
`properties-lemma-quasi-affine-invertible-nonvanishing-section`, base case (global
 generation and multiplication by a separating function) and induction step (addition).
The declaration docstring gives the accepted four-step DAG proof, including finite
local generation, padding by zero, the recorded fibre criterion, the residue-field
inverse calculation at z, and the value calculation on F.

Edge cases checked before writing:

- Empty X has no z, so the quantified statement is vacuous without excluding empty schemes.
- F empty leaves only nonvanishing at z; F may also be infinite.
- If z belongs to F the hypotheses contradict f(z) ≠ 0; no extra disjointness binder
  is necessary. If f = 0 there is similarly no instance of the hypotheses.
- The zero section s is permitted, and a zero generator family is handled in the
  proof plan by adjoining zero before applying the nonempty-family criterion.
- Nonclosed z is allowed. At the generic point of Spec Z, f = 2 has nonzero residue
  even though it is not a unit globally: the argument uses the residue-field inverse,
  not an inverse in Γ(X, O_X).
- Nonreduced schemes and zero divisors in the global section ring cause no problem:
  the nonvanishing calculation takes place over the actual residue field.
- Characteristic is unrestricted, and preservation is literal addition by zero,
  including characteristic two. No constant coefficient or distinct-scalar assumption.

Searches for an existing statement (all through the prescribed msearch wrapper or
read-only source searches):

- LeanFinder: "On an affine scheme an invertible sheaf has a global section t such
  that s plus f times t is nonzero at a point where s is zero and f is nonzero".
  Eight hits: `exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen`,
  `isLocalization_away_of_isAffine`, `exists_eq_pow_mul_of_isAffineOpen`,
  `StructureSheaf.normalize_finite_fraction_representation`,
  `IsAffineOpen.basicOpen_basicOpen_is_basicOpen`, `exists_of_res_zero_of_qcqs_of_top`,
  `LocallyRingedSpace.Γevaluation_ne_zero_iff_mem_basicOpen`, and
  `Scheme.evaluation_ne_zero_iff_mem_basicOpen`. None constructs the required correction.
- Loogle: `Module.Invertible, "exists"`. Two hits:
  `Module.Invertible.exists_finset_free_localization` and
  `Module.Invertible.exists_linearEquiv_ideal`. These concern ring modules, not the
  specified section correction and residue-value preservation.
- msearch grep, Mathlib/AlgebraicGeometry:
  `nonvanish.*(add|mul)|exists.*section.*(fibre|fiber)|section.*correction`: no hits.
- LeanSearch: "Correct a section of an invertible sheaf on an affine scheme by adding
  f times a global section to be nonzero at a point". Eight hits concerning tilde
  scalar multiplication, scalar-section localization, basic-open membership, and
  structure-sheaf constants. No exact statement.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for residue-fibre/value constructions
  found the existing `Modules.ResidueFiber` module and its consumer uses. Reused those
  definitions and added their existing DAG dependency rather than duplicating them.
- rg in the algebraic-geometry directories for section correction and affine section
  nonvanishing found the finite-set nonvanishing theorem, which has a different
  conclusion and does not state preservation of prescribed residue values.
- Exact item-id search in `lean/WeilConjectures` found no declaration of this item.
  Name search for `affine_invertible_section_fibre_correction` across Mathlib,
  `WeilConjectures`, `Sheaf`, and `dag/lean_names_upstream.json` found no conflict.

Validation: prescribed scompile compiled both sandbox and library module modes cleanly
(5.4 s and 3.9 s respectively), with no errors or warnings. All binders and universes
are explicit; no private definitions, local notation, extra hypotheses, or constructions
using sorry occur. The only admitted result is the assigned theorem.

Independent review is left to the maintainer as specified by the dispatcher brief;
no other agents were started.

## Second reading by Q114

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
