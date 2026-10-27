## Worker report

Stage 2, Q89, lem-trf-diagonal-taylor-faithful-flatness.

The previous worker's ending concerned stage 1, not this assignment. The current
node is split, reviewed PASS for Q58, has no Lean record, and occurs in queue.tsv
at stage 2. The explicit stage-handoff paragraph in coord/brief-stage2.md §0
authorizes recording its statement without reopening the accepted split. No repair
note for this item is present. The accepted statement and all proof steps are
preserved verbatim; only lean is added to the copied node.

The module Sheaf.AlgebraicGeometry.DiagonalTaylorFaithfulFlatness states
AlgebraicGeometry.diagonalTaylor_faithfullyFlat with one sorry. Its eight-step
docstring reproduces the mathematical proof and names the dependencies. All other
declarations are concrete constructions or structures packaging conclusions;
there are no additional postponed lemmas or new independent notions.

Clause-by-clause correspondence:

* The field is `k : Type u`, `[Field k]`; `U : Scheme.{u}` and `n : ℕ`
  allow every nonnegative dimension and every scheme in that universe.
* The coordinate chart is `c : MvPolynomial (Fin n) k →+* Γ(U, ⊤)`.
  By the Gamma-Spec adjunction this is precisely a morphism from U to the
  polynomial spectrum. This is the usual affine presentation of affine n-space
  over k; Mathlib's `AffineSpace.SpecIso` and renaming between `Fin n` and
  `ULift (Fin n)` give the stated presentation. `hchart` says this morphism is
  etale. Its composite with constants defines the structure map to Spec k, and
  `hft`, `hqc` say exactly that this map is of finite type, namely locally of
  finite type and quasi-compact. Thus the chart is over this structure map;
  no unrelated algebra structure is supplied.
* `b : U` is unrestricted. Its residue field is the actual `U.residueField b`,
  the field quotient of the intrinsic stalk by its maximal ideal. Neither b
  being closed nor its residue extension being algebraic is assumed.
* Every affine neighbourhood is quantified as `V : U.Opens`,
  `hV : IsAffineOpen V`, `hb : b ∈ V`. Its actual section ring is `Γ(U,V)`.
  `diagonalTaylorAffineAt` equips it with the chart's k-algebra structure, and
  equips the coefficient field with the structure induced by residue evaluation.
  The germ is `U.presheaf.germ V b hb`, and evaluation is `U.evaluation V b hb`.
* `DiagonalTaylorAffineData.augmentation` has domain `A ⊗[k] K`, and
  `augmentation_tmul` fixes its value to `e a * l` on every pure tensor.
  For K = L this is precisely epsilon of the node. Its kernel is J;
  `maximal` records that it is maximal. Thus this datum is the diagonal rational
  point of the affine part of U_K, not an arbitrarily chosen point. There is no
  need to separately choose a scheme point already specified by this kernel.
* P is `MvPolynomial (Fin n) K`, I is Mathlib's `MvPolynomial.idealOfVars`.
  `diagonalTaylorCentered` is evaluation sending X_i to x_i tensor 1 minus
  1 tensor e(x_i), with coefficients in the right tensor factor.
* `quotient q hq` is P/I^q ≃ C/J^q; `quotient_mk` fixes it to the centered
  map on polynomial representatives. `quotient_reduction` specifies reduction
  compatibility. `localQuotient q hq` is C/J^q ≃ C_J/(JC_J)^q;
  `localQuotient_mk` fixes it to localization and
  `localQuotient_reduction` specifies its reduction compatibility. Every q ≥ 1
  occurs, not just an eventual range of q.
* `diagonalTaylorLocalRing` is `Localization.AtPrime (RingHom.ker e)`;
  it installs the concrete primality proof `RingHom.ker_isPrime`. Its localization
  map is Mathlib's algebraMap. Its ideal is `Ideal.map` of the kernel. These
  small wrappers only make a concrete localization usable without asking the
  statement's consumer to supply an extra primality instance.
* `completion` is a ring equivalence from `AdicCompletion (JC_J) C_J` to
  `MvPowerSeries (Fin n) K`. Its `completion_projection` fixes every positive
  projection of its inverse to the composite quotient maps applied to
  `S.truncTotal q`. Thus this is exactly the inverse-limit equivalence of the
  node, not an arbitrary ring equivalence or an unnormalized choice.
* `stalkEquiv` identifies A_p with the actual stalk; its formula on localization
  of every section fixes the identification. `localMap_germ` fixes the first
  arrow of the displayed composite to the localization of a ↦ a tensor 1.
  `factorization` fixes T to completion followed by the normalized equivalence.
  These representative formulas specify canonical maps using the universal
  properties of localization and completion, without arbitrary-map hypotheses.
* The main existential T is a homomorphism on the intrinsic stalk, before
  quantifying over affine neighbourhoods. The same T admits the displayed
  factorization on every such neighbourhood. This is exactly affine-neighbourhood
  independence. It does not merely assert unrelated maps exist on each affine.
* `T.FaithfullyFlat` is faithful flatness of that homomorphism.
  The next conjunct is the residue/constant-coefficient formula for every stalk
  element, including fractions; the coordinate conjunct sends the germ of x_i
  to C(x_i(b)) + X_i. The factorization also pins scalar coefficients.
* Every extension is quantified as `K : Type (max u v)`, `[Field K]`,
  `i : U.residueField b →+* K`. A homomorphism of fields is injective. The
  universe dominates the residue field's universe; there is no vacuous small
  test-field condition. v is independently arbitrary, permitting larger fields.
  The Taylor map over K is explicitly `(MvPowerSeries.map i).comp T`.
* `DiagonalTaylorAffineExtension.tensorMap_tmul` fixes the tensor map.
  `quotientMap_mk`, `quotient_square` express its quotient maps and commutation
  with coefficientwise polynomial extension. `localMap_localization` fixes its
  localization; `localMap_stalk` expresses compatibility on the source stalk.
  `localQuotientMap_mk`, `localQuotient_square` give the localized quotient
  squares. `completion_projection` specifies the map induced on compatible
  sequences, and `completion_square` identifies it with `MvPowerSeries.map i`.
  This includes compatibility on A and on A_p through the germ formulas.
* `n = 0` is included in every binder: `Fin 0` is empty, the variable ideal is
  zero, and all quotient and projection formulas still apply. No positive
  dimension premise is introduced.

Dependency interfaces read and used:

* def-weil-field: `Field`, Mathlib.Algebra.Field.Defs.
* def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType, and
  `AlgebraicGeometry.QuasiCompact`, Morphisms.QuasiCompact.
* def-weil-etale-morphism: `AlgebraicGeometry.Etale`,
  Mathlib.AlgebraicGeometry.Morphisms.Etale.
* def-sbc-affine-space: `AlgebraicGeometry.AffineSpace`, and its `SpecIso`,
  Mathlib.AlgebraicGeometry.AffineSpace. The theorem uses the equivalent
  polynomial-spectrum presentation to keep the coordinate indices `Fin n`.
* def-weil-residue-field: `Scheme.residueField`, `Scheme.residue`,
  `Scheme.evaluation`, Mathlib.AlgebraicGeometry.ResidueField.
* def-pc-fibre-product: `CategoryTheory.Limits.pullback` and its projections,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback. The affine base
  change is represented by its tensor-ring presentation, as in the source.
* def-weil-pbc-mv-polynomial-ring: `MvPolynomial`, `MvPolynomial.eval₂Hom`,
  Mathlib.Algebra.MvPolynomial.Basic / Eval; `MvPolynomial.idealOfVars` from
  Mathlib.RingTheory.MvPolynomial.Homogeneous. Every variable ideal is this
  existing Mathlib notion, not a duplicate span definition.
* def-weil-pbc-localization-at-prime: `Localization.AtPrime`,
  Mathlib.RingTheory.Localization.AtPrime.Basic.
* def-weil-pbc-adic-completion: `AdicCompletion` and `AdicCompletion.evalₐ`,
  Mathlib.RingTheory.AdicCompletion.Basic / Algebra.
* def-weil-pbc-multivariate-power-series: `MvPowerSeries`, its `map` and
  `truncTotal`, Mathlib.RingTheory.MvPowerSeries.Basic / Trunc / Equiv.
* def-weil-pbc-faithfully-flat-ring-map: `RingHom.FaithfullyFlat`,
  Mathlib.RingTheory.RingHom.FaithfullyFlat, and the recorded module definition
  `Module.FaithfullyFlat` in Flat.FaithfullyFlat.Basic.

The proof imports include the recorded
`Ideal.formallyEtale_powerQuotient_associatedGraded` from
Sheaf.RingTheory.FormallyEtaleAssociatedGraded and
`AlgebraicGeometry.affine_triple_tensor_base_change` from
WeilConjectures.AlgebraicGeometry.AffineTripleTensorBaseChange, together with
the Mathlib modules named by the other proof-dependency matches. The rational-point
Taylor-isomorphism proof node has no Lean statement yet, so it has no module to
import. It is a proof dependency, not a missing notion needed to state this item.

Edge cases checked before and while drafting: q = 1 gives the residue quotient;
q = 0 is not asserted as a Taylor-neighbourhood conclusion (the naturality map
on its zero ring is harmless). For n = 0 the polynomial and series rings reduce
to the coefficient field and no coordinate is requested. For an empty U there is
no b, as in the node. At the generic point of A^1, L = k(t), the image of t is
t + X; the localization formulas allow inverses of all nonzero polynomials,
since their residues are nonzero. This retains the relative coordinate and does
not confuse completion of the original stalk with completion after diagonal
base change. Arbitrary characteristic is permitted. K = L with i = identity is
included, as are transcendental and arbitrarily large coefficient extensions.
The representative formulas also fix the localized and completed maps when n = 0.

Searches made with the prescribed msearch.py wrapper:

* LeanFinder: "An etale coordinate chart at any scheme point gives a faithfully
  flat Taylor map to power series over its residue field through diagonal base
  change and completion". Eight hits, headed by
  `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial` and
  `Algebra.IsEtaleAt`; none states the node.
* Loogle: "RingHom.FaithfullyFlat, AdicCompletion, MvPowerSeries". Zero hits.
* grep, RingTheory: "Taylor|taylor|of_flat_of_isLocalHom". Twenty-two hits,
  including polynomial Taylor equivalences and the flat-local faithful-flat
  theorem; none constructs this diagonal completion or states its naturality.
* LeanSearch: "Etale coordinates give a faithfully flat Taylor map on the local
  ring at an arbitrary scheme point to formal power series over its residue
  field". Eight hits, including `Algebra.Etale.formallyEtale`, `RingHom.Etale`,
  and `Polynomial.taylorEquiv`; no matching combined theorem.
* rg in lean/WeilConjectures and lean/Sheaf for the exact item id,
  `diagonalTaylor`, and `diagonal_taylor`: no existing declaration. Broader Taylor
  searches found the parent ImplicitTaylorCoordinateCalculus module and its
  downstream users, and `isTaylorMap` in RegularHilbertCoefficientDatum. That
  predicate only records coordinate/residue formulas; it does not state the
  quotient/completion/naturality and faithful-flatness assertion here. It is
  not copied. Searches of Mathlib MvPowerSeries supplied the existing variable
  ideal, finite total truncation, and adic-completion projection interfaces.

Source checked directly in literature/stacks-project/algebra.tex: the complete
statements and proofs of lemma-formally-etale-lift-infinitesimal (0H1D),
lemma-local-flat-ff (00HR), and lemma-completion-faithfully-flat (00MC).
They agree with the accepted Q58 assembly. There is no statement correction,
no new node, and no STATEMENT-DISPUTED issue.

Validation: the initial server compilation exposed an underdetermined tensor
base ring in helper applications. Explicit `(k := k)` arguments repaired it.
Subsequent server compilation passed both sandbox and library module checks.
The final packet is checked again by the required scompile.py and deliver2.py
dry run before pushing. No global build or direct shared-repository edit was run.

Final dry run: deliver2.py --no-push printed OK for commit 4384c10e392,
including preflight and per-file compilation. One intervening compiler run with
the complete proof imports timed out at 60 seconds; the required dry run then
passed unchanged with those imports retained. No limit was changed.

## Second reading by Q89

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
