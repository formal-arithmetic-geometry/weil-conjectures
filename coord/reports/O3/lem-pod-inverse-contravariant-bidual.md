## Worker report

The module `Sheaf.Paper.InverseContravariantBidual` states
`WeilConjectures.podInverseContravariantBidual`, with `sorry`, and constructs the
actual two coefficient-dual structures and coefficient bidual map. It makes no
change to the natural-language statement. The repaired dependency list also names
the two existing definition owners used by the statement.

Source read: current `literature/blueprint/latest/blueprint/sec-poincare-duality/
sk-thm-frobenius/prop-weil-operations.proof.md`, final duality/pairing paragraph,
and current `sec-six-functors/sk-thm-sf-package/
cor-coef-verdier-weil-equivariance.proof.md`, paragraph 2. The latter explicitly
uses the inverse contravariant formula, evaluation, transposition and arbitrary
rational theta without a stable integral lattice. The six accepted proof steps
are reproduced, including both uncurried composites, in the main theorem's
docstring. The node's source path is an older snapshot; the current versions
above were read, as the brief requires.

Hypotheses and clauses, matched individually:

- The global tuple p,a,q,k0,k with p prime, a positive and q=p^a is `D :
  FiniteFieldDatum.{u}`; the structure includes exactly those fields, cardinality
  and the algebraic closure. `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p` give the
  distinct coefficient prime. `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`
  and `[FiniteDimensional (Padic l) E]` give the finite coefficient field.
  `Ω : Type v`, its field/algebra/algebraic-closure instances and
  `ι : E →ₐ[Padic l] Ω` retain the specified embedding inside the fixed closure.
  The arrow itself is at E coefficients and does not depend on that embedding.
- `X₀ : Over (Spec (.of D.k₀))`, `[LocallyOfFiniteType X₀.hom]`,
  `[QuasiCompact X₀.hom]` and `[IsSeparated X₀.hom]` give precisely the separated
  finite-type base scheme. `D.geometricFiber X₀` is its actual base change.
  `D.geometricFrobenius X₀` is id times Spec of the inverse arithmetic Frobenius,
  with its inverse, from the recorded Frobenius module.
- `K : sfWeilComplex D l hl X₀ E` is the recorded fixed-pair category:
  `K.carrier` is the rational bounded constructible object, `K.str` its arbitrary
  rational isomorphism from `sfWeilFrobeniusPullback ...`. No lift of `K.str`,
  lattice, integrality or matrix eigenvalue condition is assumed.
- `hK : IsSfRationalCoefficientSitePerfect ... K.carrier` is the recorded local
  bounded rational finite-projective condition, including rational splittings.
- The coefficient object and its datum c are exactly
  `(FrobeniusCoefficientTwists.rationalWeilLine D l hl X₀ E 0).carrier` and `.str`.
  At twist zero that published construction is the canonical coefficient unit
  and the canonical coefficient inverse-image identification, rationalized.
- `podCoefficientDualPair` feeds precisely `(op K,E_X)` to
  `rationalDerivedInternalHom`; `podCoefficientDual` is its value.
  `podCoefficientBidualPair` similarly feeds `(op Kdual,E_X)` to the same Hom.
  The two named `*_permitted` theorems, both with `sorry`, express the
  well-definedness assertions in the node's proof Step 1, rather than new
  assumptions on the main theorem. Their proof docstrings cite perfect-dual
  stability. They select no mathematical data.
- `podInverseContravariantDatum` first uses `podRationalHomComparison`, which
  is itself the existing evaluation-defined transpose with the canonical
  `canonicalRationalPullbackTensor`. Its invertibility proof is
  `(podRationalHomComparison_laws ...).1.isIso`. It then applies the existing
  Hom functor to the full-subcategory isomorphism
  `theta.symm.op.prod c`. This is literally H(theta inverse,c) after h.
  Thus `podCoefficientDualStructure` and `podCoefficientBidualStructure` are
  the two inverse contravariant formulas in the node, as isomorphisms with
  explicitly constructed inverses. The Hom-first evaluation convention of
  this existing API is equivalent to the node's argument-first convention
  by the recorded signed tensor braiding.
- `podCoefficientBidualMap` uses `podRationalClosed.transpose` on the
  second-dual pair, applied to `pullbackTensorRationalBraiding K Kdual` followed
  by `podRationalClosed.evaluation` on the first-dual pair. The latter is the
  Hom-first counit, equal to argument-first ev after the opposite signed
  symmetry. Transposition with the node's argument-first convention inserts
  the first symmetry, giving exactly `(ev_K sigma_(Kdual,K))^sharp`.
  This is the actual canonical map, not an arbitrary bidual isomorphism.
- The conclusion is `K.str.hom ≫ delta = P.map delta ≫ gamma.hom`.
  Lean composes left to right, so this is exactly
  `delta theta_K = theta_Kdualdual P(delta)`. This is the commuting equation
  defining an arrow in the recorded fixed-pair category.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `geometricFiber`.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `FiniteFieldDatum.geometricFrobenius` (actual semilinear automorphism).
- `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleRationalHomPairs`,
  `rationalDerivedInternalHom`, `rationalDerivedPullback`, `rationalDerivedTensor`.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilComplex`,
  `sfWeilFrobeniusPullback`, `sfWeilPrimeInvertible`.
- `Sheaf.Paper.SitePerfectComplex`: `IsSfRationalCoefficientSitePerfect`.
- `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical`:
  `FrobeniusCoefficientTwists.rationalWeilLine`, `rationalDerivedLineMap` at zero.
- `Sheaf.Paper.DerivedAutomorphismHomEvaluation`: `PodPartialClosed.transpose`,
  `.evaluation`, `podRationalClosed`, `podRationalHomComparison`,
  `podRationalHomComparison_laws`; the latter's full compatibility structure
  includes actual evaluation, transposition and arbitrary-rational naturality.
- Proof imports retain `sfPerfectDualPairAndTateStability`,
  `completedTensorHomTranspose`, `rationalTensorSymmetry_laws`, and
  `derivedPullbackTensorIso` from their recorded modules. In particular the
  specified `pullbackTensorRationalBraiding` comes from the pullback tensor
  coherence module. Nothing from these proofs is redefined privately.

All variables and universes are explicitly bound, with autoImplicit and
relaxedAutoImplicit false. The type of Ω has its own universe. The scheme,
coefficient and finite-field universe convention follows the recorded categories.
There is no independent test-object universe or added equality of site universes.
Every definition contains real data. The only postponed theorems are
`podCoefficientDual_permitted`, `podCoefficientBidual_permitted`, and
`podInverseContravariantBidual`, all owned by this node and listed in its
`lean.declarations`. The first two are exactly the domain well-definedness
parts of its already accepted Step 1, not new independent assertions or nodes.

Edge cases checked before writing and against the final formulas:

- At a point, K=E and theta=l are allowed as arbitrary arrows in the localized
  category. Inverse contravariance gives l inverse, then l again; delta is the
  ordinary signed evaluation identification. No integrality predicate occurs.
- For the zero complex, its duals and all the displayed maps are zero; the
  inverse structures on zero are still categorical isomorphisms. No nonzero
  or nonempty hypothesis occurs. The empty scheme is also retained.
- For a shifted coefficient line the braiding retains the Koszul sign; neither
  symmetry in the bidual construction nor in the comparison is silently erased.
- Arbitrary invertible matrices give inverse transpose, then the original
  matrix under evaluation; the statement is not restricted to scalar theta.
- No smoothness, purity, properness or dimension bound has been added.

Searches made (actual commands/results):

- msearch leanfinder: "Coefficient evaluation bidual transpose is equivariant
  for inverse contravariant rational Weil data" returned eight module-dual and
  root-pairing results (including `Module.Dual.eval_naturality`), no exact result.
- msearch loogle: "CategoryTheory.WeilEquivariance, biduality,
  isWeilEquivariant" returned zero hits with unknown identifier
  `CategoryTheory.WeilEquivariance`; this is not treated as a successful
  negative semantic search. The follow-up `Module.Dual.eval_naturality`
  returned that module theorem, which concerns ordinary modules, not these
  partial derived coefficient operations.
- msearch grep: `bidual|toIhomIhom|dualWeilDatum` and follow-up `toIhomIhom`,
  subdirectory CategoryTheory, returned zero hits.
- Direct rg over Mathlib CategoryTheory/Monoidal/Closed, project Sheaf, and
  WeilConjectures found the generic
  `CategoryTheory.MonoidalClosed.isWeilEquivariant_toIhomIhom` in
  `WeilConjectures.CategoryTheory.WeilEquivariance`. Its full signature and
  docstring were read: it assumes a monoidal closed category and a braided
  functor, and does not state the rational specialization on the permitted Hom
  domain or its normalization. It is useful formal background, not an exact
  existing statement of this node. The already published coefficient bidual
  invertibility statement `sitePerfect_rational_bidual` was also read; it has
  a universal Hom-domain hypothesis and no Frobenius conclusion, so cannot
  replace this node's statement.
- Direct rg for `lem-pod-inverse-contravariant-bidual` in WeilConjectures and
  Sheaf found no existing declaration. Searches for all new full-name suffixes
  in `dag/lean_names_upstream.json`, Mathlib CategoryTheory, WeilConjectures and
  Sheaf found no collision. Existing dual/bidual helpers were inspected and the
  delivered helpers only apply the published partial Hom and evaluation APIs.

The returned H2 ownership omission is repaired below. No natural-language
statement correction, dependency module repair, or disputed statement.
No new DAG nodes. No source files outside the assigned sandbox were edited.

Validation: prescribed scompile.py compiled the delivered file twice (private
sandbox and library-name validation) cleanly, with no non-sorry warnings.
The server additionally compiled its landed-but-not-published perfect-dual
proof dependency as an overlay. Delivery preflight is run with deliver2.py.

## Repair of returned delivery e1b460c8da71

The return has one point, H2: two definitions used by the delivered statement
were not named in stmt_deps. Added both existing nodes, preserving every previous
dependency, including lem-pod-derived-automorphism-hom-evaluation:

- `def-sf-rational-common-tensor-symmetries` owns the existing
  `WeilConjectures.pullbackTensorRationalBraiding` and its uniqueness theorem
  in `Sheaf.Paper.DerivedPullbackTensorIso`. Its rational signed symmetry is
  exactly the symmetry used by `podCoefficientBidualMap`.
- `def-pod-partial-closed-interfaces` owns the existing `PodPartialClosed`,
  its transpose field, evaluation, and permitted-pair functor in
  `Sheaf.Paper.DerivedAutomorphismHomEvaluation`. These are exactly the partial
  closed interfaces used by the statement definitions. The automorphism-Hom
  lemma remains a dependency because its unique constructions supply
  `podRationalClosed` and `podRationalHomComparison`.

Read both existing node statements and Lean ownership records and reopened the
actual declarations and docstrings. Their modules were already imported, so
the Lean module is unchanged from the returned immutable head. The sandbox
node was compared with current main before editing: all fields other than lean
matched. The repaired node is current main plus its retained lean record and
these two appended stmt_deps; no mathematical statement, proof, or proof_deps
changes. The prescribed delivery wrapper rebases the packet on current main.

The return otherwise accepted the hypotheses, canonical inverse contravariant
formulas, signed transpose, Weil-arrow equation and the two Step-1 domain facts.
Those remain unchanged. Validation is repeated with scompile.py, deliver2.py
--no-push, then deliver2.py as required.

## Second reading by O3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
