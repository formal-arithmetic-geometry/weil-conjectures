## Worker report

The main module states `WeilConjectures.SystemTensorMate.system_clopen_tensor_compatibility`.
It is equality of the two specified composites in the ordinary unbounded derived
category of actual strict quotient-semilinear module systems. The node statement is
unchanged. One new definition node supplies the missing specialized geometric arrows.
No proof of the tensor interchange is supplied: its proof is `sorry` with the four-step
proof plan in the declaration docstring.

Hypothesis and clause correspondence:

- `K : FiniteFieldDatum` supplies the finite field, characteristic, algebraic closure
  and the algebraic-closure datum recorded by `def-weil-finite-field-fiber`.
  `[Fact l.Prime]` and `_hl : l ≠ K.p` render the prime and different-characteristic
  assumptions. `E`, `[Field E]`, `[Algebra ℚ_[l] E]` and
  `[FiniteDimensional ℚ_[l] E]` render the finite extension. The published coefficient
  rings, not a new quotient construction, are used throughout.
- `R l E X` is `coefficientSequenceCommRingSheaf l E X`; `S` and `D` are explicitly
  the published `SemilinearSections.Mod` and `SemilinearSections.D` on the vertical
  sequence topology. Index `n` means the positive exponent `n+1`. Horizontal maps
  are the published quotient transitions, with their semilinear actions. No flatness
  of a quotient transition is assumed. The original site has object universe `u+1`
  and morphism universe `u`; it is not replaced by an equal-universe site.
- The four `Over` instances and the three instances on each structural morphism
  express separated finite type schemes over the given field. Each of `k,r,p,i`
  is a morphism over that same field. The two open-immersion and quasi-compactness
  instances, two properness instances and `h : k ≫ p = r ≫ i` are the entire square
  hypothesis. There is no cartesian-square assumption.
- `o : TensorOperations l E` is a universal presentation of the canonical operations
  on these fixed actual categories, rather than an extra geometric hypothesis.
  `tensorOperations_nonempty` supplies existence. Pullback is an exact left adjoint
  to the explicitly section-defined direct image; open extension is its exact left
  adjoint. These universal constructions are determined up to their unique
  adjunction-compatible comparisons. The derived functors and adjunctions are the
  published termwise/localization and total-right-derived constructions.
- `coefficient_existsUnique` fixes the coefficient map on every constant section.
  `directComp_existsUnique` fixes composition by restriction along fibre-product
  pasting. `pullComp`, `pComp` and `square` are its adjunction conjugate and
  localization. `laxTensor_existsUnique` fixes the ordinary direct-image tensor map
  on every pure tensor. `ordinary_unit` fixes inverse-image tensor comparison by
  the ordinary unit, and `model` retains the complete published total-summand and
  K-flat normalization of its derived comparison `mu`.
- `ordinaryAlpha` is fixed by a unique open-restriction equation. The existence
  theorem's proof describes exactly open base change followed by identity on the
  clopen component and zero on its complement; it uses the geometric
  `StrictTower.squareLift_clopen`. This characterization includes noncartesian
  squares. `alpha` localizes that actual ordinary map on complexes, and `gamma`
  is exactly its proper-adjunction mate, using `mateEquiv`.
- `projection` is the transpose of `mu.hom` followed by counit tensor identity.
  `deltaInv` is the open-unit transpose followed by `mu.inv`; `deltaInv_isIso`
  supplies its invertibility and `delta` is its inverse. These are the specified
  arrows, with no invertibility premise on `gamma` or `projection`.
- `H : D l E A` and `Q : D l E F` are arbitrary unbounded inputs. The left-hand side
  is `delta_i`, then `i_!(projection_r)`, then `gamma` on
  `H tensor P_r P_i Q`. The right-hand side is `gamma_H tensor id_Q`, then
  `projection_p`, then `R_p(delta_k)` followed by
  `R_p(k_!(id_H tensor square.hom_Q))`. Both have source
  `i_! R_r H tensor Q` and target `R_p k_!(H tensor P_r P_i Q)`.
  Equality is asserted in that system derived category itself, before evaluation
  or derived inverse limit. No Tor, cartesianness of coefficients, boundedness,
  or equality-detection premise is imposed.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its coefficient module:
  the published `Padic.coefficientExtensionRing` and its finite-extension inputs.
- Mathlib's small pro-etale site: `Scheme.ProEt`, `Scheme.ProEt.topology`,
  `Scheme.proEtaleBaseChange`; scheme morphism properties are Mathlib's instances.
- `Sheaf.Paper.SemilinearDerivedSections` and its public model/calculus imports:
  `SemilinearSections.Mod`, `D`, `Data`, `ordinaryTensor`, `tensorSection`,
  `ordinaryTensorHom`, `TensorComparisonModel`, `semilinearDerivedSections`,
  and the published `coefficientSequenceCommRingSheaf`/transition/topology.
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` and its arrows import:
  `AlgebraicGeometry.ProEtale.StrictTower.squareLift_clopen`. Its fixed-coefficient
  categorical arrows are deliberately not reused as varying-ring arrows; only its
  coefficient-independent geometric clopen conclusion is used.
- `Sheaf.SixFunctors.OpenTensorNormalization`:
  `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction` and
  `openTensorNormalization`, with their unit-normalized interpretation.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`, read for
  its projection transpose convention; the specialized projection here writes
  that same counit-defined transpose on the actual system categories.
- The proof dependency `lem-sf-proper-open-projection-mate` has no recorded Lean
  module. Its intrinsic system proof is cited in the main docstring; there is
  consequently no invented import for it.

Edge cases checked in the statements and formulas: identity opens; empty open and
empty schemes; a proper disjoint component in the fibre product (the projector is
zero on that component); arbitrary noncartesian square satisfying the hypotheses;
zero inputs; exponent one at sequence index zero; nonflat quotient transitions;
noncartesian and unbounded coefficient systems. The open projector is fixed by its
restriction to the selected open since its target is extension by zero. No step
asserts that evaluation detects equality of derived morphisms. No statement fault
or `STATEMENT-DISPUTED` remains.

Searches (the verbatim wrapper results are retained in the sandbox search log and
summarized in the new node's `mathlib_searches`):

- LeanFinder: "proper open interchange mate compatible with tensor projection on
  derived coefficient systems"; eight condensed-category results, no match.
- Loogle: `CategoryTheory.mateEquiv_hcomp`; one general mate-pasting result.
- Mathlib grep: `clopen.*tensor|properOpen.*tensor|gamma.*tensor` in CategoryTheory;
  no match.
- LeanSearch: "canonical proper open tensor comparison for strict semilinear
  coefficient systems"; eight related results, no exact interface.
- LeanFinder: "derived tensor of sheaves of modules on inverse ring system diagram
  site"; general tensor results, no exact varying-ring geometric arrows.
- Mathlib grep: `semilinear|varying.*coefficient` in CategoryTheory; unrelated hits.
- Local `rg` searches of `WeilConjectures`, `lean/Sheaf`, the DAG and upstream-name
  index found the published semilinear and fixed-tower interfaces but no exact
  statement or specialized arrow interface. The exact item-id source search had
  no upstream match. `blueprint_refs.py search "system tensor mate arrows"` found
  no existing node; its ancestor command returned the adic reconstruction target.

Sources were read in the local Stacks files: more-etale.tex Tag 0F7B,
sites-modules.tex Tag 0E8I and sites-cohomology.tex Tag 0B56, together with the
current main-20261015 blueprint proof and the dependency declaration docstrings.
The helper declarations are definitions with real data or named postponed
existence/uniqueness/property theorems. Choices of maps occur only after uniqueness
characterizations; no arbitrary map or bare nonempty isomorphism replaces a
canonical construction.

Validation: the prescribed `scompile.py` compiled both delivered modules separately
in dependency order against the server library, with no errors or warnings. The
delivery wrapper additionally recompiles the exact packet and runs server preflight.

## New nodes

`def-pur-system-tensor-mate-arrows` supplies the universal geometric presentation
and the normalized pullback, open, clopen-mate, tensor, projection and open-tensor
arrows needed by the item on the actual varying coefficient systems. Its source
is the vertical-site realization of Zheng Construction 4.1/Lemma 4.10 and Stacks
Tags 0941, 0F7B, 0E8I, 0B56 and 07A4. The searches above found the general
semilinear calculus and the fixed-ring strict-tower calculus, but neither gives
this specialized interface with these section-normalized maps. It reuses their
categories and tensor models, rather than defining a second notion of system.
Every helper's postponed property is included in the new node statement and
recorded in `lean.declarations`.

## Second reading by Q68

The dispatcher's explicit instruction prohibits starting another agent. This
section therefore records a separate rereading by this worker, not a claim of
independent review by another worker; the maintainer's independent delivery review
remains necessary. Reread the node and both modules clause by clause. Checked the
orientation of `square`, both mate adjunctions, the source/target of each composite,
the inverse orientation of `delta`, and that the ordinary coefficient and tensor
normalizations prevent arbitrary transformations. The helper retains distinct
site universes and the ordinary unbounded system localization. The main node has
no statement correction; only its `lean` record and the new definition dependency
are changed.
